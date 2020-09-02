use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};
use crate::Engine;
use crate::pairing::ff::*;
use crate::SynthesisError;
use crate::worker::Worker;
use crate::plonk::polynomials::*;
use crate::plonk::fft::cooley_tukey_ntt::*;


// Custom gadget for range constraint for a 32-bit number x represented
// We can represent x via 16 constituent base-4 'quads' {q_0, ..., q_15}:
// i.e. x = \sum_{i=0}^{15} q_i 4^i.
// In program memory, we place an accumulating base-4 sum of x {a_0, ..., a_15}, where
// a_i = \sum_{j=0}^{i} q_{15-j} 4^{i-j}.
// From this, we can use our range transition constraint to validate that
// a_{i+1} - 4 a_{i}  ϵ [0, 1, 2, 3].
// We place our accumulating sums in program memory in the following sequence:
//
// +-----+-----+-----+-----+
// |  A  |  B  |  C  |  D  |
// +-----+-----+-----+-----+
// | a2  | a1  | a0  |  0  |
// | a6  | a5  | a4  | a3  |
// | a10 | a9  | a8  | a7  |
// | a14 | a13 | a12 | a11 |
// |  ?  |  ?  |  ?  | a15 |
// +-----+-----+-----+-----+
//
// on the basis of this primitive we are going to bield Excract32 gadget which gets the lese 32 bits of an integer in the case
// of (at maximum 2-bit overflow)
// more precisely for given x of bitlength at maximal 34, we take y = x[0:32] - construct the previous table for x
// where the last row will be of the form:
//
// +-----+------+------+-----+
// |  A  |  B   |  C   |  D  |
// +-----+------+------+-----+
// |  x  | of_l | of_h |  y  | 
// +-----+------+----- +-----+
//
// with the following set of custom constraints (applied for the last row only):
// x = y + of_l * 2^32 + of_h * 2^34
// of_l * (of_l - 1) * (of_l - 2) * (of_l - 3) = 0 - to assure that lower overflow_bit is in range [0; 3]
// of_h * (of_h - 1) * (of_h - 2) * (of_h - 3) = 0 - to assure that higher overflow_bit is in range [0; 3]
// the last two equations are checked by a combination of MainGate and a Custom In04Range gate over columns B and C

// for additional generality we alow x to be represented in sparse form (with particular base)
// (such an extended version of gadget will be of certain use for us in sigma_1 function)
// binary version of gadget is than equal to our generalized gadget with base = 2 
// for the composition of two successive rows 
// +-----+-----+-----+-----+
// |  A  |  B  |  C  |  D  |
// +-----+-----+-----+-----+
// | a3  | a2  | a1  | a0  |
// |-----+-----|-----+-----+
// | b3  | b2  | b1  | b0  |
// +-----+-----+-----+-----+
//
// we require the following set of equations to hold:
// a1 - base^2 * a0 \in [0, 1, base, base+1]
// a2 - base^2 * a1 \in [0, 1, base, base+1]
// a3 - base^2 * a2 \in [0, 1, base, base+1]
// b0 - base^2 * a3 \in [0, 1, base, base+1]
#[derive(Clone, Debug, Hash, Default)]
pub struct RangeCheckConstraintGate;

impl<E: Engine> GateInternal<E> for RangeCheckConstraintGate {
    fn name(&self) -> &'static str {
        "RangeCheck32ConstraintGate"
    }
    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn degree(&self) -> usize {
        4
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);
        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);
        vec![
            PolyIdentifier::GateSetupPolynomial(name, 0)
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
            PolyIdentifier::VariablesPolynomial(3),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        false
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        4
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        assert!(last_row == false, "can not be applied at the last row");
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1);

        let name = <Self as GateInternal<E>>::name(&self);
        let base = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, 0), row);

        let one = E::Fr::one();
        let mut base_plus_one = base.clone();
        base_plus_one.add_assign(&one);
        let mut base_squared = base.clone();
        base_squared.square();

        for (high, high_and_low) in [
            (d_value, c_value),
            (c_value, b_value),
            (b_value, a_value),
            (a_value, d_next_value),
        ].iter() {
            let mut shifted_high = *high;
            shifted_high.mul_assign(&base_squared);

            let mut low = *high_and_low;
            low.sub_assign(&shifted_high);

            let mut total = low;
            
            let mut tmp = low;
            tmp.sub_assign(&one);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&base);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&base_plus_one);
            total.mul_assign(&tmp);

            if !total.is_zero() {
                return total;
            }
        }

        E::Fr::zero()
    }

    fn contribute_into_quotient(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
       
        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
            ensure_in_map_or_create(&worker, 
                p, 
                domain_size, 
                omegas_bitreversed, 
                lde_factor, 
                coset_factor, 
                monomials_storage, 
                poly_storage
            )?;
        }

        let ldes_storage = &*poly_storage;

        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        );

        let mut tmp = a_ref.clone(); // just allocate, we don't actually use it
        drop(a_ref);

        let a_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
            ldes_storage
        ).as_ref();

        let b_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
            ldes_storage
        ).as_ref();

        let c_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
            ldes_storage
        ).as_ref();

        let d_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
            ldes_storage
        ).as_ref();

        let d_next_raw_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
            ldes_storage
        ).as_ref();

        let name = <Self as GateInternal<E>>::name(&self);
        let base_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
            ldes_storage
        ).as_ref();

        let one = E::Fr::one();
        // c - base^2 * d \in [0, 1, base, bae+1]
        // b - base^2 * c \in [0, 1, base, base+1]
        // a - base^2 * b \in [0, 1, base, base+1]
        // d_next - base^2 * a \in [0, 1, base, base+1]

        tmp.map_indexed(&worker,
            |i, el| {
                let a_value = a_raw_ref[i];
                let b_value = b_raw_ref[i];
                let c_value = c_raw_ref[i];
                let d_value = d_raw_ref[i];
                let d_next_value = d_next_raw_ref[i];
                let base_value = base_ref[i];

                let mut base_plus_one = base_value.clone();
                base_plus_one.add_assign(&one);
                let mut base_squared = base_value.clone();
                base_squared.square();

                let mut result = E::Fr::zero();

                for (contribution_idx, (high, high_and_low)) in [
                    (d_value, c_value),
                    (c_value, b_value),
                    (b_value, a_value),
                    (a_value, d_next_value),
                ].iter().enumerate() {
                    let mut shifted_high = *high;
                    shifted_high.mul_assign(&base_squared);

                    let mut low = *high_and_low;
                    low.sub_assign(&shifted_high);

                    let mut total = low;
                    
                    let mut tmp = low;
                    tmp.sub_assign(&one);
                    total.mul_assign(&tmp);

                    let mut tmp = low;
                    tmp.sub_assign(&base_value);
                    total.mul_assign(&tmp);

                    let mut tmp = low;
                    tmp.sub_assign(&base_plus_one);
                    total.mul_assign(&tmp);

                    total.mul_assign(&challenges[contribution_idx]);

                    result.add_assign(&total);
                }

                *el = result;
            }, 
        );

        Ok(tmp)
    }

    fn contribute_into_linearization(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
    fn contribute_into_verification_equation(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
            .ok_or(SynthesisError::AssignmentMissing)?;

        let name = <Self as GateInternal<E>>::name(&self);
        let base = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        
        let mut result = E::Fr::zero();

        let one = E::Fr::one();
        let mut base_plus_one = base.clone();
        base_plus_one.add_assign(&one);
        let mut base_squared = base.clone();
        base_squared.square();

        for (contribution_idx, (high, high_and_low)) in [
            (d_value, c_value),
            (c_value, b_value),
            (b_value, a_value),
            (a_value, d_next_value),
        ].iter().enumerate() {
            let mut shifted_high = *high;
            shifted_high.mul_assign(&base_squared);

            let mut low = *high_and_low;
            low.sub_assign(&shifted_high);

            let mut total = low;
            
            let mut tmp = low;
            tmp.sub_assign(&one);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&base);
            total.mul_assign(&tmp);

            let mut tmp = low;
            tmp.sub_assign(&base_plus_one);
            total.mul_assign(&tmp);

            total.mul_assign(&challenges[contribution_idx]);

            result.add_assign(&total);
        }

        Ok(result)
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }

    fn contribute_into_linearization_commitment(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        _challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
}

impl<E: Engine> Gate<E> for RangeCheckConstraintGate {}


// SparseInrangeCheck: for given base (which will be contained in additional this gate-specific setup selector)
// check that x has one of the following values: [0, 1, base, base + 1]
// the motivation for introduction of this gate is the following: 
// we will often meet the following pattern x = x_0 + x_1 * base
// and we want to simultaneously verify that both [x_0, x_1] are bits
// this is equivalent to x having one of 4 possible values mentioned before
// the most useful case is to handle two succesive bits of binary representaion : for this we well have base = 2
// note that this custom gate may as well check if x is a single bit: simply lay base = 0
#[derive(Clone, Debug, Hash, Default)]
pub struct SparseRangeGate {
    column_idx : usize,
}

impl SparseRangeGate {
    pub fn new(column_idx: usize) -> Self {
        SparseRangeGate { column_idx }
    }
}


impl<E: Engine> GateInternal<E> for SparseRangeGate {
    fn name(&self) -> &'static str {
        "sparse range check gate"
    }

    fn degree(&self) -> usize {
        4
    }

    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);
        vec![
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, self.column_idx)),
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(self.column_idx)),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);
        vec![
            PolyIdentifier::GateSetupPolynomial(name, self.column_idx),
        ]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![
            PolyIdentifier::VariablesPolynomial(self.column_idx),
        ]
    }

    fn benefits_from_linearization(&self) -> bool {
        false
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        vec![]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![]
    }

    fn num_quotient_terms(&self) -> usize {
        1
    }

    fn verify_on_row<'a>(&self, row: usize, poly_storage: &AssembledPolynomialStorage<'a, E>, _last_row: bool) -> E::Fr {
        let name = <Self as GateInternal<E>>::name(&self);
        let q = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(self.column_idx), row);
        let base = poly_storage.get_poly_at_step(PolyIdentifier::GateSetupPolynomial(name, self.column_idx), row);
        
        // q * (q - 1) * (q - base) * (q - base - 1)
        let mut res = q.clone();
        
        let mut tmp = q.clone();
        tmp.sub_assign(&E::Fr::one());
        res.mul_assign(&tmp);

        let mut tmp = q.clone();
        tmp.sub_assign(&base);
        res.mul_assign(&tmp);

        let mut tmp = q;
        tmp.sub_assign(&E::Fr::one());
        tmp.sub_assign(&base);
        res.mul_assign(&tmp);

        res
    }

    fn contribute_into_quotient<'a, 'b>(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<'a, E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<'b, E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
        
        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
            ensure_in_map_or_create(&worker, 
                p, 
                domain_size, 
                omegas_bitreversed, 
                lde_factor, 
                coset_factor, 
                monomials_storage, 
                poly_storage
            )?;
        }

        let ldes_storage = &*poly_storage;

        let column_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(self.column_idx)),
            ldes_storage
        );

        let mut tmp = column_ref.clone();
        drop(column_ref);

        let name = <Self as GateInternal<E>>::name(&self);
        let base_ref = get_from_map_unchecked(
            PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, self.column_idx)),
            ldes_storage
        );

        let one = E::Fr::one();

        tmp.map1(&worker, base_ref,
            |el, base| {
                let x = *el;

                let mut tmp = x.clone();
                tmp.sub_assign(&one);
                el.mul_assign(&tmp);
                
                tmp = x.clone();
                tmp.sub_assign(&base);
                el.mul_assign(&tmp);

                tmp = x;
                tmp.sub_assign(&base);
                tmp.sub_assign(&one);
                el.mul_assign(&tmp);
            }, 
        );

        // TODO: think more carefully, if index here is indeed 0
        tmp.scale(&worker, challenges[0]);

        Ok(tmp)
    }

    fn contribute_into_linearization<'a>(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _monomials_storage: & AssembledPolynomialStorageForMonomialForms<'a, E>,
        _challenges: &[E::Fr],
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
    fn contribute_into_verification_equation(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        assert_eq!(challenges.len(), 1);
        let value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(self.column_idx)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let name = <Self as GateInternal<E>>::name(&self);
        let base = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, self.column_idx)))
            .ok_or(SynthesisError::AssignmentMissing)?;
        
        let mut result = value;
        let x = result.clone();

        let mut temp = x.clone();
        temp.sub_assign(&E::Fr::one());
        result.mul_assign(&temp);

        temp = x.clone();
        temp.sub_assign(&base);
        result.mul_assign(&temp);

        temp = x;
        temp.sub_assign(&base);
        temp.sub_assign(&E::Fr::one());
        result.mul_assign(&temp);

        result.mul_assign(&challenges[0]);        
        Ok(result)
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }
    fn contribute_into_linearization_commitment(
        &self, 
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        _challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
}

impl<E: Engine> Gate<E> for SparseRangeGate {}



