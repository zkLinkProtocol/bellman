use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::pairing::{Engine};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::worker::Worker;
use crate::plonk::domains::*;
use crate::plonk::polynomials::*;

pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;
pub use super::lookup_tables::*;

use crate::plonk::fft::cooley_tukey_ntt::*;

use super::utils::*;

pub trait Circuit<E: Engine> {
    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError>;
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolynomialInConstraint {
    VariablesPolynomial(usize, TimeDilation),
    WitnessPolynomial(usize, TimeDilation),
    SetupPolynomial(&'static str, usize, TimeDilation)
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum Coefficient {
    PlusOne,
    MinusOne,
    Other
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum PolyIdentifier {
    VariablesPolynomial(usize),
    WitnessPolynomial(usize),
    SetupPolynomial(&'static str, usize),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TimeDilation(pub usize);

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct PolynomialMultiplicativeTerm(pub Coefficient, pub Vec<PolynomialInConstraint>);

impl PolynomialMultiplicativeTerm {
    fn degree(&self) -> usize {
        self.1.len()
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) struct PolynomialOpeningRequest {
    pub(crate) id: PolyIdentifier,
    pub(crate) dilation: TimeDilation,
}

pub trait GateInternal<E: Engine>: Send 
    + Sync 
    + 'static 
    + std::any::Any 
    + std::fmt::Debug
{
    fn name(&self) -> &'static str;
    fn degree(&self) -> usize;
    fn can_include_public_inputs(&self) -> bool;
    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint>;
    fn setup_polynomials(&self) -> Vec<PolyIdentifier>;
    fn variable_polynomials(&self) -> Vec<PolyIdentifier>;
    fn witness_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![]
    }
    fn benefits_from_linearization(&self) -> bool;
    fn linearizes_over(&self) -> Vec<PolyIdentifier>;
    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint>;
    // fn compute_linearization_contribution(&self, values: &[E::Fr]) -> Vec<E::Fr> {
    //     vec![]
    // } 
    fn num_quotient_terms(&self) -> usize;
    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr;
    fn contribute_into_quotient(
        &self, 
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError>;
    fn contribute_into_linearization(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError>;
    fn contribute_into_verification_equation(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError>;
    fn put_public_inputs_into_selector_id(&self) -> Option<usize>;
    fn box_clone(&self) -> Box<dyn GateInternal<E>>;
}

pub trait Gate<E: Engine>: GateInternal<E>
    + Sized
    + Clone
    + std::hash::Hash
    + std::default::Default 
{
    fn as_internal(&self) -> &dyn GateInternal<E> {
        self as &dyn GateInternal<E>
    }

    fn into_internal(self) -> Box<dyn GateInternal<E>> {
        Box::from(self) as Box<dyn GateInternal<E>>
    }
}

pub trait MainGate<E: Engine>: Gate<E> {
    const NUM_LINEAR_TERMS: usize;
    const NUM_VARIABLES: usize;
    const NUM_VARIABLES_ON_NEXT_STEP: usize;
    fn range_of_multiplicative_term() -> std::ops::Range<usize>;
    fn range_of_linear_terms() -> std::ops::Range<usize>;
    fn index_for_constant_term() -> usize;
    fn range_of_next_step_linear_terms() -> std::ops::Range<usize>;
    fn format_term(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
    fn format_linear_term_with_duplicates(instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError>;
    fn dummy_vars_to_inscribe(dummy: Variable) -> Vec<Variable>;
    fn empty_coefficients() -> Vec<E::Fr>;
    fn contribute_into_quotient_for_public_inputs(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomial_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError>;
}

impl<E: Engine> std::hash::Hash for dyn GateInternal<E> {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        self.type_id().hash(state);
        self.name().hash(state);
        self.degree().hash(state);
    }
}

impl<E: Engine> PartialEq for dyn GateInternal<E> {
    fn eq(&self, other: &Self) -> bool {
        self.type_id() == other.type_id() &&
        self.name() == other.name() &&
        self.degree() == other.degree()
    }
}

impl<E: Engine> Eq for dyn GateInternal<E> {}

impl<E: Engine> Clone for Box<dyn GateInternal<E>> {
    fn clone(&self) -> Self {
        self.box_clone()
    }
}
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct LinearCombinationOfTerms(pub Vec<PolynomialMultiplicativeTerm>);

impl LinearCombinationOfTerms {
    fn terms(&self) -> &[PolynomialMultiplicativeTerm] {
       &self.0[..]
    }
}

#[derive(Clone, Debug)]
pub enum ArithmeticTerm<E: Engine>{
    Product(Vec<Variable>, E::Fr),
    SingleVariable(Variable, E::Fr),
    Constant(E::Fr),
}

impl<E: Engine> ArithmeticTerm<E> {
    pub fn from_variable(var: Variable) -> Self {
        ArithmeticTerm::SingleVariable(var, E::Fr::one())
    }

    pub fn from_variable_and_coeff(var: Variable, coeff: E::Fr) -> Self {
        ArithmeticTerm::SingleVariable(var, coeff)
    }

    pub fn constant(coeff: E::Fr) -> Self {
        ArithmeticTerm::Constant(coeff)
    }

    pub fn mul_by_variable(self, other: Variable) -> Self {
        match self {
            ArithmeticTerm::Product(mut terms, coeff) => {
                terms.push(other);

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::SingleVariable(this, coeff) => {
                let terms = vec![this, other];

                ArithmeticTerm::Product(terms, coeff)
            },
            ArithmeticTerm::Constant(coeff) => {
                let terms = vec![other];

                ArithmeticTerm::Product(terms, coeff)
            },
        }
    }

    pub fn scale(&mut self, by: &E::Fr) {
        match self {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.mul_assign(by);
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.mul_assign(by);
            },
        }
    }
}

#[derive(Clone, Debug)]
pub struct MainGateTerm<E: Engine>{
    terms: Vec<ArithmeticTerm<E>>,
    num_multiplicative_terms: usize,
    num_constant_terms: usize
}

impl<E: Engine> MainGateTerm<E> {
    pub fn new() -> Self {
        Self {
            terms: Vec::with_capacity(8),
            num_multiplicative_terms: 0,
            num_constant_terms: 0
        }
    }

    pub fn len_without_constant(&self) -> usize {
        self.terms.len()
    }

    pub fn add_assign(&mut self, other: ArithmeticTerm<E>) {
        match &other {
            ArithmeticTerm::Product(_, _) => {
                self.num_multiplicative_terms += 1;
                self.terms.push(other);
            },
            ArithmeticTerm::SingleVariable(_, _) => {
                self.terms.push(other);
            },
            ArithmeticTerm::Constant(_) => {
                self.num_constant_terms += 1;
                self.terms.push(other);
            },
        }

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }

    pub fn sub_assign(&mut self, mut other: ArithmeticTerm<E>) {
        match &mut other {
            ArithmeticTerm::Product(_, ref mut coeff) => {
                coeff.negate();
                self.num_multiplicative_terms += 1;
            },
            ArithmeticTerm::SingleVariable(_, ref mut coeff) => {
                coeff.negate();
            },
            ArithmeticTerm::Constant(ref mut coeff) => {
                coeff.negate();
                self.num_constant_terms += 1;       
            },
        }

        self.terms.push(other);

        debug_assert!(self.num_constant_terms <= 1, "must not duplicate constants");        
    }
}

#[derive(Clone, Debug, Hash, Default)]
pub struct Width4MainGateWithDNext;

impl<E: Engine> GateInternal<E> for Width4MainGateWithDNext {
    fn name(&self) -> &'static str {
        "main gate of width 4 with D_next"
    }

    fn degree(&self) -> usize {
        3
    }

    fn can_include_public_inputs(&self) -> bool {
        true
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolynomialInConstraint::SetupPolynomial(name, 0, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 1, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 2, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 3, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 4, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 5, TimeDilation(0)),
            PolynomialInConstraint::SetupPolynomial(name, 6, TimeDilation(0)),

            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
        ]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolyIdentifier::SetupPolynomial(name, 0),
            PolyIdentifier::SetupPolynomial(name, 1),
            PolyIdentifier::SetupPolynomial(name, 2),
            PolyIdentifier::SetupPolynomial(name, 3),
            PolyIdentifier::SetupPolynomial(name, 4),
            PolyIdentifier::SetupPolynomial(name, 5),
            PolyIdentifier::SetupPolynomial(name, 6),
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
        true
    }

    fn linearizes_over(&self) -> Vec<PolyIdentifier> {
        let name = <Self as GateInternal<E>>::name(&self);

        vec![
            PolyIdentifier::SetupPolynomial(name, 0),
            PolyIdentifier::SetupPolynomial(name, 1),
            PolyIdentifier::SetupPolynomial(name, 2),
            PolyIdentifier::SetupPolynomial(name, 3),
            PolyIdentifier::SetupPolynomial(name, 4),
            PolyIdentifier::SetupPolynomial(name, 5),
            PolyIdentifier::SetupPolynomial(name, 6),
        ]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
        ]
    }

    fn num_quotient_terms(&self) -> usize {
        1
    }

    fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, last_row: bool) -> E::Fr {
        let name = <Self as GateInternal<E>>::name(&self);

        let q_a = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 0), row);
        let q_b = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 1), row);
        let q_c = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 2), row);
        let q_d = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 3), row);
        let q_m = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 4), row);
        let q_const = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 5), row);
        let q_d_next = poly_storage.get_poly_at_step(PolyIdentifier::SetupPolynomial(name, 6), row);

        // println!("{}*A + {}*B + {}*C + {}*D + {} + {}*A*A + {}*D_next", q_a, q_b, q_c, q_d, q_const, q_m, q_d_next);
        let a_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
        let b_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(1), row);
        let c_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(2), row);
        let d_value = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row);
        let d_next_value = if last_row == false {
            Some(poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(3), row+1))
        } else {
            None
        }; 

        // println!("A = {}, B = {}, C = {}, D = {}, D_Next = {:?}", a_value, b_value, c_value, d_value, d_next_value);

        let mut total = E::Fr::zero();

        for (q, v) in [a_value, b_value, c_value, d_value].iter()
                    .zip([q_a, q_b, q_c, q_d].iter())
        {
            let mut tmp = *q;
            tmp.mul_assign(v);
            total.add_assign(&tmp);
        }

        total.add_assign(&q_const);

        let mut tmp = q_m;
        tmp.mul_assign(&a_value);
        tmp.mul_assign(&b_value);
        total.add_assign(&tmp);

        if last_row == false {
            let mut tmp = d_next_value.expect("must be able to get d_next");
            tmp.mul_assign(&q_d_next);

            total.add_assign(&tmp);
        } else {
            assert!(q_d_next.is_zero());
        }

        total
    }

    fn contribute_into_quotient(
        &self, 
        _domain_size: usize,
        _poly_storage: &mut AssembledPolynomialStorage<E>,
        _monomial_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        _worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        unreachable!("this type of gate can only be used as a main gate");
    }

    fn contribute_into_linearization(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unimplemented!("NYI")
    }
    fn contribute_into_verification_equation(
        &self, 
        domain_size: usize,
        at: E::Fr,
        queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        unimplemented!("NYI")
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        Some(5)
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }
}

impl<E: Engine> Gate<E> for Width4MainGateWithDNext {

}

impl<E: Engine> MainGate<E> for Width4MainGateWithDNext {
    const NUM_LINEAR_TERMS: usize = 4;
    const NUM_VARIABLES: usize = 4;
    const NUM_VARIABLES_ON_NEXT_STEP: usize = 1;

    fn range_of_multiplicative_term() -> std::ops::Range<usize> {
        0..2
    }
    fn range_of_linear_terms() -> std::ops::Range<usize> {
        0..4
    }

    fn index_for_constant_term() -> usize {
        5
    }

    fn range_of_next_step_linear_terms() -> std::ops::Range<usize> {
        6..7
    }

    fn format_term(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        let mut flattened_variables = vec![padding; 4];
        let mut flattened_coefficients = vec![E::Fr::zero(); 7];
        let mut bitmap = SimpleBitmap::new();

        let allowed_linear = 4;
        let allowed_multiplications = 1;
        let allowed_constants = 1;

        let mut used_in_multiplication = [padding; 2];

        debug_assert!(instance.num_constant_terms <= allowed_constants, "must not containt more constants than allowed");  
        debug_assert!(instance.num_multiplicative_terms <= allowed_multiplications, "must not containt more multiplications than allowed"); 
        debug_assert!(instance.terms.len() <= allowed_constants + allowed_multiplications + allowed_linear, "gate can not fit that many terms"); 

        if instance.num_multiplicative_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Product(_, _) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Product(vars, coeff) => {
                    debug_assert_eq!(vars.len(), 2, "multiplicative terms must contain two variables");

                    flattened_variables[0] = vars[0];
                    flattened_variables[1] = vars[1];
                    used_in_multiplication[0] = vars[0];
                    used_in_multiplication[1] = vars[1];
                    flattened_coefficients[4] = coeff;
                    bitmap.set(0);
                    bitmap.set(1);
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        if instance.num_constant_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Constant(_) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Constant(coeff) => {
                    flattened_coefficients[5] = coeff;
                },
                _ => {
                    unreachable!("must be constant term");
                }
            }
        }

        // only additions left
        for term in instance.terms.into_iter() {
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let index = flattened_variables.iter().position(
                        |&t| t == var
                    );
                    if let Some(index) = index {
                        // there is some variable there already, so it must have come from multiplication
                        assert!(used_in_multiplication[0] == var || used_in_multiplication[1] == var,
                            "variable in linear term must only happen already if it was in multiplication");
                        flattened_coefficients[index] = coeff;
                    } else {
                        let idx = bitmap.get_next_unused();
                        flattened_variables[idx] = var;
                        flattened_coefficients[idx] = coeff;
                        bitmap.set(idx);
                    }
                },
                _ => {
                    unreachable!("must be additive term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }

    fn format_linear_term_with_duplicates(mut instance: MainGateTerm<E>, padding: Variable) -> Result<(Vec<Variable>, Vec<E::Fr>), SynthesisError> {
        let mut flattened_variables = vec![padding; 4];
        let mut flattened_coefficients = vec![E::Fr::zero(); 7];
        let mut bitmap = SimpleBitmap::new();

        let allowed_linear = 4;
        let allowed_multiplications = 0;
        let allowed_constants = 1;

        debug_assert!(instance.num_constant_terms <= allowed_constants, "must not containt more constants than allowed");  
        assert!(instance.num_multiplicative_terms <= allowed_multiplications, "must not containt multiplications"); 
        debug_assert!(instance.terms.len() <= allowed_constants + allowed_multiplications + allowed_linear, "gate can not fit that many terms"); 

        if instance.num_constant_terms != 0 {
            let index = instance.terms.iter().position(
                |t| {
                    match t {
                        ArithmeticTerm::Constant(_) => true,
                        _ => false,
                    }
                }
            ).unwrap();

            let term = instance.terms.swap_remove(index);
            match term {
                ArithmeticTerm::Constant(coeff) => {
                    flattened_coefficients[5] = coeff;
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        for term in instance.terms.into_iter() {
            match term {
                ArithmeticTerm::SingleVariable(var, coeff) => {
                    let idx = bitmap.get_next_unused();
                    flattened_variables[idx] = var;
                    flattened_coefficients[idx] = coeff;
                    bitmap.set(idx);
                },
                _ => {
                    unreachable!("must be multiplicative term");
                }
            }
        }

        Ok((flattened_variables, flattened_coefficients))
    }

    fn dummy_vars_to_inscribe(dummy: Variable) -> Vec<Variable> {
        vec![dummy; 4]
    }

    fn empty_coefficients() -> Vec<E::Fr> {
        vec![E::Fr::zero(); 7]
    }

    fn contribute_into_quotient_for_public_inputs(
        &self, 
        domain_size: usize,
        public_inputs: &[E::Fr],
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &Worker
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        assert!(domain_size.is_power_of_two());
        assert_eq!(challenges.len(), <Self as GateInternal<E>>::num_quotient_terms(&self));

        let lde_factor = poly_storage.lde_factor;
        assert!(lde_factor.is_power_of_two());

        assert!(poly_storage.is_bitreversed);

        let coset_factor = E::Fr::multiplicative_generator();
        // Include the public inputs
        let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(domain_size)?;
        for (idx, &input) in public_inputs.iter().enumerate() {
            inputs_poly.as_mut()[idx] = input;
        }
        // go into monomial form

        let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // add constants selectors vector
        let name = <Self as GateInternal<E>>::name(&self);

        let key = PolyIdentifier::SetupPolynomial(name, 5);
        let constants_poly_ref = monomials_storage.setup_map.get(&key).unwrap();
        inputs_poly.add_assign(&worker, constants_poly_ref);
        drop(constants_poly_ref);

        // LDE
        let mut t_1 = inputs_poly.bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            lde_factor, 
            omegas_bitreversed, 
            &coset_factor
        )?;

        for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
            // skip public constants poly (was used in public inputs)
            if p == PolynomialInConstraint::SetupPolynomial(name, 5, TimeDilation(0)) {
                continue;
            }
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

        // Q_A * A
        let q_a_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 0, TimeDilation(0)),
            ldes_storage
        );
        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            ldes_storage
        );
        let mut tmp = q_a_ref.clone();
        tmp.mul_assign(&worker, a_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_a_ref);
        drop(a_ref);

        // Q_B * B
        let q_b_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 1, TimeDilation(0)),
            ldes_storage
        );
        let b_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            ldes_storage
        );
        tmp.reuse_allocation(q_b_ref);
        tmp.mul_assign(&worker, b_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_b_ref);
        drop(b_ref);

        // // Q_C * C
        let q_c_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 2, TimeDilation(0)),
            ldes_storage
        );
        let c_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(2, TimeDilation(0)),
            ldes_storage
        );
        tmp.reuse_allocation(q_c_ref);
        tmp.mul_assign(&worker, c_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_c_ref);
        drop(c_ref);

        // // Q_D * D
        let q_d_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 3, TimeDilation(0)),
            ldes_storage
        );
        let d_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(0)),
            ldes_storage
        );
        tmp.reuse_allocation(q_d_ref);
        tmp.mul_assign(&worker, d_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_d_ref);
        drop(d_ref);

        // Q_M * A * B
        let q_m_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 4, TimeDilation(0)),
            ldes_storage
        );
        let a_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            ldes_storage
        );
        let b_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(1, TimeDilation(0)),
            ldes_storage
        );
        tmp.reuse_allocation(q_m_ref);
        tmp.mul_assign(&worker, a_ref);
        tmp.mul_assign(&worker, b_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_m_ref);
        drop(a_ref);
        drop(b_ref);

        // Q_D_next * D_next
        let q_d_next_ref = get_from_map_unchecked(
            PolynomialInConstraint::SetupPolynomial(name, 6, TimeDilation(0)),
            ldes_storage
        );
        let d_next_ref = get_from_map_unchecked(
            PolynomialInConstraint::VariablesPolynomial(3, TimeDilation(1)),
            ldes_storage
        );
        tmp.reuse_allocation(q_d_next_ref);
        tmp.mul_assign(&worker, d_next_ref);
        t_1.add_assign(&worker, &tmp);
        drop(q_d_next_ref);
        drop(d_next_ref);

        t_1.scale(&worker, challenges[0]);

        Ok(t_1)
    }
}

fn get_from_map_unchecked<E: Engine>(
    key_with_dilation: PolynomialInConstraint,
    ldes_map: &AssembledPolynomialStorage<E>
) -> &Polynomial<E::Fr, Values> {

    let (key, dilation_value) = match key_with_dilation {
        PolynomialInConstraint::VariablesPolynomial(idx, dilation) => {
            (PolyIdentifier::VariablesPolynomial(idx), dilation.0)
        },
        PolynomialInConstraint::WitnessPolynomial(idx, dilation) => {
            (PolyIdentifier::WitnessPolynomial(idx), dilation.0)
        },
        PolynomialInConstraint::SetupPolynomial(name, idx, dilation) => {
            (PolyIdentifier::SetupPolynomial(name, idx), dilation.0)
        }
    };


    let r = if dilation_value == 0 {
        match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                ldes_map.state_map.get(&k).unwrap()
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                ldes_map.witness_map.get(&k).unwrap()
            },           
            k @ PolyIdentifier::SetupPolynomial(..) => {
                ldes_map.setup_map.get(&k).unwrap()
            }
        }
    } else {
        ldes_map.scratch_space.get(&key_with_dilation).unwrap()
    };

    r
}

fn ensure_in_map_or_create<E: Engine>(
    worker: &Worker,
    key_with_dilation: PolynomialInConstraint,
    domain_size: usize,
    omegas_bitreversed: &BitReversedOmegas<E::Fr>,
    lde_factor: usize,
    coset_factor: E::Fr,
    monomials_map: &AssembledPolynomialStorageForMonomialForms<E>,
    ldes_map: &mut AssembledPolynomialStorage<E>
) -> Result<(), SynthesisError> {
    assert!(ldes_map.is_bitreversed);
    assert_eq!(ldes_map.lde_factor, lde_factor);

    let (key, dilation_value) = match key_with_dilation {
        PolynomialInConstraint::VariablesPolynomial(idx, dilation) => {
            (PolyIdentifier::VariablesPolynomial(idx), dilation.0)
        },
        PolynomialInConstraint::WitnessPolynomial(idx, dilation) => {
            (PolyIdentifier::WitnessPolynomial(idx), dilation.0)
        },
        PolynomialInConstraint::SetupPolynomial(name, idx, dilation) => {
            (PolyIdentifier::SetupPolynomial(name, idx), dilation.0)
        }
    };

    let mut contains_in_scratch_or_maps = false;

    if dilation_value == 0 {
        match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                if ldes_map.state_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                if ldes_map.witness_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            },           
            k @ PolyIdentifier::SetupPolynomial(..) => {
                if ldes_map.setup_map.get(&k).is_some() {
                    contains_in_scratch_or_maps = true;
                }
            }
        }
    } else {
        if ldes_map.scratch_space.get(&key_with_dilation).is_some() {
            contains_in_scratch_or_maps = true;
        }
    };

    if !contains_in_scratch_or_maps {
        // optimistic case: we have already calculated value without dilation
        // but now need to just rotate
        let lde_without_dilation = match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => {
                ldes_map.state_map.get(&k)
            },
            k @ PolyIdentifier::WitnessPolynomial(..) => {
                ldes_map.witness_map.get(&k)
            },           
            k @ PolyIdentifier::SetupPolynomial(..) => {
                ldes_map.setup_map.get(&k)
            }
        };

        let mut done = false;

        let rotated = if let Some(lde) = lde_without_dilation.as_ref() {
            let rotation_factor = dilation_value * lde_factor;
            let f = lde.clone_shifted_assuming_bitreversed(rotation_factor, worker)?;
            drop(lde);

            Some(f)
        } else {
            None
        };

        drop(lde_without_dilation);

        if let Some(f) = rotated {
            ldes_map.scratch_space.insert(key_with_dilation, f);

            done = true;
        };

        if !done {
            // perform LDE and push

            let monomial = match key {
                k @ PolyIdentifier::VariablesPolynomial(..) => {
                    monomials_map.state_map.get(&k).unwrap()
                },
                k @ PolyIdentifier::WitnessPolynomial(..) => {
                    monomials_map.witness_map.get(&k).unwrap()
                },           
                k @ PolyIdentifier::SetupPolynomial(..) => {
                    monomials_map.setup_map.get(&k).unwrap()
                }
            };
        
            let lde = monomial.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                omegas_bitreversed, 
                &coset_factor
            )?;
        
            let final_lde = if dilation_value != 0 {
                let rotation_factor = dilation_value * lde_factor;
                let f = lde.clone_shifted_assuming_bitreversed(rotation_factor, worker)?;
                drop(lde);
        
                f
            } else {
                lde
            };

            // insert back

            if dilation_value == 0 {
                match key {
                    k @ PolyIdentifier::VariablesPolynomial(..) => {
                        ldes_map.state_map.insert(k, final_lde);
                    },
                    k @ PolyIdentifier::WitnessPolynomial(..) => {
                        ldes_map.witness_map.insert(k, final_lde);
                    },           
                    k @ PolyIdentifier::SetupPolynomial(..) => {
                        ldes_map.setup_map.insert(k, final_lde);
                    }
                }
            } else {
                ldes_map.scratch_space.insert(key_with_dilation, final_lde);
            };

            done = true;
        }

        assert!(done);
    }

    Ok(())
}

struct SimpleBitmap(u64, usize);
impl SimpleBitmap {
    fn new() -> Self {
        Self(0u64, 0)
    }

    fn get_next_unused(&mut self) -> usize {
        for i in 0..64 {
            if self.get(i) == false {
                return i;
            }
        }

        unreachable!()
    }

    fn get(&self, idx: usize) -> bool{
        1u64 << idx & self.0 > 0
    }

    fn set(&mut self, idx: usize) {
        self.0 |= 1u64 << idx;
    }
}

pub trait PlonkConstraintSystemParams<E: Engine>: Sized + Copy + Clone + Send + Sync {
    const STATE_WIDTH: usize;
    const WITNESS_WIDTH: usize;
    const HAS_WITNESS_POLYNOMIALS: bool;
    const HAS_CUSTOM_GATES: bool;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool;
}

use std::sync::Arc;

pub trait ConstraintSystem<E: Engine> {
    type Params: PlonkConstraintSystemParams<E>;
    type MainGate: MainGate<E>;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError>;

    fn new_single_gate_for_trace_step<G: Gate<E>>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        self.begin_gates_batch_for_step()?;
        self.new_gate_in_batch(
            equation,
            coefficients_assignments,
            variables_assignments,
            witness_assignments
        )?;
        self.end_gates_batch_for_step()
    }

    fn get_main_gate(&self) -> &Self::MainGate;

    fn allocate_main_gate(&mut self, term: MainGateTerm<E>) -> Result<(), SynthesisError> {
        let (vars, coeffs) = Self::MainGate::format_term(term, Self::get_dummy_variable())?;

        let mg = Self::MainGate::default();

        self.new_single_gate_for_trace_step(
            &mg,
            &coeffs,
            &vars,
            &[]
        )
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;
    fn new_gate_in_batch<G: Gate<E>>(&mut self, 
        equation: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;
    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError>;

    fn allocate_variables_without_gate(&mut self, 
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError>;

    fn get_value(&self, _variable: Variable) -> Result<E::Fr, SynthesisError> { 
        Err(SynthesisError::AssignmentMissing)
    }

    fn get_dummy_variable() -> Variable;

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError>;
    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError>;

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<(), SynthesisError>;
    fn get_table(&self, functional_name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError>; 

    fn add_multitable(&mut self, table: MultiTableApplication<E>) -> Result<(), SynthesisError>;
    fn get_multitable(&self, functional_name: &str) -> Result<Arc<MultiTableApplication<E>>, SynthesisError>; 

    fn apply_single_lookup_gate(&mut self, variables: &[Variable], gate: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError>;
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], gate: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError>;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PlonkCsWidth4WithNextStepParams;
impl<E: Engine> PlonkConstraintSystemParams<E> for PlonkCsWidth4WithNextStepParams {
    const STATE_WIDTH: usize =  4;
    const WITNESS_WIDTH: usize = 0;
    const HAS_WITNESS_POLYNOMIALS: bool = false;
    const HAS_CUSTOM_GATES: bool =  false;
    const CAN_ACCESS_NEXT_TRACE_STEP: bool = true;
}

use crate::plonk::polynomials::*;

// pub struct PolynomialStorage<E: Engine> {
//     pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
//     pub witness_map: std::collections::HashMap<PolyIdentifier,Polynomial<E::Fr, Values>>,
//     pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
// }

#[derive(Clone)]
pub struct PolynomialStorage<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Vec<Variable>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Vec<E::Fr>>,
}

impl<E: Engine> PolynomialStorage<E> {
    pub fn new() -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
        }
    }

    pub fn get_value(&self, poly: &PolynomialInConstraint, n: usize) -> Result<E::Fr, SynthesisError> {
        match poly {
            PolynomialInConstraint::VariablesPolynomial(_, _) => {
                unreachable!("should not try to get value of the state polynomial, get variable first instead");
            },
            PolynomialInConstraint::SetupPolynomial(gate_descr, idx, TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::SetupPolynomial(gate_descr, *idx);
                let value = *self.setup_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            PolynomialInConstraint::WitnessPolynomial(_, _) => {
                unimplemented!()
            }
        }
    }

    pub fn get_variable(&self, poly: &PolynomialInConstraint, n: usize) -> Result<Variable, SynthesisError> {
        match poly {
            PolynomialInConstraint::VariablesPolynomial(idx, TimeDilation(dilation)) => {
                let final_index = n + dilation;
                let identifier = PolyIdentifier::VariablesPolynomial(*idx);
                let value = *self.state_map
                    .get(&identifier)
                    .ok_or(SynthesisError::AssignmentMissing)?
                    .get(final_index)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                Ok(value)
            },
            _ => {
                unreachable!("should not try to get variable of setup or witness polynomial");
            }
        }
    }
}

pub struct AssembledPolynomialStorage<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>,
    pub scratch_space: std::collections::HashMap<PolynomialInConstraint, Polynomial<E::Fr, Values>>,
    pub gate_selectors: std::collections::HashMap<Box<dyn GateInternal<E>>, Polynomial<E::Fr, Values>>,
    pub is_bitreversed: bool,
    pub lde_factor: usize
}

pub struct AssembledPolynomialStorageForMonomialForms<E: Engine> {
    pub state_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Coefficients>>,
    pub witness_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Coefficients>>,
    pub setup_map: std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Coefficients>>,
    pub gate_selectors: std::collections::HashMap<Box<dyn GateInternal<E>>, Polynomial<E::Fr, Coefficients>>,
}

impl<E: Engine> AssembledPolynomialStorage<E> {
    pub fn get_poly(&self, id: PolyIdentifier) -> &Polynomial<E::Fr, Values> {
        match id {
            p @ PolyIdentifier::VariablesPolynomial(..) => {
                self.state_map.get(&p).expect(&format!("poly {:?} must exist", p))
            },
            p @ PolyIdentifier::WitnessPolynomial(..) => {
                self.witness_map.get(&p).expect(&format!("poly {:?} must exist", p))
            },
            p @ PolyIdentifier::SetupPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p))
            }
        }
    }
    pub fn get_poly_at_step(&self, id: PolyIdentifier, step: usize) -> E::Fr {
        assert!(self.is_bitreversed == false);
        assert!(self.lde_factor == 1);
        let p = self.get_poly(id);
        p.as_ref()[step]
    }

    pub fn new(bitreversed: bool, lde_factor: usize) -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
            gate_selectors: std::collections::HashMap::new(),
            scratch_space: std::collections::HashMap::new(),
            is_bitreversed: bitreversed,
            lde_factor
        }
    }
}

impl<E: Engine> AssembledPolynomialStorageForMonomialForms<E> {
    pub fn get_poly(&self, id: PolyIdentifier) -> &Polynomial<E::Fr, Coefficients> {
        match id {
            p @ PolyIdentifier::VariablesPolynomial(..) => {
                self.state_map.get(&p).expect(&format!("poly {:?} must exist", p))
            },
            p @ PolyIdentifier::WitnessPolynomial(..) => {
                self.witness_map.get(&p).expect(&format!("poly {:?} must exist", p))
            },
            p @ PolyIdentifier::SetupPolynomial(..) => {
                self.setup_map.get(&p).expect(&format!("poly {:?} must exist", p))
            }
        }
    }

    pub fn new() -> Self {
        Self {
            state_map: std::collections::HashMap::new(),
            witness_map: std::collections::HashMap::new(),
            setup_map: std::collections::HashMap::new(),
            gate_selectors: std::collections::HashMap::new()
        }
    }
}

#[derive(Clone)]
pub struct GateDensityStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateInternal<E>>, BitVec>);

impl<E: Engine> GateDensityStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

pub struct GateConstantCoefficientsStorage<E: Engine>(pub std::collections::HashMap<Box<dyn GateInternal<E>>, Vec<E::Fr>>);

impl<E: Engine> GateConstantCoefficientsStorage<E> {
    pub fn new() -> Self {
        Self(std::collections::HashMap::new())
    }
}

#[derive(Clone)]
pub struct TrivialAssembly<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> {
    pub inputs_storage: PolynomialStorage<E>,
    pub aux_storage: PolynomialStorage<E>,
    pub num_input_gates: usize,
    pub num_aux_gates: usize,
    pub max_constraint_degree: usize,
    pub main_gate: MG,
    pub input_assingments: Vec<E::Fr>,
    pub aux_assingments: Vec<E::Fr>,
    pub num_inputs: usize,
    pub num_aux: usize,
    pub trace_step_for_batch: Option<usize>,
    pub is_finalized: bool,

    pub gates: std::collections::HashSet<Box<dyn GateInternal<E>>>,
    pub all_queried_polys_in_constraints: std::collections::HashSet<PolynomialInConstraint>,
    // pub sorted_setup_polynomial_ids: Vec<PolyIdentifier>,
    pub sorted_gates: Vec<Box<dyn GateInternal<E>>>,
    pub aux_gate_density: GateDensityStorage<E>,
    pub explicit_zero_variable: Option<Variable>,
    pub explicit_one_variable: Option<Variable>,

    pub tables: Vec<Arc<LookupTableApplication<E>>>,
    pub multitables: Vec<Arc<MultiTableApplication<E>>>,
    pub table_selectors: std::collections::HashMap<String, BitVec>,
    pub multitable_selectors: std::collections::HashMap<String, BitVec>,
    pub table_ids_poly: Vec<E::Fr>,
    pub individual_table_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub individual_multitable_entries: std::collections::HashMap<String, Vec<Vec<E::Fr>>>,
    pub known_table_ids: Vec<E::Fr>,
    pub num_table_lookups: usize,
    pub num_multitable_lookups: usize,

    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> ConstraintSystem<E> for TrivialAssembly<E, P, MG> {
    type Params = P;
    type MainGate = MG;

    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

        // println!("Allocated variable Aux({}) with value {}", index, value);

        Ok(Variable(Index::Aux(index)))
    }

    // allocate an input variable
    fn alloc_input<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_inputs += 1;
        let index = self.num_inputs;
        self.input_assingments.push(value);

        let input_var = Variable(Index::Input(index));

        let mut main_gate = MainGateTerm::<E>::new();
        main_gate.sub_assign(ArithmeticTerm::from_variable(input_var));

        let dummy = Self::get_dummy_variable();
        let (variables_assignments, coefficients_assignments) = MG::format_term(main_gate, dummy).expect("must make empty padding gate");

        let n = self.num_input_gates;
        Self::allocate_into_storage(
            &MG::default(), 
            &mut self.inputs_storage, 
            n, 
            &coefficients_assignments, 
            &variables_assignments, 
            &[]
        )?;

        self.num_input_gates += 1;

        Ok(input_var)
    }

    fn get_main_gate(&self) -> &MG {
        &self.main_gate
    }

    fn begin_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_none());
        self.num_aux_gates += 1;
        let n = self.num_aux_gates;
        self.trace_step_for_batch = Some(n);

        Ok(())
    }

    fn new_gate_in_batch<G: Gate<E>>(&mut self, 
        gate: &G,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        // check that gate is ok for config
        // debug_assert!(check_gate_is_allowed_for_params::<E, P, G>(&gate), format!("supplied params do not work with gate {:?}", gate));

        let n = self.trace_step_for_batch.unwrap();
        // make zero-enumerated index
        let n = n - 1;
        
        Self::allocate_into_storage(
            gate,
            &mut self.aux_storage,
            n,
            coefficients_assignments,
            variables_assignments,
            witness_assignments,
        )?;

        self.add_gate_into_list(gate);

        if let Some(tracker) = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>) {
            if tracker.len() != n {
                let padding = n - tracker.len();
                tracker.grow(padding, false);
            }
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());
        } else {
            self.aux_gate_density.0.insert(gate.clone().into_internal(), BitVec::new());
            let tracker = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>).unwrap();
            tracker.grow(n, false);
            tracker.push(true);
            debug_assert_eq!(n+1, tracker.len());
        }

        Ok(())
    }

    fn allocate_variables_without_gate(&mut self, 
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only be called in a batch");
        // make zero-enumerated index
        let n = n - 1;

        let empty_coefficients = Self::MainGate::empty_coefficients();

        let gate = Self::MainGate::default();

        Self::allocate_into_storage(
            &gate,
            &mut self.aux_storage,
            n,
            &empty_coefficients,
            variables_assignments,
            witness_assignments,
        )?;

        let apply_gate = false;

        let tracker = self.aux_gate_density.0.get_mut(gate.as_internal() as &dyn GateInternal<E>).unwrap();
        if tracker.len() != n {
            let padding = n - tracker.len();
            tracker.grow(padding, false);
        }
        tracker.push(apply_gate);
        debug_assert_eq!(n+1, tracker.len());

        Ok(())
    }

    fn end_gates_batch_for_step(&mut self) -> Result<(), SynthesisError> {
        debug_assert!(self.trace_step_for_batch.is_some());
        let n = self.trace_step_for_batch.take().unwrap();
        debug_assert_eq!(n, self.num_aux_gates, "invalid batch id");

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                use crate::rand::Rng;

                let mut rng = crate::rand::thread_rng();
                let value: E::Fr = rng.gen();

                value
                // E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(input)) => {
                self.input_assingments[input - 1]
            },
            Variable(Index::Aux(aux)) => {
                self.aux_assingments[aux - 1]
            }
        };

        Ok(value)
    }

    fn get_dummy_variable() -> Variable {
        Self::dummy_variable()
    }

    fn get_explicit_zero(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_zero_variable {
            return Ok(var);
        }

        let zero = self.alloc(|| Ok(E::Fr::zero()))?;

        self.explicit_zero_variable = Some(zero);

        Ok(zero)
    }

    fn get_explicit_one(&mut self) -> Result<Variable, SynthesisError> {
        if let Some(var) = self.explicit_one_variable {
            return Ok(var);
        }

        let one = self.alloc(|| Ok(E::Fr::one()))?;

        self.explicit_one_variable = Some(one);

        Ok(one)
    }

    fn add_table(&mut self, table: LookupTableApplication<E>) -> Result<(), SynthesisError> {
        assert!(table.applies_over().len() == 3, "only support tables of width 3");
        assert!(table.can_be_combined(), "can only add tables that are combinable");
        assert!(!self.known_table_ids.contains(&table.table_id()));
        let table_name = table.functional_name();
        let table_id = table.table_id();
        self.tables.push(Arc::from(table));
        self.individual_table_entries.insert(table_name.clone(), vec![]);
        self.table_selectors.insert(table_name, BitVec::new());
        self.known_table_ids.push(table_id);

        Ok(())
    }

    fn get_table(&self, name: &str) -> Result<Arc<LookupTableApplication<E>>, SynthesisError> {
        for t in self.tables.iter() {
            if t.functional_name() == name {
                return Ok(Arc::clone(t));
            }
        }

        Err(SynthesisError::AssignmentMissing)
    }

    fn add_multitable(&mut self, table: MultiTableApplication<E>) -> Result<(), SynthesisError> {
        let table_name = table.functional_name();
        let mut exists = false;
        for t in self.multitables.iter() {
            if t.functional_name() == table_name {
                exists = true;
            }
        }
        assert!(exists == false);
        self.multitables.push(Arc::from(table));
        self.multitable_selectors.insert(table_name.clone(), BitVec::new());
        self.individual_table_entries.insert(table_name.clone(), vec![]);

        Ok(())
    }

    fn get_multitable(&self, functional_name: &str) -> Result<Arc<MultiTableApplication<E>>, SynthesisError> {
        for t in self.multitables.iter() {
            if t.functional_name() == functional_name {
                return Ok(Arc::clone(t));
            }
        }

        Err(SynthesisError::AssignmentMissing)
    }

    fn apply_single_lookup_gate(&mut self, variables: &[Variable], table: Arc<LookupTableApplication<E>>) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only add table constraint in a transaction");
        // make zero-enumerated index
        let n = n - 1;

        debug_assert!(self.tables.contains(&table));
        assert!(table.can_be_combined() == true);
        assert!(table.applies_over().len() == 3);

        let table_name = table.functional_name();

        // we need to:
        // - mark that this table applies at this row
        // - add values into the list to later on make a sorted polynomial

        let tracker = self.table_selectors.get_mut(&table_name).unwrap();
        if tracker.len() != n {
            let padding = n - tracker.len();
            tracker.grow(padding, false);
        }
        tracker.push(true);
        debug_assert_eq!(n+1, tracker.len());

        // add values for lookup table sorting later

        let keys_and_values_len = table.applies_over().len();
        let mut table_entries = Vec::with_capacity(keys_and_values_len + 1);
        let mut values_are_known = true;
        for v in variables.iter() {
            if let Ok(value) = self.get_value(*v) {
                table_entries.push(value);
            } else {
                values_are_known = false;
                table_entries.push(E::Fr::zero());
            }
        }
        table_entries.push(table.table_id());        

        let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
        assert_eq!(variables.len(), table.applies_over().len());

        if values_are_known {
            assert!(table.is_valid_entry(&table_entries[..keys_and_values_len]));
        }
        entries.push(table_entries);

        // keep track of what table is applied at what row
        self.table_ids_poly.resize(n, E::Fr::zero());
        self.table_ids_poly.push(table.table_id());

        self.num_table_lookups += 1;

        Ok(())
    }
    
    fn apply_multi_lookup_gate(&mut self, variables: &[Variable], table: Arc<MultiTableApplication<E>>) -> Result<(), SynthesisError> {
        let n = self.trace_step_for_batch.expect("may only add table constraint in a transaction");
        // make zero-enumerated index
        let n = n - 1;

        let table_name = table.functional_name();
        let tracker = self.multitable_selectors.get_mut(&table_name).unwrap();
        if tracker.len() != n {
            let padding = n - tracker.len();
            tracker.grow(padding, false);
        }
        tracker.push(true);
        debug_assert_eq!(n+1, tracker.len());

        let mut table_entries = Vec::with_capacity(table.applies_over().len());
        for v in variables.iter() {
            if let Ok(value) = self.get_value(*v) {
                table_entries.push(value);
            } else {
                panic!("value must exist");
            }
        }

        let entries = self.individual_table_entries.get_mut(&table_name).unwrap();
        assert_eq!(variables.len(), table.applies_over().len());

        assert!(table.is_valid_entry(&table_entries));

        self.table_ids_poly.resize(n, E::Fr::zero());
        self.table_ids_poly.push(table.table_id());

        entries.push(table_entries);


        Ok(())
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>> TrivialAssembly<E, P, MG> {
    fn allocate_into_storage<G: Gate<E>>(
        gate: &G,
        storage: &mut PolynomialStorage<E>, 
        n: usize,
        coefficients_assignments: &[E::Fr],
        variables_assignments: &[Variable],
        witness_assignments: &[E::Fr]
    ) -> Result<(), SynthesisError> {
        let dummy = Self::get_dummy_variable();
        let zero = E::Fr::zero();

        let mut coeffs_it = coefficients_assignments.iter();

        for setup_poly in gate.setup_polynomials().into_iter() {
            let poly_ref = storage.setup_map.entry(setup_poly).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, E::Fr::zero());
            }
            poly_ref.push(*coeffs_it.next().unwrap_or(&zero));
        }

        debug_assert!(coeffs_it.next().is_none(), "must consume all the coefficients for gate");

        let mut variable_it = variables_assignments.iter();

        for var_poly in gate.variable_polynomials().into_iter() {
            let poly_ref = storage.state_map.entry(var_poly).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, dummy);
            }
            if poly_ref.len() == n {
                // we consume variable only ONCE
                let var = *variable_it.next().unwrap_or(&dummy);
                poly_ref.push(var);
            }
        }

        debug_assert!(variable_it.next().is_none(), "must consume all variables for gate");

        let mut witness_it = witness_assignments.iter();

        for key in gate.witness_polynomials().into_iter() {
            let poly_ref = storage.witness_map.entry(key).or_insert(vec![]);
            if poly_ref.len() < n {
                poly_ref.resize(n, E::Fr::zero());
            } 
            poly_ref.push(*witness_it.next().unwrap_or(&zero));
        }

        Ok(())
    }

    pub fn n(&self) -> usize {
        self.num_input_gates + self.num_aux_gates
    }

    // fn add_gate_setup_polys_into_list<G: Gate<E>>(&mut self, gate: &G) {
    //     for key in gate.setup_polynomials().into_iter() {
    //         self.sorted_setup_polynomial_ids.push(key);
    //     }
    // }

    fn add_gate_into_list<G: Gate<E>>(&mut self, gate: &G) {
        if !self.gates.contains(gate.as_internal() as &dyn GateInternal<E>) {
            self.gates.insert(gate.clone().into_internal());

            // self.add_gate_setup_polys_into_list(gate);
            for p in gate.all_queried_polynomials().into_iter() {
                self.all_queried_polys_in_constraints.insert(p);
            }
            
            self.sorted_gates.push(gate.clone().into_internal());

            let degree = gate.degree();
            if self.max_constraint_degree < degree {
                self.max_constraint_degree = degree;
            }
        }        
    }

    pub fn new() -> Self {
        let mut tmp = Self {
            inputs_storage: PolynomialStorage::new(),
            aux_storage: PolynomialStorage::new(),

            max_constraint_degree: 0,

            num_input_gates: 0,
            num_aux_gates: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            main_gate: MG::default(),

            trace_step_for_batch: None,

            gates: std::collections::HashSet::new(),
            all_queried_polys_in_constraints: std::collections::HashSet::new(),

            aux_gate_density: GateDensityStorage::new(),

            // sorted_setup_polynomial_ids: vec![],
            sorted_gates: vec![],

            is_finalized: false,

            explicit_zero_variable: None,
            explicit_one_variable: None,

            tables: vec![],
            multitables: vec![],
            table_selectors: std::collections::HashMap::new(),
            multitable_selectors: std::collections::HashMap::new(),
            table_ids_poly: vec![],

            individual_table_entries: std::collections::HashMap::new(),
            individual_multitable_entries: std::collections::HashMap::new(),

            known_table_ids: vec![],

            num_table_lookups: 0,
            num_multitable_lookups: 0,

            _marker: std::marker::PhantomData
        };

        tmp.add_gate_into_list(&MG::default());

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable() -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let mut min_space_for_lookups = self.num_table_lookups;
        for table in self.tables.iter() {
            let table_num_rows = table.size();
            min_space_for_lookups += table_num_rows;
        }
        min_space_for_lookups += self.n();

        let new_size_candidates = [(self.n() + 1).next_power_of_two() - 1, (min_space_for_lookups + 1).next_power_of_two() - 1];

        let new_size = *new_size_candidates.iter().max().unwrap();

        let dummy = Self::get_dummy_variable();

        // let empty_gate = MainGateTerm::<E>::new();
        let empty_vars = vec![dummy; <Self as ConstraintSystem<E>>::Params::STATE_WIDTH];
        let empty_witness = vec![E::Fr::zero(); <Self as ConstraintSystem<E>>::Params::WITNESS_WIDTH];

        // let mg = MG::default();

        for _ in self.n()..new_size {

            self.begin_gates_batch_for_step().unwrap();

            self.allocate_variables_without_gate(
                &empty_vars,
                &empty_witness
            ).unwrap();

            self.end_gates_batch_for_step().unwrap();

            // self.new_single_gate_for_trace_step(
            //     &mg, 
            //     &coeffs, 
            //     &vars,
            //     &[]
            // ).expect("must add padding gate");
        }

        let new_size_for_aux = new_size - self.num_input_gates;

        // pad gate selectors
        for (_, tracker) in self.aux_gate_density.0.iter_mut() {
            tracker.grow(new_size_for_aux, false);
        }

        // pad lookup selectors
        for (_, selector) in self.table_selectors.iter_mut() {
            selector.grow(new_size_for_aux, false);
        }

        // pad special purpose table selector poly
        self.table_ids_poly.resize(new_size_for_aux, E::Fr::zero());

        assert!((self.n()+1).is_power_of_two());
        self.is_finalized = true;
    }

    fn get_storage_for_trace_step(&self, step: usize) -> &PolynomialStorage<E> {
        if step < self.num_input_gates {
            &self.inputs_storage
        } else {
            &self.aux_storage
        }
    }

    pub fn is_satisfied(&self) -> bool {
        // expect a small number of inputs

        // TODO: handle public inputs

        // for i in 0..self.num_input_gates {
        //     let gate = self.input_assingments
        // }

        // let one = E::Fr::one();
        // let mut minus_one = E::Fr::one();
        // minus_one.negate();

        let n = self.n() - 1;

        let worker = Worker::new();

        let storage = self.make_assembled_poly_storage(&worker, false).unwrap();

        for (gate_type, density) in self.aux_gate_density.0.iter() {
            for (gate_index, is_applicable) in density.iter().enumerate() {
                if is_applicable == false {
                    continue;
                }

                let trace_index = self.num_input_gates + gate_index;

                let last = trace_index == n;

                let value = gate_type.verify_on_row(trace_index, &storage, last);

                if value.is_zero() == false {
                    println!("Unsatisfied at aux gate {} (zero enumerated)", gate_index);
                    println!("Constraint value = {}", value);
                    println!("Gate {:?}", gate_type.name());
                    return false;
                }
            }
        }

        true
    }

    pub(crate) fn make_permutations(&self, worker: &Worker) -> Vec<Polynomial::<E::Fr, Values>> {
        assert!(self.is_finalized);

        let num_gates = self.n();
        let num_partitions = self.num_inputs + self.num_aux;
        let num_inputs = self.num_inputs;
        // in the partition number i there is a set of indexes in V = (a, b, c) such that V_j = i
        let mut partitions = vec![vec![]; num_partitions + 1];

        let mut poly_ids = vec![];
        for i in 0..P::STATE_WIDTH {
            let id = PolyIdentifier::VariablesPolynomial(i);
            poly_ids.push(id);
        }

        // gate_idx is zero-enumerated here
        for gate_idx in 0..num_gates
        {
            let storage = self.get_storage_for_trace_step(gate_idx);
            for (state_poly_index, poly_id) in poly_ids.iter().enumerate() {
                let variables_vec_ref = storage.state_map.get(&poly_id).expect("must get a variables polynomial");
                let storage_idx = if gate_idx < self.num_input_gates {
                    gate_idx
                } else {
                    gate_idx - self.num_input_gates
                };

                let v = variables_vec_ref[storage_idx];
                match v {
                    Variable(Index::Aux(0)) => {
                        // Dummy variables do not participate in the permutation
                    },
                    Variable(Index::Input(0)) => {
                        unreachable!("There must be no input with index 0");
                    },
                    Variable(Index::Input(index)) => {
                        let i = index; // inputs are [1, num_inputs]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                    Variable(Index::Aux(index)) => {
                        let i = index + num_inputs; // aux are [num_inputs + 1, ..]
                        partitions[i].push((state_poly_index, gate_idx+1));
                    },
                }
            }
        }

        // sanity check
        assert_eq!(partitions[0].len(), 0);

        let domain = Domain::new_for_size(num_gates as u64).expect("must have enough roots of unity to fit the circuit");

        // now we need to make root at it's cosets
        let domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, &worker
        );

        // domain_elements.pop().unwrap();

        use crate::ff::SqrtField;
        use crate::ff::LegendreSymbol;

        let mut non_residues = vec![];
        non_residues.push(E::Fr::one());
        non_residues.extend(make_non_residues::<E::Fr>(P::STATE_WIDTH - 1, &domain));

        assert_eq!(non_residues.len(), 4);

        let mut sigmas = vec![];
        for i in 0..P::STATE_WIDTH {
            let mut sigma_i = Polynomial::from_values_unpadded(domain_elements.clone()).unwrap();
            sigma_i.scale(&worker, non_residues[i]);
            sigmas.push(sigma_i);
        }

        let mut permutations = vec![vec![]; num_partitions + 1];

        fn rotate<T: Sized>(mut vec: Vec<T>) -> Vec<T> {
            if vec.len() > 1 {
                let mut els: Vec<_> = vec.drain(0..1).collect();
                els.reverse();
                vec.push(els.pop().unwrap());
            }

            vec
        }

        for (i, partition) in partitions.into_iter().enumerate().skip(1) {
            // copy-permutation should have a cycle around the partition

            // we do not need to permute over partitions of length 1,
            // as this variable only happends in one place
            if partition.len() == 1 {
                continue;
            }

            let permutation = rotate(partition.clone());
            permutations[i] = permutation.clone();

            for (original, new) in partition.into_iter()
                                    .zip(permutation.into_iter()) 
            {
                // (column_idx, trace_step_idx)
                let new_zero_enumerated = new.1 - 1;
                let mut new_value = domain_elements[new_zero_enumerated];

                // we have shuffled the values, so we need to determine FROM
                // which of k_i * {1, omega, ...} cosets we take a value
                // for a permutation polynomial
                new_value.mul_assign(&non_residues[new.0]);

                // check to what witness polynomial the variable belongs
                let place_into = &mut sigmas[original.0].as_mut();

                let original_zero_enumerated = original.1 - 1;
                place_into[original_zero_enumerated] = new_value;
            }
        }

        sigmas
    }

    fn make_setup_polynomials(
        &self,
        with_finalization: bool
    ) -> Result<std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }

        let total_num_gates = self.n();
        let num_input_gates = self.num_input_gates;

        let mut map = std::collections::HashMap::new();

        let setup_poly_ids: Vec<_> = self.aux_storage.setup_map.keys().collect();

        for &id in setup_poly_ids.into_iter() {
            let mut assembled_poly = vec![E::Fr::zero(); total_num_gates];
            if num_input_gates != 0 {
                let input_gates_coeffs = &mut assembled_poly[..num_input_gates];
                input_gates_coeffs.copy_from_slice(&self.inputs_storage.setup_map.get(&id).unwrap()[..]);
            }

            {
                let src = &self.aux_storage.setup_map.get(&id).unwrap()[..];
                let src_len = src.len();
                let aux_gates_coeffs = &mut assembled_poly[num_input_gates..(num_input_gates+src_len)];
                aux_gates_coeffs.copy_from_slice(src);
            }

            let as_poly = Polynomial::from_values_unpadded(assembled_poly)?;

            map.insert(id, as_poly);
        }

        Ok(map)
    }

    pub fn perform_setup(
        &self, 
        worker: &Worker
    ) -> Result<
    (std::collections::HashMap<PolyIdentifier, Polynomial<E::Fr, Values>>, Vec<Polynomial<E::Fr, Values>>), 
    SynthesisError
    > {
        let map = self.make_setup_polynomials(true)?;
        let permutation_polys = self.make_permutations(&worker);

        Ok((map, permutation_polys))
    }

    pub fn output_gate_selectors(&self, worker: &Worker) -> Result<Vec<Vec<E::Fr>>, SynthesisError> {
        if self.sorted_gates.len() == 1 {
            return Ok(vec![]);
        }

        let num_gate_selectors = self.sorted_gates.len();

        let one = E::Fr::one();
        let empty_poly_values = vec![E::Fr::zero(); self.n()];
        let mut poly_values = vec![empty_poly_values.clone(); num_gate_selectors];
        let num_input_gates = self.num_input_gates;

        // first gate in sorted in a main gate and applies on public inputs
        for p in poly_values[0][..num_input_gates].iter_mut() {
            *p = one;
        }

        worker.scope(poly_values.len(), |scope, chunk| {
            for (i, lh) in poly_values.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = &self.sorted_gates[idx];
                        let density = self.aux_gate_density.0.get(id).unwrap();
                        let poly_mut_slice: &mut [E::Fr] = &mut lh[num_input_gates..];
                        for (i, d) in density.iter().enumerate() {
                            if d {
                                poly_mut_slice[i] = one;
                            }
                        }
                    }
                });
            }
        });

        Ok(poly_values)
    }

    pub fn calculate_t_polynomial_values_for_single_application_tables(&self) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError> {
        
        if self.tables.len() == 0 {
            return Ok(vec![])
        }
        
        // we should pass over every table and append it

        let mut width = 0;
        for table in self.tables.iter() {
            if width == 0 {
                width = table.width();
            } else {
                assert_eq!(width, table.width());
            }
        }

        assert_eq!(width, 3, "only support tables that span over 3 polynomials for now");

        let mut column_contributions = vec![vec![]; width + 1];

        for table in self.tables.iter() {
            let entries = table.get_table_values_for_polys();
            // these are individual column vectors, so just copy
            for (idx, e) in entries.into_iter().enumerate() {
                column_contributions[idx].extend(e);
            }

            let table_id = table.table_id();
            let pad_to_len = column_contributions[0].len();

            column_contributions.last_mut().unwrap().resize(pad_to_len, table_id);
        }


        Ok(column_contributions)
    }

    pub fn calculate_s_poly_contributions_from_witness(&self) ->
        Result<Vec<Vec<E::Fr>>, SynthesisError> 
    {
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }
        // we first form a set of all occured witness values,
        // then include table entries to the set
        // and then sort this set

        let mut kv_set_entries = vec![];
        let mut contributions_per_column = vec![vec![]; 4];
        for single_application in self.tables.iter() {
            // copy all queries from witness
            let table_name = single_application.functional_name();
            for kv_values in self.individual_table_entries.get(&table_name).unwrap() {
                let entry = KeyValueSet::<E>::from_slice(&kv_values[..3]);
                kv_set_entries.push(entry);
            }

            // copy table elements themselves

            let entries = single_application.get_table_values_for_polys();
            // those are full values of polynomials, so we have to virtually transpose

            let size = entries[0].len();
            for i in 0..size {
                let entry = KeyValueSet::new([entries[0][i], entries[1][i], entries[2][i]]);
                kv_set_entries.push(entry)
            }

            kv_set_entries.sort();

            // now copy backward with addition of the table id

            for kv in kv_set_entries.iter() {
                for i in 0..3 {
                    contributions_per_column[i].push(kv.inner[i]);
                }
            }

            let table_id = single_application.table_id();
            let pad_to_len = contributions_per_column[0].len();
            contributions_per_column.last_mut().unwrap().resize(pad_to_len, table_id);

            kv_set_entries.truncate(0);
        }

        Ok(contributions_per_column)
    }

    pub fn calculate_f_poly_contribution_from_witness(
        &self,
        storage: &AssembledPolynomialStorage<E>
    ) -> 
        Result<Vec<Vec<E::Fr>>, SynthesisError>
    {
        assert!(self.is_finalized);
        if self.tables.len() == 0 {
            return Ok(vec![]);
        }

        let table_ids_vector = self.table_ids_poly.clone();

        // total number of gates, Input + Aux
        let size = self.n();

        // number of gates that are padding a circuit for lookup table value
        let tmp = self.calculate_t_polynomial_values_for_single_application_tables()?;

        let reserved_len = tmp[0].len();

        assert!(size > reserved_len);

        let aux_gates_start = self.num_input_gates;
        // input + aux gates without t-polys
        let aux_gates_end = size - reserved_len;

        let num_aux_gates = aux_gates_end - aux_gates_start;

        let mut contributions_per_column = vec![vec![E::Fr::zero(); size]; 4];
        for single_application in self.tables.iter() {
            let table_name = single_application.functional_name();
            let keys_and_values = single_application.applies_over();
            let selector_bitvec = self.table_selectors.get(&table_name).unwrap();

            for aux_gate_idx in 0..num_aux_gates {
                if selector_bitvec[aux_gate_idx] {
                    for (idx, &poly_id) in keys_and_values.iter().enumerate() {
                        let global_gate_idx = aux_gate_idx + aux_gates_start;
                        let value = storage.get_poly_at_step(poly_id, global_gate_idx);
                        contributions_per_column[idx][global_gate_idx] = value;
                    }
                }
            }
        }

        let aux_gates_slice = &table_ids_vector[..num_aux_gates];

        contributions_per_column.last_mut().unwrap()[aux_gates_start..aux_gates_end].copy_from_slice(aux_gates_slice);

        Ok(contributions_per_column)
    }

    fn sort_by_t(
        witness_entries: &Vec<Vec<E::Fr>>,
        table_entries: &Vec<Vec<E::Fr>>,
    ) -> Result< Vec<Vec<E::Fr>>, SynthesisError> {
        assert_eq!(witness_entries.len(), table_entries.len());

        if witness_entries.len() == 0 {
            return Ok(vec![]);
        }

        // make s = f sorted by t (elements in s appear in the same order as elements in t)

        let entries_len = table_entries[0].len();
        let witnesses_len = witness_entries[0].len();

        let mut index_lookups_for_sorting = vec![std::collections::HashMap::with_capacity(entries_len); witness_entries.len()];

        for (idx, table) in table_entries.iter().enumerate() {
            for (entry_index, &entry_value) in table.iter().enumerate() {
                // make a reverse lookup field element -> index
                index_lookups_for_sorting[idx].insert(entry_value, entry_index);
            }
        }

        let mut column_contributions = vec![];

        for (idx, witness_column) in witness_entries.iter().enumerate() {
            let mut indexes = vec![usize::max_value(); witnesses_len];
            for (witness_index, witness_value) in witness_column.iter().enumerate() {
                let reverse_lookup_index = index_lookups_for_sorting[idx].get(witness_value).unwrap();
                indexes[witness_index] = *reverse_lookup_index;
            }

            indexes.sort();

            println!("sorted_index = {:?}", indexes);

            let mut s_for_column = Vec::with_capacity(witnesses_len);

            for sorted_index in indexes.into_iter() {
                let table = &table_entries[idx];
                s_for_column.push(table[sorted_index]);
            }

            column_contributions.push(s_for_column);
        }


        Ok(column_contributions)
    }

    pub fn make_state_and_witness_polynomials(
        &self,
        worker: &Worker,
        with_finalization: bool
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<Vec<E::Fr>>), SynthesisError>
    {
        if with_finalization {
            assert!(self.is_finalized);
        }

        let mut full_assignments = if with_finalization {
            vec![Vec::with_capacity((self.n()+1).next_power_of_two()); P::STATE_WIDTH]
        } else {
            vec![Vec::with_capacity(self.n()+1); P::STATE_WIDTH]
        };

        let pad_to = if with_finalization {
            (self.n()+1).next_power_of_two()
        } else {
            self.n()+1
        };

        let num_input_gates = self.num_input_gates;
        let num_aux_gates = self.num_aux_gates;

        full_assignments[0].extend_from_slice(&self.input_assingments);
        assert!(full_assignments[0].len() == num_input_gates);
        for i in 1..P::STATE_WIDTH {
            full_assignments[i].resize(num_input_gates, E::Fr::zero());
        }

        let dummy = Self::get_dummy_variable();

        worker.scope(full_assignments.len(), |scope, chunk| {
            for (i, lh) in full_assignments.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let id = PolyIdentifier::VariablesPolynomial(idx);
                        let poly_ref = self.aux_storage.state_map.get(&id).unwrap();
                        for i in 0..num_aux_gates {
                            let var = poly_ref.get(i).unwrap_or(&dummy);
                            let value = self.get_value(*var).unwrap();
                            lh.push(value);
                        }
                    }
                });
            }
        });

        for p in full_assignments.iter_mut() {
            p.resize(pad_to - 1, E::Fr::zero());
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), pad_to - 1);
        }

        Ok((full_assignments, vec![]))
    }

    pub fn make_assembled_poly_storage(&self, worker: &Worker, with_finalization: bool) -> Result<AssembledPolynomialStorage<E>, SynthesisError> {
        if with_finalization {
            assert!(self.is_finalized);
        }
        
        let (state_polys, witness_polys) = self.make_state_and_witness_polynomials(&worker, with_finalization)?;
        let setup_polys_map = self.make_setup_polynomials(with_finalization)?;
        let gate_selectors = self.output_gate_selectors(&worker)?;

        let mut state_polys_map = std::collections::HashMap::new();
        for (idx, poly) in state_polys.into_iter().enumerate() {
            let key = PolyIdentifier::VariablesPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            state_polys_map.insert(key, p);
        }

        let mut witness_polys_map = std::collections::HashMap::new();
        for (idx, poly) in witness_polys.into_iter().enumerate() {
            let key = PolyIdentifier::WitnessPolynomial(idx);
            let p = Polynomial::from_values_unpadded(poly)?;
            witness_polys_map.insert(key, p);
        }

        let mut gate_selectors_map = std::collections::HashMap::new();
        for (gate, poly) in self.sorted_gates.iter().zip(gate_selectors.into_iter()) {
            let key = gate.clone();
            let p = Polynomial::from_values_unpadded(poly)?;
            gate_selectors_map.insert(key, p);
        }

        let assembled = AssembledPolynomialStorage::<E> {
            state_map: state_polys_map,
            witness_map: witness_polys_map,
            setup_map: setup_polys_map,
            scratch_space: std::collections::HashMap::new(),
            gate_selectors: gate_selectors_map,
            is_bitreversed: false,
            lde_factor: 1
        };

        Ok(assembled)
    }

    pub fn create_monomial_storage(
        worker: &Worker,
        omegas_inv: &OmegasInvBitreversed<E::Fr>,
        value_form_storage: &AssembledPolynomialStorage<E>,
        include_setup: bool,
    ) -> Result<AssembledPolynomialStorageForMonomialForms<E>, SynthesisError> {
        assert_eq!(value_form_storage.lde_factor, 1);
        assert!(value_form_storage.is_bitreversed == false);

        let mut monomial_storage = AssembledPolynomialStorageForMonomialForms::<E>::new();

        for (&k, v) in value_form_storage.state_map.iter() {
            let mon_form = v.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker, 
                omegas_inv, 
                &E::Fr::one()
            )?;
            monomial_storage.state_map.insert(k, mon_form);
        }

        for (&k, v) in value_form_storage.witness_map.iter() {
            let mon_form = v.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker, 
                omegas_inv, 
                &E::Fr::one()
            )?;
            monomial_storage.witness_map.insert(k, mon_form);
        }

        for (k, v) in value_form_storage.gate_selectors.iter() {
            let mon_form = v.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker, 
                omegas_inv, 
                &E::Fr::one()
            )?;
            monomial_storage.gate_selectors.insert(k.box_clone(), mon_form);
        }

        if include_setup {
            for (&k, v) in value_form_storage.setup_map.iter() {
                let mon_form = v.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                    &worker, 
                    omegas_inv, 
                    &E::Fr::one()
                )?;
                monomial_storage.setup_map.insert(k, mon_form);
            }
        }

        Ok(monomial_storage)
    }

    pub fn create_lde_storage(
        worker: &Worker, 
        omegas: &BitReversedOmegas<E::Fr>, 
        lde_factor: usize,
        monomial_storage: &AssembledPolynomialStorageForMonomialForms<E>
    ) -> Result<AssembledPolynomialStorage<E>, SynthesisError> {
        unimplemented!()
    }

    pub fn prover_stub(self, worker: &Worker) -> Result<(), SynthesisError> {
        use crate::pairing::CurveAffine;

        assert!(self.is_finalized);

        let values_storage = self.make_assembled_poly_storage(worker, true)?;
        let permutation_polys = self.make_permutations(&worker);

        let num_state_polys = <Self as ConstraintSystem<E>>::Params::STATE_WIDTH;
        let num_witness_polys = <Self as ConstraintSystem<E>>::Params::WITNESS_WIDTH;
        
        assert_eq!(permutation_polys.len(), num_state_polys);

        let required_domain_size = self.n() + 1;
        assert!(required_domain_size.is_power_of_two());

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(required_domain_size);
        let omegas_inv_bitreversed = <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(required_domain_size);

        let mut ldes_storage = AssembledPolynomialStorage::<E>::new(
            true, 
            self.max_constraint_degree.next_power_of_two()
        );
        let monomials_storage = Self::create_monomial_storage(
            &worker, 
            &omegas_inv_bitreversed, 
            &values_storage, 
            true
        )?;

        // step 1 - commit state and witness, enumerated. Also commit sorted polynomials for table arguments
        let mut commitments = vec![];

        for i in 0..num_state_polys {
            // TODO
            let id = PolyIdentifier::VariablesPolynomial(i);
            let commitment = E::G1Affine::zero();
            commitments.push(commitment);
        }

        for i in 0..num_witness_polys {
            // TODO
            let id = PolyIdentifier::WitnessPolynomial(i);
            let commitment = E::G1Affine::zero();
            commitments.push(commitment);
        }

        // step 1.5 - if there are lookup tables then draw random "eta" to linearlize over tables
        let mut lookup_data: Option<LookupDataHolder<E>> = if self.tables.len() > 0 {
            // TODO: Some of those values are actually part of the setup, but deal with it later

            let eta = E::Fr::from_str("987").unwrap();

            // these are selected rows from witness (where lookup applies)
            let mut f_polys_values = self.calculate_f_poly_contribution_from_witness(&values_storage)?;
            assert_eq!(f_polys_values.len(), 4);

            let witness_len = f_polys_values[0].len();
            assert_eq!(witness_len, required_domain_size - 1);

            let mut f_poly_values_aggregated = f_polys_values.drain(0..1).collect::<Vec<_>>().pop().unwrap();
            let mut current = eta;
            for t in f_polys_values.into_iter() {
                let op = BinopAddAssignScaled::new(current);
                binop_over_slices(&worker, &op, &mut f_poly_values_aggregated, &t);
                
                current.mul_assign(&eta);
            }

            // these are unsorted rows of lookup tables
            let mut t_poly_ends = self.calculate_t_polynomial_values_for_single_application_tables()?;

            assert_eq!(t_poly_ends.len(), 4);

            let mut t_poly_values_aggregated = t_poly_ends.drain(0..1).collect::<Vec<_>>().pop().unwrap();
            let mut current = eta;
            for t in t_poly_ends.into_iter() {
                let op = BinopAddAssignScaled::new(current);
                binop_over_slices(&worker, &op, &mut t_poly_values_aggregated, &t);
                
                current.mul_assign(&eta);
            }

            let copy_start = witness_len - t_poly_values_aggregated.len();
            let mut full_t_poly_values = vec![E::Fr::zero(); witness_len];
            let mut full_t_poly_values_shifted = full_t_poly_values.clone();

            full_t_poly_values[copy_start..].copy_from_slice(&t_poly_values_aggregated);
            full_t_poly_values_shifted[(copy_start - 1)..(witness_len-1)].copy_from_slice(&t_poly_values_aggregated);

            assert!(full_t_poly_values[0].is_zero());

            let mut s_poly_ends = self.calculate_s_poly_contributions_from_witness()?;
            assert_eq!(s_poly_ends.len(), 4);

            let mut s_poly_values_aggregated = s_poly_ends.drain(0..1).collect::<Vec<_>>().pop().unwrap();
            let mut current = eta;
            for t in s_poly_ends.into_iter() {
                let op = BinopAddAssignScaled::new(current);
                binop_over_slices(&worker, &op, &mut s_poly_values_aggregated, &t);
                
                current.mul_assign(&eta);
            }

            let sorted_copy_start = witness_len - s_poly_values_aggregated.len();

            let mut full_s_poly_values = vec![E::Fr::zero(); witness_len];
            let mut full_s_poly_values_shifted = full_s_poly_values.clone();

            full_s_poly_values[sorted_copy_start..].copy_from_slice(&s_poly_values_aggregated);
            full_s_poly_values_shifted[(sorted_copy_start - 1)..(witness_len-1)].copy_from_slice(&s_poly_values_aggregated);

            assert!(full_s_poly_values[0].is_zero());

            let data = LookupDataHolder::<E> {
                f_poly_unpadded_values: Some(Polynomial::from_values_unpadded(f_poly_values_aggregated)?),
                t_poly_unpadded_values: Some(Polynomial::from_values_unpadded(full_t_poly_values)?),
                t_shifted_unpadded_values: Some(Polynomial::from_values_unpadded(full_t_poly_values_shifted)?),
                s_poly_unpadded_values: Some(Polynomial::from_values_unpadded(full_s_poly_values)?),
                s_shifted_unpadded_values: Some(Polynomial::from_values_unpadded(full_s_poly_values_shifted)?),
                f_poly_monomial: None,
                t_poly_monomial: None,
                s_poly_monomial: None,
            };

            Some(data)
        } else {
            None
        };

        if self.multitables.len() > 0 {
            unimplemented!("do not support multitables yet")
        }

        // step 2 - grand product arguments

        let beta_for_copy_permutation = E::Fr::from_str("123").unwrap();
        let gamma_for_copy_permutation = E::Fr::from_str("456").unwrap();

        // copy permutation grand product argument

        let mut grand_products_protos_with_gamma = vec![];

        for i in 0..num_state_polys {
            let id = PolyIdentifier::VariablesPolynomial(i);

            let mut p = values_storage.state_map.get(&id).unwrap().clone();
            p.add_constant(&worker, &gamma_for_copy_permutation);

            grand_products_protos_with_gamma.push(p);
        }
        
        let required_domain_size = required_domain_size;

        let domain = Domain::new_for_size(required_domain_size as u64)?;

        let mut domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, 
            &worker
        );

        domain_elements.pop().expect("must pop last element for omega^i");

        let non_residues = make_non_residues(num_state_polys - 1, &domain);

        let mut domain_elements_poly_by_beta = Polynomial::from_values_unpadded(domain_elements)?;
        domain_elements_poly_by_beta.scale(&worker, beta_for_copy_permutation);

        // we take A, B, C, ... values and form (A + beta * X * non_residue + gamma), etc and calculate their grand product

        let mut z_num = {
            let mut grand_products_proto_it = grand_products_protos_with_gamma.iter().cloned();

            let mut z_1 = grand_products_proto_it.next().unwrap();
            z_1.add_assign(&worker, &domain_elements_poly_by_beta);

            for (mut p, non_res) in grand_products_proto_it.zip(non_residues.iter()) {
                p.add_assign_scaled(&worker, &domain_elements_poly_by_beta, non_res);
                z_1.mul_assign(&worker, &p);
            }

            z_1
        };

        // we take A, B, C, ... values and form (A + beta * perm_a + gamma), etc and calculate their grand product

        let mut permutation_polynomials_values_of_size_n_minus_one = vec![];
        
        for p in permutation_polys.iter() {
            let mut coeffs = p.clone().into_coeffs();
            coeffs.pop().unwrap();

            let p = Polynomial::from_values_unpadded(coeffs)?;
            permutation_polynomials_values_of_size_n_minus_one.push(p);
        }

        let z_den = {
            assert_eq!(
                permutation_polynomials_values_of_size_n_minus_one.len(), 
                grand_products_protos_with_gamma.len()
            );
            let mut grand_products_proto_it = grand_products_protos_with_gamma.into_iter();
            let mut permutation_polys_it = permutation_polynomials_values_of_size_n_minus_one.iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(&worker, permutation_polys_it.next().unwrap(), &beta_for_copy_permutation);

            for (mut p, perm) in grand_products_proto_it
                                            .zip(permutation_polys_it) {
                // permutation polynomials 
                p.add_assign_scaled(&worker, &perm, &beta_for_copy_permutation);
                z_2.mul_assign(&worker, &p);
            }

            z_2.batch_inversion(&worker)?;

            z_2
        };

        z_num.mul_assign(&worker, &z_den);
        drop(z_den);

        let z = z_num.calculate_shifted_grand_product(&worker)?;
        drop(z_num);

        assert!(z.size().is_power_of_two());

        assert!(z.as_ref()[0] == E::Fr::one());

        let copy_permutation_z_in_monomial_form = z.ifft_using_bitreversed_ntt(
            &worker, 
            &omegas_inv_bitreversed, 
            &E::Fr::one()
        )?;

        // TODO: move to setup
        let mut permutation_polys_in_monomial_form = vec![];
        for p in permutation_polys.into_iter() {
            let p = p.ifft_using_bitreversed_ntt(
                &worker, 
                &omegas_inv_bitreversed, 
                &E::Fr::one()
            )?;

            permutation_polys_in_monomial_form.push(p);
        }

        let mut beta_for_lookup = None; 
        let mut gamma_for_lookup = None;

        let mut lookup_z_poly_in_monomial_form = if let Some(data) = lookup_data.as_mut() {
            let beta_for_lookup_permutation = E::Fr::from_str("789").unwrap();
            let gamma_for_lookup_permutation = E::Fr::from_str("1230").unwrap();

            beta_for_lookup = Some(beta_for_lookup_permutation);
            gamma_for_lookup = Some(gamma_for_lookup_permutation);
    
            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);
    
            let expected = gamma_beta.pow([(required_domain_size-1) as u64]);
            
            let f_poly_unpadded_values = data.f_poly_unpadded_values.take().unwrap();
            let t_poly_unpadded_values = data.t_poly_unpadded_values.take().unwrap();
            let t_shifted_unpadded_values = data.t_shifted_unpadded_values.take().unwrap();
            let s_poly_unpadded_values = data.s_poly_unpadded_values.take().unwrap();
            let s_shifted_unpadded_values = data.s_shifted_unpadded_values.take().unwrap();

            // Z(x*omega) = Z(x) * 
            // (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) / 
            // (\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) 

            let mut z_num = {
                // (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))

                let mut t = t_poly_unpadded_values.clone();
                t.add_assign_scaled(&worker, &t_shifted_unpadded_values, &beta_for_lookup_permutation);
                t.add_constant(&worker, &gamma_beta);

                let mut tmp = f_poly_unpadded_values.clone();
                tmp.add_constant(&worker, &gamma_for_lookup_permutation);
                tmp.scale(&worker, beta_plus_one);

                t.mul_assign(&worker, &tmp);
                drop(tmp);

                t
            };

            let z_den = {
                // (\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

                let mut t = s_poly_unpadded_values.clone();
                t.add_assign_scaled(&worker, &s_shifted_unpadded_values, &beta_for_lookup_permutation);
                t.add_constant(&worker, &gamma_beta);

                t.batch_inversion(&worker)?;

                t
            };

            z_num.mul_assign(&worker, &z_den);
            drop(z_den);

            let z = z_num.calculate_shifted_grand_product(&worker)?;
            drop(z_num);

            assert!(z.size().is_power_of_two());

            assert_eq!(z.as_ref()[0], E::Fr::one());
            assert_eq!(*z.as_ref().last().unwrap(), expected);

            let f_poly_monomial = f_poly_unpadded_values.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker,
                &omegas_inv_bitreversed,
                &E::Fr::one()
            )?;

            let t_poly_monomial = t_poly_unpadded_values.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker,
                &omegas_inv_bitreversed,
                &E::Fr::one()
            )?;

            let s_poly_monomial = s_poly_unpadded_values.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(
                &worker,
                &omegas_inv_bitreversed,
                &E::Fr::one()
            )?;

            data.f_poly_monomial = Some(f_poly_monomial);
            data.t_poly_monomial = Some(t_poly_monomial);
            data.s_poly_monomial = Some(s_poly_monomial);

            let z = z.ifft_using_bitreversed_ntt(
                &worker, 
                &omegas_inv_bitreversed, 
                &E::Fr::one()
            )?;

            Some(z)
        } else {
            None
        };

        // TODO: commit to z polynomials

        // now draw alpha and add all the contributions to the quotient polynomial

        let alpha = E::Fr::from_str("1234567890").unwrap();
        
        let mut total_powers_of_alpha_for_gates = 0;
        for g in self.sorted_gates.iter() {
            total_powers_of_alpha_for_gates += g.num_quotient_terms();
        }

        println!("Have {} terms from {} gates", total_powers_of_alpha_for_gates, self.sorted_gates.len());

        let mut current_alpha = E::Fr::one();
        let mut powers_of_alpha_for_gates = Vec::with_capacity(total_powers_of_alpha_for_gates);
        powers_of_alpha_for_gates.push(current_alpha);
        for _ in 1..total_powers_of_alpha_for_gates {
            current_alpha.mul_assign(&alpha);
            powers_of_alpha_for_gates.push(current_alpha);
        }

        assert_eq!(powers_of_alpha_for_gates.len(), total_powers_of_alpha_for_gates);

        let mut all_gates = self.sorted_gates.clone();
        let num_different_gates = self.sorted_gates.len();

        let mut challenges_slice = &powers_of_alpha_for_gates[..];

        let mut lde_factor = num_state_polys;
        for g in self.sorted_gates.iter() {
            let degree = g.degree();
            if degree > lde_factor {
                lde_factor = degree;
            }
        }

        assert!(lde_factor <= 4);

        let coset_factor = E::Fr::multiplicative_generator();

        let mut t_poly = {
            let gate = all_gates.drain(0..1).into_iter().next().unwrap();
            assert!(<Self as ConstraintSystem<E>>::MainGate::default().into_internal() == gate);
            let gate = <Self as ConstraintSystem<E>>::MainGate::default();
            let num_challenges = gate.num_quotient_terms();
            let (for_gate, rest) = challenges_slice.split_at(num_challenges);
            challenges_slice = rest;

            let input_values = self.input_assingments.clone();

            let mut t = gate.contribute_into_quotient_for_public_inputs(
                required_domain_size,
                &input_values,
                &mut ldes_storage,
                &monomials_storage,
                for_gate,
                &omegas_bitreversed,
                &omegas_inv_bitreversed,
                &worker
            )?;

            if num_different_gates > 1 {
                // we have to multiply by the masking poly (selector)
                
                let monomial_selector = monomials_storage.gate_selectors.get(gate.as_internal()).unwrap();
                let lde = monomial_selector.clone_padded_to_domain()?.bitreversed_lde_using_bitreversed_ntt(
                    &worker, 
                    lde_factor, 
                    &omegas_bitreversed, 
                    &coset_factor
                )?;

                t.mul_assign(&worker, &lde);
                drop(lde);
            }

            t
        };

        let non_main_gates = all_gates;

        for gate in non_main_gates.into_iter() {
            let num_challenges = gate.num_quotient_terms();
            let (for_gate, rest) = challenges_slice.split_at(num_challenges);
            challenges_slice = rest;

            let mut contribution = gate.contribute_into_quotient(
                required_domain_size,
                &mut ldes_storage,
                &monomials_storage,
                for_gate,
                &omegas_bitreversed,
                &omegas_inv_bitreversed,
                &worker
            )?;

            {
                // we have to multiply by the masking poly (selector)
                
                let monomial_selector = monomials_storage.gate_selectors.get(&gate).unwrap();
                let lde = monomial_selector.clone_padded_to_domain()?.bitreversed_lde_using_bitreversed_ntt(
                    &worker, 
                    lde_factor, 
                    &omegas_bitreversed, 
                    &coset_factor
                )?;

                contribution.mul_assign(&worker, &lde);
                drop(lde);
            }

            t_poly.add_assign(&worker, &contribution);
        }

        assert_eq!(challenges_slice.len(), 0);

        println!("Power of alpha for a start of normal permutation argument = {}", total_powers_of_alpha_for_gates);

        // perform copy-permutation argument

        // we precompute L_{0} here cause it's necessary for both copy-permutation and lookup permutation

        // z(omega^0) - 1 == 0
        let l_0 = calculate_lagrange_poly::<E::Fr>(&worker, required_domain_size.next_power_of_two(), 0)?;

        let l_0_coset_lde_bitreversed = l_0.bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            lde_factor, 
            &omegas_bitreversed, 
            &coset_factor
        )?;

        {
            // now compute the permutation argument

            let z_coset_lde_bitreversed = copy_permutation_z_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            assert!(z_coset_lde_bitreversed.size() == required_domain_size*lde_factor);

            let z_shifted_coset_lde_bitreversed = z_coset_lde_bitreversed.clone_shifted_assuming_bitreversed(
                lde_factor,
                &worker,
            )?;

            assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size*lde_factor);

            // For both Z_1 and Z_2 we first check for grand products
            // z*(X)(A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma) - 
            // - (A + beta*perm_a(X) + gamma)(B + beta*perm_b(X) + gamma)(C + beta*perm_c(X) + gamma)*Z(X*Omega)== 0

            // we use evaluations of the polynomial X and K_i * X on a large domain's coset
            let mut contrib_z = z_coset_lde_bitreversed.clone();

            // precompute x poly
            let mut x_poly = Polynomial::from_values(vec![
                coset_factor;
                required_domain_size*lde_factor
            ])?;
            x_poly.distribute_powers(&worker, z_shifted_coset_lde_bitreversed.omega);
            x_poly.bitreverse_enumeration(&worker);
    
            assert_eq!(x_poly.size(), required_domain_size * lde_factor);

            // A + beta*X + gamma

            let mut tmp = ldes_storage.state_map.get(&PolyIdentifier::VariablesPolynomial(0)).unwrap().clone();
            tmp.add_constant(&worker, &gamma_for_copy_permutation);
            tmp.add_assign_scaled(&worker, &x_poly, &beta_for_copy_permutation);
            contrib_z.mul_assign(&worker, &tmp);

            assert_eq!(non_residues.len() + 1, num_state_polys);

            for (poly_idx, non_res) in (1..num_state_polys).zip(non_residues.iter()) {
                let mut factor = beta_for_copy_permutation;
                factor.mul_assign(&non_res);

                let key = PolyIdentifier::VariablesPolynomial(poly_idx);
                tmp.reuse_allocation(&ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(&worker, &gamma_for_copy_permutation);
                tmp.add_assign_scaled(&worker, &x_poly, &factor);
                contrib_z.mul_assign(&worker, &tmp);
            }

            t_poly.add_assign_scaled(&worker, &contrib_z, &current_alpha);

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            for (poly_idx, perm) in (0..4).zip(permutation_polys_in_monomial_form.iter()) {
                let key = PolyIdentifier::VariablesPolynomial(poly_idx);

                tmp.reuse_allocation(&ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(&worker, &gamma_for_copy_permutation);
                let perm = perm.clone().bitreversed_lde_using_bitreversed_ntt(
                    &worker, 
                    lde_factor, 
                    &omegas_bitreversed, 
                    &coset_factor
                )?;
                tmp.add_assign_scaled(&worker, &perm, &beta_for_copy_permutation);
                contrib_z.mul_assign(&worker, &tmp);
                drop(perm);
            }

            t_poly.sub_assign_scaled(&worker, &contrib_z, &current_alpha);

            drop(contrib_z);

            drop(tmp);

            // Z(x) * L_{0}(x) - 1 == 0
            current_alpha.mul_assign(&alpha);

            {
                let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
                z_minus_one_by_l_0.sub_constant(&worker, &E::Fr::one());

                z_minus_one_by_l_0.mul_assign(&worker, &l_0_coset_lde_bitreversed);

                t_poly.add_assign_scaled(&worker, &z_minus_one_by_l_0, &current_alpha);
            }
        }

        let inverse_divisor_on_coset_lde_natural_ordering = {
            let mut vanishing_poly_inverse_bitreversed =
                evaluate_vanishing_polynomial_of_degree_on_domain_size::<E::Fr>(
                    required_domain_size as u64,
                    &E::Fr::multiplicative_generator(),
                    (required_domain_size * lde_factor) as u64,
                    &worker,
                )?;
            vanishing_poly_inverse_bitreversed.batch_inversion(&worker)?;
            // vanishing_poly_inverse_bitreversed.bitreverse_enumeration(&worker)?;

            vanishing_poly_inverse_bitreversed
        };

        t_poly.bitreverse_enumeration(&worker);

        t_poly.mul_assign(&worker, &inverse_divisor_on_coset_lde_natural_ordering);

        drop(inverse_divisor_on_coset_lde_natural_ordering);

        // add contribution from grand product for loopup polys if there is one

        if let Some(z_poly_in_monomial_form) = lookup_z_poly_in_monomial_form.take() {
            let beta_for_lookup_permutation = beta_for_lookup.unwrap();
            let gamma_for_lookup_permutation = gamma_for_lookup.unwrap();

            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);
    
            let expected = gamma_beta.pow([(required_domain_size-1) as u64]);

            current_alpha.mul_assign(&alpha);

            // same grand product argument for lookup permutation except divisor is now with one point cut

            let z_lde = z_poly_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            let z_lde_shifted = z_lde.clone_shifted_assuming_bitreversed(
                lde_factor,
                &worker
            )?;

            // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -  
            // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) 

            let data = lookup_data.as_ref().unwrap();

            let s_lde = data.s_poly_monomial.as_ref().unwrap().clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            let s_lde_shifted = s_lde.clone_shifted_assuming_bitreversed(
                lde_factor,
                &worker
            )?;

            // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

            let mut contribution = s_lde;
            contribution.add_assign_scaled(&worker, &s_lde_shifted, &beta_for_lookup_permutation);
            contribution.add_constant(&worker, &gamma_beta);
            contribution.mul_assign(&worker, &z_lde_shifted);

            drop(s_lde_shifted);
            drop(z_lde_shifted);

            let t_lde = data.t_poly_monomial.as_ref().unwrap().clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            let t_lde_shifted = t_lde.clone_shifted_assuming_bitreversed(
                lde_factor,
                &worker
            )?;

            let f_lde = data.f_poly_monomial.as_ref().unwrap().clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))

            let mut tmp = f_lde;
            tmp.add_constant(&worker, &gamma_for_lookup_permutation);
            tmp.mul_assign(&worker, &z_lde);
            tmp.scale(&worker, beta_plus_one);

            let mut t = t_lde;
            t.add_assign_scaled(&worker, &t_lde_shifted, &beta_for_lookup_permutation);
            t.add_constant(&worker, &gamma_beta);

            tmp.mul_assign(&worker, &t);
            
            drop(t);
            drop(t_lde_shifted);

            contribution.sub_assign(&worker, &tmp);

            contribution.scale(&worker, current_alpha);

            // check that (Z(x) - 1) * L_{0} == 0
            current_alpha.mul_assign(&alpha);
            
            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(&worker, &E::Fr::one());
            tmp.mul_assign(&worker, &l_0_coset_lde_bitreversed);

            drop(l_0_coset_lde_bitreversed);

            // {
            //     let mut mon = tmp.clone();
            //     mon.bitreverse_enumeration(&worker);
            //     let mon = mon.icoset_fft_for_generator(&worker, &coset_factor);
            //     let vals = mon.fft(&worker);
    
            //     println!("Z(X) - 1 values lde = {:?}", vals.as_ref());
            // }

            contribution.add_assign_scaled(&worker, &tmp, &current_alpha);

            // check that (Z(x) - expected) * L_{n-1}  == 0

            current_alpha.mul_assign(&alpha);

            let l_last = calculate_lagrange_poly::<E::Fr>(&worker, required_domain_size.next_power_of_two(), required_domain_size - 1)?;

            let l_last_coset_lde_bitreversed = l_last.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                lde_factor, 
                &omegas_bitreversed, 
                &coset_factor
            )?;

            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(&worker, &expected);
            tmp.mul_assign(&worker, &l_last_coset_lde_bitreversed);

            drop(l_last_coset_lde_bitreversed);

            contribution.add_assign_scaled(&worker, &tmp, &current_alpha);

            drop(tmp);
            drop(z_lde);

            contribution.bitreverse_enumeration(&worker);

            let vanishing_for_lookup = {
                let normally_enumerated = calculate_inverse_vanishing_polynomial_with_last_point_cut(
                    &worker,
                    required_domain_size * lde_factor,
                    required_domain_size,
                    coset_factor,
                )?;

                normally_enumerated
            };

            contribution.mul_assign(&worker, &vanishing_for_lookup);

            t_poly.add_assign(&worker, &contribution);

            drop(contribution);

            lookup_z_poly_in_monomial_form = Some(z_poly_in_monomial_form);
        } else {
            drop(l_0_coset_lde_bitreversed);
        }
        
        let t_poly = t_poly.icoset_fft_for_generator(&worker, &coset_factor);

        println!("Lde factor = {}", lde_factor);

        // println!("Quotient poly = {:?}", t_poly.as_ref());

        // degree is 4n-4

        let l = t_poly.as_ref().len();
        assert_eq!(&t_poly.as_ref()[(l-4)..], &[E::Fr::zero(); 4][..]);

        println!("Quotient poly degree = {}", get_degree::<E::Fr>(&t_poly));

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;
    use crate::pairing::ff::PrimeField;

    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            // 2a - b = 0

            let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
            let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
            let mut term = MainGateTerm::new();
            term.add_assign(two_a);
            term.add_assign(minus_b);

            cs.allocate_main_gate(term)?;

            // c - a*b == 0 

            let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
            ab_term.scale(&negative_one);
            let c_term = ArithmeticTerm::from_variable(c);
            let mut term = MainGateTerm::new();
            term.add_assign(c_term);
            term.add_assign(ab_term);

            cs.allocate_main_gate(term)?;

            // d - 100 == 0 

            let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
            let d_term = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(d_term);
            term.sub_assign(hundred);

            cs.allocate_main_gate(term)?;

            let gamma = cs.alloc_input(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            // gamma - b == 0 

            let gamma_term = ArithmeticTerm::from_variable(gamma);
            let b_term = ArithmeticTerm::from_variable(b);
            let mut term = MainGateTerm::new();
            term.add_assign(gamma_term);
            term.sub_assign(b_term);

            cs.allocate_main_gate(term)?;

            // 2a
            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(a, two));

            let dummy = CS::get_dummy_variable();

            // 2a - d_next = 0

            let (vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            *coeffs.last_mut().unwrap() = negative_one;

            // here d is equal = 2a, so we need to place b there
            // and compensate it with -b somewhere before

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable(b));

            // b + 0 + 0 - b = 0
            let (mut vars, mut coeffs) = CS::MainGate::format_term(term, dummy)?;
            coeffs[3] = negative_one;
            vars[3] = b;

            cs.new_single_gate_for_trace_step(&CS::MainGate::default(), 
                &coeffs, 
                &vars, 
                &[]
            )?;

            Ok(())
        }
    }

    struct TestCircuit4WithLookups<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E> for TestCircuit4WithLookups<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            let columns = vec![PolyIdentifier::VariablesPolynomial(0), PolyIdentifier::VariablesPolynomial(1), PolyIdentifier::VariablesPolynomial(2)];
            let range_table = LookupTableApplication::new_range_table_of_width_3(2, columns.clone())?;
            let range_table_name = range_table.functional_name();

            let xor_table = LookupTableApplication::new_xor_table(2, columns.clone())?;
            let xor_table_name = xor_table.functional_name();

            let and_table = LookupTableApplication::new_and_table(2, columns)?;
            let and_table_name = and_table.functional_name();

            cs.add_table(range_table)?;
            cs.add_table(xor_table)?;
            cs.add_table(and_table)?;

            let a = cs.alloc(|| {
                Ok(E::Fr::from_str("10").unwrap())
            })?;

            println!("A = {:?}", a);

            let b = cs.alloc(|| {
                Ok(E::Fr::from_str("20").unwrap())
            })?;

            println!("B = {:?}", b);

            let c = cs.alloc(|| {
                Ok(E::Fr::from_str("200").unwrap())
            })?;

            println!("C = {:?}", c);

            let d = cs.alloc(|| {
                Ok(E::Fr::from_str("100").unwrap())
            })?;

            println!("D = {:?}", d);

            let e = cs.alloc(|| {
                Ok(E::Fr::from_str("2").unwrap())
            })?;

            let binary_x_value = E::Fr::from_str("3").unwrap();
            let binary_y_value = E::Fr::from_str("1").unwrap();

            let binary_x = cs.alloc(|| {
                Ok(binary_x_value)
            })?;

            let binary_y = cs.alloc(|| {
                Ok(binary_y_value)
            })?;

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            // 2a - b = 0

            let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
            let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
            let mut term = MainGateTerm::new();
            term.add_assign(two_a);
            term.add_assign(minus_b);

            cs.allocate_main_gate(term)?;

            // c - a*b == 0 

            let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
            ab_term.scale(&negative_one);
            let c_term = ArithmeticTerm::from_variable(c);
            let mut term = MainGateTerm::new();
            term.add_assign(c_term);
            term.add_assign(ab_term);

            cs.allocate_main_gate(term)?;

            let dummy = CS::get_dummy_variable();

            // and table
            {
                let table = cs.get_table(&and_table_name)?;
                let num_keys_and_values = table.width();

                let and_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

                let binary_z = cs.alloc(|| {
                    Ok(and_result_value)
                })?;

                cs.begin_gates_batch_for_step()?;

                let vars = [binary_x, binary_y, binary_z, dummy];
                cs.allocate_variables_without_gate(
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            // d - 100 == 0 

            let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
            let d_term = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(d_term);
            term.sub_assign(hundred);

            cs.allocate_main_gate(term)?;

            let var_zero = cs.get_explicit_zero()?;

            // range table
            {
                let table = cs.get_table(&range_table_name)?;
                let num_keys_and_values = table.width();

                cs.begin_gates_batch_for_step()?;

                let mut term = MainGateTerm::<E>::new();
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(e, E::Fr::zero()));
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(var_zero, E::Fr::zero()));
                term.add_assign(ArithmeticTerm::from_variable_and_coeff(var_zero, E::Fr::zero()));

                let (vars, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy)?;

                cs.new_gate_in_batch(
                    &CS::MainGate::default(),
                    &coeffs,
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            // xor table
            {
                let table = cs.get_table(&xor_table_name)?;
                let num_keys_and_values = table.width();

                let xor_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

                let binary_z = cs.alloc(|| {
                    Ok(xor_result_value)
                })?;

                cs.begin_gates_batch_for_step()?;

                let vars = [binary_x, binary_y, binary_z, dummy];
                cs.allocate_variables_without_gate(
                    &vars,
                    &[]
                )?;

                cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

                cs.end_gates_batch_for_step()?;
            }

            let one = cs.get_explicit_one()?;

            cs.new_single_gate_for_trace_step(
                &TestBitGate::default(),
                &[],
                &[one],
                &[],
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_trivial_circuit_with_gate_agnostic_cs() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.gates.len() == 1);

        // println!("Assembly state polys = {:?}", assembly.storage.state_map);

        // println!("Assembly setup polys = {:?}", assembly.storage.setup_map);    

        println!("Assembly contains {} gates", assembly.n());
        assembly.finalize();
        assert!(assembly.is_satisfied());

        assembly.finalize();

        let worker = Worker::new();

        let (_storage, _permutation_polys) = assembly.perform_setup(&worker).unwrap();
    }

    #[test]
    fn test_circuit_with_combined_lookups() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        let circuit = TestCircuit4WithLookups::<Bn256> {
            _marker: PhantomData
        };

        circuit.synthesize(&mut assembly).expect("must work");

        assert!(assembly.gates.len() == 2);  

        println!("Assembly contains {} gates", assembly.n());
        assert!(assembly.is_satisfied());

        assembly.finalize();

        println!("Finalized assembly contains {} gates", assembly.n());

        let worker = Worker::new();

        let _ = assembly.prover_stub(&worker).unwrap();
    }


    #[derive(Clone, Debug, Hash, Default)]
    pub struct TestBitGate;

    impl<E: Engine> GateInternal<E> for TestBitGate {
        fn name(&self) -> &'static str {
            "Test bit gate on A"
        }

        fn degree(&self) -> usize {
            2
        }

        fn can_include_public_inputs(&self) -> bool {
            false
        }

        fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
            vec![
                PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
            ]
        }

        fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
            vec![]
        }

        fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
            vec![
                PolyIdentifier::VariablesPolynomial(0),
            ]
        }

        fn benefits_from_linearization(&self) -> bool {
            false
        }

        fn linearizes_over(&self) -> Vec<PolyIdentifier> {
            vec![]
        }

        fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
            vec![]
        }

        fn num_quotient_terms(&self) -> usize {
            1
        }

        fn verify_on_row(&self, row: usize, poly_storage: &AssembledPolynomialStorage<E>, _last_row: bool) -> E::Fr {
            let q_a = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);
            
            let mut tmp = q_a;
            tmp.sub_assign(&E::Fr::one());
            tmp.mul_assign(&q_a);

            tmp
        }

        fn contribute_into_quotient(
            &self, 
            domain_size: usize,
            poly_storage: &mut AssembledPolynomialStorage<E>,
            monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
            challenges: &[E::Fr],
            omegas_bitreversed: &BitReversedOmegas<E::Fr>,
            omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
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

            // (A - 1) * A 
            let a_ref = get_from_map_unchecked(
                PolynomialInConstraint::VariablesPolynomial(0, TimeDilation(0)),
                ldes_storage
            );

            let mut tmp = a_ref.clone();
            drop(a_ref);

            let one = E::Fr::one();

            tmp.map(&worker,
                |el| {
                    let mut tmp = *el;
                    tmp.sub_assign(&one);
                    tmp.mul_assign(&*el);

                    *el = tmp;
                }, 
            );

            Ok(tmp)
        }

        fn contribute_into_linearization(
            &self, 
            domain_size: usize,
            at: E::Fr,
            queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
            monomials_storage: & AssembledPolynomialStorageForMonomialForms<E>,
            challenges: &[E::Fr],
            worker: &Worker
        ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
            unimplemented!("NYI")
        }
        fn contribute_into_verification_equation(
            &self, 
            domain_size: usize,
            at: E::Fr,
            queried_values: std::collections::HashMap<PolynomialInConstraint, E::Fr>,
            challenges: &[E::Fr],
        ) -> Result<E::Fr, SynthesisError> {
            unimplemented!("NYI")
        }

        fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
            None
        }

        fn box_clone(&self) -> Box<dyn GateInternal<E>> {
            Box::from(self.clone())
        }
    }

    impl<E: Engine> Gate<E> for TestBitGate {}
}