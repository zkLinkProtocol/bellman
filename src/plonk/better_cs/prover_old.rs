use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::plonk::domains::*;

use std::marker::PhantomData;

use super::cs::*;
use super::keys::{SetupPolynomials, Proof, SetupPolynomialsPrecomputations};

use crate::source::{DensityTracker, DensityTrackerersChain};

use crate::kate_commitment::*;

// #[derive(Debug, Clone)]
pub struct ProverAssembly<E: Engine, P: PlonkConstraintSystemParams<E>> {
    m: usize,
    n: usize,
    // input_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,
    // aux_gates: Vec<(P::StateVariables, P::ThisTraceStepCoefficients, P::NextTraceStepCoefficients)>,

    num_inputs: usize,
    num_aux: usize,

    input_assingments: Vec<E::Fr>,
    aux_assingments: Vec<E::Fr>,

    wire_assignments: Vec<Vec<E::Fr>>,

    aux_densities: Vec<DensityTracker>,

    inputs_map: Vec<usize>,
    dummy_var: Variable,

    is_finalized: bool,

    _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ConstraintSystem<E, P> for ProverAssembly<E, P> {
    // allocate a variable
    fn alloc<F>(&mut self, value: F) -> Result<Variable, SynthesisError>
    where
        F: FnOnce() -> Result<E::Fr, SynthesisError> 
    {
        let value = value()?;

        self.num_aux += 1;
        let index = self.num_aux;
        self.aux_assingments.push(value);

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

        // let dummy = self.get_dummy_variable();

        // let vars = P::StateVariables::from_variable_and_padding(input_var, dummy);
        // let this_step_coeffs = P::ThisTraceStepCoefficients::identity();
        // let next_step_coeffs = P::NextTraceStepCoefficients::empty();

        // self.input_gates.push((vars, this_step_coeffs, next_step_coeffs));

        Ok(input_var)

    }

    // allocate an abstract gate
    fn new_gate(&mut self, 
        variables: P::StateVariables, 
        this_step_coeffs: P::ThisTraceStepCoefficients,
        next_step_coeffs: P::NextTraceStepCoefficients
    ) -> Result<(), SynthesisError>
    {

        for (idx, &v) in variables.as_ref().iter().enumerate() {
            self.aux_densities[idx].add_element();
            let val = self.get_value(v)?;
            if val.is_zero() == false {
                self.aux_densities[idx].inc(self.n);
            }
            // if v != self.dummy_var {
            //     self.aux_densities[idx].inc(self.n);
            // }
        }
        // self.aux_gates.push((variables, this_step_coeffs, next_step_coeffs));
        self.n += 1;

        Ok(())
    }

    fn get_value(&self, var: Variable) -> Result<E::Fr, SynthesisError> {
        let value = match var {
            Variable(Index::Aux(0)) => {
                E::Fr::zero()
                // return Err(SynthesisError::AssignmentMissing);
            }
            Variable(Index::Input(0)) => {
                unreachable!();
                // return Err(SynthesisError::AssignmentMissing);
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

    fn get_dummy_variable(&self) -> Variable {
        self.dummy_variable()
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> ProverAssembly<E, P> {
    pub fn new() -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: vec![],
            aux_assingments: vec![],

            wire_assignments: vec![vec![]; P::STATE_WIDTH],
        
            aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: vec![],
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }

    pub fn new_with_size_hints(num_inputs: usize, num_aux: usize) -> Self {
        let tmp = Self {
            n: 0,
            m: 0,

            num_inputs: 0,
            num_aux: 0,

            input_assingments: Vec::with_capacity(num_inputs),
            aux_assingments: Vec::with_capacity(num_aux),

            wire_assignments: vec![Vec::with_capacity(num_inputs + num_aux); P::STATE_WIDTH],
        
            aux_densities: vec![DensityTracker::new(); P::STATE_WIDTH],

            inputs_map: Vec::with_capacity(num_inputs),
            dummy_var: Variable(Index::Aux(0)),

            is_finalized: false,

            _marker: std::marker::PhantomData
        };

        tmp
    }

    // return variable that is not in a constraint formally, but has some value
    fn dummy_variable(&self) -> Variable {
        Variable(Index::Aux(0))
    }

    pub fn num_gates(&self) -> usize {
        self.n
    }

    pub fn finalize(&mut self) {
        if self.is_finalized {
            return;
        }

        let n = self.n;
        if (n+1).is_power_of_two() {
            self.is_finalized = true;
            return;
        }

        self.n = (n+1).next_power_of_two() - 1;

        // let dummy = self.get_dummy_variable();

        // let vars = P::StateVariables::from_variable_and_padding(dummy, dummy);
        // let this_step_coeffs = P::ThisTraceStepCoefficients::empty();
        // let next_step_coeffs = P::NextTraceStepCoefficients::empty();

        // let empty_gate = (vars, this_step_coeffs, next_step_coeffs);

        // let new_aux_len = (n+1).next_power_of_two() - 1 - self.input_gates.len();

        // self.aux_gates.resize(new_aux_len, empty_gate);

        // let n = self.input_gates.len() + self.aux_gates.len();
        // assert!((n+1).is_power_of_two());

        self.is_finalized = true;
    }

    pub fn make_witness_polynomials(
        self
    ) -> Result<(Vec<Vec<E::Fr>>, Vec<DensityTracker>), SynthesisError>
    {
        assert!(self.is_finalized);

        let mut full_assignments = vec![Vec::with_capacity((self.n+1).next_power_of_two()); self.wire_assignments.len()];

        for inp in self.input_assingments.into_iter() {
            // inputs will always go into A wire
            full_assignments[0].push(inp);
            for i in 1..full_assignments.len() {
                full_assignments[i].push(E::Fr::zero());
            }
        }

        for (idx, aux) in self.wire_assignments.into_iter().enumerate() {
            full_assignments[idx].extend(aux);
            full_assignments[idx].resize((self.n+1).next_power_of_two() - 1, E::Fr::zero());
        }

        let mut aux_densities = self.aux_densities;

        for d in aux_densities.iter_mut() {
            d.pad((self.n+1).next_power_of_two() - 1);
        }

        for a in full_assignments.iter() {
            assert_eq!(a.len(), (self.n+1).next_power_of_two() - 1);
        }

        Ok((full_assignments, aux_densities))
    }
}

// later we can alias traits
// pub trait PlonkCsWidth3WithNextStep<E: Engine> = ConstraintSystem<E, PlonkCsWidth3WithNextStepParams>;

pub type ProverAssembly3WithNextStep<E> = ProverAssembly<E, PlonkCsWidth3WithNextStepParams>;
pub type ProverAssembly4WithNextStep<E> = ProverAssembly<E, PlonkCsWidth4WithNextStepParams>;

use crate::plonk::commitments::transcript::*;
use crate::plonk::fft::cooley_tukey_ntt::*;

impl<E: Engine> ProverAssembly4WithNextStep<E> {
    pub fn prove<T: Transcript<E::Fr>, CP: CTPrecomputations<E::Fr>, CPI: CTPrecomputations<E::Fr>>(
        self, 
        worker: &Worker, 
        setup: &SetupPolynomials<E, PlonkCsWidth4WithNextStepParams>,
        setup_precomputations: &SetupPolynomialsPrecomputations<E, PlonkCsWidth4WithNextStepParams>,
        crs_vals: &Crs<E, CrsForLagrangeForm>, 
        crs_mon: &Crs<E, CrsForMonomialForm>,
        omegas_bitreversed: &CP,
        omegas_inv_bitreversed: &CPI
    ) -> Result<Proof<E, PlonkCsWidth4WithNextStepParams>, SynthesisError> {
        use crate::pairing::CurveAffine;
        use std::sync::Arc;

        let mut transcript = T::new();

        assert!(self.is_finalized);

        let input_values = self.input_assingments.clone();

        for inp in input_values.iter() {
            transcript.commit_field_element(inp);
        }

        let num_inputs = self.num_inputs;

        let n = self.n;

        let required_domain_size = n + 1;
        assert!(required_domain_size.is_power_of_two());

        let (full_assignments, densities) = self.make_witness_polynomials()?;

        let mut input_density_a = DensityTracker::new();
        let mut input_density_other = DensityTracker::new();
        for i in 0..num_inputs {
            input_density_a.add_element();
            input_density_other.add_element();

            input_density_a.inc(i);
        }

        let mut input_densities = vec![input_density_a];
        input_densities.resize(densities.len(), input_density_other);

        let mut chained_densities = vec![];
        for (i, a) in input_densities.into_iter().zip(densities.into_iter()) {
            let chain = DensityTrackerersChain::new(i, a);
            chained_densities.push(Arc::new(chain));
        }

        let mut proof = Proof {
            num_inputs,
            n,
            input_values: input_values,
            wire_commitments: vec![],
            grand_product_commitments: vec![],
            quotient_poly_commitments: vec![],

            opening_at_z_proof: E::G1Affine::zero(),
            opening_at_z_omega_proof: E::G1Affine::zero(),

            _marker: std::marker::PhantomData
        };

        // Commit wire polynomials 

        for (wire_poly, density) in full_assignments.iter().zip(chained_densities.into_iter()) {
            let commitment = commit_using_values_with_density(
                wire_poly, 
                density, 
                &crs_vals, 
                &worker
            )?;

            transcript.commit_bytes(commitment.into_compressed().as_ref());

            proof.wire_commitments.push(commitment);
        }

        // now transform assignments in the polynomials

        let mut assignment_polynomials = vec![];
        for p in full_assignments.into_iter() {
            let p = Polynomial::from_values_unpadded(p)?;
            assignment_polynomials.push(p);
        }

        // make grand product polynomials

        // draw challenged for grand products

        let beta = transcript.get_challenge();
        let gamma = transcript.get_challenge();

        let mut grand_products_protos = assignment_polynomials.clone();

        for p in grand_products_protos.iter_mut() {
            p.add_constant(&worker, &gamma);
        }

        let domain = Domain::new_for_size(required_domain_size as u64)?;

        let mut domain_elements = materialize_domain_elements_with_natural_enumeration(
            &domain, 
            &worker
        );

        domain_elements.pop().unwrap();

        let mut domain_elements_poly_by_beta = Polynomial::from_values_unpadded(domain_elements)?;
        domain_elements_poly_by_beta.scale(&worker, beta);

        use super::generator::make_non_residues;

        let non_residues = make_non_residues::<E::Fr>(grand_products_protos.len() - 1);

        // let mut scaled_non_redisues = vec![];
        // scaled_non_redisues.push(non_residues[0]);
        // let mut tmp = non_residues[0];
        // for non_res in non_residues.iter().skip(1) {
        //     let mut inv = tmp.inverse().unwrap();
        //     let mut scaled_non_res = *non_res;
        //     scaled_non_res.mul_assign(&inv);

        //     scaled_non_redisues.push(scaled_non_res);

        //     tmp = *non_res;
        // }

        // we take A, B, C, ... values and form (A + beta * X * non_residue + gamma), etc and calculate their grand product

        let z_1 = {
            let mut grand_products_proto_it = grand_products_protos.iter().cloned();

            let mut z_1 = grand_products_proto_it.next().unwrap();
            z_1.add_assign(&worker, &domain_elements_poly_by_beta);

            for (mut p, non_res) in grand_products_proto_it.zip(non_residues.iter()) {
                p.add_assign_scaled(&worker, &domain_elements_poly_by_beta, non_res);
                z_1.mul_assign(&worker, &p);
            }

            let z_1 = z_1.calculate_shifted_grand_product(&worker)?;

            assert!(z_1.size().is_power_of_two());

            z_1
        };

        // we take A, B, C, ... values and form (A + beta * perm_a + gamma), etc and calculate their grand product

        let z_2 = {
            let mut grand_products_proto_it = grand_products_protos.into_iter();
            let mut permutation_polys_it = setup_precomputations.permutation_polynomials_values_of_size_n_minus_one.iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(&worker, &permutation_polys_it.next().unwrap(), &beta);

            for (mut p, perm) in grand_products_proto_it
                                            .zip(permutation_polys_it) {
                // permutation polynomials 
                p.add_assign_scaled(&worker, &perm, &beta);
                z_2.mul_assign(&worker, &p);
            }

            let z_2 = z_2.calculate_shifted_grand_product(&worker)?;

            assert!(z_2.size().is_power_of_two());

            z_2
        };

        assert!(z_1.as_ref()[0] == E::Fr::one());
        assert!(z_2.as_ref()[0] == E::Fr::one());
        assert!(z_2.as_ref().last().expect("must exist") == z_1.as_ref().last().expect("must exist"));

        let z_1_commitment = commit_using_values(
            &z_1, 
            &crs_vals, 
            &worker
        )?;

        let z_2_commitment = commit_using_values(
            &z_2, 
            &crs_vals, 
            &worker
        )?;

        transcript.commit_bytes(z_1_commitment.into_compressed().as_ref());
        transcript.commit_bytes(z_2_commitment.into_compressed().as_ref());

        // interpolate on the main domain
        let z_1_in_monomial_form = z_1.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
        let z_2_in_monomial_form = z_2.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;

        // those are z(x*Omega) formally
        let mut z_1_shifted_in_monomial_form = z_1_in_monomial_form.clone();
        z_1_shifted_in_monomial_form.distribute_powers(&worker, z_1_in_monomial_form.omega);
        
        let mut z_2_shifted_in_monomial_form = z_2_in_monomial_form.clone();
        z_2_shifted_in_monomial_form.distribute_powers(&worker, z_2_in_monomial_form.omega);

        // now we have to LDE everything and compute quotient polynomial
        // also to save on openings that we will have to do from the monomial form anyway
        // we can forget densities and other stuff

        let mut witness_polys_in_monomial_form = vec![];
        let mut witness_ldes_on_coset = vec![];

        for w in assignment_polynomials.into_iter() {
            let monomial = w.clone_padded_to_domain()?.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
            witness_polys_in_monomial_form.push(monomial.clone());
            let lde = monomial.bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;
            witness_ldes_on_coset.push(lde);
        }

        let alpha = transcript.get_challenge();

        // calculate first part of the quotient polynomial - the gate itself
        // A + B + C + D + AB + CONST + D_NEXT == 0 everywhere but on the last point of the domain

        let mut quotient_linearization_challenge = E::Fr::one();

        let (mut t_1, mut tmp) = {
            let mut t_1 = setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[5].clone();

            // Q_A * A
            let mut tmp = setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[0].clone();
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            t_1.add_assign(&worker, &tmp);

            // Q_B * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[1]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            // Q_C * C
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[2]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[2]);
            t_1.add_assign(&worker, &tmp);

            // Q_D * D
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[3]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[3]);
            t_1.add_assign(&worker, &tmp);

            // Q_M * A * B
            tmp.reuse_allocation(&setup_precomputations.selector_polynomials_on_coset_of_size_4n_bitreversed[4]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[0]);
            tmp.mul_assign(&worker, &witness_ldes_on_coset[1]);
            t_1.add_assign(&worker, &tmp);

            (t_1, tmp)
        };

        // now compute the permutation argument

        let z_1_coset_lde_bitreversed = z_1_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_1_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_1_shifted_coset_lde_bitreversed = z_1_shifted_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_1_shifted_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_2_coset_lde_bitreversed = z_2_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_2_coset_lde_bitreversed.size() == required_domain_size*4);

        let z_2_shifted_coset_lde_bitreversed = z_2_shifted_in_monomial_form.clone().bitreversed_lde_using_bitreversed_ntt(
            &worker, 
            4, 
            omegas_bitreversed, 
            &E::Fr::multiplicative_generator()
        )?;

        assert!(z_2_shifted_coset_lde_bitreversed.size() == required_domain_size*4);

        // For both Z_1 and Z_2 we first check for grand products
        // (A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma)*Z(k) - Z(k+1) == 0

        // we use evaluations of the polynomial X and K_i * X on a large domain's coset

        quotient_linearization_challenge.mul_assign(&alpha);

        {
            let mut contrib_z_1 = z_1_coset_lde_bitreversed.clone();

            // A + beta*X + gamma

            tmp.reuse_allocation(&witness_ldes_on_coset[0]);
            tmp.add_constant(&worker, &gamma);
            tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &beta);
            contrib_z_1.mul_assign(&worker, &tmp);

            for (w, non_res) in witness_ldes_on_coset[1..].iter().zip(non_residues.iter()) {
                let mut factor = beta;
                factor.mul_assign(&non_res);

                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &setup_precomputations.x_on_coset_of_size_4n_bitreversed, &factor);
                contrib_z_1.mul_assign(&worker, &tmp);
            }

            contrib_z_1.sub_assign(&worker, &z_1_shifted_coset_lde_bitreversed);

            t_1.add_assign_scaled(&worker, &contrib_z_1, &quotient_linearization_challenge);

            drop(contrib_z_1);
        }

        quotient_linearization_challenge.mul_assign(&alpha);

        {
            let mut contrib_z_2 = z_2_coset_lde_bitreversed.clone();

            // A + beta*perm_a + gamma

            for (w, perm) in witness_ldes_on_coset.iter()
            .zip(setup_precomputations.permutation_polynomials_on_coset_of_size_4n_bitreversed.iter()) {
                tmp.reuse_allocation(&w);
                tmp.add_constant(&worker, &gamma);
                tmp.add_assign_scaled(&worker, &perm, &beta);
                contrib_z_2.mul_assign(&worker, &tmp);
            }

            contrib_z_2.sub_assign(&worker, &z_2_shifted_coset_lde_bitreversed);

            t_1.add_assign_scaled(&worker, &contrib_z_2, &quotient_linearization_challenge);

            drop(contrib_z_2);
        }

        // z_1(omega^0) - 1 == 0
        // z_2(omega^0) - 1 == 0
        // z_1(omega^n-1) == z_2(omega^n-1)


        let l_0 = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), 0)?;
        let l_n_minus_one = self.calculate_lagrange_poly(&worker, required_domain_size.next_power_of_two(), n-1)?;

        {
            let mut z_1_minus_z_2_shifted = z_1_shifted_coset_lde_bitreversed.clone();
            z_1_minus_z_2_shifted.sub_assign(&worker, &z_2_shifted_coset_lde_bitreversed);

            let l_coset_lde_bitreversed = l_n_minus_one.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            z_1_minus_z_2_shifted.mul_assign(&worker, &l_coset_lde_bitreversed);
            drop(l_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            z_1_minus_z_2_shifted.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &z_1_minus_z_2_shifted);
        }

        {
            let mut z_1_minus_z_2 = z_1_coset_lde_bitreversed.clone();
            z_1_minus_z_2.sub_assign(&worker, &z_2_coset_lde_bitreversed);

            let l_coset_lde_bitreversed = l_0.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            z_1_minus_z_2.mul_assign(&worker, &l_coset_lde_bitreversed);
            drop(l_coset_lde_bitreversed);

            vanishing_poly_inverse_bitreversed.scale(&worker, alpha);

            z_1_minus_z_2.mul_assign(&worker, &vanishing_poly_inverse_bitreversed);

            t_1.add_assign(&worker, &z_1_minus_z_2);
        }

        Ok(proof)
    }
}

use crate::ff::SqrtField;

fn make_non_residues<F: SqrtField>(num: usize) -> Vec<F> {

    use crate::ff::LegendreSymbol;

    let mut non_residues = vec![];
    let mut current = F::one();
    let one = F::one();
    for _ in 0..num {
        loop {
            if current.legendre() != LegendreSymbol::QuadraticNonResidue {
                current.add_assign(&one);
            } else {
                non_residues.push(current);
                break;
            }
        }
    }

    non_residues
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::pairing::Engine;

    #[derive(Clone)]
    struct TestCircuit4<E:Engine>{
        _marker: PhantomData<E>
    }

    impl<E: Engine> Circuit<E, PlonkCsWidth4WithNextStepParams> for TestCircuit4<E> {
        fn synthesize<CS: ConstraintSystem<E, PlonkCsWidth4WithNextStepParams> >(&self, cs: &mut CS) -> Result<(), SynthesisError> {
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

            let zero = E::Fr::zero();

            let one = E::Fr::one();

            let mut two = one;
            two.double();

            let mut negative_one = one;
            negative_one.negate();

            let dummy = cs.get_dummy_variable();

            // 2a - b == 0
            cs.new_gate(
                [a, b, dummy, dummy], 
                [two, negative_one, zero, zero, zero, zero],
                [zero]
            )?;

            // 10b - c = 0
            let ten = E::Fr::from_str("10").unwrap();

            cs.new_gate(
                [b, c, dummy, dummy], 
                [ten, negative_one, zero, zero, zero, zero],
                [zero]
            )?;

            // c - a*b == 0 

            cs.new_gate(
                [a, b, dummy, c], 
                [zero, zero, zero, negative_one, one, zero],
                [zero]
            )?;

            // 10a + 10b - c - d == 0

            cs.new_gate(
                [a, b, c, d], 
                [ten, ten, negative_one, negative_one, zero, zero],
                [zero]
            )?;


            Ok(())
        }
    }

    #[test]
    fn test_prove_trivial_circuit() {
        use crate::pairing::bn256::{Bn256, Fr};
        use crate::worker::Worker;
        use crate::plonk::better_cs::generator::*;
        use crate::plonk::better_cs::keys::*;

        let mut assembly = GeneratorAssembly4WithNextStep::<Bn256>::new();

        let circuit = TestCircuit4::<Bn256> {
            _marker: PhantomData
        };

        circuit.clone().synthesize(&mut assembly).expect("must work");

        // println!("{:?}", assembly);

        assembly.finalize();

        let worker = Worker::new();

        let setup = assembly.setup(&worker).unwrap();

        let precomputations = SetupPolynomialsPrecomputations::from_setup(
            &setup, 
            &worker
        ).unwrap();

        let mut assembly = ProverAssembly4WithNextStep::<Bn256>::new();

        circuit.clone().synthesize(&mut assembly).expect("must work");

        assembly.finalize();

        let size = setup.permutation_polynomials[0].size();

        let crs_mons = Crs::<Bn256, CrsForMonomialForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);
        let crs_vals = Crs::<Bn256, CrsForLagrangeForm>::crs_42(setup.permutation_polynomials[0].size(), &worker);

        type Transcr = Blake2sTranscript<Fr>;

        let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = <OmegasInvBitreversed::<Fr> as CTPrecomputations::<Fr>>::new_for_domain_size(size.next_power_of_two());

        let _proof = assembly.prove::<Transcr, _, _>(
            &worker,
            &setup,
            &precomputations,
            &crs_vals,
            &crs_mons,
            &omegas_bitreversed,
            &omegas_inv_bitreversed,
        ).unwrap();

    }
}