use super::cs::*;

use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};

use crate::{SynthesisError};
use crate::plonk::polynomials::*;
use crate::worker::Worker;
use crate::plonk::domains::*;

use crate::kate_commitment::*;

use std::marker::PhantomData;

use super::utils::calculate_inverse_vanishing_polynomial_in_a_coset;

pub struct SetupPolynomials<E: Engine, P: PlonkConstraintSystemParams<E>> {
    pub selector_polynomials: Vec<Polynomial<E::Fr, Coefficients>>,
    pub next_step_selector_polynomials: Vec<Polynomial<E::Fr, Coefficients>>,
    pub permutation_polynomials: Vec<Polynomial<E::Fr, Coefficients>>,

    pub(crate) _marker: std::marker::PhantomData<P>
}

pub struct SetupPolynomialsPrecomputations<E: Engine, P: PlonkConstraintSystemParams<E>> {
    pub selector_polynomials_on_coset_of_size_4n_bitreversed: Vec<Polynomial<E::Fr, Values>>,
    pub next_step_selector_polynomials_on_coset_of_size_4n_bitreversed: Vec<Polynomial<E::Fr, Values>>,
    pub permutation_polynomials_on_coset_of_size_4n_bitreversed: Vec<Polynomial<E::Fr, Values>>,
    pub permutation_polynomials_values_of_size_n_minus_one: Vec<Polynomial<E::Fr, Values>>,
    pub inverse_divisor_on_coset_of_size_4n_bitreversed: Polynomial<E::Fr, Values>,
    pub x_on_coset_of_size_4n_bitreversed: Polynomial<E::Fr, Values>,

    pub(crate) _marker: std::marker::PhantomData<P>
}

use crate::plonk::fft::cooley_tukey_ntt::{BitReversedOmegas, CTPrecomputations};

impl<E: Engine, P: PlonkConstraintSystemParams<E>> SetupPolynomialsPrecomputations<E, P> {
    pub fn from_setup_and_precomputations<CP: CTPrecomputations<E::Fr>> (
        setup: &SetupPolynomials<E, P>,
        worker: &Worker,
        omegas_bitreversed: &CP,
    ) -> Result<Self, SynthesisError> {
        let mut new = Self {
            selector_polynomials_on_coset_of_size_4n_bitreversed: vec![],
            next_step_selector_polynomials_on_coset_of_size_4n_bitreversed: vec![],
            permutation_polynomials_on_coset_of_size_4n_bitreversed: vec![],
            permutation_polynomials_values_of_size_n_minus_one: vec![],
            inverse_divisor_on_coset_of_size_4n_bitreversed: Polynomial::from_values(vec![E::Fr::one()]).unwrap(),
            x_on_coset_of_size_4n_bitreversed: Polynomial::from_values(vec![E::Fr::one()]).unwrap(),
            
            _marker: std::marker::PhantomData
        };

        let required_domain_size = setup.selector_polynomials[0].size();

        for p in setup.selector_polynomials.iter() {
            let ext = p.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            new.selector_polynomials_on_coset_of_size_4n_bitreversed.push(ext);
        }

        for p in setup.next_step_selector_polynomials.iter() {
            let ext = p.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;

            new.next_step_selector_polynomials_on_coset_of_size_4n_bitreversed.push(ext);
        }

        for p in setup.permutation_polynomials.iter() {
            let lde = p.clone().bitreversed_lde_using_bitreversed_ntt(
                &worker, 
                4, 
                omegas_bitreversed, 
                &E::Fr::multiplicative_generator()
            )?;
            new.permutation_polynomials_on_coset_of_size_4n_bitreversed.push(lde);
            
            let as_values = p.clone().fft(&worker);
            let mut as_values = as_values.into_coeffs();
            as_values.pop().unwrap();

            let p = Polynomial::from_values_unpadded(as_values)?;

            new.permutation_polynomials_values_of_size_n_minus_one.push(p);
        }

        let mut vanishing_poly_inverse_bitreversed = calculate_inverse_vanishing_polynomial_in_a_coset::<E::Fr>(
            &worker, 
            new.permutation_polynomials_values_of_size_n_minus_one[0].size(), 
            required_domain_size.next_power_of_two()
        )?;

        vanishing_poly_inverse_bitreversed.bitreverse_enumeration(&worker);

        // evaluate polynomial X on the coset
        let mut x_poly = Polynomial::from_values(vec![E::Fr::multiplicative_generator(); vanishing_poly_inverse_bitreversed.size()])?;
        x_poly.distribute_powers(&worker, x_poly.omega);
        x_poly.bitreverse_enumeration(&worker);

        new.inverse_divisor_on_coset_of_size_4n_bitreversed = vanishing_poly_inverse_bitreversed;
        new.x_on_coset_of_size_4n_bitreversed = x_poly;

        Ok(new)
    }

    pub fn from_setup (
        setup: &SetupPolynomials<E, P>,
        worker: &Worker,
    ) -> Result<Self, SynthesisError> {
        let precomps = BitReversedOmegas::new_for_domain_size(setup.permutation_polynomials[0].size());

        Self::from_setup_and_precomputations(
            setup, 
            worker, 
            &precomps
        )  
    }
}



pub struct Proof<E: Engine, P: PlonkConstraintSystemParams<E>> {
    pub num_inputs: usize,
    pub n: usize,
    pub input_values: Vec<E::Fr>,
    pub wire_commitments: Vec<E::G1Affine>,
    pub grand_product_commitments: Vec<E::G1Affine>,
    pub quotient_poly_commitments: Vec<E::G1Affine>,

    pub opening_at_z_proof: E::G1Affine,
    pub opening_at_z_omega_proof: E::G1Affine,

    pub(crate) _marker: std::marker::PhantomData<P>
}


pub struct VerificationKey<E: Engine, P: PlonkConstraintSystemParams<E>> {
    pub selector_commitments: Vec<E::G1Affine>,
    pub next_step_selector_commitments: Vec<E::G1Affine>,
    pub permutation_commitments: Vec<E::G1Affine>,

    pub(crate) _marker: std::marker::PhantomData<P>
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>> VerificationKey<E, P> {
    pub fn from_setup(setup: &SetupPolynomials<E, P>, worker: &Worker, crs: &Crs<E, CrsForMonomialForm>) -> Result<Self, SynthesisError> {
        assert_eq!(setup.selector_polynomials.len(), P::STATE_WIDTH + 2);
        if P::CAN_ACCESS_NEXT_TRACE_STEP == false {
            assert_eq!(setup.next_step_selector_polynomials.len(), 0);
        }
        assert_eq!(setup.permutation_polynomials.len(), P::STATE_WIDTH);

        let mut new = Self {
            selector_commitments: vec![],
            next_step_selector_commitments: vec![],
            permutation_commitments: vec![],
        
            _marker: std::marker::PhantomData
        };

        for p in setup.selector_polynomials.iter() {
            let commitment = commit_using_monomials(p, &crs, &worker)?;
            new.selector_commitments.push(commitment);
        }

        for p in setup.next_step_selector_polynomials.iter() {
            let commitment = commit_using_monomials(p, &crs, &worker)?;
            new.next_step_selector_commitments.push(commitment);
        }

        for p in setup.permutation_polynomials.iter() {
            let commitment = commit_using_monomials(p, &crs, &worker)?;
            new.permutation_commitments.push(commitment);
        }

        Ok(new)
    }
}



