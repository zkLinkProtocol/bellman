use crate::pairing::{Engine};
use crate::pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use crate::worker::Worker;
use crate::plonk::commitments::transparent::utils::log2_floor;
use super::*;
use super::tree_hash::*;
use super::binary_tree::{BinaryTree, BinaryTreeParams};
use crate::plonk::polynomials::*;
use super::multioracle::Multioracle;
use super::super::cs::*;
use crate::SynthesisError;

pub struct SetupMultioracle<E: Engine, H: BinaryTreeHasher<E::Fr>> {
    polynomial_ldes: Vec<Polynomial<E::Fr, Values>>,
    tree: BinaryTree<E, H>
}

const LDE_FACTOR: usize = 4;
const FRI_VALUES_PER_LEAF: usize = 8;

impl<E: Engine, H: BinaryTreeHasher<E::Fr>> SetupMultioracle<E, H> {
    pub fn from_assembly<P: PlonkConstraintSystemParams<E>, MG: MainGateEquation>(
        assembly: TrivialAssembly<E, P, MG>,
        tree_hasher: H,
        worker: &Worker
    ) -> Result<Self, SynthesisError> {
        use crate::plonk::fft::cooley_tukey_ntt::*;

        let size = assembly.n().next_power_of_two();

        let (mut storage, permutations) = assembly.perform_setup(&worker)?;
        let gate_selectors = assembly.output_gate_selectors(&worker)?;
        let ids = assembly.sorted_setup_polynomial_ids.clone();
        println!("IDs = {:?}", ids);
        drop(assembly);

        let mut setup_polys = vec![];

        let omegas_bitreversed = BitReversedOmegas::<E::Fr>::new_for_domain_size(size.next_power_of_two());
        let omegas_inv_bitreversed = <OmegasInvBitreversed::<E::Fr> as CTPrecomputations::<E::Fr>>::new_for_domain_size(size.next_power_of_two());
    
        for id in ids.into_iter() {
            let mut setup_poly = storage.remove(&id).unwrap();
            setup_poly.pad_to_domain()?;
            let coeffs = setup_poly.ifft_using_bitreversed_ntt(&worker, &omegas_inv_bitreversed, &E::Fr::one())?;
            let lde = coeffs.bitreversed_lde_using_bitreversed_ntt(&worker, LDE_FACTOR, &omegas_bitreversed, &E::Fr::multiplicative_generator())?;

            setup_polys.push(lde);
        }

        for mut p in permutations.into_iter() {
            p.pad_to_domain()?;
            let coeffs = p.ifft_using_bitreversed_ntt(&worker, &omegas_inv_bitreversed, &E::Fr::one())?;
            let lde = coeffs.bitreversed_lde_using_bitreversed_ntt(&worker, LDE_FACTOR, &omegas_bitreversed, &E::Fr::multiplicative_generator())?;

            setup_polys.push(lde);
        }

        for mut selector in gate_selectors.into_iter() {
            selector.pad_to_domain()?;
            let coeffs = selector.ifft_using_bitreversed_ntt(&worker, &omegas_inv_bitreversed, &E::Fr::one())?;
            let lde = coeffs.bitreversed_lde_using_bitreversed_ntt(&worker, LDE_FACTOR, &omegas_bitreversed, &E::Fr::multiplicative_generator())?;

            setup_polys.push(lde);
        }

        let multioracle = Multioracle::<E, H>::new_from_polynomials(
            &setup_polys, 
            tree_hasher, 
            FRI_VALUES_PER_LEAF,
            &worker
        );

        let tree = multioracle.tree;

        Ok(
            Self {
                polynomial_ldes: setup_polys,
                tree
            }
        )
    }
}

