use crate::pairing::{Engine};
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::worker::Worker;
use crate::plonk::commitments::transparent::utils::log2_floor;
use super::*;
use super::tree_hash::*;
use super::binary_tree::{BinaryTree, BinaryTreeParams};
use crate::plonk::polynomials::*;

pub struct Multioracle<'a, E: Engine, H: BinaryTreeHasher<E::Fr> > {
    pub polynomial_values_refs: Vec<&'a [E::Fr]>,
    pub tree: BinaryTree<E, H>
}

impl<'a, E: Engine, H: BinaryTreeHasher<E::Fr>> Multioracle<'a, E, H> {
    pub fn new_from_polynomials(
        polynomials: &'a [Polynomial<E::Fr, Values>],
        tree_hasher: H,
        num_values_from_one_poly_into_leaf: usize,
        worker: &Worker
    ) -> Self {
        // first make combinations of leaf values
        // expect polynomials to be in bitreverse enumeration
        let num_polys = polynomials.len();
        let values_per_leaf = num_polys * num_values_from_one_poly_into_leaf;
        let num_leafs = polynomials[0].size() / num_values_from_one_poly_into_leaf;
        assert!(num_leafs.is_power_of_two());

        let tree_params = BinaryTreeParams {
            values_per_leaf: values_per_leaf
        };

        // we need vector (over leafs)
        // of vectors(over individual polys)
        // of references
        let mut leaf_refs_combined: Vec<Vec<&[E::Fr]>> = vec![vec![&[]; num_polys]; num_leafs];

        let poly_refs: Vec<_> = polynomials.iter().map(|el| el.as_ref()).collect();

        let poly_refs_ref = &poly_refs;

        worker.scope(leaf_refs_combined.len(), |scope, chunk| {
            for (i, lh) in leaf_refs_combined.chunks_mut(chunk)
                            .enumerate() {
                scope.spawn(move |_| {
                    // we take `values_per_leaf` values from each of the polynomial
                    // and push them into the conbinations
                    let base_idx = i*chunk;
                    for (j, lh) in lh.iter_mut().enumerate() {
                        let idx = base_idx + j;
                        let start = idx * num_values_from_one_poly_into_leaf;
                        let end = start + num_values_from_one_poly_into_leaf;

                        for (idx, &poly_values) in poly_refs_ref.iter().enumerate() {
                            let slice = &poly_values[start..end];
                            lh[idx] = slice;
                        }
                    }
                });
            }
        });

        let tree = BinaryTree::create_from_combined_leafs(
            &leaf_refs_combined,
            tree_hasher,
            &tree_params
        );

        Self {
            polynomial_values_refs: poly_refs,
            tree
        }
    }
}