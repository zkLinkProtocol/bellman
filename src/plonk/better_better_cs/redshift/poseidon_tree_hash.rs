use crate::pairing::ff::{Field, PrimeField};
use poseidon_hash::{PoseidonEngine, PoseidonHashParams, poseidon_hash};
use super::tree_hash::BinaryTreeHasher;

pub struct PoseidonBinaryTreeHasher<'a, E: PoseidonEngine> {
    params: &'a E::Params,
}

impl<'a, E: PoseidonEngine> PoseidonBinaryTreeHasher<'a, E> {
    pub fn new(params: &'a E::Params) -> Self {
        assert_eq!(params.rate(), 2u32);
        assert_eq!(params.output_len(), 1u32);
        Self {
            params: params
        }
    }
}

impl<'a, E: PoseidonEngine> Clone for PoseidonBinaryTreeHasher<'a, E> {
    fn clone(&self) -> Self {
        Self {
            params: self.params
        }
    }
}


impl<'a, E: PoseidonEngine> BinaryTreeHasher<E::Fr> for PoseidonBinaryTreeHasher<'a, E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut as_vec = poseidon_hash::<E>(self.params, input);

        as_vec.pop().unwrap()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        let mut as_vec = poseidon_hash::<E>(self.params, &input[..]);

        as_vec.pop().unwrap()
    }
}