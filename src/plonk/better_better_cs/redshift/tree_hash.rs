use crate::pairing::ff::{Field, PrimeField};
use rescue_hash::{RescueEngine, RescueHashParams, rescue_hash};

pub use super::poseidon_tree_hash::*;

pub trait BinaryTreeHasher<F: PrimeField>: Sized + Send + Sync + Clone {
    type Output: Sized + Clone + Copy + Send + Sync + PartialEq + Eq; 

    fn placeholder_output() -> Self::Output;
    fn leaf_hash(&self, input: &[F]) -> Self::Output;
    fn node_hash(&self, input: &[Self::Output; 2], level: usize) -> Self::Output;
}

pub struct RescueBinaryTreeHasher<'a, E: RescueEngine> {
    params: &'a E::Params,
}

impl<'a, E: RescueEngine> RescueBinaryTreeHasher<'a, E> {
    pub fn new(params: &'a E::Params) -> Self {
        assert_eq!(params.rate(), 2u32);
        assert_eq!(params.output_len(), 1u32);
        Self {
            params: params
        }
    }
}

impl<'a, E: RescueEngine> Clone for RescueBinaryTreeHasher<'a, E> {
    fn clone(&self) -> Self {
        Self {
            params: self.params
        }
    }
}


impl<'a, E: RescueEngine> BinaryTreeHasher<E::Fr> for RescueBinaryTreeHasher<'a, E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(self.params, input);

        as_vec.pop().unwrap()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        let mut as_vec = rescue_hash::<E>(self.params, &input[..]);

        as_vec.pop().unwrap()
    }
}

use std::sync::atomic::{AtomicUsize, Ordering};

pub static COUNTER: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Copy, Debug, Hash)]
pub struct CountingHash<E: RescueEngine> {
    dummy: E::Fr,
}

impl<E: RescueEngine> CountingHash<E> {
    pub fn new() -> Self {
        Self {
            dummy: E::Fr::zero()
        }
    }
}

impl<E: RescueEngine> BinaryTreeHasher<E::Fr> for CountingHash<E> {
    type Output = E::Fr;

    #[inline]
    fn placeholder_output() -> Self::Output {
        E::Fr::zero()
    }

    fn leaf_hash(&self, input: &[E::Fr]) -> Self::Output {
        let mut num_invocations = input.len() / 2;
        if input.len() % 2 != 0 {
            num_invocations += 1;
        }

        COUNTER.fetch_add(num_invocations, Ordering::SeqCst);

        E::Fr::zero()
    }

    fn node_hash(&self, input: &[Self::Output; 2], _level: usize) -> Self::Output {
        COUNTER.fetch_add(2, Ordering::SeqCst);

        E::Fr::zero()
    }
}

