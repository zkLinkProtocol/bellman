use crate::pairing::ff::*;
use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::Zero;

use super::tables::{
    SHA256_CHOOSE_BASE,
    SHA256_MAJORITY_BASE,
    SHA256_EXPANSION_BASE,
};

// in general all bit-friendly transformations (such as xor or SHA256 majority and choose operations)
// are hadled by the gadget library itself with the use of tables
// however, in some our wires are actually constants and not allocated variables
// for them we do not want apply the common strategy 
// ( split in chunks -- chunk-by-chunk transform via tables -- compose chunks back )
// but want to do all the bitwise transformations on the whole constant number in one turn
// this is done by the corresponding "normalizer" mappings, contained in this module


fn general_normalizer<Fr: PrimeField>(fr : Fr, bit_table: &[u64], base: usize) -> Fr
{
    let mut input = BigUint::default();
    let fr_repr = fr.into_repr();
    for n in fr_repr.as_ref().iter().rev() {
        input <<= 64;
        input += *n;
    }

    let mut acc : u64 = 0; 
    let mut count = 0;
 
    while !input.is_zero() {
        let remainder = (input.clone() % BigUint::from(base)).to_u64().unwrap();
        let bit = bit_table[remainder as usize];
        acc += bit << count;
        input /= base;
        count += 1;
    }

    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = acc;
    let mut res = Fr::from_repr(repr).expect("should parse");

    res
}

pub fn ch_map_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_CHOOSE_BASE] = [ 0, 0, 0, 1, 0, 1, 1 ];
    let base = SHA256_CHOOSE_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn ch_xor_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_CHOOSE_BASE] = [ 0, 1, 0, 1, 0, 1, 0 ];
    let base = SHA256_CHOOSE_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn maj_map_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_MAJORITY_BASE] =  [ 0, 0, 1, 1 ]; 
    let base = SHA256_MAJORITY_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn maj_xor_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_MAJORITY_BASE] =  [ 0, 1, 0, 1 ]; 
    let base = SHA256_MAJORITY_BASE;
    general_normalizer(fr, &bit_table[..], base)
}

pub fn sheduler_xor_normalizer<Fr: PrimeField>(fr: Fr) -> Fr 
{
    let bit_table : [u64; SHA256_EXPANSION_BASE] =  [ 0, 1, 0, 1 ]; 
    let base = SHA256_EXPANSION_BASE;
    general_normalizer(fr, &bit_table[..], base)
}