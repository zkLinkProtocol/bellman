use crate::pairing::ff::*;

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{Zero, One};

use std::ops::Range;
use std::{ iter, mem };


pub fn pow(base: usize, exp: usize) -> usize {
    let mut res = 1;
    for _i in 0..exp {
        res *= base;
    }

    res
}


pub fn u64_to_ff<Fr: PrimeField>(n: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let res = Fr::from_repr(repr).expect("should parse");
    res
}

pub fn u64_exp_to_ff<Fr: PrimeField>(n: u64, exp: u64) -> Fr {
    let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
    repr.as_mut()[0] = n;
    let mut res = Fr::from_repr(repr).expect("should parse");

    if exp != 0 {
        res = res.pow(&[exp]);
    }
    res
}


pub fn ff_to_u64<Fr: PrimeField>(fr: &Fr) -> u64 {
    fr.into_repr().as_ref()[0]
}

pub const KECCAK_FIRST_SPARSE_BASE : u64 = 13;
pub fn keccak_u64_first_conveter(n: u64) -> u64 
{
    assert!(n < KECCAK_FIRST_SPARSE_BASE);
    // simple xor
    n & 1
}

// conveter for the function that unites together xi and i trnasformations of keccak:
// f_log = a ^ (~b & c) ^ d
// the corresponding algebraic encoding is f_alg: 2a + b + 3c + 2d
// | idx | a | b | c | d | a ^ (~b & c) ^ d | 2a + b + 3c + 2d |
// -------------------------------------------------------------
// |  0  | 0 | 0 | 0 | 0 |         0        |          0       |
// |  1  | 0 | 0 | 0 | 1 |         1        |          2       |
// |  2  | 0 | 0 | 1 | 0 |         1        |          3       |
// |  3  | 0 | 0 | 1 | 1 |         0        |          5       |
// |  4  | 0 | 1 | 0 | 0 |         0        |          1       |
// |  5  | 0 | 1 | 0 | 1 |         1        |          3       |
// |  6  | 0 | 1 | 1 | 0 |         0        |          4       |
// |  7  | 0 | 1 | 1 | 1 |         1        |          6       |
// |  8  | 1 | 0 | 0 | 0 |         1        |          2       |
// |  9  | 1 | 0 | 0 | 1 |         0        |          4       |
// | 10  | 1 | 0 | 1 | 0 |         0        |          5       |
// | 11  | 1 | 0 | 1 | 1 |         1        |          7       |
// | 12  | 1 | 1 | 0 | 0 |         1        |          3       |
// | 13  | 1 | 1 | 0 | 1 |         0        |          5       |
// | 14  | 1 | 1 | 1 | 0 |         1        |          6       |
// | 15  | 1 | 1 | 1 | 1 |         0        |          8       |
// -----------------------------------------|------------------|
// this table shows that mapping f_alg -> f_log is indeed well-defined
pub const KECCAK_SECOND_SPARSE_BASE : u64 = 9;
pub fn keccak_u64_second_converter(n: u64) -> u64 {
    assert!(n < KECCAK_SECOND_SPARSE_BASE);
    let bit_table : [u64; KECCAK_SECOND_SPARSE_BASE as usize] = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    bit_table[n as usize]
}


pub const FIELD_LIMB_COUNT : usize = 8;
pub fn general_ff_converter<Fr: PrimeField, T: Fn(u64) -> u64>(fr : Fr, input_base: u64, output_base: u64, transform_f: T) -> Fr
{
    let mut input = BigUint::default();
    let fr_repr = fr.into_repr();
    for n in fr_repr.as_ref().iter().rev() {
        input <<= 64;
        input += *n;
    }

    let mut acc = BigUint::default(); 
    let mut base = BigUint::one();
 
    while !input.is_zero() {
        let remainder = (input.clone() % BigUint::from(input_base)).to_u64().unwrap();
        let output_chunk = transform_f(remainder);
        acc += output_chunk * base.clone();
        input /= input_base;
        base *= output_base;
    }

    let res = Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
    res
}

pub fn keccak_ff_first_converter<Fr: PrimeField>(fr: Fr, output_base: u64) -> Fr 
{
    general_ff_converter(fr, KECCAK_FIRST_SPARSE_BASE, output_base, |x| { keccak_u64_first_conveter(x)} )
}

pub fn keccak_ff_second_converter<Fr: PrimeField>(fr: Fr, output_base: u64) -> Fr 
{
    general_ff_converter(fr, KECCAK_SECOND_SPARSE_BASE, output_base, |x| { keccak_u64_second_converter(x)} )
}


pub trait IdentifyFirstLast: Iterator + Sized {
    fn identify_first_last(self) -> Iter<Self>;
}

impl<I> IdentifyFirstLast for I where I: Iterator {
    fn identify_first_last(self) -> Iter<Self> {
        Iter(true, self.peekable())
    }
}

pub struct Iter<I>(bool, iter::Peekable<I>) where I: Iterator;

impl<I> Iterator for Iter<I> where I: Iterator {
    type Item = (bool, bool, I::Item);

    fn next(&mut self) -> Option<Self::Item> {
        let first = mem::replace(&mut self.0, false);
        self.1.next().map(|e| (first, self.1.peek().is_none(), e))
    }
}