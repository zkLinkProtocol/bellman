use crate::pairing::ff::*;


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
    let mut res = Fr::from_repr(repr).expect("should parse");
    res
}


pub fn ff_to_u64<Fr: PrimeField>(fr: &Fr) -> u64 {
    fr.into_repr().as_ref()[0]
}


pub fn xor_conveter(n: u64) -> u64 
{
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
pub const KECCAK_SECOND_SPARSE_BASE : usize = 9;
pub fn keccak_converter(n: u64) -> u64 {
    assert!((n as usize) < KECCAK_SECOND_SPARSE_BASE);
    let bit_table : [u64; KECCAK_SECOND_SPARSE_BASE] = [0, 0, 1, 1, 0, 0, 1, 1, 0];
    bit_table[n as usize]
}
