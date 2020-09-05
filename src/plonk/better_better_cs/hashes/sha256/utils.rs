use crate::num_bigint::BigUint;
use crate::num_traits::{ Zero, One };

// converts x = (x_0, x_1, ..., x_n) - bit decomposition of x into y = \sum_{i=1}^{n} x_i * base^i
pub fn map_into_sparse_form(input: usize, base: usize) -> BigUint
{
    // if base is zero, than no convertion is actually needed
    if base == 0 {
        return BigUint::from(input);
    }
    
    let mut out = BigUint::zero();
    let mut base_accumulator = BigUint::one();
    let mut converted = input;

    while converted > 0 {
        let sparse_bit = converted & 1;
        converted >>= 1;
        if sparse_bit > 0 {
            out += base_accumulator.clone();
        }
        base_accumulator *= base;
    }
    
    out
}


pub fn map_from_sparse_form(input: usize, base: usize) -> usize
{
    let mut target : usize = input;
    let mut output : usize = 0;
    let mut count : usize = 0;

    while target > 0 {
        let slice = target % base;
        // althoough slice is not bound to {0, 1} we are only interested in its value modulo 2
        let bit = slice & 1usize;
        output += bit << count;
        count += 1;
        target = target / base;
    }

    output
}


// for given x=(x_0, x_1, ..., x_n) extract the k lower bits: y = (x_0, x_1, ..., x_{k-1}, 0, ..., 0)
// and then rotate
// NOTE: by rotate we always mean right rotate of 32-bit numbers!
pub fn rotate_extract(value: usize, rotation: usize, extraction: usize) -> usize
{
    let temp = if extraction > 0 {value & ((1 << extraction) - 1)} else {value}; 
    let res = if rotation > 0 {(temp >> rotation) + ((temp << (32 - rotation)) & 0xffffffff) } else {temp};

    res
}

// simple right shift
pub fn shift_right(value: usize, shift: usize) -> usize
{
    if shift > 0 {value >> shift} else {value}
}