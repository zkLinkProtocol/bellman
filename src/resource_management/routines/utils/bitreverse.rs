pub const fn bitreverse_index(size: usize, index: usize) -> usize {
    const USIZE_BITS: usize = 0_usize.count_zeros() as usize;
    // debug_assert!(index < size);
    if size == 1 {
        0
    } else {
        // debug_assert!(size.is_power_of_two());
        let bits = size.trailing_zeros() as usize;
        index.reverse_bits() >> (USIZE_BITS - bits)
    }
}

pub fn bitreverse_index_for_constant_size<const N: usize>(index: usize) -> usize {
    const USIZE_BITS: usize = 0_usize.count_zeros() as usize;
    debug_assert!(N.is_power_of_two());
    debug_assert!(index < N);
    if N == 1 {
        0
    } else {
        index.reverse_bits() >> (USIZE_BITS - N)
    }
}

pub fn bitreverse_enumeration<T: Sized>(v: &mut [T]) {
    let n = v.len();
    for i in 0..n {
        let j = bitreverse_index(n, i);
        if j > i {
            v.swap(i, j);
        }
    }
}