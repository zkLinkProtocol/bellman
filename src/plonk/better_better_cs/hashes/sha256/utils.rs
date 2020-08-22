// converts x = (x_0, x_1, ..., x_n) - bit decomposition of x into y = \sum_{i=1}^{n} x_i * base^i
// due to our choices of base and input bit_length the sum never exceeds usize MAX VALUE
pub fn map_into_sparse_form(input: usize, base: usize) -> usize
{
    let mut out : usize = 0;
    let mut base_accumulator : usize = 1;
    let mut converted = input;

    while converted > 0 {
        let sparse_bit = converted & 1;
        converted >>= 1;
        out += sparse_bit * base_accumulator;
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
pub fn rotate_extract(value: usize, rotation: usize, extraction: usize) -> usize
{
    let temp = if extraction > 0 {value & ((1 << extraction) - 1)} else {value}; 
    let res = if rotation > 0 {(temp >> rotation) + (temp << (64 - rotation))} else {temp};

    res
}