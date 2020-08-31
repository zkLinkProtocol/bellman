use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use super::utils::*;
use crate::SynthesisError;
use crate::Engine;


pub fn pow(base: usize, exp: usize) -> usize {

    let mut res = 1;
    for _i in 0..exp {
        res *= base;
    }

    res
}

// for given bit_width, rotation parameter, extraction parameter and base construct the following table:
// first column containts all values of x in the range [0, 2^bits - 1]
// the corresponding value in the second column is sparse representation of x
// while the value in the thrid column is sparse representation of shifted and extracted value of x 
// see utils file for more details
#[derive(Clone)]
pub struct Sha256SparseRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    bits: usize,
    rotation: usize,
    extraction: usize,
    base: usize,
    name: &'static str,
}


impl<E: Engine> Sha256SparseRotateTable<E> {

    pub fn new(bits: usize, rotation: usize, extraction: usize, base: usize, name: &'static str) -> Self {
        let mut key = Vec::with_capacity(1 << bits);
        let mut value_0 = Vec::with_capacity(1 << bits);
        let mut value_1 = Vec::with_capacity(1 << bits);
        let mut map = std::collections::HashMap::with_capacity(1 << bits);

        for x in 0..(1 << bits) {
            let y = map_into_sparse_form(x, base);
            let z = map_into_sparse_form(rotate_extract(x, rotation, extraction), base);

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            let z = E::Fr::from_str(&z.to_string()).unwrap();
            
            key.push(x);
            value_0.push(y);
            value_1.push(z);

            map.insert(x, (y, z));
        }

        Self {
            table_entries: [key, value_0, value_1],
            table_lookup_map: map,
            bits,
            rotation,
            extraction,
            base,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for Sha256SparseRotateTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256SparseRotateTable")
            .field("bits", &self.bits)
            .field("rotation", &self.rotation)
            .field("extraction", &self.extraction)
            .field("base", &self.base)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for Sha256SparseRotateTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << self.bits
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        2
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0], values[1]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![entry.0, entry.1])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// for given bit_width, shift parameter and base construct the following table:
// first column containts all values of x in the range [0, 2^bits - 1]
// the corresponding value in the second column is sparse representation of x >> shift
// the thirf column is unused
#[derive(Clone)]
pub struct Sha256SparseShiftTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 2],
    table_lookup_map: std::collections::HashMap<E::Fr, E::Fr>,
    bits: usize,
    shift: usize,
    base: usize,
    name: &'static str,
}


impl<E: Engine> Sha256SparseShiftTable<E> {

    pub fn new(bits: usize, shift: usize, base: usize, name: &'static str) -> Self {
        let mut key = Vec::with_capacity(1 << bits);
        let mut value = Vec::with_capacity(1 << bits);
        let mut map = std::collections::HashMap::with_capacity(1 << bits);

        for x in 0..(1 << bits) {
            let y = map_into_sparse_form(shift_right(x, shift), base);
            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();

            key.push(x);
            value.push(y);
            map.insert(x, y);
        }

        Self {
            table_entries: [key, value],
            table_lookup_map: map,
            bits,
            shift,
            base,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for Sha256SparseShiftTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256SparseShiftTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .field("base", &self.base)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for Sha256SparseShiftTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << self.bits
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 2);
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// Sha256 normalization table is parametrized by two parameters: sparse representation base (or simply base) and num of chunks
// let x be any number in [0, base^num_chunks - 1], hence x can ne represented as base-ary number with num_of_chunks digits:
// x = \sum_{i=0}^{num_chunks-1} x_i * base^i, where each x_i \in [0, base-1]
// the purpose of normalization table is to transform every such x into y:
// y = \sum_{i=0}^{num_chunks-1} y_i 2^i, where y_i \in [0, 1] - bit decomposition of y of bitlegth = num_of_chunks
// here every y_i = x_i mod 2
// the table actually contains two colums (x, y) - the third is always zero
#[derive(Clone)]
pub struct Sha256NormalizationTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, E::Fr>,
    base: usize,
    num_of_chunks: usize,
    name: &'static str,
}


impl<E: Engine> Sha256NormalizationTable<E> {

    pub fn new(base: usize, num_of_chunks: usize, name: &'static str) -> Self {
        
        let table_size = pow(base, num_of_chunks);
        let mut key = Vec::with_capacity(table_size);
        let mut value = Vec::with_capacity(table_size);
        let unused = vec![E::Fr::zero(); table_size];
        let mut map = std::collections::HashMap::with_capacity(table_size);

        for x in 0..table_size {
            let y = map_from_sparse_form(x, base);

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            
            key.push(x);
            value.push(y);

            map.insert(x, y);
        }

        Self {
            table_entries: [key, value, unused],
            table_lookup_map: map,
            base,
            num_of_chunks,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for Sha256NormalizationTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256NormalizationTable")
            .field("base", &self.base)
            .field("num_of_chunks", &self.num_of_chunks)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for Sha256NormalizationTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        pow(self.base, self.num_of_chunks)
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        column_num == 2
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


// Sha256 choose table:
// one of major components of Sha256 hash is bitwise application for a choose function 
// choose(e, f, g) = (e & f) ^ (~e & g), where e, f, g - bits for current 32bit-words E, F, G
// in order to do it effectively we take the following approach: 
// convert all of E, F, G into sparse form with base 7 with the help od Sha256SparseRotateTable 
// now for a given bits (e, f, g) and  t = (e & f) ^ (~e & g) we apply Daira's trick: want to create a unique encoding of 't', 
// using some arithmetic relationship between e, f and g.
// one of such possible algebraic mappings is between t and e + 2f + 3g:
// 
// | e | f | g | t | e + 2f + 3g |
// -------------------------------
// | 0 | 0 | 0 | 0 |           0 |
// | 0 | 0 | 1 | 1 |           3 |
// | 0 | 1 | 0 | 0 |           2 |
// | 0 | 1 | 1 | 1 |           5 |
// | 1 | 0 | 0 | 0 |           1 |
// | 1 | 0 | 1 | 0 |           4 |
// | 1 | 1 | 0 | 1 |           3 |
// | 1 | 1 | 1 | 1 |           6 |
// --------------------------------
//
// so there is a well defined function "choose" t = f(x) from x = e + 2f + 3g \in [0, 6] to t \in [0, 1].
// We construct a Sha256ChooserTable for accomplish this transformation.
// However, having a table of such a small size is not that usefulm hence we go into operating on several bits (or chunks) at once:
// assuming that x = \sum_{i = 0}^{num_chunks - 1} x_i 7^i, out table entry is (x, y), 
// where y = \sum_{i = 0}^{num_chunks - 1} f(x_i) 2^i.
pub const SHA256_CHOOSE_BASE: usize = 7;
#[derive(Clone)]
pub struct Sha256ChooseTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, E::Fr>,
    num_of_chunks: usize,
    name: &'static str,
}


impl<E: Engine> Sha256ChooseTable<E> {

    pub fn apply(key: usize) -> usize {

        let bit_table : [usize; SHA256_CHOOSE_BASE] = [
            0, // e + 2f + 3g = 0 => e = 0, f = 0, g = 0 => t = 0
            0, // e + 2f + 3g = 1 => e = 1, f = 0, g = 0 => t = 0
            0, // e + 2f + 3g = 2 => e = 0, f = 1, g = 0 => t = 0
            1, // e + 2f + 3g = 3 => e = 0, f = 0, g = 1 OR e = 1, f = 1, g = 0 => t = 1
            0, // e + 2f + 3g = 4 => e = 1, f = 0, g = 1 => t = 0
            1, // e + 2f + 3g = 5 => e = 0, f = 1, g = 1 => t = 1
            1, // e + 2f + 3g = 6 => e = 1, f = 1, g = 1 => t = 1
        ];

        let mut accumulator : usize = 0;
        let mut input: usize = key;
        let mut count: usize = 0;
    
        while input > 0 {
            let bit = bit_table[input % SHA256_CHOOSE_BASE];
            accumulator += bit << count;
            input /= SHA256_CHOOSE_BASE;
            count += 1;
        }

        accumulator
    }

    pub fn new(num_of_chunks: usize, name: &'static str) -> Self {
        
        let table_size = pow(SHA256_CHOOSE_BASE, num_of_chunks);
        let mut key = Vec::with_capacity(table_size);
        let mut value = Vec::with_capacity(table_size);
        let unused = vec![E::Fr::zero(); table_size];
        let mut map = std::collections::HashMap::with_capacity(table_size);

        for x in 0..table_size {
            let y = Self::apply(x);

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            
            key.push(x);
            value.push(y);

            map.insert(x, y);
        }

        Self {
            table_entries: [key, value, unused],
            table_lookup_map: map,
            num_of_chunks,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for Sha256ChooseTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256ChooseTable")
            .field("base", &SHA256_CHOOSE_BASE)
            .field("num_of_chunks", &self.num_of_chunks)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for Sha256ChooseTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        pow(SHA256_CHOOSE_BASE, self.num_of_chunks)
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name())
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        column_num == 2
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == 1);

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}
    

// table for Sha256 majority subroutine : majority(e, f, g) = (a & b) ^ (a & c) ^ (b & c)
// all the comments related to Sha256 choose table are applicable here, the only difference is that now
// the algebraic mapping is from x = e + f + g to y = majority(e, f, g)
// indeed:
//
// | a | b | c | y |  a + b + c  |
//  -------------------------------
// | 0 | 0 | 0 | 0 |           0 |
// | 0 | 0 | 1 | 0 |           1 |
// | 0 | 1 | 0 | 0 |           1 |
// | 0 | 1 | 1 | 1 |           2 |
// | 1 | 0 | 0 | 0 |           1 |
// | 1 | 0 | 1 | 1 |           2 |
// | 1 | 1 | 0 | 1 |           2 |
// | 1 | 1 | 1 | 0 |           3 |
//
// this well-formed function f(x): [0; 3] -> [0;1] is called majority
pub const SHA256_MAJORITY_BASE: usize = 4;
#[derive(Clone)]
pub struct Sha256MajorityTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, E::Fr>,
    num_of_chunks: usize,
    name: &'static str,
}


impl<E: Engine> Sha256MajorityTable<E> {

    pub fn apply(key: usize) -> usize {

        let bit_table : [usize; SHA256_MAJORITY_BASE] = [
            0, // a + b + c = 0 => (a & b) ^ (a & c) ^ (b & c) = 0
            0, // a + b + c = 1 => (a & b) ^ (a & c) ^ (b & c) = 0
            1, // a + b + c = 2 => (a & b) ^ (a & c) ^ (b & c) = 1
            1, // a + b + c = 3 => (a & b) ^ (a & c) ^ (b & c) = 0
        ];

        let mut accumulator : usize = 0;
        let mut input: usize = key;
        let mut count: usize = 0;
    
        while input > 0 {
            let bit = bit_table[input % SHA256_MAJORITY_BASE];
            accumulator += bit << count;
            input /= SHA256_MAJORITY_BASE;
            count += 1;
        }

        accumulator
    }

    pub fn new(num_of_chunks: usize, name: &'static str) -> Self {
        
        let table_size = pow(SHA256_MAJORITY_BASE, num_of_chunks);
        let mut key = Vec::with_capacity(table_size);
        let mut value = Vec::with_capacity(table_size);
        let unused = vec![E::Fr::zero(); table_size];
        let mut map = std::collections::HashMap::with_capacity(table_size);

        for x in 0..table_size {
            let y = Self::apply(x);

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            
            key.push(x);
            value.push(y);

            map.insert(x, y);
        }

        Self {
            table_entries: [key, value, unused],
            table_lookup_map: map,
            num_of_chunks,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for Sha256MajorityTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Sha256ChooseTable")
            .field("base", &SHA256_MAJORITY_BASE)
            .field("num_of_chunks", &self.num_of_chunks)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for Sha256MajorityTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        pow(SHA256_MAJORITY_BASE, self.num_of_chunks)
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        1
    }
    fn allows_combining(&self) -> bool {
        true
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries[0].clone(), self.table_entries[1].clone(), self.table_entries[2].clone()]
    }
    fn table_id(&self) -> E::Fr {
        table_id_from_string(self.name)
    }
    fn sort(&self, _values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
    fn column_is_trivial(&self, column_num: usize) -> bool {
        assert!(column_num < 3);
        column_num == 2
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}

pub const SHA256_EXPANSION_BASE: usize = 4;

