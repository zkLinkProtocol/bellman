use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use crate::SynthesisError;
use crate::Engine;

use itertools::Itertools;

use super::utils::*;


// simultaneous range check for all three columns together!
#[derive(Clone)]
pub struct TinyRangeTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    upper_bound: u64,
    name: &'static str,
}

impl<E: Engine> TinyRangeTable<E> {
    pub fn new(upper_bound: u64, name: &'static str) -> Self {
        let mut elems = Vec::with_capacity(upper_bound as usize);
        let unused_0 = vec![E::Fr::zero(); upper_bound as usize];
        let unused_1 = vec![E::Fr::zero(); upper_bound as usize];

        for x in 0..upper_bound {
            let x = u64_to_ff::<E::Fr>(x);
            elems.push(x);
        }

        Self {
            table_entries: [elems, unused_0, unused_1],
            upper_bound,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for TinyRangeTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TinyRangeTable")
            .field("upper_bound", &self.upper_bound)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for TinyRangeTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        self.upper_bound as usize
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
        assert!(column_num < 2);
        column_num > 0
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());

        let num = keys[0].into_repr().as_ref()[0];
        num < self.upper_bound
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        let num = ff_to_u64(&keys[0]);
        if num < self.upper_bound {
            return Ok(vec![E::Fr::zero(); 2])
        }
        Err(SynthesisError::Unsatisfiable)
    }
}

// for given bases (b, c), transformation function f: [0, b) -> [0, c) and num_of_chunks n this table transforms:
// x = \sum_{i=0}^n x_i b^i -> y = \sum_{i=0}^m f(x_i) c^i.
// first column - input x; 
// second column - number of non-zero chunks (as in extended range-check table)
// third column - output y;
//
#[derive(Clone)]
pub struct ExtendedBaseConverterTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    num_chunks: usize,
    base_b: u64,
    base_c: u64,
    name: &'static str,
}

impl<E: Engine> ExtendedBaseConverterTable<E> {
    pub fn new<F: Fn(u64) -> u64>(num_chunks: usize, base_b: u64, base_c: u64, transform_f: F, name: &'static str) -> Self {
        let table_size = pow(base_b as usize, num_chunks);
        let mut keys_vec = Vec::with_capacity(table_size);
        let mut chunk_count_vec = Vec::with_capacity(table_size);
        let mut values_vec = Vec::with_capacity(table_size);
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let base_b_fr = u64_to_ff::<E::Fr>(base_b);
        let base_c_fr = u64_to_ff::<E::Fr>(base_c);
        let zero_fr = E::Fr::zero();

        for coefs in (0..num_chunks).map(|_| 0..base_b).multi_cartesian_product() {
            let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_b_fr);
                tmp.add_assign(u64_to_ff(*x));
                tmp
            });

            let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_c_fr);
                tmp.add_assign(u64_to_ff(transform_f(*x)));
                tmp
            });

            let chunk_count = (num_chunks - coefs.iter().take_while(|x| **x == 0).count()) as u64;
            let chunk_count_fr = u64_to_ff(chunk_count);

            keys_vec.push(key);
            chunk_count_vec.push(chunk_count_fr);
            values_vec.push(value);
            map.insert(key, (chunk_count_fr, value));
        }

        Self {
            table_entries: [keys_vec, chunk_count_vec, values_vec],
            table_lookup_map: map,
            num_chunks,
            base_b,
            base_c,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for ExtendedBaseConverterTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedBaseConverterTable")
            .field("num_chunks", &self.num_chunks)
            .field("base_b", &self.base_b)
            .field("base_c", &self.base_c)
            .finish()
    }
}

impl<E: Engine, F: Fn(u64) -> u64> LookupTableInternal<E> for ExtendedBaseConverterTable<E, F> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << pow(self.base_b as usize, self.num_chunks)
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

// TD: double base converter - convert simultaneously into two different bases
// TD: convert 0 and 64-th chunk


