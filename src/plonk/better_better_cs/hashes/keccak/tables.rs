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
    lower_bound: usize,
    upper_bound: usize,
    name: &'static str,
}

impl<E: Engine> TinyRangeTable<E> {
    pub fn new(lower_bound: usize, upper_bound: usize, name: &'static str) -> Self {
        let table_size = pow(upper_bound - lower_bound, 3);
        let mut col1 = Vec::with_capacity(table_size);
        let mut col2 = Vec::with_capacity(table_size);
        let mut col3 = Vec::with_capacity(table_size);

        for x in lower_bound..upper_bound {
            for y in lower_bound..upper_bound {
                for z in lower_bound..upper_bound {
                    let x = u64_to_ff::<E::Fr>(x as u64);
                    let y = u64_to_ff::<E::Fr>(y as u64);
                    let z = u64_to_ff::<E::Fr>(z as u64);
                    
                    col1.push(x);
                    col2.push(y);
                    col3.push(z);
                }
            }
        }

        Self {
            table_entries: [col1, col2, col3],
            lower_bound,
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
        pow(self.upper_bound - self.lower_bound, 3)
    }
    fn num_keys(&self) -> usize {
        3
    }
    fn num_values(&self) -> usize {
        0
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

    fn is_valid_entry(&self, keys: &[E::Fr], _values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());

        let n0 = keys[0].into_repr().as_ref()[0] as usize;
        let n1 = keys[1].into_repr().as_ref()[0] as usize;
        let n2 = keys[2].into_repr().as_ref()[0] as usize;
        let range = self.lower_bound..self.upper_bound;
        range.contains(&n0) && range.contains(&n1) && range.contains(&n2)
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        let num0 = ff_to_u64(&keys[0]) as usize;
        let num1 = ff_to_u64(&keys[1]) as usize;
        let num2 = ff_to_u64(&keys[2]) as usize;
        let range = self.lower_bound..self.upper_bound;
        if range.contains(&num0) && range.contains(&num1) && range.contains(&num2) {
            return Ok(vec![])
        }
        Err(SynthesisError::Unsatisfiable)
    }
}

// for given bases (b, c), transformation function f: [0, b) -> [0, c) and num_of_chunks n this table transforms:
// x = \sum_{i=0}^n x_i b^i -> y = \sum_{i=0}^m f(x_i) c^i.
// first column - input x; 
// second column - number of non-zero chunks (as in extended range-check table)
// third column - output y;
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
                tmp.add_assign(&u64_to_ff(*x));
                tmp
            });

            let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_c_fr);
                tmp.add_assign(&u64_to_ff(transform_f(*x)));
                tmp
            });

            let mut chunk_count = (num_chunks - coefs.iter().take_while(|x| **x == 0).count()) as u64;
            // optimization: if the number is zero, than chunk count is set to one: 
            chunk_count = if chunk_count > 0 {chunk_count} else {1};
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

impl<E: Engine> LookupTableInternal<E> for ExtendedBaseConverterTable<E> {
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


#[derive(Clone)]
pub struct MultiBaseConverterTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    num_chunks: usize,
    input_base: u64,
    first_output_base: u64,
    second_output_base: u64,
    name: &'static str,
}

impl<E: Engine> MultiBaseConverterTable<E> {
    pub fn new<F>(num_ch: usize, input_base: u64, output_base1: u64, output_base2: u64, transform_f: F, name: &'static str) -> Self 
    where F : Fn(u64) -> u64
    {
        let table_size = pow(input_base as usize, num_ch);
        let mut keys_vec = Vec::with_capacity(table_size);
        let mut values1_vec = Vec::with_capacity(table_size);
        let mut values2_vec = Vec::with_capacity(table_size);
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let input_base_fr = u64_to_ff::<E::Fr>(input_base);
        let first_output_base_fr = u64_to_ff::<E::Fr>(output_base1);
        let second_output_base_fr = u64_to_ff::<E::Fr>(output_base2);
        let zero_fr = E::Fr::zero();

        for coefs in (0..num_ch).map(|_| 0..input_base).multi_cartesian_product() {
            let key = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&input_base_fr);
                tmp.add_assign(&u64_to_ff(*x));
                tmp
            });

            let value1 = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&first_output_base_fr);
                tmp.add_assign(&u64_to_ff(transform_f(*x)));
                tmp
            });

            let value2 = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&second_output_base_fr);
                tmp.add_assign(&u64_to_ff(transform_f(*x)));
                tmp
            });

            keys_vec.push(key);
            values1_vec.push(value1);
            values2_vec.push(value2);
            map.insert(key, (value1, value2));
        }

        Self {
            table_entries: [keys_vec, values1_vec, values2_vec],
            table_lookup_map: map,
            num_chunks : num_ch,
            input_base,
            first_output_base : output_base1,
            second_output_base : output_base2,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for MultiBaseConverterTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MultiBaseConverterTable")
            .field("num_chunks", &self.num_chunks)
            .field("input_base", &self.input_base)
            .field("first_output_base", &self.first_output_base)
            .field("second_output_base", &self.second_output_base)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for MultiBaseConverterTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << pow(self.input_base as usize, self.num_chunks)
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


#[derive(Clone)]
pub struct OverflowFriendlyBaseConverterTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, E::Fr>,
    num_chunks: usize,
    base_b: u64,
    base_c: u64,
    high_chunk_offset : u64,
    name: &'static str,
}

impl<E: Engine> OverflowFriendlyBaseConverterTable<E> {
    pub fn new<F: Fn(u64) -> u64>(num_chunks: usize, base_b: u64, base_c: u64, offset: u64, f: F, name: &'static str) -> Self {
        let table_size = pow(base_b as usize, num_chunks);
        let mut keys_vec = Vec::with_capacity(table_size);
        let mut values_vec = Vec::with_capacity(table_size);
        let unused = vec![E::Fr::zero(); table_size];
        let mut map = std::collections::HashMap::with_capacity(table_size);

        let base_b_fr = u64_to_ff::<E::Fr>(base_b);
        let base_c_fr = u64_to_ff::<E::Fr>(base_c);
        let offset_fr = u64_exp_to_ff::<E::Fr>(base_b, offset);
        let zero_fr = E::Fr::zero();

        for mut coefs in (0..num_chunks).map(|_| 0..base_b).multi_cartesian_product() {
            let high = coefs.drain(0..1).next().unwrap();
            let mut high_fr = u64_to_ff::<E::Fr>(high);
            high_fr.mul_assign(&offset_fr);

            let mut key = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_b_fr);
                tmp.add_assign(&u64_to_ff(*x));
                tmp
            });
            key.add_assign(&high_fr);

            *coefs.last_mut().unwrap() += high;
            let value = coefs.iter().fold(zero_fr.clone(), |acc, x| {
                let mut tmp = acc;
                tmp.mul_assign(&base_c_fr);
                tmp.add_assign(&u64_to_ff(f(*x)));
                tmp
            });

            keys_vec.push(key);
            values_vec.push(value);
            map.insert(key, value);
        }

        Self {
            table_entries: [keys_vec, values_vec, unused],
            table_lookup_map: map,
            num_chunks,
            base_b,
            base_c,
            high_chunk_offset: offset,
            name,
        }
    }
}

impl<E: Engine> std::fmt::Debug for OverflowFriendlyBaseConverterTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExtendedBaseConverterTable")
            .field("num_chunks", &self.num_chunks)
            .field("base_b", &self.base_b)
            .field("base_c", &self.base_c)
            .field("high_chunk_offset", &self.high_chunk_offset)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for OverflowFriendlyBaseConverterTable<E> {
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
        column_num == 2
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return entry == &values[0];
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&keys[0]) {
            return Ok(vec![*entry, E::Fr::zero()])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


