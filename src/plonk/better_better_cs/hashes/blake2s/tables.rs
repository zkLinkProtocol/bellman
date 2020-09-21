use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use crate::SynthesisError;
use crate::Engine;


#[derive(Clone)]
pub struct XorTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    name: &'static str,
}


impl<E: Engine> XorTable<E> {

    pub fn new(bits: usize, name: &'static str) -> Self {
        let mut key0 = Vec::with_capacity(1 << bits);
        let mut key1 = Vec::with_capacity(1 << bits);
        let mut value = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let z = x ^ y;

                let x = E::Fr::from_str(&x.to_string()).unwrap();
                let y = E::Fr::from_str(&y.to_string()).unwrap();
                let z = E::Fr::from_str(&z.to_string()).unwrap();

                key0.push(x);
                key1.push(y);
                value.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [key0, key1, value],
            table_lookup_map: map,
            bits,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for XorTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("XorTable")
            .field("bits", &self.bits)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for XorTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
    }
    fn num_keys(&self) -> usize {
        2
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
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


#[derive(Clone)]
pub struct CompoundShiftTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    shift: usize,
    name: &'static str,
}


impl<E: Engine> CompoundShiftTable<E> {

    pub fn new(bits: usize, shift: usize, name: &'static str) -> Self {
        assert!(shift < bits);

        let mut key0 = Vec::with_capacity(1 << bits);
        let mut key1 = Vec::with_capacity(1 << bits);
        let mut value = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));
        let mask = (1 << (bits - shift)) - 1;

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let z = ( y >> shift) | ((x & mask) << (bits - shift));

                let x = E::Fr::from_str(&x.to_string()).unwrap();
                let y = E::Fr::from_str(&y.to_string()).unwrap();
                let z = E::Fr::from_str(&z.to_string()).unwrap();

                key0.push(x);
                key1.push(y);
                value.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [key0, key1, value],
            table_lookup_map: map,
            bits,
            shift,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for CompoundShiftTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CompoundShiftTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for CompoundShiftTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
    }
    fn num_keys(&self) -> usize {
        2
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
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}


#[derive(Clone)]
pub struct SplitTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<E::Fr, (E::Fr, E::Fr)>,
    bits: usize,
    split_offset: usize,
    name: &'static str,
}


impl<E: Engine> SplitTable<E> {

    pub fn new(bits: usize, split_offset: usize, name: &'static str) -> Self {
        assert!(split_offset < bits);

        let mut key = Vec::with_capacity(1 << bits);
        let mut value0 = Vec::with_capacity(1 << bits);
        let mut value1 = Vec::with_capacity(1 << bits);
        let mut map = std::collections::HashMap::with_capacity(1 << bits);
        let mask = (1 << split_offset) - 1;

        for x in 0..(1 << bits) {
            let y = x >> split_offset;
            let z = x & mask;

            let x = E::Fr::from_str(&x.to_string()).unwrap();
            let y = E::Fr::from_str(&y.to_string()).unwrap();
            let z = E::Fr::from_str(&z.to_string()).unwrap();

            key.push(x);
            value0.push(y);
            value1.push(z);

            map.insert(x, (y, z));    
        }

        Self {
            table_entries: [key, value0, value1],
            table_lookup_map: map,
            bits,
            split_offset,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for SplitTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplitTable")
            .field("bits", &self.bits)
            .field("split_offset", &self.split_offset)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for SplitTable<E> {
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


#[derive(Clone)]
pub struct XorRotateTable<E: Engine> {
    table_entries: [Vec<E::Fr>; 3],
    table_lookup_map: std::collections::HashMap<(E::Fr, E::Fr), E::Fr>,
    bits: usize,
    shift: usize,
    name: &'static str,
}


impl<E: Engine> XorRotateTable<E> {

    pub fn new(bits: usize, shift: usize, name: &'static str) -> Self {
        let mut key0 = Vec::with_capacity(1 << bits);
        let mut key1 = Vec::with_capacity(1 << bits);
        let mut value = Vec::with_capacity(1 << (2 * bits));
        let mut map = std::collections::HashMap::with_capacity(1 << (2 * bits));

        for x in 0..(1 << bits) {
            for y in 0..(1 << bits) {
                let tmp = x ^ y;
                let z : u32 = (tmp >> shift) | ((tmp << (32 - shift)) & 0xffffffff);

                let x = E::Fr::from_str(&x.to_string()).unwrap();
                let y = E::Fr::from_str(&y.to_string()).unwrap();
                let z = E::Fr::from_str(&z.to_string()).unwrap();

                key0.push(x);
                key1.push(y);
                value.push(z);

                map.insert((x, y), z);
            }    
        }

        Self {
            table_entries: [key0, key1, value],
            table_lookup_map: map,
            bits,
            shift,
            name,
        }
    }
}


impl<E: Engine> std::fmt::Debug for XorRotateTable<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("XorRotateTable")
            .field("bits", &self.bits)
            .field("shift", &self.shift)
            .finish()
    }
}


impl<E: Engine> LookupTableInternal<E> for XorRotateTable<E> {
    fn name(&self) -> &'static str {
        self.name
    }
    fn table_size(&self) -> usize {
        1 << (2 * self.bits)
    }
    fn num_keys(&self) -> usize {
        2
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
        false
    }

    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == self.num_keys());
        assert!(values.len() == self.num_values());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return entry == &(values[0]);
        }
        false
    }

    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == self.num_keys());

        if let Some(entry) = self.table_lookup_map.get(&(keys[0], keys[1])) {
            return Ok(vec![*entry])
        }

        Err(SynthesisError::Unsatisfiable)
    }
}