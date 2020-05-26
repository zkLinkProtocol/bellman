use crate::pairing::ff::{Field, PrimeField};
use crate::pairing::{Engine};
use crate::bit_vec::BitVec;

use crate::{SynthesisError};
use std::marker::PhantomData;

use crate::worker::Worker;
use crate::plonk::domains::*;
use crate::plonk::polynomials::*;

pub use crate::plonk::cs::variable::*;
use crate::plonk::better_cs::utils::*;
use super::cs::*;

pub trait LookupTableInternal<E: Engine>: Send 
    + Sync 
    + 'static 
    + std::any::Any 
    + std::fmt::Debug {
        fn name(&self) -> &'static str;
        fn table_size(&self) -> usize;
        fn num_keys(&self) -> usize;
        fn num_values(&self) -> usize;
        fn allows_combining(&self) -> bool;
        fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool;
        fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError>;
        fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>>;
        fn table_id(&self) -> E::Fr;
        fn sort(&self, values: &[E::Fr], column: usize) -> Result<Vec<E::Fr>, SynthesisError>;
        fn box_clone(&self) -> Box<dyn LookupTableInternal<E>>;
    }

impl<E: Engine> std::hash::Hash for dyn LookupTableInternal<E> {
    fn hash<H>(&self, state: &mut H) where H: std::hash::Hasher {
        self.type_id().hash(state);
        self.name().hash(state);
        self.table_size().hash(state);
        self.num_keys().hash(state);
        self.num_values().hash(state);
    }
}

impl<E: Engine> PartialEq for dyn LookupTableInternal<E> {
    fn eq(&self, other: &Self) -> bool {
        self.type_id() == other.type_id() &&
        self.name() == other.name() &&
        self.table_size() == other.table_size() &&
        self.num_keys() == other.num_keys() &&
        self.num_values() == other.num_values()
    }
}

impl<E: Engine> Eq for dyn LookupTableInternal<E> {}

/// Applies a single lookup table to a specific set of columns
#[derive(Debug)]
pub struct LookupTableApplication<E: Engine> {
    name: &'static str,
    apply_over: Vec<PolyIdentifier>,
    table_to_apply: Box<dyn LookupTableInternal<E>>,
    can_be_combined: bool
}

impl<E: Engine> PartialEq for LookupTableApplication<E> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name &&
        self.apply_over == other.apply_over &&
        &self.table_to_apply == &other.table_to_apply &&
        self.can_be_combined == other.can_be_combined
    }
}

impl<E: Engine> Eq for LookupTableApplication<E> {}

impl<E: Engine> LookupTableApplication<E> {
    pub fn new<L: LookupTableInternal<E>>(
        name: &'static str,
        table: L,
        apply_over: Vec<PolyIdentifier>,
        can_be_combined: bool
    ) -> Self {
        Self {
            name,
            apply_over,
            table_to_apply: Box::from(table) as Box<dyn LookupTableInternal<E>>,
            can_be_combined
        }
    }

    pub fn name(&self) -> String {
        format!("{} over {:?}", self.table_to_apply.name(), self.apply_over)
    }

    pub fn applies_over(&self) -> &[PolyIdentifier] {
        &self.apply_over
    }

    pub fn can_be_combined(&self) -> bool {
        self.table_to_apply.allows_combining()
    }

    pub fn is_valid_entry(&self, values: &[E::Fr]) -> bool {
        let num_keys = self.table_to_apply.num_keys();
        let num_values = self.table_to_apply.num_values();

        assert_eq!(num_keys + num_values, values.len());

        let (keys, values) = values.split_at(num_keys);

        self.table_to_apply.is_valid_entry(keys, values)
    }

    pub fn table_id(&self) -> E::Fr {
        self.table_to_apply.table_id()
    }

    pub fn size(&self) -> usize {
        self.table_to_apply.table_size()
    }
}

/// Apply multiple tables at the same time to corresponding columns
#[derive(Debug)]
pub struct MultiTableApplication<E: Engine> {
    name: &'static str,
    apply_over: Vec<PolyIdentifier>,
    table_to_apply: Vec<Box<dyn LookupTableInternal<E>>>,
    table_size: usize,
    id: E::Fr
}

impl<E: Engine> PartialEq for MultiTableApplication<E> {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name &&
        self.apply_over == other.apply_over &&
        &self.table_to_apply == &other.table_to_apply &&
        self.table_size == other.table_size
    }
}

impl<E: Engine> Eq for MultiTableApplication<E> {}

impl<E: Engine> MultiTableApplication<E> {
    pub fn name(&self) -> String {
        format!("Table {} of size {}", self.name, self.table_size)
    }

    pub fn functional_name(&self) -> String {
        self.name.to_string()
    }

    pub fn new_range_table_of_width_3(width: usize, over: Vec<PolyIdentifier>) -> Result<Self, SynthesisError> {
        let table = RangeCheckTableOverSingleColumn::new(width);

        let name = "Range check table";

        Ok(Self {
            name: name,
            apply_over: over,
            table_to_apply: vec![table.box_clone(), table.box_clone(), table.box_clone()],
            table_size: 1 << width,
            id: table_id_from_string::<E::Fr>(name)
        })
    }

    pub fn applies_over(&self) -> &[PolyIdentifier] {
        &self.apply_over
    }

    pub fn is_valid_entry(&self, values: &[E::Fr]) -> bool {
        assert_eq!(values.len(), 3);
        let mut all_values = values;
        let mut valid = true;
        for t in self.table_to_apply.iter() {
            let num_keys = t.num_keys();
            let num_values = t.num_values();
            let (keys, rest) = all_values.split_at(num_keys);
            let (values, rest) = rest.split_at(num_values);
            valid &= t.is_valid_entry(keys, values);
            all_values = rest;
        }

        valid
    }

    pub fn size(&self) -> usize {
        self.table_size
    }

    pub fn table_id(&self) -> E::Fr {
        self.id
    }
}
#[derive(Clone)]
pub struct RangeCheckTableOverSingleColumn<E: Engine> {
    table_entries: Vec<E::Fr>,
    bits: usize
}

impl<E: Engine> RangeCheckTableOverSingleColumn<E> {
    pub fn new(bits: usize) -> Self {
        let mut entries = Vec::with_capacity(1 << bits);
        for i in 0..(1 << bits) {
            let value = E::Fr::from_str(&i.to_string()).unwrap();
            entries.push(value);
        }

        Self {
            table_entries: entries,
            bits
        }
    }
}

impl<E: Engine> std::fmt::Debug for RangeCheckTableOverSingleColumn<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RangeCheckTableOverSingleColumn")
            .field("bits", &self.bits)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for RangeCheckTableOverSingleColumn<E> {
    fn name(&self) -> &'static str {
        "Range check table for a single column"
    }
    fn table_size(&self) -> usize {
        1usize << self.bits
    }
    fn num_keys(&self) -> usize {
        1
    }
    fn num_values(&self) -> usize {
        0
    }
    fn allows_combining(&self) -> bool {
        false
    }
    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == 1);
        assert!(values.len() == 0);

        self.table_entries.contains(&keys[0])
    }
    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == 1);

        if self.table_entries.contains(&keys[0]) {
            return Ok(vec![]);
        } else {
            return Err(SynthesisError::Unsatisfiable);
        }
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries.clone()]
    }
    fn table_id(&self) -> E::Fr {
        E::Fr::from_str("1234").unwrap()
    }
    fn sort(&self, values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
}
#[derive(Clone)]
pub struct RangeCheckTableOverOneColumnOfWidth3<E: Engine> {
    table_entries: Vec<E::Fr>,
    dummy_entries: Vec<E::Fr>,
    bits: usize
}

impl<E: Engine> RangeCheckTableOverOneColumnOfWidth3<E> {
    pub fn new(bits: usize) -> Self {
        let mut entries = Vec::with_capacity(1 << bits);
        for i in 0..(1 << bits) {
            let value = E::Fr::from_str(&i.to_string()).unwrap();
            entries.push(value);
        }

        let dummy_entries = vec![E::Fr::zero(); 1 << bits];
        Self {
            table_entries: entries,
            dummy_entries,
            bits
        }
    }
}

impl<E: Engine> std::fmt::Debug for RangeCheckTableOverOneColumnOfWidth3<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RangeCheckTableOverOneColumnOfWidth3")
            .field("bits", &self.bits)
            .finish()
    }
}

impl<E: Engine> LookupTableInternal<E> for RangeCheckTableOverOneColumnOfWidth3<E> {
    fn name(&self) -> &'static str {
        "Range check table for a single column only with width 3"
    }
    fn table_size(&self) -> usize {
        1usize << self.bits
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
    fn is_valid_entry(&self, keys: &[E::Fr], values: &[E::Fr]) -> bool {
        assert!(keys.len() == 3);
        assert!(values.len() == 0);

        let mut valid = self.table_entries.contains(&keys[0]);
        valid = valid & keys[1].is_zero();
        valid = valid & keys[2].is_zero();

        valid

    }
    fn query(&self, keys: &[E::Fr]) -> Result<Vec<E::Fr>, SynthesisError> {
        assert!(keys.len() == 3);

        let is_valid = self.is_valid_entry(keys, &[]);

        if is_valid {
            return Ok(vec![]);
        } else {
            return Err(SynthesisError::Unsatisfiable);
        }
    }
    fn get_table_values_for_polys(&self) -> Vec<Vec<E::Fr>> {
        vec![self.table_entries.clone(), self.dummy_entries.clone(), self.dummy_entries.clone()]
    }
    fn table_id(&self) -> E::Fr {
        E::Fr::from_str("5678").unwrap()
    }
    fn sort(&self, values: &[E::Fr], _column: usize) -> Result<Vec<E::Fr>, SynthesisError> {
        unimplemented!()
    }
    fn box_clone(&self) -> Box<dyn LookupTableInternal<E>> {
        Box::from(self.clone())
    }
}


fn table_id_from_string<F: PrimeField>(
    s: &str
) -> F {
    let mut h = tiny_keccak::keccak256(s.as_bytes());
    for i in 0..4 {
        h[i] = 0u8;
    }

    use crate::pairing::ff::PrimeFieldRepr;

    let mut repr = F::Repr::default();
    repr.read_be(&h[..]).unwrap();

    F::from_repr(repr).unwrap()
}