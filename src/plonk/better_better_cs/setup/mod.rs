use super::cs::*;
use super::data_structures::*;
use crate::pairing::ff::*;
use crate::pairing::*;
use crate::plonk::polynomials::*;
use std::collections::HashMap;

#[derive(Clone)]
pub struct Setup<E: Engine, C: Circuit<E>> {
    pub n: usize,
    pub num_inputs: usize,
    pub gate_setup_monomials: Vec<Polynomial<E::Fr, Coefficients>>,
    pub gate_selectors_monomials: Vec<Polynomial<E::Fr, Coefficients>>,
    pub permutation_monomials: Vec<Polynomial<E::Fr, Coefficients>>,

    pub total_lookup_entries_length: usize,
    pub lookup_selector_monomial: Option<Polynomial<E::Fr, Coefficients>>,
    pub lookup_tables_monomials: Vec<Polynomial<E::Fr, Coefficients>>,
    pub lookup_table_type_monomial: Option<Polynomial<E::Fr, Coefficients>>,

    marker: std::marker::PhantomData<C>
}

impl<E: Engine, C: Circuit<E>> std::fmt::Debug for Setup<E, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Setup")
            .field("n", &self.n)
            .field("num_inputs", &self.num_inputs)
            .field("gate_setup_monomials", &self.gate_setup_monomials)
            .field("gate_selectors_monomials", &self.gate_selectors_monomials)
            .field("permutation_monomials", &self.permutation_monomials)
            .field("total_lookup_entries_length", &self.total_lookup_entries_length)
            .field("lookup_selector_monomial", &self.lookup_selector_monomial)
            .field("lookup_tables_monomials", &self.lookup_tables_monomials)
            .field("lookup_table_type_monomial", &self.lookup_table_type_monomial)
            .finish()
    }
}

impl<E: Engine, C: Circuit<E>> Setup<E, C> {
    pub fn empty() -> Self {
        Self {
            n: 0,
            num_inputs: 0,
            gate_setup_monomials: vec![],
            gate_selectors_monomials: vec![],
            permutation_monomials: vec![],
        
            total_lookup_entries_length: 0,
            lookup_selector_monomial: None,
            lookup_tables_monomials: vec![],
            lookup_table_type_monomial: None,
        
            marker: std::marker::PhantomData
        }
    }
}
