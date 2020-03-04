use crate::pairing::Engine;
use crate::plonk::polynomials::*;

pub mod generator;
pub mod prover;

pub struct IndexedSetup<E: Engine> {
    pub a_num_non_zero: usize,
    pub b_num_non_zero: usize,
    pub c_num_non_zero: usize,
    pub domain_h_size: usize,
    pub domain_k_size: usize,
    pub a_matrix_poly: Polynomial<E::Fr, Coefficients>,
    pub b_matrix_poly: Polynomial<E::Fr, Coefficients>,
    pub c_matrix_poly: Polynomial<E::Fr, Coefficients>,
    pub a_row_poly: Polynomial<E::Fr, Coefficients>,
    pub b_row_poly: Polynomial<E::Fr, Coefficients>,
    pub c_row_poly: Polynomial<E::Fr, Coefficients>,
    pub a_col_poly: Polynomial<E::Fr, Coefficients>,
    pub b_col_poly: Polynomial<E::Fr, Coefficients>,
    pub c_col_poly: Polynomial<E::Fr, Coefficients>,
    pub a_row_indexes: Vec<usize>,
    pub b_row_indexes: Vec<usize>,
    pub c_row_indexes: Vec<usize>,
    pub a_col_indexes: Vec<usize>,
    pub b_col_indexes: Vec<usize>,
    pub c_col_indexes: Vec<usize>,
}