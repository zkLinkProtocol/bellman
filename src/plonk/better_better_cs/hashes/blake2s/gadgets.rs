use crate::plonk::better_better_cs::cs::*;
use crate::plonk::better_better_cs::lookup_tables::*;
use crate::plonk::better_better_cs::utils;
use crate::pairing::ff::*;
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};
use crate::SynthesisError;
use crate::Engine;
use crate::plonk::better_better_cs::gadgets::num::{
    AllocatedNum,
    Num,
};

use super::tables::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};
use std::sync::Arc;

type Result<T> = std::result::Result<T, SynthesisError>;

const CHUNK_SIZE : usize = 8; 
const SHIFT : usize = 4;
const SPLIT_POINT : usize = 7; 


#[derive(Clone)]
pub struct DecomposedRegister<E : Engine> {
    t0 : Num<E>,
    t1: Num<E>,
    t2: Num<E>,
    t3: Num<E>,
}


#[derive(Clone)]
pub enum Register<E: Engine> {
    Full(Num<E>),
    Decomposed(DecomposedRegister<E>),
}


pub struct Blake2sGadget<E: Engine> {
    xor_table: Arc<LookupTableApplication<E>>,
    compound_shift_table: Arc<LookupTableApplication<E>>,
    split_table: Arc<LookupTableApplication<E>>,
    iv: [E::Fr; 8],
}

impl<E: Engine> Blake2sGadget<E> {
   
    // returns n ^ exp if exp is not zero, n otherwise
    fn u64_exp_to_ff(n: u64, exp: u64) -> E::Fr {
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = n;
        let mut res = E::Fr::from_repr(repr).expect("should parse");

        if exp != 0 {
            res = res.pow(&[exp]);
        }

        res
    }

    fn u64_to_ff(n: u64) -> E::Fr {
        Self::u64_exp_to_ff(n, 0)
    }

    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self> {
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "xor_table";
        let xor_table = LookupTableApplication::new(
            name1,
            XorTable::new(CHUNK_SIZE),
            columns3.clone(),
            true
        );

        let name2 : &'static str = "compound_table";
        let compound_shift_table = LookupTableApplication::new(
            name2,
            CompoundShiftTable::new(CHUNK_SIZE, SHIFT, name2),
            columns3.clone(),
            true
        );

        let name3 : &'static str = "split_table";
        let split_table = LookupTableApplication::new(
            name3,
            SplitTable::new(CHUNK_SIZE, SPLIT_POINT, name3),
            columns3.clone(),
            true
        );

        let xor_table = cs.add_table(xor_table)?;
        let sha256_maj_normalization_table = cs.add_table(sha256_maj_normalization_table)?;
        let sha256_ch_xor_table  = cs.add_table(sha256_ch_xor_table)?;
        

        // Initialize IV values:
        // (first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19):
        let iv = [ 
            Self::u64_to_ff(0x6a09e667),
            Self::u64_to_ff(0xbb67ae85),
            Self::u64_to_ff(0x3c6ef372),
            Self::u64_to_ff(0xa54ff53a),
            Self::u64_to_ff(0x510e527f),
            Self::u64_to_ff(0x9b05688c),
            Self::u64_to_ff(0x1f83d9ab),
            Self::u64_to_ff(0x5be0cd19),
        ];

      

        Ok(Sha256GadgetParams {
            global_strategy,
            global_table,
            majority_strategy,

            ch_base_num_of_chunks,
            maj_base_num_of_chunks,
            sheduler_base_num_of_chunks,

            sha256_base7_rot6_table,
            sha256_base7_rot3_extr10_table,
            sha256_ch_normalization_table,
            sha256_ch_xor_table,

            sha256_base4_rot2_table,
            sha256_base4_rot2_extr10_table,
            sha256_maj_normalization_table,
            sha256_maj_xor_table,

            sha256_base4_rot7_table,
            sha256_base4_widh10_table,
            sha256_base4_shift3_table,
            sha256_base4_rot9_table,
            sha256_sheduler_xor_table,

            iv,
            round_constants,

            _marker : std::marker::PhantomData,
        })
    }
