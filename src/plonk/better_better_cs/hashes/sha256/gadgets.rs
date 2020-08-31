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
use super::converters::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};

use super::utils::*;
use super::tables::*;
use super::custom_gates::*;
use std::sync::Arc;
use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use std::ops::Add;
use std::iter;


type Result<T> = std::result::Result<T, SynthesisError>;
pub const SHA256_EXPANSION_BASE: usize = 4;


// helper struct for tracking how far current value from being in 32-bit range
// our gadget is suited to handle at most 4-bit overflows itself
#[derive(Copy, Clone)]
pub enum OverflowTracker {
    NoOverflow,
    OneBitOverflow,
    SmallOverflow(u64), // overflow less or equal than 4 bits
    SignificantOverflow
}

impl Into<u64> for OverflowTracker {
    fn into(self: Self) -> u64 {
        match self {
            OverflowTracker::NoOverflow => 0,
            OverflowTracker::OneBitOverflow => 1,
            OverflowTracker::SmallOverflow(x) => x,
            OverflowTracker::SignificantOverflow => 5,
        }
    }
}


impl From<u64> for OverflowTracker {
    fn from(n: u64) -> Self {
        match n {
            0 => OverflowTracker::NoOverflow,
            1 => OverflowTracker::OneBitOverflow,
            2 | 3| 4 => OverflowTracker::SmallOverflow(n),
            _ => OverflowTracker::SignificantOverflow,
        }
    }
}

impl Add for OverflowTracker {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let a : u64 = self.into();
        let b : u64 = other.into();
        let new_of_tracker : OverflowTracker = (a+b).into();
        new_of_tracker
    }
}

#[derive(Clone)]
pub struct NumWithTracker<E: Engine> {
    num: Num<E>,
    overflow_tracker: OverflowTracker,
}

impl<E: Engine> From<Num<E>> for NumWithTracker<E> 
{
    fn from(num: Num<E>) -> Self {
        NumWithTracker {
            num,
            overflow_tracker: OverflowTracker::NoOverflow
        }
    }
}

impl<E: Engine> NumWithTracker<E> {
    pub fn add<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &Num<E>) -> Result<Self> {
        let new_num = self.num.add(cs, other)?;
        let new_tracker = match self.num.is_constant() && other.is_constant() {
            true => OverflowTracker::NoOverflow,
            false => self.overflow_tracker + OverflowTracker::OneBitOverflow,
        };

        Ok(NumWithTracker{
            num: new_num,
            overflow_tracker: new_tracker,
        })
    }

    pub fn add_two<CS: ConstraintSystem<E>>(&self, cs: &mut CS, first: &Num<E>, second: &Num<E>) -> Result<Self> {
        let new_num = self.num.add_two(cs, first, second)?;
        let new_tracker = match (self.num.is_constant(), first.is_constant(), second.is_constant()) {
            (true, true, true) => OverflowTracker::NoOverflow,
            (false, true, true) => self.overflow_tracker + OverflowTracker::OneBitOverflow,
            (true, false, true) | (true, true, false) => OverflowTracker::OneBitOverflow,
            (true, false, false) => OverflowTracker::SmallOverflow(2),
            (false, _, _) => self.overflow_tracker + OverflowTracker::SmallOverflow(2),
        };

         Ok(NumWithTracker{
            num: new_num,
            overflow_tracker: new_tracker,
        })
    }
}


#[derive(Copy, Clone)]
pub enum Strategy {
    UseTwoTables,
    UseCustomGadgets,
}

#[derive(Clone)]
pub struct SparseChValue<E: Engine> {
    normal: Num<E>,
    sparse: Num<E>,
    // all rots are in sparse representation as well
    rot6: Num<E>,
    rot11: Num<E>,
    rot25: Num<E>,
}

#[derive(Clone)]
pub struct SparseMajValue<E: Engine> {
    normal: Num<E>,
    sparse: Num<E>,
    // all rots are in sparse representation as well
    rot2: Num<E>,
    rot13: Num<E>,
    rot22: Num<E>,
}


pub struct Sha256Registers<E: Engine> {
    a : NumWithTracker<E>,
    b : NumWithTracker<E>,
    c : NumWithTracker<E>,
    d : NumWithTracker<E>,
    e : NumWithTracker<E>,
    f : NumWithTracker<E>,
    g : NumWithTracker<E>,
    h : NumWithTracker<E>,
}


pub struct Sha256GadgetParams<E: Engine> {
    // for the purpose of this flag, see comments at the beginning of "convert_into_sparse_majority_form" function
    majority_strategy: Strategy,

    // the purpose of these parameters is discussed before the "normalize" function
    ch_base_num_of_chunks: usize,
    maj_base_num_of_chunks: usize,
    // NOTE : actually the majority vand sheduler bases are the same (4), so thre is no reason for their corresponding
    // number of chunks to be different
    // we prefer to separate these parameters for coherency of implementation and ease of future modifications
    sheduler_base_num_of_chunks: usize,

    // tables used for chooser (ch) implementation    
    sha256_base7_rot6_table: Arc<LookupTableApplication<E>>,
    sha256_base7_rot3_extr10_table: Arc<LookupTableApplication<E>>,
    sha256_ch_normalization_table: Arc<LookupTableApplication<E>>,
    // mod 2 normalization_table (and similar for maj - only base used will be diffent)
    sha256_ch_xor_table: Arc<LookupTableApplication<E>>,

    // tables used for majority (maj) implementation
    sha256_base4_rot2_table: Arc<LookupTableApplication<E>>,
    sha256_base4_rot2_extr10_table: Option<Arc<LookupTableApplication<E>>>,
    sha256_maj_normalization_table: Arc<LookupTableApplication<E>>,
    sha256_maj_xor_table: Arc<LookupTableApplication<E>>,

    // tables used for message expansion (message sheduler, in other terms)
    sha256_base4_rot7_table: Arc<LookupTableApplication<E>>,
    // the special property of this table is that it operates on 10-but chunks
    // the third column is unused completely
    sha256_base4_widh10_table: Arc<LookupTableApplication<E>>,
    // for normalization we are going to use the same table as in majority function - as their bases (4) are the same!
    // we may implement R_3 and S_19 (see below) either with the help of tables, 
    // or with the help of specially crafted custom gadgets
    r3_strategy: Strategy,
    sha256_base4_shift3_table : Option<Arc<LookupTableApplication<E>>>,
    s19_strategy: Strategy,
    sha256_base4_rot9_table : Option<Arc<LookupTableApplication<E>>>,

    // constants 
    iv: [E::Fr; 8],
    round_constants: [E::Fr; 64],

    _marker: std::marker::PhantomData<E>,
}

const SHA256_GADGET_CHUNK_SIZE : usize = 11; 
const SHA256_REG_WIDTH : usize = 32;
const CH_BASE_DEFAULT_NUM_OF_CHUNKS : usize = 4; // 7^4 is fine
const MAJ_BASE_DEFAULT_NUM_OF_CHUNKS : usize = 6; // 4^6 is fine
const SHEDULER_BASE_DEFAULT_NUM_OF_CHUNKS : usize = 6; // 4^6 is STILL fine (nothing happaned from previous line of code)


impl<E: Engine> Sha256GadgetParams<E> {

    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, 

        majority_strategy: Strategy,
        r3_strategy: Strategy,
        s19_strategy: Strategy,

        ch_base_num_of_chunks: Option<usize>,
        maj_base_num_of_chunks: Option<usize>,
        sheduler_base_num_of_chunks: Option<usize>

    ) -> Result<Self> {

        let ch_base_num_of_chunks = ch_base_num_of_chunks.unwrap_or(CH_BASE_DEFAULT_NUM_OF_CHUNKS);
        let maj_base_num_of_chunks = maj_base_num_of_chunks.unwrap_or(MAJ_BASE_DEFAULT_NUM_OF_CHUNKS);
        let sheduler_base_num_of_chunks = sheduler_base_num_of_chunks.unwrap_or(SHEDULER_BASE_DEFAULT_NUM_OF_CHUNKS);
        
        let columns = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "sha256_base7_rot6_table";
        let sha256_base7_rot6_table = LookupTableApplication::new(
            name1,
            Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 6, 0, SHA256_CHOOSE_BASE, name1),
            columns.clone(),
            true
        );

        let name2 : &'static str = "sha256_base7_rot3_extr10_table";
        let sha256_base7_rot3_extr10_table = LookupTableApplication::new(
            name2,
            Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 3, SHA256_GADGET_CHUNK_SIZE-1, SHA256_CHOOSE_BASE, name2),
            columns.clone(),
            true
        );

        let name3 : &'static str = "sha256_base4_rot2_table";
        let sha256_base4_rot2_table = LookupTableApplication::new(
            name3,
            Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 2, 0, SHA256_MAJORITY_BASE, name3),
            columns.clone(),
            true
        );

        let sha256_base7_rot6_table = cs.add_table(sha256_base7_rot6_table)?;
        let sha256_base7_rot3_extr10_table = cs.add_table(sha256_base7_rot3_extr10_table)?;
        let sha256_base4_rot2_table  = cs.add_table(sha256_base4_rot2_table)?;

        let name4 : &'static str = "sha256_base4_rot2_extr10_table";
        let sha256_base4_rot2_extr10_table = match majority_strategy {
            Strategy::UseCustomGadgets => None,
            Strategy::UseTwoTables => {
                let sha256_base4_rot2_extr10_table = LookupTableApplication::new(
                    name4,
                    Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 2, SHA256_GADGET_CHUNK_SIZE-1, SHA256_MAJORITY_BASE, name4),
                    columns.clone(),
                    true
                );

                Some(cs.add_table(sha256_base4_rot2_extr10_table)?)
            }
        };

        let name5 : &'static str = "sha256_ch_normalization_table";
        let sha256_ch_normalization_table = LookupTableApplication::new(
            name5,
            Sha256ChooseTable::new(ch_base_num_of_chunks, name5),
            columns.clone(),
            true
        );

        let name6 : &'static str = "sha256_maj_normalization_table";
        let sha256_maj_normalization_table = LookupTableApplication::new(
            name6,
            Sha256MajorityTable::new(maj_base_num_of_chunks, name6),
            columns.clone(),
            true
        );

        let name7 : &'static str = "sha256_ch_xor_table";
        let sha256_ch_xor_table = LookupTableApplication::new(
            name7,
            Sha256NormalizationTable::new(SHA256_CHOOSE_BASE, ch_base_num_of_chunks, name7),
            columns.clone(),
            true
        );

        let name8 : &'static str = "sha256_maj_xor_table";
        let sha256_maj_xor_table = LookupTableApplication::new(
            name8,
            Sha256NormalizationTable::new(SHA256_MAJORITY_BASE, maj_base_num_of_chunks, name8),
            columns.clone(),
            true
        );

        let name9 : &'static str = "sha256_base4_rot7_table";
        let sha256_base4_rot7_table = LookupTableApplication::new(
            name9,
            Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 7, 0, SHA256_EXPANSION_BASE, name9),
            columns.clone(),
            true
        );
        
        let name10 : &'static str = "sha256_base4_widh10_table";
        let sha256_base4_widh10_table = LookupTableApplication::new(
            name10,
            Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE - 1, 0, 0, SHA256_EXPANSION_BASE, name10),
            columns.clone(),
            true
        );

        let sha256_ch_normalization_table = cs.add_table(sha256_ch_normalization_table)?;
        let sha256_maj_normalization_table = cs.add_table(sha256_maj_normalization_table)?;
        let sha256_ch_xor_table  = cs.add_table(sha256_ch_xor_table)?;
        let sha256_maj_xor_table  = cs.add_table(sha256_maj_xor_table)?;
        let sha256_base4_rot7_table = cs.add_table(sha256_base4_rot7_table)?;
        let sha256_base4_widh10_table = cs.add_table(sha256_base4_widh10_table)?;

        let name11 : &'static str = "sha256_base4_shift3_table";
        let sha256_base4_shift3_table = match r3_strategy {
            Strategy::UseCustomGadgets => None,
            Strategy::UseTwoTables => {
                let sha256_base4_shift3_table = LookupTableApplication::new(
                    name11,
                    Sha256SparseShiftTable::new(SHA256_GADGET_CHUNK_SIZE, 3, SHA256_EXPANSION_BASE, name11),
                    columns.clone(),
                    true
                );

                Some(cs.add_table(sha256_base4_shift3_table)?)
            }
        };

        let name12 : &'static str = "sha256_base4_rot9_table";
        let sha256_base4_rot9_table = match s19_strategy {
            Strategy::UseCustomGadgets=> None,
            Strategy::UseTwoTables => {
                let sha256_base4_rot9_table = LookupTableApplication::new(
                    name11,
                    Sha256SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 9, 0, SHA256_EXPANSION_BASE, name12),
                    columns.clone(),
                    true
                );

                Some(cs.add_table(sha256_base4_rot9_table)?)
            }
        };

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

        // Initialize array of round constants:
        // (first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311):
        let round_constants = [
            Self::u64_to_ff(0x428a2f98), Self::u64_to_ff(0x71374491), Self::u64_to_ff(0xb5c0fbcf), Self::u64_to_ff(0xe9b5dba5), 
            Self::u64_to_ff(0x3956c25b), Self::u64_to_ff(0x59f111f1), Self::u64_to_ff(0x923f82a4), Self::u64_to_ff(0xab1c5ed5),
            Self::u64_to_ff(0xd807aa98), Self::u64_to_ff(0x12835b01), Self::u64_to_ff(0x243185be), Self::u64_to_ff(0x550c7dc3), 
            Self::u64_to_ff(0x72be5d74), Self::u64_to_ff(0x80deb1fe), Self::u64_to_ff(0x9bdc06a7), Self::u64_to_ff(0xc19bf174),
            Self::u64_to_ff(0xe49b69c1), Self::u64_to_ff(0xefbe4786), Self::u64_to_ff(0x0fc19dc6), Self::u64_to_ff(0x240ca1cc), 
            Self::u64_to_ff(0x2de92c6f), Self::u64_to_ff(0x4a7484aa), Self::u64_to_ff(0x5cb0a9dc), Self::u64_to_ff(0x76f988da),
            Self::u64_to_ff(0x983e5152), Self::u64_to_ff(0xa831c66d), Self::u64_to_ff(0xb00327c8), Self::u64_to_ff(0xbf597fc7), 
            Self::u64_to_ff(0xc6e00bf3), Self::u64_to_ff(0xd5a79147), Self::u64_to_ff(0x06ca6351), Self::u64_to_ff(0x14292967),
            Self::u64_to_ff(0x27b70a85), Self::u64_to_ff(0x2e1b2138), Self::u64_to_ff(0x4d2c6dfc), Self::u64_to_ff(0x53380d13), 
            Self::u64_to_ff(0x650a7354), Self::u64_to_ff(0x766a0abb), Self::u64_to_ff(0x81c2c92e), Self::u64_to_ff(0x92722c85),
            Self::u64_to_ff(0xa2bfe8a1), Self::u64_to_ff(0xa81a664b), Self::u64_to_ff(0xc24b8b70), Self::u64_to_ff(0xc76c51a3), 
            Self::u64_to_ff(0xd192e819), Self::u64_to_ff(0xd6990624), Self::u64_to_ff(0xf40e3585), Self::u64_to_ff(0x106aa070),
            Self::u64_to_ff(0x19a4c116), Self::u64_to_ff(0x1e376c08), Self::u64_to_ff(0x2748774c), Self::u64_to_ff(0x34b0bcb5), 
            Self::u64_to_ff(0x391c0cb3), Self::u64_to_ff(0x4ed8aa4a), Self::u64_to_ff(0x5b9cca4f), Self::u64_to_ff(0x682e6ff3),
            Self::u64_to_ff(0x748f82ee), Self::u64_to_ff(0x78a5636f), Self::u64_to_ff(0x84c87814), Self::u64_to_ff(0x8cc70208), 
            Self::u64_to_ff(0x90befffa), Self::u64_to_ff(0xa4506ceb), Self::u64_to_ff(0xbef9a3f7), Self::u64_to_ff(0xc67178f2),
        ];

        Ok(Sha256GadgetParams {
            majority_strategy,
            r3_strategy,
            s19_strategy,

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

            iv,
            round_constants,

            _marker : std::marker::PhantomData,
        })
    }

    // here we assume that maximal overflow is not more than 4 bits
    // we return both the extracted 32bit value and of_l and of_h (both - two bits long)
    fn extract_32_from_constant(x: &E::Fr) -> (E::Fr, E::Fr, E::Fr) {
        let mut repr = x.into_repr();
        let mut of_l_repr = repr.clone();
        let mut of_h_repr = repr.clone();
        
        repr.as_mut()[0] &= (1 << 32) - 1; 
        let extracted = E::Fr::from_repr(repr).expect("should decode");

        of_l_repr.as_mut()[0] >>= 32;
        of_l_repr.as_mut()[0] &= 3;
        let of_l = E::Fr::from_repr(repr).expect("should decode");

        of_h_repr.as_mut()[0] >>= 34;
        let of_h = E::Fr::from_repr(repr).expect("should decode");

        (extracted, of_l, of_h)
    } 
        
    fn extact_32_from_overflowed_num<CS: ConstraintSystem<E>>(cs: &mut CS, var: &Num<E>) -> Result<Num<E>> {
        let res = match var {
            Num::Constant(x) => {
                Num::Constant(Self::extract_32_from_constant(x).0)
            },
            Num::Allocated(x) => {
                //create a_0, a_1, ..., a_15 = extracted.
                let mut vars = Vec::with_capacity(16);
                vars.push(AllocatedNum::alloc_zero(cs)?);

                for i in 0..16 {
                    let val = x.get_value().map(| elem | {
                        let mut repr = elem.into_repr();
                        repr.as_mut()[0] >>= 30 - 2 * i;
                        let extracted = E::Fr::from_repr(repr).expect("should decode");

                        extracted
                    });

                    vars.push(AllocatedNum::alloc(cs, || val.grab())?);
                }

                for i in 0..4 {
                    let x = [vars[4*i].get_variable(), vars[4*i+1].get_variable(), vars[4*i+2].get_variable(), vars[4*i+3].get_variable()];
                    cs.new_single_gate_for_trace_step(
                        &RangeCheck32ConstraintGate::default(), 
                        &[], 
                        &x, 
                        &[]
                    )?;
                }

                let (of_l_value, of_h_value) = match x.get_value() {
                    None => (None, None),
                    Some(elem) => {
                        let temp = Self::extract_32_from_constant(&elem);
                        (Some(temp.1), Some(temp.2))
                    },
                };

                let of_l_var = AllocatedNum::alloc(cs, || of_l_value.grab())?;
                let of_h_var = AllocatedNum::alloc(cs, || of_h_value.grab())?;
                let mut two = E::Fr::one();
                two.double();

                cs.begin_gates_batch_for_step()?;
                
                cs.new_gate_in_batch( 
                    &SparseRangeGate::new(1),
                    &[two.clone()],
                    &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
                    &[],
                )?;

                cs.new_gate_in_batch( 
                    &SparseRangeGate::new(2),
                    &[two.clone()],
                    &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
                    &[],
                )?;

                // the selectors in the main gate go in the following order:
                // [q_a, q_b, q_c, q_d, q_m, q_const, q_d_next]
                // we constraint the equation: q_a - 2^32 q_b - 2^34 q_c - q_d = 0;
                // so in our case: q_a = -1, q_b = 2^32; q_c = 2^34; q_d = 1; q_m = q_const = q_d_next = 0;

                let zero = E::Fr::zero();
                let one = E::Fr::one();
                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut temp32_repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
                temp32_repr.as_mut()[0] = 1 << 32;
                let coef32 = E::Fr::from_repr(temp32_repr).expect("should parse");

                let mut temp34_repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
                temp34_repr.as_mut()[0] = 1 << 34;
                let coef34 = E::Fr::from_repr(temp34_repr).expect("should parse");

                cs.new_gate_in_batch(
                    &CS::MainGate::default(),
                    &[minus_one, coef32, coef34, one, zero.clone(), zero.clone(), zero],
                    &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
                    &[],
                )?;

                cs.end_gates_batch_for_step()?;

                Num::Allocated(vars.pop().expect("top element exists"))
            }
        };

        Ok(res)
    }

    fn extact_32_from_tracked_num<CS: ConstraintSystem<E>>(cs: &mut CS, var: NumWithTracker<E>) -> Result<Num<E>> {
        let res = match var.overflow_tracker {
            OverflowTracker::NoOverflow => var.num,
            OverflowTracker::SignificantOverflow => unimplemented!(),
            _ => Self::extact_32_from_overflowed_num(cs, &var.num)?,
        };

        Ok(res)
    }

    // for given 11-bit number x, y|hb|lbb, where lbb - 2-bits, hb - 1bit and y 8-bit
    // (all are represented in sparse form)
    // returns the components of decomposition: y, hbb, lb
    fn unpack_chunk<CS>(cs: &mut CS, x: AllocatedNum<E>) -> Result<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)> 
    where CS: ConstraintSystem<E>
    {   
        unimplemented!();
    }
    

    fn converter_helper(n: u64, sparse_base: usize, rotation: usize, extraction: usize) -> E::Fr {
        
        let t = map_into_sparse_form(rotate_extract(n as usize, rotation, extraction), sparse_base);
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = t as u64;
        E::Fr::from_repr(repr).expect("should parse")
    }

    fn allocate_converted_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        var: &AllocatedNum<E>, 
        chunk_bitlen: usize, 
        chunk_num: usize, 
        sparse_base: usize,
        rotation: usize, 
        extraction: usize
    ) -> Result<AllocatedNum<E>> 
    {
        let new_val = var.get_value().map( |fr| {
            let repr = fr.into_repr();
            let n = (repr.as_ref()[0] >> (chunk_bitlen * chunk_num)) & ((1 << chunk_bitlen) - 1);
            Self::converter_helper(n, sparse_base, rotation, extraction)
        });

        AllocatedNum::alloc(cs, || new_val.grab())
    }

    pub fn query_table1<CS>(cs: &mut CS, table: &Arc<LookupTableApplication<E>>, key: &AllocatedNum<E>) -> Result<AllocatedNum<E>> 
    where CS: ConstraintSystem<E>
    {
        let res = match key.get_value() {
            None => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
            Some(val) => {
                let new_val = table.query(&[val])?[0];
                AllocatedNum::alloc(cs, || Ok(new_val))?
            },     
        };

        cs.begin_gates_batch_for_step()?;

        let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();
        let vars = [key.get_variable(), res.get_variable(), dummy, dummy];
        cs.allocate_variables_without_gate(
            &vars,
            &[]
        )?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        cs.end_gates_batch_for_step()?;

        Ok(res)
    }

    pub fn query_table2<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>, 
        key: &AllocatedNum<E>
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>)> 
    {
        let res = match key.get_value() {
            None => (
                AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?, 
                AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?
            ),
            Some(val) => {
                let new_vals = table.query(&[val])?;
                (
                    AllocatedNum::alloc(cs, || Ok(new_vals[0]))?,
                    AllocatedNum::alloc(cs, || Ok(new_vals[1]))?
                )
            },     
        };

        cs.begin_gates_batch_for_step()?;

        let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();
        let vars = [key.get_variable(), res.0.get_variable(), res.1.get_variable(), dummy];
        cs.allocate_variables_without_gate(
            &vars,
            &[]
        )?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        cs.end_gates_batch_for_step()?;
        Ok(res)
    }

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

    // returns closets upper integer to a / b
    fn round_up(a: usize, b : usize) -> usize {
        let additional_chunks : usize = if a % b > 0 {1} else {0};
        a/b + additional_chunks
    }

    fn convert_into_sparse_chooser_form<CS : ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        input: NumWithTracker<E>, 
    ) -> Result<SparseChValue<E>> 
    { 
        let var = match input.overflow_tracker {
            OverflowTracker::SignificantOverflow => unimplemented!(),
            OverflowTracker::SmallOverflow(_) => Self::extact_32_from_overflowed_num(cs, &input.num)?,
            _ => input.num,
        };
        
        match var {
            Num::Constant(x) => {
                let repr = x.into_repr();
                // NOTE : think, if it is safe for n to be overflowed
                let n = repr.as_ref()[0] & ((1 << 32) - 1); 
                
                let res = SparseChValue {
                    normal: Num::Constant(x),
                    sparse: Num::Constant(Self::converter_helper(n, SHA256_CHOOSE_BASE, 0, 0)),
                    rot6: Num::Constant(Self::converter_helper(n, SHA256_CHOOSE_BASE, 6, 0)),
                    rot11: Num::Constant(Self::converter_helper(n, SHA256_CHOOSE_BASE, 11, 0)),
                    rot25: Num::Constant(Self::converter_helper(n, SHA256_CHOOSE_BASE, 25, 0)),
                };

                return Ok(res)
            },
            Num::Allocated(var) => {
                
                // split our 32bit variable into 11-bit chunks:
                // there will be three chunks (low, mid, high) for 32bit number
                // note that, we can deal here with possible 1-bit overflow: (as 3 * 11 = 33)
                // in order to do this we allow extraction set to 10 for the table working with highest chunk
                
                let low = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
                let mid = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 1, 0, 0, 0)?;
                let high = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 2, 0, 0, SHA256_GADGET_CHUNK_SIZE - 1)?;

                let (sparse_low, sparse_low_rot6) = Self::query_table2(cs, &self.sha256_base7_rot6_table, &low)?;
                let (sparse_mid, _sparse_mid_rot6) = Self::query_table2(cs, &self.sha256_base7_rot6_table, &mid)?;
                let (sparse_high, sparse_high_rot3) = Self::query_table2(cs, &self.sha256_base7_rot3_extr10_table, &high)?;

                let full_normal = {
                    // compose full normal = low + 2^11 * mid + 2^22 * high
                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), Self::u64_exp_to_ff(1 << 11, 0), Self::u64_exp_to_ff(1 << 22, 0)],
                        &[low, mid, high],
                        &var,
                    )?;

                    var.clone()
                };

                let full_sparse = {
                    // full_sparse = low_sparse + 7^11 * mid_sparse + 7^22 * high_sparse
                    let sparse_full = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 0, SHA256_REG_WIDTH - 1
                    )?;

                    let limb_1_shift = Self::u64_exp_to_ff(7, 11);
                    let limb_2_shift = Self::u64_exp_to_ff(7, 22);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), limb_1_shift, limb_2_shift],
                        &[sparse_low.clone(), sparse_mid.clone(), sparse_high.clone()],
                        &sparse_full,
                    )?;

                    sparse_full
                };

                let full_sparse_rot6 = {
                    // full_sparse_rot6 = low_sparse_rot6 + 7^(11-6) * sparse_mid + 7^(22-6) * sparse_high
                    let full_sparse_rot6 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 6, SHA256_REG_WIDTH - 1
                    )?;

                    let rot6_limb_1_shift = Self::u64_exp_to_ff(7, 11-6);
                    let rot6_limb_2_shift = Self::u64_exp_to_ff(7, 22 - 6);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot6_limb_1_shift, rot6_limb_2_shift],
                        &[sparse_low_rot6, sparse_mid.clone(), sparse_high.clone()],
                        &full_sparse_rot6,
                    )?;

                    full_sparse_rot6
                };

                let full_sparse_rot11 = {
                    // full_sparse_rot11 = sparse_mid + 7^(22-11) * sparse_high + 7^(32-11) * sparse_low
                    let full_sparse_rot11 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 11, SHA256_REG_WIDTH - 1
                    )?;

                    let rot11_limb_0_shift = Self::u64_exp_to_ff(7, 32 - 11);
                    let rot11_limb_2_shift = Self::u64_exp_to_ff(7, 22 - 11);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot11_limb_0_shift, rot11_limb_2_shift],
                        &[sparse_mid, sparse_low.clone(), sparse_high.clone()],
                        &full_sparse_rot11,
                    )?;

                    full_sparse_rot11
                };

                let full_sparse_rot_25 = {
                    // full_sparse_rot25 = sparse_high_rot3 + 7^(32-25) * sparse_low + 7^(32-25+11) * sparse_mid
                    let full_sparse_rot25 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 25, SHA256_REG_WIDTH - 1
                    )?;

                    let rot11_limb_0_shift = Self::u64_exp_to_ff(7, 32 - 25);
                    let rot11_limb_2_shift = Self::u64_exp_to_ff(7, 32 - 25 + 11);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot11_limb_0_shift, rot11_limb_2_shift],
                        &[sparse_high_rot3, sparse_low, sparse_high],
                        &full_sparse_rot25,
                    )?;

                    full_sparse_rot25
                };

                let res = SparseChValue{
                    normal: Num::Allocated(full_normal),
                    sparse: Num::Allocated(full_sparse),
                    rot6: Num::Allocated(full_sparse_rot6),
                    rot11: Num::Allocated(full_sparse_rot11),
                    rot25: Num::Allocated(full_sparse_rot_25),
                };
                return Ok(res);
            }
        }
    }

    // IMPORTANT NOTE:
    // there is a small difference between conversion into sparse chooser form and ... majority form functions 
    // more precisely, we are using 2 different tables in the first case: rot6 table for low and mid chunks and rot3 - for upper one
    // this allows to embed handling of 1-bit overflow into the table itself without additional overflow check (as called above)
    // this works as following: we split our number into  3 11-bit chunks, hence there 33 bits overall
    // however, our upper table for chooser has nontrivial extraction: we forget about the top-most bit of highest chunk, 
    // so our ombined full result will be of length 11 + 11 + 10 = 32, as required
    // NB:
    // 1) this way, we may handle only potential one-bit overflows, for the case of 2-bit overflows and more traditional 
    // approaches are required (as used inside extract_32_from_overflowed_num function)
    // 2) we can use the same approach inside the "conversion into sparse majority form" function - or. in other words, 
    // create two tables instead of one: both will be base4_rot2, but the second one will also containt non-trivial extraction 
    // which forgets about the highest bit of 11-bit chunks. Sometimes, creation of additional goes for free (e.g. in current 
    // implementation, we do not have any penalty in prover's\verifier's workload with the introduction of new table as long as 
    // there total number is less than closest power of 2). The choice of strategy: either work with two tables or work only with
    // base4_rot_2 and ALWAYS do overflow_check (even if we are sure, that we have only one bit of overflow) is handled
    // by MAJORITY_CONVERSION_STRATEGY flag

    fn convert_into_sparse_majority_form<CS : ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        input: NumWithTracker<E>, 
    ) -> Result<SparseMajValue<E>> 
    {      
        let var = match (input.overflow_tracker, self.majority_strategy)  {
            (OverflowTracker::SignificantOverflow, _) => unimplemented!(),
            (OverflowTracker::SmallOverflow(_), _) | (OverflowTracker::OneBitOverflow, Strategy::UseCustomGadgets) => {
                Self::extact_32_from_overflowed_num(cs, &input.num)?
            },
            (_, _) => input.num,
        };

        match var {
            Num::Constant(x) => {
                let repr = x.into_repr();
                // NOTE : think, if it is safe for n to be overflowed
                let n = repr.as_ref()[0] & ((1 << 32) - 1); 
                
                let res = SparseMajValue {
                    normal: Num::Constant(x),
                    sparse: Num::Constant(Self::converter_helper(n, SHA256_MAJORITY_BASE, 0, 0)),
                    rot2: Num::Constant(Self::converter_helper(n, SHA256_MAJORITY_BASE, 2, 0)),
                    rot13: Num::Constant(Self::converter_helper(n, SHA256_MAJORITY_BASE, 13, 0)),
                    rot22: Num::Constant(Self::converter_helper(n, SHA256_MAJORITY_BASE, 22, 0)),
                };

                return Ok(res)
            },
            Num::Allocated(var) => {
                
                // split our 32bit variable into 11-bit chunks:
                // there will be three chunks (low, mid, high) for 32bit number
                // note that, we can deal here with possible 1-bit overflow: (as 3 * 11 = 33)
                // in order to do this we allow extraction set to 10 for the table working with highest chunk
                
                let low = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
                let mid = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 1, 0, 0, 0)?;
                let high = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 2, 0, 0, SHA256_GADGET_CHUNK_SIZE - 1)?;

                let (sparse_low, sparse_low_rot2) = Self::query_table2(cs, &self.sha256_base4_rot2_table, &low)?;
                let (sparse_mid, sparse_mid_rot2) = Self::query_table2(cs, &self.sha256_base4_rot2_table, &mid)?;
                let high_chunk_table = match self.majority_strategy {
                    Strategy::UseTwoTables => self.sha256_base4_rot2_extr10_table.as_ref().unwrap(),
                    Strategy::UseCustomGadgets => &self.sha256_base4_rot2_table,
                };
                let (sparse_high, _sparse_high_rot2) = Self::query_table2(cs, high_chunk_table, &high)?;

                let full_normal = {
                    // compose full normal = low + 2^11 * mid + 2^22 * high
                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), Self::u64_exp_to_ff(1 << 11, 0), Self::u64_exp_to_ff(1 << 22, 0)],
                        &[low, mid, high],
                        &var,
                    )?;

                    var.clone()
                };

                let full_sparse = {
                    // full_sparse = low_sparse + 4^11 * mid_sparse + 4^22 * high_sparse
                    let sparse_full = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_MAJORITY_BASE, 0, SHA256_REG_WIDTH - 1
                    )?;

                    let limb_1_shift = Self::u64_exp_to_ff(4, 11);
                    let limb_2_shift = Self::u64_exp_to_ff(4, 22);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), limb_1_shift, limb_2_shift],
                        &[sparse_low.clone(), sparse_mid.clone(), sparse_high.clone()],
                        &sparse_full,
                    )?;

                    sparse_full
                };

                let full_sparse_rot2 = {
                    // full_sparse_rot6 = low_sparse_rot2 + 4^(11-2) * sparse_mid + 4^(22-2) * sparse_high
                    let full_sparse_rot2 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 2, SHA256_REG_WIDTH - 1
                    )?;

                    let rot2_limb_1_shift = Self::u64_exp_to_ff(4, 11-2);
                    let rot2_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 6);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot2_limb_1_shift, rot2_limb_2_shift],
                        &[sparse_low_rot2, sparse_mid.clone(), sparse_high.clone()],
                        &full_sparse_rot2,
                    )?;

                    full_sparse_rot2
                };

                let full_sparse_rot13 = {
                    // full_sparse_rot13 = sparse_mid_rot2 + 4^(22-11-2) * sparse_high + 4^(32-11-2) * sparse_low
                    let full_sparse_rot13 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 13, SHA256_REG_WIDTH - 1
                    )?;

                    let rot13_limb_0_shift = Self::u64_exp_to_ff(4, 32 - 2 - 11);
                    let rot13_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 2 - 11);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot13_limb_0_shift, rot13_limb_2_shift],
                        &[sparse_mid_rot2, sparse_low.clone(), sparse_high.clone()],
                        &full_sparse_rot13,
                    )?;

                    full_sparse_rot13
                };

                let full_sparse_rot_22 = {
                    // full_sparse_rot22 = sparse_high + 4^(32 - 22) * sparse_low + 4^(32 - 22 + 11) * sparse_mid
                    let full_sparse_rot22 = Self::allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 22, SHA256_REG_WIDTH - 1
                    )?;

                    let rot22_limb_0_shift = Self::u64_exp_to_ff(4, 32 - 22);
                    let rot22_limb_1_shift = Self::u64_exp_to_ff(4, 32 - 22 + 11);

                    AllocatedNum::ternary_lc_eq(
                        cs, 
                        &[E::Fr::one(), rot22_limb_0_shift, rot22_limb_1_shift],
                        &[sparse_high, sparse_low, sparse_mid],
                        &full_sparse_rot22,
                    )?;

                    full_sparse_rot22
                };

                let res = SparseMajValue{
                    normal: Num::Allocated(full_normal),
                    sparse: Num::Allocated(full_sparse),
                    rot2: Num::Allocated(full_sparse_rot2),
                    rot13: Num::Allocated(full_sparse_rot13),
                    rot22: Num::Allocated(full_sparse_rot_22),
                };
                return Ok(res);
            }
        }
    }

    // this function does the following: 
    // given any x = \sum_{i=0}^{n} x_i * base^i and well-defined mapping f: [0; base-1] -> [0; 1]
    // (among possible variants for f are "parity": f(k) = k mod 2, choose_function or majority_function:
    // for the description of the latter two refer to "tables" module)
    // return the "normalized" variable z = \sum_{i=0}^{n} f(x_i) 2^i
    //
    // the problem with table approach is actually the following:
    // we are unable to create long table holding all possible values of x in the range [0; base^n - 1] (granting that n is fixed)
    // the reason is that we do not want our tables to be EXTREMELY large, hence we require one additional step of workaround:
    // given adjustible parameter NUM_OF_CHUNKS we split our x in the linear combination of [ n / NUM_OF_CHUNKS] summands y_i,
    // each of which itself consists of no more than NUM_OF_CHUNKS summands
    //
    // in other words, we have:
    // x = \sum_{j=0}^{[n / NUM_OF_CHUNKS]} y_j * base^{j * NUM_OF_CHUNKS},
    // where y_j = \sum_{i=0}^{NUM_CHUNKS - 1} x_{j * NUM_OF_CHUNKS + x_i} * base^{j}
    // each such y_j is in smaller range [0; base^NUM_CHUNKS-1]
    // and for each such y_j we may apply the corresponding (and realtively small) normalization table and get
    // z_j = \sum_{i=0}^{NUM_CHUNKS} f(x_{j * NUM_OF_CHUNKS + x_i}) 2^j
    // the final z is then constructed as a linear conbination of {z_j} with simple weigt coefficients 
    // (in order for each z_j to be placed in an appropriate position in the bit representation of final result z)
    //
    // note, that for each possible pair of normalization transformation f(x) and base,
    // the parameter NUM_OF_CHUNKS may be determined separately
    // 
    // e.g. in reference implementation Barretenberg a = NUM_OF_CHUNKS = 4 for base = 7 and b = NUM_OF_CHUNKS = 6 for base = 4
    // IMHO, the motivation for such choice of parameters is the following:
    // in any case we would use sparse_rotate_extract tables with 11-bit chunks (and hence of size c = 2^11)
    // parameters a and b are chosen in a way, so that table sizes for normalization transforms of sizes 7^a and 4^b
    // approximately have the same order of magnitude as c, so that all used tables will be of relatively the same size
    // it is obvious, that following this logic, a = 4 and b = 6 (or may be 5(!)) are best possible choices
    //
    // in any case we do not want to be two strict here, and allow NUM_OF_CHUNKS for bases 7 and 4
    // to be specified as constructor parameters for Sha256Gadget gadget

    fn normalize<CS: ConstraintSystem<E>, F: Fn(E::Fr) -> E::Fr>(
        cs: &mut CS, 
        input: &Num<E>, 
        table: &Arc<LookupTableApplication<E>>, 
        converter_func: F,
        base: usize, 
        num_chunks: usize
    ) -> Result<Num<E>>
    {
        match input {
            Num::Constant(x) => {
                let output = converter_func(x.clone());
                return Ok(Num::Constant(output));
            }
            Num::Allocated(x) => {
                // split and slice!
                let num_slices = Self::round_up(SHA256_GADGET_CHUNK_SIZE, num_chunks);
                let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                let mut output_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                let input_slice_modulus = pow(base, num_chunks);

                match x.get_value() {
                    None => {
                        for _i in 0..num_slices {
                            let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
                            input_slices.push(tmp);
                        }
                    },
                    Some(f) => {
                        // here we have to operate on row biguint number
                        let mut big_f = BigUint::default();
                        let f_repr = f.clone().into_repr();
                        for n in f_repr.as_ref().iter().rev() {
                            big_f <<= 64;
                            big_f += *n;
                        } 

                        for _i in 0..num_slices {
                            let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
                            let new_val = Self::u64_exp_to_ff(remainder, 0);
                            big_f /= input_slice_modulus;
                            let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
                            input_slices.push(tmp);
                        }
                    }
                }

                for i in 0..num_slices {
                    let tmp = Self::query_table1(cs, table, &input_slices[i])?;
                    output_slices.push(tmp);
                }

                let output = AllocatedNum::alloc(cs, || x.get_value().map(| fr | converter_func(fr)).grab())?;
                let input_base = Self::u64_exp_to_ff(input_slice_modulus as u64, 0);
                let output_base = Self::u64_exp_to_ff(2, num_chunks as u64);

                AllocatedNum::long_weighted_sum_eq(cs, &input_slices[..], &input_base, x)?;
                AllocatedNum::long_weighted_sum_eq(cs, &output_slices[..], &output_base, &output)?;

                return Ok(Num::Allocated(output));
            }
        }
    }

    fn choose<CS>(&self, cs: &mut CS, e: SparseChValue<E>, f: SparseChValue<E>, g: SparseChValue<E>) -> Result<NumWithTracker<E>>
    where CS: ConstraintSystem<E>
    {
        let mut two = E::Fr::one();
        two.double();
        let mut three = two.clone();
        three.add_assign(&E::Fr::one());
        
        let t0 = Num::lc(cs, &[E::Fr::one(), two, three], &[e.sparse, f.sparse, g.sparse])?; 
        let t1 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[e.rot6, e.rot11, e.rot25])?;

        let r0 = Self::normalize(
            cs, &t0, 
            &self.sha256_ch_normalization_table,
            ch_map_normalizer,  
            SHA256_CHOOSE_BASE, 
            self.ch_base_num_of_chunks
        )?;
        let r1 = Self::normalize(
            cs, &t1, 
            &self.sha256_ch_xor_table, 
            ch_xor_normalizer,
            SHA256_CHOOSE_BASE, 
            self.ch_base_num_of_chunks
        )?;

        let r0 : NumWithTracker<E> = r0.into();
       
        r0.add(cs, &r1)
    }

    fn majority<CS>(&self, cs: &mut CS, a: SparseMajValue<E>, b: SparseMajValue<E>, c: SparseMajValue<E>) -> Result<NumWithTracker<E>>
    where CS: ConstraintSystem<E>
    {   
        let t0 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[a.sparse, b.sparse, c.sparse])?; 
        let t1 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[a.rot2, a.rot13, a.rot22])?;

        let r0 = Self::normalize(
            cs, &t0, 
            &self.sha256_maj_normalization_table,
            maj_map_normalizer, 
            SHA256_MAJORITY_BASE, 
            self.maj_base_num_of_chunks,
        )?;
        let r1 = Self::normalize(
            cs, &t1, 
            &self.sha256_maj_xor_table, 
            maj_xor_normalizer,
            SHA256_MAJORITY_BASE, 
            self.maj_base_num_of_chunks
        )?;

        let r0 : NumWithTracker<E> = r0.into();
       
        r0.add(cs, &r1)
    }

    // one round of inner SHA256 cycle 
    // the hash for single block of 512 chunks requires 64 such cycles
    fn sha256_inner_block<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS, 
        regs: Sha256Registers<E>, 
        inputs: &[Num<E>], 
        round_constants: &[E::Fr],
    ) -> Result<Sha256Registers<E>>
    {
        let mut a = self.convert_into_sparse_majority_form(cs, regs.a.clone())?;
        let mut b = self.convert_into_sparse_majority_form(cs, regs.b.clone())?;
        let mut c = self.convert_into_sparse_majority_form(cs, regs.c.clone())?;
        let mut d = self.convert_into_sparse_majority_form(cs, regs.d.clone())?;
        let mut e = self.convert_into_sparse_chooser_form(cs, regs.e.clone())?;
        let mut f = self.convert_into_sparse_chooser_form(cs, regs.f.clone())?;
        let mut g = self.convert_into_sparse_chooser_form(cs, regs.g.clone())?;
        let mut h = self.convert_into_sparse_chooser_form(cs, regs.h.clone())?;

        for i in 0..64 {
            let ch = self.choose(cs, e.clone(), f.clone(), g.clone())?;
            let maj = self.majority(cs, a.clone(), b.clone(), c.clone())?;
            
            // temp1 will be overflowed two much (4 bits in total), so we are going to reduce it in any case
            // TODO: may be it is possible to optimize it somehow?
            let rc = Num::Constant(round_constants[i]);
            let temp1_unreduced = Num::sum(cs, &[h.normal, ch.num, inputs[i].clone(), rc])?;
            let temp1 = Self::extact_32_from_overflowed_num(cs, &temp1_unreduced)?;

            h = g;
            g = f;
            f = e;
            let mut temp2 : NumWithTracker<E> = d.normal.into();
            temp2 = temp2.add(cs, &temp1)?;
            e = self.convert_into_sparse_chooser_form(cs, temp2)?;
            d = c;
            c = b;
            b = a;
            let temp3 = maj.add(cs, &temp1)?;
            a =self. convert_into_sparse_majority_form(cs, temp3)?;
        }

        let regs = Sha256Registers {
            a: regs.a.add(cs, &a.normal)?,
            b: regs.b.add(cs, &b.normal)?,
            c: regs.c.add(cs, &c.normal)?,
            d: regs.d.add(cs, &d.normal)?,
            e: regs.e.add(cs, &e.normal)?,
            f: regs.f.add(cs, &f.normal)?,
            g: regs.g.add(cs, &g.normal)?,
            h: regs.h.add(cs, &h.normal)?,
        };
        
        Ok(regs)
    }

    // computes sigma_0(x) = S_7(x) ^ S_18(x) ^ R_3(x)
    // S_i and R_j are defined in the comments related to "message_expansion" function
    // we assume that there is no oveflow in input argument num
    // fn sigma_0<CS: ConstraintSystem<E>>(&self, cs: &mut CS, num: Num<E>) -> Result<Num<E>>
    // {
    //     match num {
    //         Num::Constant(x) => {
    //             let repr = x.into_repr();
    //             // NOTE : think, if it is safe for n to be overflowed
    //             let n = repr.as_ref()[0];

    //             let s7 = rotate_extract(n, 7, 0);
    //             let s18 = rotate_extract(n, 18, 0);
    //             let r3 = shift(n, 3);
    //             let res =  Self::u64_to_ff(s7 ^ s18 ^ r3);

    //             return Ok(Num::Constant(res));
    //         }
    //         Num::Allocated(var) => {
    //             // split our 32bit variable into 11-bit chunks:
    //             // there will be three chunks (low, mid, high) for 32bit number
    //             let low = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
    //             let mid = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 1, 0, 0, 0)?;
    //             let high = Self::allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 2, 0, 0, 0)?;

    //             let (sparse_low, sparse_low_rot7) = Self::query_table2(cs, &self.sha256_base4_rot7_table, &low)?;
    //             let (sparse_mid, sparse_mid_rot7) = Self::query_table2(cs, &self.sha256_base4_rot7_table, &mid)?;
    //             let (sparse_high, sparse_high_rot7) = Self::query_table2(cs, &self.sha256_base4_rot7_table, &high)?;

    //             let full_normal = {
    //                 // compose full normal = low + 2^11 * mid + 2^22 * high
    //                 let ful_normal = AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), Self::u64_exp_to_ff(1 << 11, 0), Self::u64_exp_to_ff(1 << 22, 0)],
    //                     &[low, mid, high],
    //                     &var,
    //                 )?;
    //                 full_normal
    //             };

    //             let full_sparse_rot7 = {
    //                 // full_sparse_rot7 = low_sparse_rot7 + 4^(11-7) * sparse_mid + 4^(22-7) * sparse_high
    //                 let full_sparse_rot7 = Self::allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 7, 0
    //                 )?;

    //                 let rot7_limb_1_shift = Self::u64_exp_to_ff(4, 11 - 7);
    //                 let rot7_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 7);

    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), rot7_limb_1_shift, rot7_limb_2_shift],
    //                     &[sparse_low_rot7, sparse_mid.clone(), sparse_high.clone()],
    //                     &full_sparse_rot7,
    //                 )?;

    //                 full_sparse_rot7
    //             };

    //             let full_sparse_rot18 = {
    //                 // full_sparse_rot18 = sparse_mid_rot7 + 4^(22-11-7) * sparse_high + 4^(32-11-7) * sparse_low
    //                 let full_sparse_rot18 = Self::allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 13, 0
    //                 )?;

    //                 let rot18_limb_0_shift = Self::u64_exp_to_ff(4, 32 - 7 - 11);
    //                 let rot18_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 7 - 11);

    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), rot18_limb_0_shift, rot18_limb_2_shift],
    //                     &[sparse_mid_rot7, sparse_low.clone(), sparse_high.clone()],
    //                     &full_sparse_rot18,
    //                 )?;

    //                 full_sparse_rot18
    //             };

    //             let full_sparse_shift_3 = {
    //                 // we are going to implement R_3(x) (in sparse form) without use of tables
    //                 // the algorithm is the following: assuming our sparse base is 4 
    //                 // and we already have at our disposal the sparse representation of x = /sum x_i 4^i
    //                 // R_3(x) in sparse form will be y = /sum x_{i+3} 4^i, hence
    //                 // x = y * 4^3 + x_0 + x_1 * 4 + x_2 * 16;
    //                 // we rearrange it as following: 
    //                 // u = x_0 + x_1 * 4, x = y + u + x_2 * 16
    //                 // where u may take only the following possible values: [0, 1, 4, 5]
    //                 // and x_2 is boolean
    //                 // Note: we should also check that y is at most eight bit long!

    //                 let mut vars = Vec::with_capacity(16);
    //             vars.push(AllocatedNum::alloc_zero(cs)?);

    //             for i in 0..16 {
    //                 let val = x.get_value().map(| elem | {
    //                     let mut repr = elem.into_repr();
    //                     repr.as_mut()[0] >>= 30 - 2 * i;
    //                     let extracted = E::Fr::from_repr(repr).expect("should decode");

    //                     extracted
    //                 });

    //                 vars.push(AllocatedNum::alloc(cs, || val.grab())?);
    //             }

    //             for i in 0..4 {
    //                 let x = [vars[4*i].get_variable(), vars[4*i+1].get_variable(), vars[4*i+2].get_variable(), vars[4*i+3].get_variable()];
    //                 cs.new_single_gate_for_trace_step(
    //                     &RangeCheck32ConstraintGate::default(), 
    //                     &[], 
    //                     &x, 
    //                     &[]
    //                 )?;
    //             }

    //             let (of_l_value, of_h_value) = match x.get_value() {
    //                 None => (None, None),
    //                 Some(elem) => {
    //                     let temp = Self::extract_32_from_constant(&elem);
    //                     (Some(temp.1), Some(temp.2))
    //                 },
    //             };

    //             let of_l_var = AllocatedNum::alloc(cs, || of_l_value.grab())?;
    //             let of_h_var = AllocatedNum::alloc(cs, || of_h_value.grab())?;
    //             let mut two = E::Fr::one();
    //             two.double();

    //             cs.begin_gates_batch_for_step()?;
                
    //             cs.new_gate_in_batch( 
    //                 &SparseRangeGate::new(1),
    //                 &[two.clone()],
    //                 &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
    //                 &[],
    //             )?;

    //             cs.new_gate_in_batch( 
    //                 &SparseRangeGate::new(2),
    //                 &[two.clone()],
    //                 &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
    //                 &[],
    //             )?;

    //             // the selectors in the main gate go in the following order:
    //             // [q_a, q_b, q_c, q_d, q_m, q_const, q_d_next]
    //             // we constraint the equation: q_a - 2^32 q_b - 2^34 q_c - q_d = 0;
    //             // so in our case: q_a = -1, q_b = 2^32; q_c = 2^34; q_d = 1; q_m = q_const = q_d_next = 0;

    //             let zero = E::Fr::zero();
    //             let one = E::Fr::one();
    //             let mut minus_one = E::Fr::one();
    //             minus_one.negate();

    //             let mut temp32_repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
    //             temp32_repr.as_mut()[0] = 1 << 32;
    //             let coef32 = E::Fr::from_repr(temp32_repr).expect("should parse");

    //             let mut temp34_repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
    //             temp34_repr.as_mut()[0] = 1 << 34;
    //             let coef34 = E::Fr::from_repr(temp34_repr).expect("should parse");

    //             cs.new_gate_in_batch(
    //                 &CS::MainGate::default(),
    //                 &[minus_one, coef32, coef34, one, zero.clone(), zero.clone(), zero],
    //                 &[x.get_variable(), of_l_var.get_variable(), of_h_var.get_variable(), vars[15].get_variable()],
    //                 &[],
    //             )?;

    //             cs.end_gates_batch_for_step()?;

    //             Num::Allocated(vars.pop().expect("top element exists"))
                    
    //                 // full_sparse_shift3 = sparse_low_shift3 + 4^(11 - 3) * sparse_mid + 4^(22 - 3) * sparse_high
    //                 let full_sparse_shift3 = Self::allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_CHOOSE_BASE, 22, SHA256_REG_WIDTH - 1
    //                 )?;

    //                 let rot22_limb_0_shift = Self::u64_exp_to_ff(4, 32 - 22);
    //                 let rot22_limb_1_shift = Self::u64_exp_to_ff(4, 32 - 22 + 11);

    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), rot22_limb_0_shift, rot22_limb_1_shift],
    //                     &[sparse_high, sparse_low, sparse_mid],
    //                     &full_sparse_rot22,
    //                 )?;

    //                 full_sparse_rot22
    //             };

    //             let res = SparseMajValue{
    //                 normal: Num::Allocated(full_normal),
    //                 sparse: Num::Allocated(full_sparse),
    //                 rot2: Num::Allocated(full_sparse_rot2),
    //                 rot13: Num::Allocated(full_sparse_rot13),
    //                 rot22: Num::Allocated(full_sparse_rot_22),
    //             };
    //             return Ok(res);
    // }

    fn sigma_0<CS: ConstraintSystem<E>>(&self, cs: &mut CS, num: &Num<E>) -> Result<Num<E>>
    {
        unimplemented!();
    }

    fn sigma_1<CS: ConstraintSystem<E>>(&self, cs: &mut CS, num: &Num<E>) -> Result<Num<E>>
    {
        unimplemented!();
    }

    // Expanded message blocks W0, W1, ..., W63 are computed from [M0, ..., M15] as follows via the
    // SHA-256 message schedule:
    // Wj = Mj for j = [0; 15]
    // For j = 16 to 63:
    //      Wj = sigma_1(W_{j-2}) + W_{j-7} + sigma_0(W_{j-15}) + W_{j-16}
    // where 
    //      sigma_0(x) = S_7(x) ^ S_18(x) ^ R_3(x)
    //      sigma_1(x) = S_17(x) ^ S_19(x) ^ R_10(x)
    // here S_n - is right circular n-bit rotation
    // and R_n - right n-nit shift
    fn message_expansion<CS: ConstraintSystem<E>>(&self, cs: &mut CS, message: &[Num<E>]) -> Result<Vec<Num<E>>>
    {
        assert_eq!(message.len(), 16);
        let mut res = Vec::with_capacity(64);

        for i in 0..16 {
            res.push(message[i].clone());
        }

        for j in 16..64 {
            let tmp1 = self.sigma_1(cs, &res[j - 2])?;
            let tmp2 = self.sigma_0(cs, &res[j - 15])?;

            let mut tmp3 = Num::sum(cs, &[tmp1, res[j-7].clone(), tmp2, res[j-16].clone()])?;
            tmp3 = Self::extact_32_from_overflowed_num(cs, &tmp3)?;
            res.push(tmp3);
        }

        Ok(res)
    }

    // finally! the only one exported function
    pub fn sha256<CS: ConstraintSystem<E>>(&self, cs: &mut CS, message: &[Num<E>]) -> Result<[Num<E>; 8]>
    {    
        // we assume that input is already well-padded
        assert!(message.len() % 16 == 0);
        
        let mut regs = Sha256Registers {
            a: Num::Constant(self.iv[0].clone()).into(),
            b: Num::Constant(self.iv[1].clone()).into(),
            c: Num::Constant(self.iv[2].clone()).into(),
            d: Num::Constant(self.iv[3].clone()).into(),
            e: Num::Constant(self.iv[4].clone()).into(),
            f: Num::Constant(self.iv[5].clone()).into(),
            g: Num::Constant(self.iv[6].clone()).into(),
            h: Num::Constant(self.iv[7].clone()).into(),
        };

        for block in message.chunks(16) {
            let expanded_block = self.message_expansion(cs, block)?;
            regs = self.sha256_inner_block(cs, regs, &expanded_block[..], &self.round_constants)?;
        }

        let res = [
            Self::extact_32_from_tracked_num(cs, regs.a)?,
            Self::extact_32_from_tracked_num(cs, regs.b)?,
            Self::extact_32_from_tracked_num(cs, regs.c)?,
            Self::extact_32_from_tracked_num(cs, regs.d)?,
            Self::extact_32_from_tracked_num(cs, regs.e)?,
            Self::extact_32_from_tracked_num(cs, regs.f)?,
            Self::extact_32_from_tracked_num(cs, regs.g)?,
            Self::extact_32_from_tracked_num(cs, regs.h)?,
        ];
        Ok(res)
    }
}
   






