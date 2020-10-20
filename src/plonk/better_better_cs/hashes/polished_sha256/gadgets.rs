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
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};

use super::tables::*;
use super::utils::*;

use std::sync::Arc;
use std::ops::Add;
use std::iter;
use std::cmp::Ordering;
use std::cmp;

type Result<T> = std::result::Result<T, SynthesisError>;


const SHA256_GADGET_CHUNK_SIZE : usize = 11; 
const SHA256_REG_WIDTH : usize = 32;
const CH_DEFAULT_NUM_OF_CHUNKS : usize = 5; // 7^4 is fine
const MAJ_AND_SHEDULER_DEFAULT_NUM_OF_CHUNKS : usize = 8; // 4^6 is fine
const BINARY_BASE : u64 = 2;
const DEFAULT_RANGE_TABLE_WIDTH : usize = 16;


// helper struct for tracking how far current value from being in 32-bit range
// our gadget is suited to handle at most 4-bit overflows itself
#[derive(Copy, Clone, Eq)]
pub enum OverflowTracker {
    NoOverflow,
    OneBitOverflow,
    SignificantOverflow(u64), //overflowed by 2 or more bits    
}

impl OverflowTracker {
    fn is_overflowed(&self) -> bool {
        let res = match self {
            OverflowTracker::NoOverflow => false,
            _ => true,
        };
        res
    }

    fn get_template(&self) -> u64 {
        let offset = match self {
            OverflowTracker::NoOverflow => SHA256_REG_WIDTH as u64,
            OverflowTracker::OneBitOverflow => 1 + SHA256_REG_WIDTH as u64,
            OverflowTracker::SignificantOverflow(n) => *n + (SHA256_REG_WIDTH as u64),
        };
        let res : u64 = (1u64 << offset) - 1;
        res
    }

    fn num_bits(num: u64) -> u64 {
        assert!(num > 0);

        let mut pow = 0;
        while (1 << pow) <= num {
            pow += 1;
        }
        pow
    }

    fn new_from_template(template: u64) -> Self {
        let val = Self::num_bits(template) - (SHA256_REG_WIDTH as u64);
        val.into()
    }
}

impl Ord for OverflowTracker {
    fn cmp(&self, other: &Self) -> Ordering {
        let a : u64 = self.clone().into();
        let b : u64 = other.clone().into();
        a.cmp(&b)
    }
}

impl PartialOrd for OverflowTracker {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for OverflowTracker {
    fn eq(&self, other: &Self) -> bool {
        let a : u64 = self.clone().into();
        let b : u64 = other.clone().into();
        a == b
    }
}

impl Into<u64> for OverflowTracker {
    fn into(self: Self) -> u64 {
        match self {
            OverflowTracker::NoOverflow => 0,
            OverflowTracker::OneBitOverflow => 1,
            OverflowTracker::SignificantOverflow(x) => x,
        }
    }
}

impl From<u64> for OverflowTracker {
    fn from(n: u64) -> Self {
        match n {
            0 => OverflowTracker::NoOverflow,
            1 => OverflowTracker::OneBitOverflow,
            _ => OverflowTracker::SignificantOverflow(n),
        }
    }
}

impl Add for OverflowTracker {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let a : u64 = self.into();
        let b : u64 = other.into();
        let new_of_tracker : OverflowTracker = (a + b).into();
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

    pub fn add_tracked<CS: ConstraintSystem<E>>(&self, cs: &mut CS, other: &NumWithTracker<E>) -> Result<Self> {
        let new_num = self.num.add(cs, &other.num)?;
        let new_tracker = match self.num.is_constant() && other.num.is_constant() {
            true => OverflowTracker::NoOverflow,
            false => cmp::max(self.overflow_tracker, other.overflow_tracker) + OverflowTracker::OneBitOverflow,
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
            (true, false, false) => OverflowTracker::SignificantOverflow(2),
            (false, _, _) =>  match self.overflow_tracker {
                OverflowTracker::NoOverflow => OverflowTracker::SignificantOverflow(2),
                _ => self.overflow_tracker + OverflowTracker::OneBitOverflow,
            },
        };

        Ok(NumWithTracker{
            num: new_num,
            overflow_tracker: new_tracker,
        })
    }
}


#[derive(Clone)]
pub struct SparseChValue<E: Engine> {
    normal: NumWithTracker<E>,
    sparse: Num<E>,
    // all rots are in sparse representation as well
    rot6: Num<E>,
    rot11: Num<E>,
    rot25: Num<E>,
}

#[derive(Clone)]
pub struct SparseMajValue<E: Engine> {
    normal: NumWithTracker<E>,
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


pub struct Sha256Gadget<E: Engine> {
    // is is possible to reduce the number of constraints even more by exploiting not only d_next,
    // but also c_prev
    use_c_prev : bool,

    // the purpose of these parameters is discussed before the "normalize" function
    ch_num_of_chunks: usize,
    // NOTE : actually the majority vand sheduler bases are the same (4), so there is no reason for their corresponding
    // number of chunks to be different
    maj_and_sheduler_num_of_chunks: usize,
   
    // tables used for chooser (ch) implementation    
    sha256_base7_rot6_table: Arc<LookupTableApplication<E>>,
    sha256_base7_rot3_extr10_table: Arc<LookupTableApplication<E>>,
    sha256_ch_normalization_table: Arc<LookupTableApplication<E>>,
   
    // tables used for majority (maj) implementation
    sha256_base4_rot2_table: Arc<LookupTableApplication<E>>,
    // the special property of this table is that it operates on 10-but chunks
    sha256_base4_rot2_width10_table: Arc<LookupTableApplication<E>>,
    sha256_maj_normalization_table: Arc<LookupTableApplication<E>>,

    // tables used for message expansion (message sheduler, in other terms)
    sha256_base4_rot7_table: Arc<LookupTableApplication<E>>,
    // for normalization we are going to use the same table as in majority function - as their bases (4) are the same!
    // we also implement R_3 and S_19 (see below) with the help of specially crafted addtional tables,
    // namely: Sha256ShedulerHelperTable
    sha256_sheduler_helper_table : Arc<LookupTableApplication<E>>,

    // there is an option to handle of range checks via globally defined range table
    // if there is no such table available, we are not going to create such a range table ourselves
    // instead we accomplish rabge checks via sha_specific sparse_rotate tables
    // in fact, there is not much benefit from using 16-bit range table than our inner 11-bit tables
    // but if we are given one as a gift. why not to exploit it?
    use_global_range_table: bool,
    global_range_table_width: usize,
    global_range_table: Option<Arc<LookupTableApplication<E>>>,
    max_of_width: usize,

    // constants 
    iv: [E::Fr; 8],
    round_constants: [E::Fr; 64],
}


impl<E: Engine> Sha256Gadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        ch_base_num_of_chunks: Option<usize>,
        maj_sheduler_base_num_of_chunks: Option<usize>,
        use_c_prev : bool,
        use_global_range_table: bool,
        global_range_table_width : usize,
        global_range_table_name: &str,
    ) -> Result<Self> {

        let ch_num_of_chunks = ch_base_num_of_chunks.unwrap_or(CH_DEFAULT_NUM_OF_CHUNKS);
        let maj_and_sheduler_num_of_chunks = maj_sheduler_base_num_of_chunks.unwrap_or(MAJ_AND_SHEDULER_DEFAULT_NUM_OF_CHUNKS);

        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "sha256_base7_rot6_table";
        let sha256_base7_rot6_table = LookupTableApplication::new(
            name1,
            SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 6, 0, SHA256_CHOOSE_BASE, name1),
            columns3.clone(),
            true
        );
        let sha256_base7_rot6_table = cs.add_table(sha256_base7_rot6_table)?;

        let name2 : &'static str = "sha256_base7_rot3_extr10_table";
        let sha256_base7_rot3_extr10_table = LookupTableApplication::new(
            name2,
            SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 3, SHA256_GADGET_CHUNK_SIZE-1, SHA256_CHOOSE_BASE, name2),
            columns3.clone(),
            true
        );
        let sha256_base7_rot3_extr10_table = cs.add_table(sha256_base7_rot3_extr10_table)?;

        let name3 : &'static str = "sha256_base4_rot2_table";
        let sha256_base4_rot2_table = LookupTableApplication::new(
            name3,
            SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 2, 0, SHA256_MAJORITY_SHEDULER_BASE, name3),
            columns3.clone(),
            true
        );
        let sha256_base4_rot2_table  = cs.add_table(sha256_base4_rot2_table)?;
        
        let name4 : &'static str = "sha256_base4_rot2_width10_table";
        let sha256_base4_rot2_width10_table = LookupTableApplication::new(
            name4,
            SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE - 1, 2, 0, SHA256_MAJORITY_SHEDULER_BASE, name4),
            columns3.clone(),
            true,
        );
        let sha256_base4_rot2_width10_table = cs.add_table(sha256_base4_rot2_width10_table)?;

        let xor_f = | x | { x & 1};
        let ch_f = | x | { ch_u64_normalizer(x) };
        let maj_f = | x | { maj_u64_normalizer(x) };
        
        let name5 : &'static str = "sha256_ch_normalization_table";
        let sha256_ch_normalization_table = LookupTableApplication::new(
            name5,
            MultiBaseNormalizationTable::new(ch_num_of_chunks, SHA256_CHOOSE_BASE, BINARY_BASE, BINARY_BASE, ch_f, xor_f, name5),
            columns3.clone(),
            true
        );
        let sha256_ch_normalization_table = cs.add_table(sha256_ch_normalization_table)?;

        let name6 : &'static str = "sha256_maj_normalization_table";
        let sha256_maj_normalization_table = LookupTableApplication::new(
            name6,
            MultiBaseNormalizationTable::new(
                maj_and_sheduler_num_of_chunks, SHA256_MAJORITY_SHEDULER_BASE, BINARY_BASE, BINARY_BASE, maj_f, xor_f, name6
            ),
            columns3.clone(),
            true
        );
        let sha256_maj_normalization_table = cs.add_table(sha256_maj_normalization_table)?;

        let name7 : &'static str = "sha256_base4_rot7_table";
        let sha256_base4_rot7_table = LookupTableApplication::new(
            name7,
            SparseRotateTable::new(SHA256_GADGET_CHUNK_SIZE, 7, 0, SHA256_MAJORITY_SHEDULER_BASE, name7),
            columns3.clone(),
            true
        );
        let sha256_base4_rot7_table = cs.add_table(sha256_base4_rot7_table)?;
        
        let name8 : &'static str = "sha256_sheduler_helper_table";
        let sha256_sheduler_helper_table = LookupTableApplication::new(
            name8,
            Sha256ShedulerHelperTable::new(name8),
            columns3.clone(),
            true
        );
        let sha256_sheduler_helper_table = cs.add_table(sha256_sheduler_helper_table)?;
    
        // Initialize IV values:
        // (first 32 bits of the fractional parts of the square roots of the first 8 primes 2..19):
        let iv = [ 
            u64_to_ff(0x6a09e667), u64_to_ff(0xbb67ae85), u64_to_ff(0x3c6ef372), u64_to_ff(0xa54ff53a),
            u64_to_ff(0x510e527f), u64_to_ff(0x9b05688c), u64_to_ff(0x1f83d9ab), u64_to_ff(0x5be0cd19),
        ];

        // Initialize array of round constants:
        // (first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311):
        let round_constants = [
            u64_to_ff(0x428a2f98), u64_to_ff(0x71374491), u64_to_ff(0xb5c0fbcf), u64_to_ff(0xe9b5dba5), 
            u64_to_ff(0x3956c25b), u64_to_ff(0x59f111f1), u64_to_ff(0x923f82a4), u64_to_ff(0xab1c5ed5),
            u64_to_ff(0xd807aa98), u64_to_ff(0x12835b01), u64_to_ff(0x243185be), u64_to_ff(0x550c7dc3), 
            u64_to_ff(0x72be5d74), u64_to_ff(0x80deb1fe), u64_to_ff(0x9bdc06a7), u64_to_ff(0xc19bf174),
            u64_to_ff(0xe49b69c1), u64_to_ff(0xefbe4786), u64_to_ff(0x0fc19dc6), u64_to_ff(0x240ca1cc), 
            u64_to_ff(0x2de92c6f), u64_to_ff(0x4a7484aa), u64_to_ff(0x5cb0a9dc), u64_to_ff(0x76f988da),
            u64_to_ff(0x983e5152), u64_to_ff(0xa831c66d), u64_to_ff(0xb00327c8), u64_to_ff(0xbf597fc7), 
            u64_to_ff(0xc6e00bf3), u64_to_ff(0xd5a79147), u64_to_ff(0x06ca6351), u64_to_ff(0x14292967),
            u64_to_ff(0x27b70a85), u64_to_ff(0x2e1b2138), u64_to_ff(0x4d2c6dfc), u64_to_ff(0x53380d13), 
            u64_to_ff(0x650a7354), u64_to_ff(0x766a0abb), u64_to_ff(0x81c2c92e), u64_to_ff(0x92722c85),
            u64_to_ff(0xa2bfe8a1), u64_to_ff(0xa81a664b), u64_to_ff(0xc24b8b70), u64_to_ff(0xc76c51a3), 
            u64_to_ff(0xd192e819), u64_to_ff(0xd6990624), u64_to_ff(0xf40e3585), u64_to_ff(0x106aa070),
            u64_to_ff(0x19a4c116), u64_to_ff(0x1e376c08), u64_to_ff(0x2748774c), u64_to_ff(0x34b0bcb5), 
            u64_to_ff(0x391c0cb3), u64_to_ff(0x4ed8aa4a), u64_to_ff(0x5b9cca4f), u64_to_ff(0x682e6ff3),
            u64_to_ff(0x748f82ee), u64_to_ff(0x78a5636f), u64_to_ff(0x84c87814), u64_to_ff(0x8cc70208), 
            u64_to_ff(0x90befffa), u64_to_ff(0xa4506ceb), u64_to_ff(0xbef9a3f7), u64_to_ff(0xc67178f2),
        ];

        let (global_range_table, max_of_width) = match use_global_range_table {
            true => {
                // there is no point in using small range tables
                assert!(global_range_table_width > SHA256_GADGET_CHUNK_SIZE);
                // for now only range table of width 16 is supported
                assert_eq!(global_range_table_width, DEFAULT_RANGE_TABLE_WIDTH);
                (Some(cs.get_table(global_range_table_name)?), global_range_table_width)
            },
            false => (None, SHA256_GADGET_CHUNK_SIZE),
        };

        Ok(Sha256Gadget {
            use_c_prev,
            ch_num_of_chunks,
            maj_and_sheduler_num_of_chunks,

            sha256_base7_rot6_table,
            sha256_base7_rot3_extr10_table,
            sha256_ch_normalization_table,
            
            sha256_base4_rot2_table,
            sha256_base4_rot2_width10_table,
            sha256_maj_normalization_table,
        
            sha256_base4_rot7_table,
            sha256_sheduler_helper_table,

            use_global_range_table,
            global_range_table_width,
            global_range_table,
            max_of_width,

            iv,
            round_constants,
        })
    }

    
    // -----------------------------------------------------------------------------------------------------------------------
    // -----------------------------------------------------------------------------------------------------------------------
    // helper functions
    // ------------------------------------------------------------------------------------------------------------------------
    // ------------------------------------------------------------------------------------------------------------------------

    // for list of overflowed numbers, deduce the maximal possible overflow of their sum
    fn deduce_of(&self, mut of_trackers: Vec<OverflowTracker>) -> OverflowTracker
    {
        assert!(!of_trackers.is_empty());

        let mut total : u64 = 0;
        for of in of_trackers {
            total += of.get_template();
        }
        OverflowTracker::new_from_template(total)
    }
  
    fn converter_helper(&self, n: u64, sparse_base: u64, rotation: usize, extraction: usize) -> E::Fr {
        let t = map_into_sparse_form(rotate_extract(n as usize, rotation, extraction), sparse_base as usize);
        E::Fr::from_str(&t.to_string()).unwrap()
    }

    fn allocate_converted_num<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        var: &AllocatedNum<E>, 
        chunk_bitlen: usize, 
        chunk_offset: usize, 
        sparse_base: u64,
        rotation: usize, 
        extraction: usize
    ) -> Result<AllocatedNum<E>> 
    {
        let new_val = var.get_value().map( |fr| {
            let repr = fr.into_repr();
            let n = (repr.as_ref()[0] >> chunk_offset) & ((1 << chunk_bitlen) - 1);
            self.converter_helper(n, sparse_base, rotation, extraction)
        });

        AllocatedNum::alloc(cs, || new_val.grab())
    }

    // the idea realized in this function is to combine accumulation of running sum with normalization
    // assume we have representation of x as x = \sum x_i a^i, where each x_i is in [0, a-1] and we have
    // highy nonlinear normalization funtion f: [0, a-1] -> [0, b-1], implemented via corresponding table
    // the wanted result is y = \sum f(x_i) b^i
    // we can conbine transformation of each chunk x_i and accumulation of resulting y_i via f on the same row:
    // start with acc = 0
    // for the row [x_i, f(x_i), acc_prev, acc_new], let acc_new = acc_prev * b^i + f(x_i)
    
    // actual implementation is the following:
    // for row of the form [x, f(x), g(x), acc] do:
    // table query x => f(x), g(x)
    // running sum for input: acc_next = acc - coef * x
    // if is_final is set, simply check: acc = coef * x
    // returns (f(x), g(x), acc_next)
    fn query_table_acc<CS: ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        table: &Arc<LookupTableApplication<E>>, 
        key: &AllocatedNum<E>,
        prev_acc: &AllocatedNum<E>,
        coef: &E::Fr,
        is_final: bool,
    ) -> Result<(AllocatedNum<E>, AllocatedNum<E>, AllocatedNum<E>)> 
    {
        let (f_key, g_key) = match key.get_value() {
            None => {
                (
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?, 
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
                )
            },
            Some(val) => {
                let vals = table.query(&[val])?;
                (AllocatedNum::alloc(cs, || Ok(vals[0]))?, AllocatedNum::alloc(cs, || Ok(vals[1]))?)
            },     
        };

        let new_acc = if !is_final {
            AllocatedNum::alloc(cs, || {
                let mut res = prev_acc.get_value().grab()?;
                let mut tmp = key.get_value().grab()?;
                tmp.mul_assign(coef);
                res.sub_assign(&(f_key.get_value().grab())?);
                Ok(tmp)
            })?
        }
        else {
            AllocatedNum::alloc_zero(cs)?
        };

        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();

        let range_of_linear_terms = CS::MainGate::range_of_linear_terms();
        let range_of_next_step_linear_terms = CS::MainGate::range_of_next_step_linear_terms();
        let idx_of_last_linear_term = range_of_next_step_linear_terms.last().expect("must have an index");

        // new_acc = prev_acc - base * key
        // or: base * key + new_acc - prev_acc = 0;
        let vars = [key.get_variable(), f_key.get_variable(), g_key.get_variable(), new_acc.get_variable()];
        let coeffs = [coef.clone(), E::Fr::zero(), E::Fr::zero(), minus_one];

        cs.begin_gates_batch_for_step()?;

        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
    
        let mut gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;

        for (idx, coef) in range_of_linear_terms.zip(coeffs.into_iter()) {
            gate_coefs[idx] = *coef;
        }

        if !is_final {
            gate_coefs[idx_of_last_linear_term] = E::Fr::one();
        }

        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(
            &mg,
            &gate_coefs,
            &vars,
            &[]
        )?;

        cs.end_gates_batch_for_step()?;

        Ok((f_key, g_key, new_acc))
    }

    // range check for of, assuming of is at most SHA256_GADGET_CHUNK bits long
    // we accomplish range check exploting sha-specific sparse-rotations tables
    // the row has the form: [of, sparse(of), sparse_rotate(of), of_shifted]
    // also check that of * coef = of_shifted
    fn of_range_check<CS>(&self, cs: &mut CS, of: &AllocatedNum<E>, of_shifted: &AllocatedNum<E>, coef: &E::Fr) -> Result<()> 
    where CS: ConstraintSystem<E>
    {
        let table = match self.use_global_range_table {
            false => &self.sha256_base4_rot2_table,
            true => self.global_range_table.as_ref().unwrap(),
        };

        let mut minus_one = E::Fr::one();
        minus_one.negate();
        let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();

        let linear_terms = CS::MainGate::range_of_linear_terms();
        let a_idx = linear_terms.start;
        let d_idx = linear_terms.end - 1; 

        let (b, c) = match of.get_value() {
            None => {
                (
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?, 
                    AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
                )
            },
            Some(val) => {
                let vals = table.query(&[val])?;
                (AllocatedNum::alloc(cs, || Ok(vals[0]))?, AllocatedNum::alloc(cs, || Ok(vals[1]))?)
            },     
        };
        let vars = [of.get_variable(), b.get_variable(), c.get_variable(), of_shifted.get_variable()];

        cs.begin_gates_batch_for_step()?;

        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
        let mut gate_term = MainGateTerm::new();
        let (_, mut gate_coefs) = CS::MainGate::format_term(gate_term, dummy)?;
        gate_coefs[a_idx] = coef.clone();
        gate_coefs[d_idx] = minus_one;
        
        let mg = CS::MainGate::default();
        cs.new_gate_in_batch(&mg, &gate_coefs, &vars, &[])?;
        
        cs.end_gates_batch_for_step()?;

        Ok(())
    }

    fn query_table<CS: ConstraintSystem<E>>(
        &self,
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

        //let dummy = AllocatedNum::alloc_zero(cs)?.get_variable();
        let vars = [key.get_variable(), res.0.get_variable(), res.1.get_variable(), key.get_variable()];
        cs.allocate_variables_without_gate(
            &vars,
            &[]
        )?;
        cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;

        cs.end_gates_batch_for_step()?;
        Ok(res)
    }

    fn extact_32_bits_from_tracked_num<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: NumWithTracker<E>) -> Result<Num<E>> 
    {
        let res = match input.overflow_tracker {
            OverflowTracker::NoOverflow => input.num,
            _ => match &input.num {
                Num::Constant(fr) => {
                    let repr = fr.into_repr();
                    let n = repr.as_ref()[0] & ((1 << SHA256_REG_WIDTH) - 1); 
                    Num::Constant(Self::u64_to_ff(n))
                },
                Num::Allocated(var) => {
                    let res = if self.use_global_range_table {
                        // NB: the only supported value for range table width is 16!
                        let range_table_width = DEFAULT_RANGE_TABLE_WIDTH;
                        let low = self.allocate_converted_num(cs, var, range_table_width, 0, 0, 0, 0)?;
                        let high = self.allocate_converted_num(cs, var, range_table_width, range_table_width, 0, 0, 0)?;
                        let of = self.allocate_converted_num(cs, var, range_table_width, range_table_width * 2, 0, 0, 0)?;

                        let cf = [
                            E::Fr::one(), u64_to_ff(1 << range_table_width), u64_to_ff(1 << (2 * range_table_width)),
                        ];
                        let table = &self.global_range_table.as_ref().unwrap();

                        let mut acc = var.clone();
                        let (_, _, acc) = self.query_table_acc(cs, table, &low, &acc, &cf[0], false)?;
                        let (_, _, acc) = self.query_table_acc(cs, table, &high, &acc, &cf[1], false)?;
                        let (_, _, acc) = self.query_table_acc(cs, table, &of, &acc, &cf[2], true)?;

                        let extracted = self.allocate_converted_num(cs, var, SHA256_REG_WIDTH, 0, 0, 0, 0)?;
                        let dummy = AllocatedNum::alloc_zero(cs)?;
                        
                        AllocatedNum::ternary_lc_eq(
                            cs, 
                            &[cf[0].clone(), cf[1].clone(), E::Fr::zero()],
                            &[low, high, dummy],
                            &extracted,
                        )?;
                        Num::Allocated(extracted)
                    }
                    else {
                        let low = self.allocate_converted_num(cs, var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
                        let mid = self.allocate_converted_num(cs, var, SHA256_GADGET_CHUNK_SIZE, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;
                        let high = self.allocate_converted_num(
                            cs, var, SHA256_GADGET_CHUNK_SIZE - 1, SHA256_GADGET_CHUNK_SIZE * 2, 0, 0, 0
                        )?;
                        let of = self.allocate_converted_num(cs, var, SHA256_GADGET_CHUNK_SIZE, SHA256_REG_WIDTH, 0, 0, 0)?;

                        let cf = [
                            E::Fr::one(), u64_to_ff(1 << SHA256_GADGET_CHUNK_SIZE), 
                            u64_to_ff(1 << (2 * SHA256_GADGET_CHUNK_SIZE)), u64_to_ff(1 << SHA256_REG_WIDTH),
                        ];

                        let mut acc = var.clone();
                        let trunc_table = &self.sha256_base4_rot2_width10_table;
                        let (_, _, acc) = self.query_table_acc(cs, &self.sha256_base4_rot2_table, &low, &acc, &cf[0], false)?;
                        let (_, _, acc) = self.query_table_acc(cs, &self.sha256_base4_rot2_table, &mid, &acc, &cf[1], false)?;
                        let (_, _, acc) = self.query_table_acc(cs, &trunc_table, &high, &acc, &cf[2], false)?;
                        let (_, _, acc) = self.query_table_acc(cs, &self.sha256_base4_rot2_table, &of, &acc, &cf[3], true)?;

                        let extracted = self.allocate_converted_num(cs, var, SHA256_REG_WIDTH, 0, 0, 0, 0)?;
        
                        AllocatedNum::ternary_lc_eq(
                            cs, 
                            &[cf[0].clone(), cf[1].clone(), cf[2].clone()],
                            &[low, mid, high],
                            &extracted,
                        )?;
                        Num::Allocated(extracted)
                    };
                    res
                },
            }
        };
        
        Ok(res)
    }

    // --------------------------------------------------------------------------------------------------------------------------
    // --------------------------------------------------------------------------------------------------------------------------
    // convertion and normalization routines
    // ---------------------------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------------------------------------------------------------

    fn convert_into_sparse_chooser_form<CS : ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        input: NumWithTracker<E>, 
    ) -> Result<SparseChValue<E>> 
    {   
        if let OverflowTracker::SignificantOverflow(n) = input.overflow_tracker {
            assert!(n <= (self.max_of_width as u64) + 1);
        };
        
        if let Num::Constant(x) = input.num {
            let repr = x.into_repr();
            let n = repr.as_ref()[0] & ((1 << 32) - 1); 
            
            let res = SparseChValue {
                normal: (Num::Constant(x)).into(),
                sparse: Num::Constant(self.converter_helper(n, SHA256_CHOOSE_BASE, 0, 0)),
                rot6: Num::Constant(self.converter_helper(n, SHA256_CHOOSE_BASE, 6, 0)),
                rot11: Num::Constant(self.converter_helper(n, SHA256_CHOOSE_BASE, 11, 0)),
                rot25: Num::Constant(self.converter_helper(n, SHA256_CHOOSE_BASE, 25, 0)),
            };

            return Ok(res)
        }

        let var = input.num.get_variable().unwrap();
        let mut of_flag_dropped = false;          

        // split our 32bit variable into 11-bit chunks:
        // there will be three chunks (low, mid, high) for 32bit number
        // note that, we can deal here with possible 1-bit overflow: (as 3 * 11 = 33)
        // in order to do this we allow extraction set to 10 for the table working with highest chunk
        
        let low = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
        let mid = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;
        let high = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 2 * SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;

        let mut acc = var.clone();
        let flag = match input.overflow_tracker {
            OverflowTracker::NoOverflow | OverflowTracker::OneBitOverflow => true,
            _ => false,
        };
        let cf = [
            E::Fr::one(), u64_to_ff(1 << SHA256_GADGET_CHUNK_SIZE), 
            u64_to_ff(1 << (2 * SHA256_GADGET_CHUNK_SIZE)), u64_to_ff(1 << (3 * SHA256_GADGET_CHUNK_SIZE)),
        ];

        let (sparse_low, sparse_low_rot6, acc) = self.query_table_acc(cs, &self.sha256_base7_rot6_table, &low, &acc, &cf[0], false)?;
        let (sparse_mid, _sparse_mid_rot6, acc) = self.query_table_acc(cs, &self.sha256_base7_rot6_table, &mid, &acc, &cf[1], false)?;
        let (sparse_high, sparse_high_rot3, acc) = self.query_table_acc(
            cs, &self.sha256_base7_rot3_extr10_table, &high, &acc, &cf[2], flag
        )?;

        let full_normal = match input.overflow_tracker {
            OverflowTracker::NoOverflow | OverflowTracker::OneBitOverflow => var,
            OverflowTracker::SignificantOverflow(n) => {
                // full normal = low + 2^11 * mid + 2^22 * high + 2^33 * overflow
                // allocate overflow on the next row alongside with the range check
                let of = self.allocate_converted_num(cs, &var, self.max_of_width, SHA256_GADGET_CHUNK_SIZE * 3, 0, 0, 0)?;
                self.of_range_check(cs, &of, &acc, &cf[3])?;

                let full_normal = if n >= (self.max_of_width as u64 - 1) {
                    of_flag_dropped = true;
                    let truncated = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE * 3, 0, 0, 0, 0)?;
                    AllocatedNum::ternary_lc_eq(
                        cs, &[cf[0].clone(), cf[1].clone(), cf[2].clone()], &[low, mid, high], &truncated,
                    )?;
                    truncated
                }
                else { 
                    var 
                };

                full_normal
            },
        };
   
        let full_sparse = {
            // full_sparse = low_sparse + 7^11 * mid_sparse + 7^22 * high_sparse
            let sparse_full = self.allocate_converted_num(
                cs, &var, SHA256_REG_WIDTH + 1, 0, SHA256_CHOOSE_BASE, 0, SHA256_REG_WIDTH
            )?;

            let limb_1_shift = u64_exp_to_ff(7, 11);
            let limb_2_shift = u64_exp_to_ff(7, 22);

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
            let full_sparse_rot6 = self.allocate_converted_num(
                cs, &var, SHA256_REG_WIDTH + 1, 0, SHA256_CHOOSE_BASE, 6, SHA256_REG_WIDTH
            )?;

            let rot6_limb_1_shift = u64_exp_to_ff(7, 11-6);
            let rot6_limb_2_shift = u64_exp_to_ff(7, 22 - 6);

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
            let full_sparse_rot11 = self.allocate_converted_num(
                cs, &var, SHA256_REG_WIDTH + 1, 0, SHA256_CHOOSE_BASE, 11, SHA256_REG_WIDTH
            )?;

            let rot11_limb_0_shift = u64_exp_to_ff(7, 32 - 11);
            let rot11_limb_2_shift = u64_exp_to_ff(7, 22 - 11);

            AllocatedNum::ternary_lc_eq(
                cs, 
                &[E::Fr::one(), rot11_limb_0_shift, rot11_limb_2_shift],
                &[sparse_mid.clone(), sparse_low.clone(), sparse_high],
                &full_sparse_rot11,
            )?;

            full_sparse_rot11
        };

        let full_sparse_rot_25 = {
            // full_sparse_rot25 = sparse_high_rot3 + 7^(11-3) * sparse_low + 7^(22-3) * sparse_mid
            let full_sparse_rot25 = self.allocate_converted_num(
                cs, &var, SHA256_REG_WIDTH + 1, 0, SHA256_CHOOSE_BASE, 25, SHA256_REG_WIDTH
            )?;

            let rot25_limb_0_shift = u64_exp_to_ff(7, 10 - 3);
            let rot25_limb_1_shift = u64_exp_to_ff(7, 21 - 3);

            AllocatedNum::ternary_lc_eq(
                cs, 
                &[E::Fr::one(), rot25_limb_0_shift, rot25_limb_1_shift],
                &[sparse_high_rot3, sparse_low, sparse_mid],
                &full_sparse_rot25,
            )?;

            full_sparse_rot25
        };

        let new_tracker = if of_flag_dropped {OverflowTracker::OneBitOverflow} else {input.overflow_tracker};

        let res = SparseChValue{
            normal: NumWithTracker { 
                num: Num::Allocated(full_normal), 
                overflow_tracker: new_tracker, 
            },
            sparse: Num::Allocated(full_sparse),
            rot6: Num::Allocated(full_sparse_rot6),
            rot11: Num::Allocated(full_sparse_rot11),
            rot25: Num::Allocated(full_sparse_rot_25),
        };
        return Ok(res);
    }

    // IMPORTANT NOTE:
    // there is a small difference between conversion into sparse chooser form and majority form functions 
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
        if let OverflowTracker::SignificantOverflow(n) = input.overflow_tracker {
            assert!(n <= self.max_of_width as u64);
        };

        if let Num::Constant(x) = input.num {
            let repr = x.into_repr();
            // NOTE : think, if it is safe for n to be overflowed
            let n = repr.as_ref()[0] & ((1 << 32) - 1); 
            
            let res = SparseMajValue {
                normal: (Num::Constant(x)).into(),
                sparse: Num::Constant(self.converter_helper(n, SHA256_MAJORITY_BASE, 0, 0)),
                rot2: Num::Constant(self.converter_helper(n, SHA256_MAJORITY_BASE, 2, 0)),
                rot13: Num::Constant(self.converter_helper(n, SHA256_MAJORITY_BASE, 13, 0)),
                rot22: Num::Constant(self.converter_helper(n, SHA256_MAJORITY_BASE, 22, 0)),
            };

            return Ok(res)
        };

        let var = input.num.get_variable().unwrap();
        let mut of_flag_dropped = false;          

        let mut acc = var.clone();
        let flag = match input.overflow_tracker {
            OverflowTracker::NoOverflow => true,
            _ => false,
        };
        let cf = [
            E::Fr::one(), u64_to_ff(1 << SHA256_GADGET_CHUNK_SIZE), 
            u64_to_ff(1 << (2 * SHA256_GADGET_CHUNK_SIZE)), u64_to_ff(1 << (3 * SHA256_REG_WIDTH)),
        ];
           
        // split our 32bit variable into 11-bit chunks:
        // there will be three chunks (low, mid, high) for 32bit number
        // note that, we can deal here with possible 1-bit overflow: (as 3 * 11 = 33)
        // in order to do this we allow extraction set to 10 for the table working with highest chunk
        
        let low = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
        let mid = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;
        let high = self.allocate_converted_num(
            cs, &var, SHA256_GADGET_CHUNK_SIZE - 1, 2 * SHA256_GADGET_CHUNK_SIZE, 0, 0, SHA256_GADGET_CHUNK_SIZE
        )?;

        let (sparse_low, sparse_low_rot2, acc) = self.query_table_acc(cs, &self.sha256_base4_rot2_table, &low, &acc, &cf[0], false)?;
        let (sparse_mid, sparse_mid_rot2, acc) = self.query_table_acc(cs, &self.sha256_base4_rot2_table, &mid, &acc, &cf[1], false)?;
        let (sparse_high, _, acc) = self.query_table_acc(cs, &elf.sha256_base4_rot2_width10_table, &high, &acc, &cf[2], flag)?;

        let full_normal = match input.overflow_tracker {
            OverflowTracker::NoOverflow => var,
            OverflowTracker::OneBitOverflow | OverflowTracker::SignificantOverflow(n) => {
                // full normal = low + 2^11 * mid + 2^22 * high + 2^33 * overflow
                // allocate overflow on the next row alongside with the range check
                let of = self.allocate_converted_num(cs, &var, self.max_of_width, SHA256_GADGET_CHUNK_SIZE * 3, 0, 0, 0)?;
                self.of_range_check(cs, &of, &acc, &cf[3])?;

                let full_normal = if n >= (self.max_of_width as u64 - 1) {
                    of_flag_dropped = true;
                    let truncated = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE * 3, 0, 0, 0, 0)?;
                    AllocatedNum::ternary_lc_eq(
                        cs, &[cf[0].clone(), cf[1].clone(), cf[2].clone()], &[low, mid, high], &truncated,
                    )?;
                    truncated
                }
                else { 
                    var 
                };

                full_normal
            },
        };

                let (sparse_low, sparse_low_rot2) = self.query_table2(cs, &self.sha256_base4_rot2_table, &low)?;
                let (sparse_mid, sparse_mid_rot2) = self.query_table2(cs, &self.sha256_base4_rot2_table, &mid)?;
                //assert_eq!(self.majority_strategy, Strategy::UseCustomTable);
                // let high_chunk_table = match self.majority_strategy {
                //     Strategy::UseCustomTable => self.sha256_base4_rot2_extr10_table.as_ref().unwrap(),
                //     Strategy::NaivaApproach => &self.sha256_base4_rot2_table,
                // };
                let (sparse_high, _) = self.query_table2(cs, &self.sha256_base4_widh10_table, &high)?;

                let full_normal = match input.overflow_tracker 
                {
                    OverflowTracker::NoOverflow => {
                        // compose full normal = low + 2^11 * mid + 2^22 * high
                        AllocatedNum::ternary_lc_eq(
                            cs, 
                            &[E::Fr::one(), Self::u64_exp_to_ff(1 << 11, 0), Self::u64_exp_to_ff(1 << 22, 0)],
                            &[low, mid, high],
                            &var,
                        )?;
                        var.clone()
                    }
                    _ => {
                        // full normal = low + 2^11 * mid + 2^22 * high - 2^32 * overflow
                        // allocate overflow on the next row alongside with the range check
                        let of = self.allocate_converted_num(
                            cs, &var, RANGE_TABLE_WIDTH, SHA256_REG_WIDTH, 0, 0, 0
                        )?;

                        AllocatedNum::quartic_lc_eq(
                            cs,
                            &[E::Fr::one(), Self::u64_to_ff(1 << 11), Self::u64_to_ff(1 << 22), Self::u64_to_ff(1 << 32)],
                            &[low.clone(), mid.clone(), high.clone(), of.clone()],
                            &var,
                        )?;

                        self.query_table2(cs, &self.range_table, &of)?;

                        let full_normal = match input.overflow_tracker {
                            OverflowTracker::SignificantOverflow(n) if n >= 15 => {
                                of_flag_dropped = true;
                                let truncated = self.allocate_converted_num(cs, &var, SHA256_REG_WIDTH, 0, 0, 0, 0)?;
                                AllocatedNum::ternary_lc_eq(
                                    cs,
                                    &[E::Fr::one(), Self::u64_to_ff(1 << 11), Self::u64_to_ff(1 << 22)],
                                    &[low, mid, high],
                                    &truncated,
                                )?;
                                truncated
                            },
                            _ => var.clone()
                        };
                        full_normal
                    }
                };

                let full_sparse = {
                    // full_sparse = low_sparse + 4^11 * mid_sparse + 4^22 * high_sparse
                    let sparse_full = self.allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_MAJORITY_BASE, 0, SHA256_REG_WIDTH
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
                    // full_sparse_rot2 = low_sparse_rot2 + 4^(11-2) * sparse_mid + 4^(22-2) * sparse_high
                    let full_sparse_rot2 = self.allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_MAJORITY_BASE, 2, SHA256_REG_WIDTH
                    )?;

                    let rot2_limb_1_shift = Self::u64_exp_to_ff(4, 11 - 2);
                    let rot2_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 2);

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
                    let full_sparse_rot13 = self.allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_MAJORITY_BASE, 13, SHA256_REG_WIDTH
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
                    let full_sparse_rot22 = self.allocate_converted_num(
                        cs, &var, SHA256_REG_WIDTH, 0, SHA256_MAJORITY_BASE, 22, SHA256_REG_WIDTH
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

                let new_tracker = if of_flag_dropped {OverflowTracker::NoOverflow} else {input.overflow_tracker};

                let res = SparseMajValue{
                    normal: NumWithTracker {
                        num: Num::Allocated(full_normal), 
                        overflow_tracker: new_tracker, 
                    },
                    sparse: Num::Allocated(full_sparse),
                    rot2: Num::Allocated(full_sparse_rot2),
                    rot13: Num::Allocated(full_sparse_rot13),
                    rot22: Num::Allocated(full_sparse_rot_22),
                };
                return Ok(res);
            }
        }
    }

    // // this function does the following: 
    // // given any x = \sum_{i=0}^{n} x_i * base^i and well-defined mapping f: [0; base-1] -> [0; 1]
    // // (among possible variants for f are "parity": f(k) = k mod 2, choose_function or majority_function:
    // // for the description of the latter two refer to "tables" module)
    // // return the "normalized" variable z = \sum_{i=0}^{n} f(x_i) 2^i
    // //
    // // the problem with table approach is actually the following:
    // // we are unable to create long table holding all possible values of x in the range [0; base^n - 1] (granting that n is fixed)
    // // the reason is that we do not want our tables to be EXTREMELY large, hence we require one additional step of workaround:
    // // given adjustible parameter NUM_OF_CHUNKS we split our x in the linear combination of [ n / NUM_OF_CHUNKS] summands y_i,
    // // each of which itself consists of no more than NUM_OF_CHUNKS summands
    // //
    // // in other words, we have:
    // // x = \sum_{j=0}^{[n / NUM_OF_CHUNKS]} y_j * base^{j * NUM_OF_CHUNKS},
    // // where y_j = \sum_{i=0}^{NUM_CHUNKS - 1} x_{j * NUM_OF_CHUNKS + x_i} * base^{j}
    // // each such y_j is in smaller range [0; base^NUM_CHUNKS-1]
    // // and for each such y_j we may apply the corresponding (and realtively small) normalization table and get
    // // z_j = \sum_{i=0}^{NUM_CHUNKS} f(x_{j * NUM_OF_CHUNKS + x_i}) 2^j
    // // the final z is then constructed as a linear conbination of {z_j} with simple weigt coefficients 
    // // (in order for each z_j to be placed in an appropriate position in the bit representation of final result z)
    // //
    // // note, that for each possible pair of normalization transformation f(x) and base,
    // // the parameter NUM_OF_CHUNKS may be determined separately
    // // 
    // // e.g. in reference implementation Barretenberg a = NUM_OF_CHUNKS = 4 for base = 7 and b = NUM_OF_CHUNKS = 6 for base = 4
    // // IMHO, the motivation for such choice of parameters is the following:
    // // in any case we would use sparse_rotate_extract tables with 11-bit chunks (and hence of size c = 2^11)
    // // parameters a and b are chosen in a way, so that table sizes for normalization transforms of sizes 7^a and 4^b
    // // approximately have the same order of magnitude as c, so that all used tables will be of relatively the same size
    // // it is obvious, that following this logic, a = 4 and b = 6 (or may be 5(!)) are best possible choices
    // //
    // // in any case we do not want to be two strict here, and allow NUM_OF_CHUNKS for bases 7 and 4
    // // to be specified as constructor parameters for Sha256Gadget gadget

    // fn normalize<CS: ConstraintSystem<E>, F: Fn(E::Fr) -> E::Fr>(
    //     &self,
    //     cs: &mut CS, 
    //     input: &Num<E>, 
    //     table: &Arc<LookupTableApplication<E>>, 
    //     converter_func: F,
    //     base: usize, 
    //     num_chunks: usize
    // ) -> Result<Num<E>>
    // {
    //     match input {
    //         Num::Constant(x) => {
    //             let output = converter_func(x.clone());
    //             return Ok(Num::Constant(output));
    //         }
    //         Num::Allocated(x) => {
    //             // split and slice!
    //             let num_slices = Self::round_up(SHA256_REG_WIDTH, num_chunks);
    //             let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
    //             //let mut output_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
    //             let input_slice_modulus = pow(base, num_chunks);

    //             match x.get_value() {
    //                 None => {
    //                     for _i in 0..num_slices {
    //                         let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
    //                         input_slices.push(tmp);
    //                     }
    //                 },
    //                 Some(f) => {
    //                     // here we have to operate on row biguint number
    //                     let mut big_f = BigUint::default();
    //                     let f_repr = f.into_repr();
    //                     for n in f_repr.as_ref().iter().rev() {
    //                         big_f <<= 64;
    //                         big_f += *n;
    //                     } 

    //                     for _i in 0..num_slices {
    //                         let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
    //                         let new_val = Self::u64_to_ff(remainder);
    //                         big_f /= input_slice_modulus;
    //                         let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
    //                         input_slices.push(tmp);
    //                     }

    //                     assert!(big_f.is_zero());
    //                 }
    //             }

    //             let mut output_acc = AllocatedNum::alloc_zero(cs)?;
    //             let output_base = Self::u64_exp_to_ff(2, num_chunks as u64);
    //             for input_chunk in input_slices.iter().rev() {
    //                output_acc = self.query_table_accumulate(cs, table, input_chunk, &output_acc, &output_base)?;
    //             }

    //             // for i in 0..num_slices {
    //             //     let tmp = self.query_table1(cs, table, &input_slices[i])?;
    //             //     output_slices.push(tmp);
    //             // }
    //             // let output = AllocatedNum::alloc(cs, || x.get_value().map(| fr | converter_func(fr)).grab())?;
    //             // AllocatedNum::long_weighted_sum_eq(cs, &output_slices[..], &output_base, &output)?;
                
    //             // TODO: use negative dialation for A!
    //             //println!("OPTIMIZE");
    //             let input_base = Self::u64_to_ff(input_slice_modulus as u64);
    //             AllocatedNum::long_weighted_sum_eq(cs, &input_slices[..], &input_base, x)?;
                
    //             return Ok(Num::Allocated(output_acc));
    //         }
    //     }
    // }

    // fn choose<CS>(&self, cs: &mut CS, e: SparseChValue<E>, f: SparseChValue<E>, g: SparseChValue<E>) -> Result<NumWithTracker<E>>
    // where CS: ConstraintSystem<E>
    // {
    //     let mut two = E::Fr::one();
    //     two.double();
    //     let mut three = two.clone();
    //     three.add_assign(&E::Fr::one());
        
    //     let t0 = Num::lc(cs, &[E::Fr::one(), two, three], &[e.sparse, f.sparse, g.sparse])?; 
    //     let t1 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[e.rot6, e.rot11, e.rot25])?;

    //     let r0 = self.normalize(
    //         cs, &t0, 
    //         &self.sha256_ch_normalization_table,
    //         ch_map_normalizer,  
    //         SHA256_CHOOSE_BASE, 
    //         self.ch_base_num_of_chunks
    //     )?;
        
    //     let r1 = self.normalize(
    //         cs, &t1, 
    //         &self.sha256_ch_xor_table, 
    //         ch_xor_normalizer,
    //         SHA256_CHOOSE_BASE, 
    //         self.ch_base_num_of_chunks
    //     )?;

    //     let r0 : NumWithTracker<E> = r0.into();
       
    //     r0.add(cs, &r1)
    // }

    // fn majority<CS>(&self, cs: &mut CS, a: SparseMajValue<E>, b: SparseMajValue<E>, c: SparseMajValue<E>) -> Result<NumWithTracker<E>>
    // where CS: ConstraintSystem<E>
    // {   
    //     let t0 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[a.sparse, b.sparse, c.sparse])?; 
    //     let t1 = Num::lc(cs, &[E::Fr::one(), E::Fr::one(), E::Fr::one()], &[a.rot2, a.rot13, a.rot22])?;

    //     let r0 = self.normalize(
    //         cs, &t0, 
    //         &self.sha256_maj_normalization_table,
    //         maj_map_normalizer, 
    //         SHA256_MAJORITY_BASE, 
    //         self.maj_base_num_of_chunks,
    //     )?;
    //     let r1 = self.normalize(
    //         cs, &t1, 
    //         &self.sha256_maj_xor_table, 
    //         maj_xor_normalizer,
    //         SHA256_MAJORITY_BASE, 
    //         self.maj_base_num_of_chunks
    //     )?;

    //     let r0 : NumWithTracker<E> = r0.into();
       
    //     r0.add(cs, &r1)
    // }

    // // one round of inner SHA256 cycle 
    // // the hash for single block of 512 chunks requires 64 such cycles
    // fn sha256_inner_block<CS: ConstraintSystem<E>>(
    //     &self,
    //     cs: &mut CS, 
    //     regs: Sha256Registers<E>, 
    //     inputs: &[NumWithTracker<E>], 
    //     round_constants: &[E::Fr],
    // ) -> Result<Sha256Registers<E>>
    // {
    //     let mut a = self.convert_into_sparse_majority_form(cs, regs.a.clone())?;
    //     let mut b = self.convert_into_sparse_majority_form(cs, regs.b.clone())?;
    //     let mut c = self.convert_into_sparse_majority_form(cs, regs.c.clone())?;
    //     let mut d = self.convert_into_sparse_majority_form(cs, regs.d.clone())?;
        
    //     let mut e = self.convert_into_sparse_chooser_form(cs, regs.e.clone())?;
    //     let mut f = self.convert_into_sparse_chooser_form(cs, regs.f.clone())?;
    //     let mut g = self.convert_into_sparse_chooser_form(cs, regs.g.clone())?;
    //     let mut h = self.convert_into_sparse_chooser_form(cs, regs.h.clone())?;

    //     for i in 0..64 {
    //         let ch = self.choose(cs, e.clone(), f.clone(), g.clone())?;
    //         let maj = self.majority(cs, a.clone(), b.clone(), c.clone())?;
            
    //         // temp1 will be overflowed two much (4 bits in total), so we are going to reduce it in any case
    //         // TODO: may be it is possible to optimize it somehow?
    //         let rc = Num::Constant(round_constants[i]);
    //         // ch overflow is no more than 1 bit
    //         // ch + input + const = 3 bits of
    //         // hence if h is overflowed, wo wan't catch this!
            
    //         let var_args = &[h.normal.num, ch.num, inputs[i].num.clone(), rc];
    //         let of_vec = vec![
    //             h.normal.overflow_tracker, ch.overflow_tracker, inputs[i].overflow_tracker, OverflowTracker::NoOverflow
    //         ];
    //         // TODO: use negative DIALATION for tmp2
    //         //println!("QQQ");
    //         let temp1 = NumWithTracker {
    //             num: Num::sum(cs, var_args)?,
    //             overflow_tracker: self.deduce_of(of_vec),
    //         }; 
    //         //let temp1 = self.extact_32_from_overflowed_num(cs, &temp1_unreduced)?;

    //         h = g;
    //         g = f;
    //         f = e;
    //         let mut temp2 : NumWithTracker<E> = d.normal.into();
    //         temp2 = temp2.add_tracked(cs, &temp1)?;
    //         e = self.convert_into_sparse_chooser_form(cs, temp2)?;
    //         d = c;
    //         c = b;
    //         b = a;
    //         let temp3 = maj.add_tracked(cs, &temp1)?;
    //         a =self.convert_into_sparse_majority_form(cs, temp3)?;
    //     }

    //     let regs = Sha256Registers {
    //         a: regs.a.add_tracked(cs, &a.normal)?,
    //         b: regs.b.add_tracked(cs, &b.normal)?,
    //         c: regs.c.add_tracked(cs, &c.normal)?,
    //         d: regs.d.add_tracked(cs, &d.normal)?,
    //         e: regs.e.add_tracked(cs, &e.normal)?,
    //         f: regs.f.add_tracked(cs, &f.normal)?,
    //         g: regs.g.add_tracked(cs, &g.normal)?,
    //         h: regs.h.add_tracked(cs, &h.normal)?,
    //     };
        
    //     Ok(regs)
    // }

    // // computes sigma_0(x) = S_7(x) ^ S_18(x) ^ R_3(x)
    // // S_i and R_j are defined in the comments related to "message_expansion" function
    // // we assume that there is no oveflow in input argument num
    // fn sigma_0<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &NumWithTracker<E>) -> Result<Num<E>>
    // {
    //     if let OverflowTracker::SignificantOverflow(n) = input.overflow_tracker {
    //         assert!(n <= 16);
    //     };
      
    //     match &input.num {
    //         Num::Constant(x) => {
    //             let repr = x.into_repr();
    //             // NOTE : think, if it is safe for n to be overflowed
    //             let n = (repr.as_ref()[0] & ((1 << SHA256_REG_WIDTH) - 1)) as usize;

    //             let s7 = rotate_extract(n, 7, 0);
    //             let s18 = rotate_extract(n, 18, 0);
    //             let r3 = shift_right(n, 3);
    //             let res =  Self::u64_to_ff((s7 ^ s18 ^ r3) as u64);

    //             return Ok(Num::Constant(res));
    //         }
    //         Num::Allocated(var) => {
    //             // split our 32bit variable into 11-bit chunks:
    //             // there will be three chunks (low, mid, high) for 32bit number
    //             let low = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
    //             let mid = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;
    //             let high = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE-1, 2 * SHA256_GADGET_CHUNK_SIZE, 0, 0, 0)?;

    //             let (sparse_low, sparse_low_rot7) = self.query_table2(cs, &self.sha256_base4_rot7_table, &low)?;
    //             let (sparse_mid, sparse_mid_rot7) = self.query_table2(cs, &self.sha256_base4_rot7_table, &mid)?;
    //             let (sparse_high, _) = self.query_table2(cs, &self.sha256_base4_widh10_table, &high)?;

    //             match input.overflow_tracker 
    //             {
    //                 OverflowTracker::NoOverflow => {
    //                     // compose full normal = low + 2^11 * mid + 2^22 * high
    //                     AllocatedNum::ternary_lc_eq(
    //                         cs, 
    //                         &[E::Fr::one(), Self::u64_exp_to_ff(1 << 11, 0), Self::u64_exp_to_ff(1 << 22, 0)],
    //                         &[low.clone(), mid.clone(), high.clone()],
    //                         &var,
    //                     )?;
    //                 }
    //                 _ => {
    //                     // full normal = low + 2^11 * mid + 2^22 * high + 2^32 * overflow
    //                     // allocate overflow on the next row alongside with the range check
    //                     let of = self.allocate_converted_num(
    //                         cs, &var, RANGE_TABLE_WIDTH, SHA256_REG_WIDTH, 0, 0, 0
    //                     )?;

    //                     AllocatedNum::quartic_lc_eq(
    //                         cs,
    //                         &[E::Fr::one(), Self::u64_to_ff(1 << 11), Self::u64_to_ff(1 << 22), Self::u64_to_ff(1 << 32)],
    //                         &[low.clone(), mid.clone(), high.clone(), of.clone()],
    //                         &var,
    //                     )?;
    //                     self.query_table2(cs, &self.range_table, &of)?;
    //                 }
    //             };

    //             let full_sparse_rot7 = {
    //                 // full_sparse_rot7 = low_sparse_rot7 + 4^(11-7) * sparse_mid + 4^(22-7) * sparse_high
    //                 let full_sparse_rot7 = self.allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 7, 0
    //                 )?;

    //                 let t = var.get_value().unwrap();
    //                 let repr = t.into_repr();
    //                 let n = (repr.as_ref()[0] >> 0) & ((1 << SHA256_REG_WIDTH) - 1);
    //                 let m = self.converter_helper(n, SHA256_EXPANSION_BASE, 7, 0);

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
    //                 let full_sparse_rot18 = self.allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 18, 0
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
    //                 // the additional difficulty is that y is itself represented in sparse form
    //                 let r3 = match self.global_strategy {
    //                     GlobalStrategy::UseSpecializedTables => {
    //                         self.query_table1(cs, self.sha256_base4_shift3_table.as_ref().unwrap(), &low)? 
    //                     },
    //                     GlobalStrategy::UseCustomGadgets => {
    //                         let (y, _hb, _lbb) = self.unpack_chunk(cs, sparse_low, SHA256_EXPANSION_BASE)?;
    //                         y
    //                     },
    //                     // work in base 2 and then apply table
    //                     _ => {
    //                         let (y_normal, _hb_normal, _lb_normal) = self.unpack_chunk(cs, low, 2)?;
    //                         let (y, _) = self.query_table2(cs, &self.sha256_base4_rot7_table, &y_normal)?;
    //                         y
    //                     }
    //                 };
              
    //                 let new_val = var.get_value().map( |fr| {
    //                     let input_repr = fr.into_repr();
    //                     let n = input_repr.as_ref()[0] & ((1 << SHA256_REG_WIDTH) - 1);
                        
    //                     let m = map_into_sparse_form(shift_right(n as usize, 3), SHA256_EXPANSION_BASE);
    //                     E::Fr::from_str(&m.to_string()).unwrap()
    //                 });
    //                 let full_sparse_shift3 = AllocatedNum::alloc(cs, || new_val.grab())?;

    //                 // full_sparse_shift3 = sparse_low_shift3 + 4^(11 - 3) * sparse_mid + 4^(22 - 3) * sparse_high
    //                 let shift3_limb_1_shift = Self::u64_exp_to_ff(4, 11 - 3);
    //                 let shift3_limb_2_shift = Self::u64_exp_to_ff(4, 22 - 3);
                    
    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), shift3_limb_1_shift, shift3_limb_2_shift],
    //                     &[r3, sparse_mid, sparse_high],
    //                     &full_sparse_shift3,
    //                 )?;
    //                 full_sparse_shift3
    //             };

    //             // now we have all the components: 
    //             // S7 = full_sparse_rot7, S18 = full_sparse_rot18, R3 = full_sparse_shift3
    //             let t = Num::Allocated(full_sparse_rot7.add_two(cs, full_sparse_rot18, full_sparse_shift_3)?);      
    //             let r = self.normalize(
    //                 cs, &t, 
    //                 &self.sha256_sheduler_xor_table,
    //                 sheduler_xor_normalizer, 
    //                 SHA256_EXPANSION_BASE, 
    //                 self.sheduler_base_num_of_chunks,
    //             )?;
        
    //             return Ok(r);
    //         }
    //     }
    // }

    // // sigma_1(x) = S_17(x) ^ S_19(x) ^ R_10(x)
    // // this function is almost similar to sigma_0(x) except for the following optimization tricks:
    // // in all previous functions we have split x in chunks of equal size (11), now we restrict the lowest chunk to be
    // // 10 bits, so x = | 11 | 11 | 10 | is still 32 bits-length in total
    // // such an unusual split will simplify R_10 in an obvious way
    // fn sigma_1<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: &NumWithTracker<E>) -> Result<Num<E>>
    // {
    //     if let OverflowTracker::SignificantOverflow(n) = input.overflow_tracker {
    //         assert!(n <= 16);
    //     };
        
    //     match &input.num {
    //         Num::Constant(x) => {
    //             let repr = x.into_repr();
    //             // NOTE : think, if it is safe for n to be overflowed
    //             let n = (repr.as_ref()[0] & ((1 << SHA256_REG_WIDTH) - 1)) as usize;

    //             let s17 = rotate_extract(n, 17, 0);
    //             let s19 = rotate_extract(n, 19, 0);
    //             let r10 = shift_right(n, 10);
    //             let res =  Self::u64_to_ff((s17 ^ s19 ^ r10) as u64);

    //             return Ok(Num::Constant(res));
    //         }
    //         Num::Allocated(var) => {
    //             // split our 32bit variable into one 10-bit chunk (lowest one) and two 11-bit chunks:
    //             // there will be three chunks (low, mid, high) for 32bit number
    //             let low = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE-1, 0, 0, 0, 0)?;
    //             let mid = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, SHA256_GADGET_CHUNK_SIZE-1, 0, 0, 0)?;
    //             let high = self.allocate_converted_num(cs, &var, SHA256_GADGET_CHUNK_SIZE, 2*SHA256_GADGET_CHUNK_SIZE-1, 0, 0, 0)?;

    //             let (sparse_low, _) = self.query_table2(cs, &self.sha256_base4_widh10_table, &low)?;
    //             let (sparse_mid, sparse_mid_rot7) = self.query_table2(cs, &self.sha256_base4_rot7_table, &mid)?;
    //             let (sparse_high, _sparse_high_rot7) = self.query_table2(cs, &self.sha256_base4_rot7_table, &high)?;

    //             match input.overflow_tracker 
    //             {
    //                 OverflowTracker::NoOverflow => {
    //                     // compose full normal = low + 2^10 * mid + 2^21 * high
    //                     AllocatedNum::ternary_lc_eq(
    //                         cs, 
    //                         &[E::Fr::one(), Self::u64_exp_to_ff(1 << 10, 0), Self::u64_exp_to_ff(1 << 21, 0)],
    //                         &[low.clone(), mid.clone(), high.clone()],
    //                         &var,
    //                     )?;
    //                 }
    //                 _ => {
    //                     // full normal = low + 2^10 * mid + 2^21 * high - 2^32 * overflow
    //                     // allocate overflow on the next row alongside with the range check
    //                     let of = self.allocate_converted_num(
    //                         cs, &var, RANGE_TABLE_WIDTH, SHA256_REG_WIDTH, 0, 0, 0
    //                     )?;

    //                     AllocatedNum::quartic_lc_eq(
    //                         cs,
    //                         &[E::Fr::one(), Self::u64_to_ff(1 << 10), Self::u64_to_ff(1 << 21), Self::u64_to_ff(1 << 32)],
    //                         &[low.clone(), mid.clone(), high.clone(), of.clone()],
    //                         &var,
    //                     )?;
    //                     self.query_table2(cs, &self.range_table, &of)?;
    //                 }
    //             };

    //             let full_sparse_rot17 = {
    //                 // full_sparse_rot17 = mid_sparse_rot7 + 4^(11-7) * sparse_high + 4^(22-7) * sparse_low
    //                 let full_sparse_rot17 = self.allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 17, 0
    //                 )?;

    //                 let rot17_limb_2_shift = Self::u64_exp_to_ff(4, 11 - 7);
    //                 let rot17_limb_0_shift = Self::u64_exp_to_ff(4, 22 - 7);

    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), rot17_limb_0_shift, rot17_limb_2_shift],
    //                     &[sparse_mid_rot7, sparse_low.clone(), sparse_high.clone()],
    //                     &full_sparse_rot17,
    //                 )?;

    //                 full_sparse_rot17
    //             };

    //             let full_sparse_shift10 = {
    //                 // full_sparse_shift10 = mid_sparse + 4^(11) * sparse_high
    //                 // HERE IS THE CURRENT ERROR!
    //                 let full_sparse_shift10 = self.allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH - 10, 10, SHA256_EXPANSION_BASE, 0, 0,
    //                 )?;
    //                 let dummy = AllocatedNum::alloc_zero(cs)?;

    //                 let shift10_limb_2_shift = Self::u64_exp_to_ff(4, 11);
    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), shift10_limb_2_shift, E::Fr::zero()],
    //                     &[sparse_mid.clone(), sparse_high.clone(), dummy],
    //                     &full_sparse_shift10,
    //                 )?;
    //                 full_sparse_shift10
    //             };

    //             let full_sparse_rot19 = {
    //                 let sparse_mid_rot9 = match self.global_strategy {
    //                     GlobalStrategy::UseSpecializedTables => {
    //                         self.query_table2(cs, self.sha256_base4_rot9_table.as_ref().unwrap(), &mid)?.1 
    //                     },
    //                     GlobalStrategy::UseCustomGadgets => {
    //                         // we already have x = mid_rot7 (in sparse form!) - and we need to rotate it two more bits right
    //                         // in order, to accomplish this we do the following :
    //                         // split x as y| hb | lbb
    //                         // the result, we are looking for is z = lbb | y | hb  
    //                         let (y, hb, lbb) = self.unpack_chunk(cs, sparse_mid, SHA256_EXPANSION_BASE)?;
    //                         let sparse_mid_rot9 = self.allocate_converted_num(
    //                             cs, &mid, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 9, 0
    //                         )?;

    //                         let y_coef = Self::u64_exp_to_ff(4, 1);
    //                         let lbb_coef = Self::u64_exp_to_ff(4, 9);

    //                         AllocatedNum::ternary_lc_eq(
    //                             cs, 
    //                             &[E::Fr::one(), y_coef, lbb_coef],
    //                             &[hb, y, lbb],
    //                             &sparse_mid_rot9,
    //                         )?;
    //                         sparse_mid_rot9
    //                     },
                        
    //                     _ => {
    //                         // a bit hacky!
    //                         let sparse_mid_rot9 = self.allocate_converted_num(
    //                             cs, &mid, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 9, 0
    //                         )?;
    //                         let (y_normal, hb_normal, lbb_normal) = self.unpack_chunk(cs, mid.clone(), 2)?;
    //                         let dummy = AllocatedNum::alloc_zero(cs)?;

    //                         let y_coef = Self::u64_to_ff(1 << 1);
    //                         let tmp = AllocatedNum::ternary_lc_with_const(
    //                             cs, 
    //                             &[E::Fr::one(), y_coef, E::Fr::zero()],
    //                             &[hb_normal, y_normal, dummy.clone()],
    //                             &E::Fr::zero(),
    //                         )?;

    //                         let (_, sparse_mid_rot9_a) = self.query_table2(cs, &self.sha256_base4_rot7_table, &tmp)?;
    //                         let (sparse_mid_rot9_b, _) = self.query_table2(cs, &self.sha256_base4_rot7_table, &lbb_normal)?;
                            
    //                         AllocatedNum::ternary_lc_eq(
    //                             cs, 
    //                             &[E::Fr::one(), Self::u64_exp_to_ff(4, 32 - 9), E::Fr::zero()],
    //                             &[sparse_mid_rot9_a, sparse_mid_rot9_b, dummy],
    //                             &sparse_mid_rot9
    //                         )?;

    //                         sparse_mid_rot9
    //                     },
    //                 };

    //                 // full_sparse_rot19 = mid_sparse_rot9 + 4^(11-9) * sparse_high + 4^(22-9) * sparse_low
    //                 let full_sparse_rot19 = self.allocate_converted_num(
    //                     cs, &var, SHA256_REG_WIDTH, 0, SHA256_EXPANSION_BASE, 19, 0
    //                 )?;
              
    //                 let rot19_limb_0_shift = Self::u64_exp_to_ff(4, 22 - 9);
    //                 let rot19_limb_2_shift = Self::u64_exp_to_ff(4, 11 - 9);

    //                 AllocatedNum::ternary_lc_eq(
    //                     cs, 
    //                     &[E::Fr::one(), rot19_limb_0_shift, rot19_limb_2_shift],
    //                     &[sparse_mid_rot9, sparse_low, sparse_high],
    //                     &full_sparse_rot19,
    //                 )?;
    //                 full_sparse_rot19
    //             };

    //             let t = Num::Allocated(full_sparse_rot17.add_two(cs, full_sparse_rot19, full_sparse_shift10)?);     
    //             let r = self.normalize(
    //                 cs, &t, 
    //                 &self.sha256_sheduler_xor_table,
    //                 sheduler_xor_normalizer, 
    //                 SHA256_EXPANSION_BASE, 
    //                 self.sheduler_base_num_of_chunks,
    //             )?;
        
    //             return Ok(r);
    //         }
    //     }
    // }

    // // Expanded message blocks W0, W1, ..., W63 are computed from [M0, ..., M15] as follows via the
    // // SHA-256 message schedule:
    // // Wj = Mj for j = [0; 15]
    // // For j = 16 to 63:
    // //      Wj = sigma_1(W_{j-2}) + W_{j-7} + sigma_0(W_{j-15}) + W_{j-16}
    // // where 
    // //      sigma_0(x) = S_7(x) ^ S_18(x) ^ R_3(x)
    // //      sigma_1(x) = S_17(x) ^ S_19(x) ^ R_10(x)
    // // here S_n - is right circular n-bit rotation
    // // and R_n - right n-nit shift
    // fn message_expansion<CS: ConstraintSystem<E>>(&self, cs: &mut CS, message: &[Num<E>]) -> Result<Vec<NumWithTracker<E>>>
    // {
    //     assert_eq!(message.len(), 16);
    //     let mut res : Vec<NumWithTracker<E>> = Vec::with_capacity(64);

    //     for i in 0..16 {
    //         res.push(message[i].clone().into());
    //     }

    //     for j in 16..64 {
    //         let tmp1 = self.sigma_1(cs, &res[j - 2])?;
    //         let tmp2 = self.sigma_0(cs, &res[j - 15])?;

    //         let var_args = &[tmp1, res[j-7].num.clone(), tmp2, res[j-16].num.clone()];
    //         let of_vec = vec![
    //             OverflowTracker::NoOverflow, OverflowTracker::NoOverflow, res[j-7].overflow_tracker, res[j-16].overflow_tracker
    //         ];
    //         // TODO: use negative DIALATION for tmp2
    //         //println!("RRR");
    //         let tmp3 = NumWithTracker {
    //             num: Num::sum(cs, var_args)?,
    //             overflow_tracker: self.deduce_of(of_vec),
    //         }; 
    //         res.push(tmp3);
    //     }

    //     Ok(res)
    // }

    // fn optimized_extact_32_from_tracked_num<CS: ConstraintSystem<E>>(&self, cs: &mut CS, input: NumWithTracker<E>) -> Result<Num<E>> 
    // {
    //     let res = match input.overflow_tracker {
    //         OverflowTracker::NoOverflow => input.num,
    //         _ => match &input.num {
    //             Num::Constant(fr) => {
    //                 let repr = fr.into_repr();
    //                 let n = repr.as_ref()[0] & ((1 << 32) - 1); 
    //                 Num::Constant(Self::u64_to_ff(n))
    //             }
    //             Num::Allocated(var) => {
    //                 let low = self.allocate_converted_num(cs, var, RANGE_TABLE_WIDTH, 0, 0, 0, 0)?;
    //                 let high = self.allocate_converted_num(cs, var, RANGE_TABLE_WIDTH, RANGE_TABLE_WIDTH, 0, 0, 0)?;
    //                 let of = self.allocate_converted_num(cs, var, RANGE_TABLE_WIDTH, RANGE_TABLE_WIDTH * 2, 0, 0, 0)?;

    //                 // we will have three rows: first row - range check for low, second for high, third for of
    //                 // apart from range checks we will pack arithmetic
    //                 // row1 : low, 0, 0, 0 - no additional constraints
    //                 // row2: high, 0, low, extracted - low + 2^32 * high = extracted
    //                 // row3: of, 0, extracted, input - extracted + of*2^32 = input
                    
    //                 let table = &self.range_table;
    //                 let mut minus_one = E::Fr::one();
    //                 minus_one.negate();
    //                 let dummy = AllocatedNum::alloc_zero(cs)?;
    //                 let extracted = AllocatedNum::alloc(cs, || {
    //                     let low = low.get_value().grab()?;
    //                     let high = high.get_value().grab()?;
    //                     let mut tmp = Self::u64_to_ff(1 << 16);
    //                     tmp.mul_assign(&high);
    //                     tmp.add_assign(&low);
    //                     Ok(tmp)
    //                 })?;
    //                 let range_of_linear_terms = CS::MainGate::range_of_linear_terms();

    //                 let _first_row = self.query_table2(cs, table, &low)?;

    //                 // second row
    //                 cs.begin_gates_batch_for_step()?;
    //                 let vars = [high.get_variable(), dummy.get_variable(), low.get_variable(), extracted.get_variable()];
    //                 let coeffs = [Self::u64_to_ff(1 << 16), E::Fr::zero(), E::Fr::one(), minus_one.clone()];
                    
    //                 cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
                    
    //                 let mut gate_term = MainGateTerm::new();
    //                 let (_, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy.get_variable())?;
    //                 for (idx, coef) in range_of_linear_terms.clone().zip(coeffs.iter()) {
    //                     local_coeffs[idx] = coef.clone();
    //                 }

    //                 let mg = CS::MainGate::default();
    //                 cs.new_gate_in_batch(
    //                     &mg,
    //                     &local_coeffs,
    //                     &vars,
    //                     &[]
    //                 )?;

    //                 cs.end_gates_batch_for_step()?;
                    
    //                 // third row 
    //                 cs.begin_gates_batch_for_step()?;
    //                 let vars = [of.get_variable(), dummy.get_variable(), extracted.get_variable(), var.get_variable()];
    //                 let coeffs = [Self::u64_to_ff(1 << 32), E::Fr::zero(), E::Fr::one(), minus_one.clone()];
                    
    //                 cs.apply_single_lookup_gate(&vars[..table.width()], table.clone())?;
                    
    //                 let mut gate_term = MainGateTerm::new();
    //                 let (_, mut local_coeffs) = CS::MainGate::format_term(gate_term, dummy.get_variable())?;
    //                 for (idx, coef) in range_of_linear_terms.zip(coeffs.iter()) {
    //                     local_coeffs[idx] = coef.clone();
    //                 }

    //                 let mg = CS::MainGate::default();
    //                 cs.new_gate_in_batch(
    //                     &mg,
    //                     &local_coeffs,
    //                     &vars,
    //                     &[]
    //                 )?;

    //                 cs.end_gates_batch_for_step()?;

    //                 Num::Allocated(extracted)
    //             }
    //         }
    //     };
        
    //     Ok(res)
    // }
                    
    // // finally! the only one exported function
    // pub fn sha256<CS: ConstraintSystem<E>>(&self, cs: &mut CS, message: &[Num<E>]) -> Result<[Num<E>; 8]>
    // {    
    //     // we assume that input is already well-padded
    //     assert!(message.len() % 16 == 0);
        
    //     let mut regs = Sha256Registers {
    //         a: Num::Constant(self.iv[0].clone()).into(),
    //         b: Num::Constant(self.iv[1].clone()).into(),
    //         c: Num::Constant(self.iv[2].clone()).into(),
    //         d: Num::Constant(self.iv[3].clone()).into(),
    //         e: Num::Constant(self.iv[4].clone()).into(),
    //         f: Num::Constant(self.iv[5].clone()).into(),
    //         g: Num::Constant(self.iv[6].clone()).into(),
    //         h: Num::Constant(self.iv[7].clone()).into(),
    //     };

    //     for block in message.chunks(16) {
    //         let expanded_block = self.message_expansion(cs, block)?;
    //         regs = self.sha256_inner_block(cs, regs, &expanded_block[..], &self.round_constants)?;
    //     }

    //     let res = [
    //         self.optimized_extact_32_from_tracked_num(cs, regs.a)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.b)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.c)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.d)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.e)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.f)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.g)?,
    //         self.optimized_extact_32_from_tracked_num(cs, regs.h)?,
    //     ];
    //     Ok(res)
    // }
}
   






