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
use super::utils::*;
use crate::plonk::better_better_cs::gadgets::assignment::{
    Assignment
};

use std::sync::Arc;
use std::collections::HashMap;
use std::cell::RefCell;
use std::ops::{Index, IndexMut};

use crate::num_bigint::BigUint;
use crate::num_traits::cast::ToPrimitive;
use crate::num_traits::{Zero, One};
use itertools::Itertools;

type Result<T> = std::result::Result<T, SynthesisError>;


// keccak full_width = 1600 bits = 200 bytes
// rate = 136 byte = 1088 bits = 17 (64-bit) words
const KECCAK_RATE_WORDS_SIZE : usize = 17;
const KECCAK_DIGEST_WORDS_SIZE : usize = 4;
const DEFAULT_BINARY_NUM_OF_CHUNKS : usize = 16; // 2^16 is fine
const DEFAULT_FIRST_BASE_NUM_OF_CHUNKS : usize = 4; 
const DEFAULT_OF_FIRST_BASE_NUM_OF_CHUNKS : usize = 2;
const DEFAULT_SECOND_BASE_NUM_OF_CHUNKS : usize = 5;
const BINARY_BASE: u64 = 2;
// keccak state has 5 x 5 x 64 - bits, 
// each row of 64 bits is a lane.
const KECCAK_STATE_WIDTH : usize = 5;
const KECCAK_LANE_WIDTH : usize = 64;
const KECCAK_NUM_ROUNDS : usize = 24;
#[derive(Clone)]
pub struct KeccakState<E: Engine>([[Num<E>; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH]);

impl<E: Engine> Default for KeccakState<E> {
    fn default() -> Self {
        KeccakState(<[[Num<E>; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH]>::default())
    }
}

impl<E: Engine> Index<(usize, usize)> for KeccakState<E> {
    type Output = Num<E>;

    fn index(&self, index: (usize, usize)) -> &Self::Output {
        assert!(index.0 < KECCAK_STATE_WIDTH);
        assert!(index.1 < KECCAK_STATE_WIDTH);

        &self.0[index.0][index.1]
    }
}

impl<E: Engine> IndexMut<(usize, usize)> for KeccakState<E> {
    fn index_mut(&mut self, index: (usize, usize)) -> &mut Self::Output {
        assert!(index.0 < KECCAK_STATE_WIDTH);
        assert!(index.1 < KECCAK_STATE_WIDTH);

        &mut self.0[index.0][index.1]
    }
}

pub struct KeccakGadget<E: Engine> {
    // table used to convert binary register into first_sparse_base
    binary_to_first_base_converter_table: Arc<LookupTableApplication<E>>,
    // tables used to convert elements from first_sparse base into second - standard and overflow friendly
    first_to_second_base_converter_table: Arc<LookupTableApplication<E>>,
    of_first_to_second_base_converter_table: Arc<LookupTableApplication<E>>,
    // small range table for overflows
    ternary_range_table: Arc<LookupTableApplication<E>>,
    // table used to convert elements from second base: either to binary form or back to first sparse base
    from_second_base_converter_table: Arc<LookupTableApplication<E>>,
    
    binary_base_num_of_chunks: usize,
    first_base_num_of_chunks: usize,
    of_first_base_num_of_chunks: usize,
    range_table_lower_bound: usize,
    range_table_upper_bound : usize,
    second_base_num_of_chunks: usize,

    allocated_cnsts : RefCell<HashMap<E::Fr, AllocatedNum<E>>>,
    offsets : [[usize; KECCAK_STATE_WIDTH]; KECCAK_STATE_WIDTH],
    round_cnsts : [E::Fr; KECCAK_NUM_ROUNDS],
}

impl<E: Engine> KeccakGadget<E> {
    pub fn new<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        binary_base_num_of_chunks: Option<usize>,
        first_base_num_of_chunks: Option<usize>,
        of_first_base_num_of_chunks: Option<usize>,
        second_base_num_of_chunks: Option<usize>,
    ) -> Result<Self> 
    {
        let binary_base_num_of_chunks = binary_base_num_of_chunks.unwrap_or(DEFAULT_BINARY_NUM_OF_CHUNKS);
        let first_base_num_of_chunks = first_base_num_of_chunks.unwrap_or(DEFAULT_FIRST_BASE_NUM_OF_CHUNKS);
        let of_first_base_num_of_chunks = of_first_base_num_of_chunks.unwrap_or(DEFAULT_OF_FIRST_BASE_NUM_OF_CHUNKS);
        let second_base_num_of_chunks = second_base_num_of_chunks.unwrap_or(DEFAULT_SECOND_BASE_NUM_OF_CHUNKS);
        let range_table_lower_bound = 1usize;
        let range_table_upper_bound = first_base_num_of_chunks;
        
        let columns3 = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "binary_to_first_base_converter_table";
        let binary_to_first_base_converter_table = LookupTableApplication::new(
            name1,
            ExtendedBaseConverterTable::new(binary_base_num_of_chunks, BINARY_BASE, KECCAK_FIRST_SPARSE_BASE, |x| {x}, name1),
            columns3.clone(),
            true
        );

        let name2 : &'static str = "first_to_second_base_converter_table";
        let f = |x| { keccak_u64_first_conveter(x)};
        let first_to_second_base_converter_table = LookupTableApplication::new(
            name2,
            ExtendedBaseConverterTable::new(first_base_num_of_chunks, KECCAK_FIRST_SPARSE_BASE, KECCAK_SECOND_SPARSE_BASE, f, name2),
            columns3.clone(),
            true
        );

        let name3 : &'static str = "of_first_to_second_base_converter_table";
        let f = |x| { keccak_u64_first_conveter(x)};
        let of_first_to_second_base_converter_table = LookupTableApplication::new(
            name3,
            OverflowFriendlyBaseConverterTable::new(
                first_base_num_of_chunks, KECCAK_FIRST_SPARSE_BASE, KECCAK_SECOND_SPARSE_BASE, KECCAK_LANE_WIDTH as u64, f, name3
            ),
            columns3.clone(),
            true
        );

        let name4 : &'static str = "ternary_range_table";
        let f = |x| { keccak_u64_second_converter(x)};
        let ternary_range_table = LookupTableApplication::new(
            name4,
            TinyRangeTable::new(range_table_lower_bound, range_table_upper_bound, name4),
            columns3.clone(),
            true
        );
        
        let name5 : &'static str = "from_second_base_converter_table";
        let from_second_base_converter_table = LookupTableApplication::new(
            name5,
            MultiBaseConverterTable::new(
                second_base_num_of_chunks, KECCAK_SECOND_SPARSE_BASE, KECCAK_FIRST_SPARSE_BASE, BINARY_BASE, f, name5
            ),
            columns3.clone(),
            true
        );

        let binary_to_first_base_converter_table = cs.add_table(binary_to_first_base_converter_table)?;
        let first_to_second_base_converter_table = cs.add_table(first_to_second_base_converter_table)?;
        let of_first_to_second_base_converter_table = cs.add_table(of_first_to_second_base_converter_table)?;
        let ternary_range_table = cs.add_table(ternary_range_table)?;
        let from_second_base_converter_table = cs.add_table(from_second_base_converter_table)?;

        let allocated_cnsts = RefCell::new(HashMap::new());

        let offsets = [
            [64, 28, 61, 46, 23], 
            [63, 20, 54, 19, 62], 
            [2, 58, 21, 49, 3], 
            [36, 9, 39, 43, 8], 
            [37, 44, 25, 56, 50]
        ];

        let f = |mut input: u64| -> E::Fr {
            let mut acc = BigUint::default(); 
            let mut base = BigUint::one();
 
            while input > 0 {
                let bit = input & 1;
                input >>= 1;
                acc += bit * base.clone();
                base *= KECCAK_SECOND_SPARSE_BASE;
            }

            let res = E::Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
            res
        };
        let round_cnsts = [
            f(0x0000000000000001), f(0x0000000000008082), f(0x800000000000808A), f(0x8000000080008000),
            f(0x000000000000808B), f(0x0000000080000001), f(0x8000000080008081), f(0x8000000000008009),
            f(0x000000000000008A), f(0x0000000000000088), f(0x0000000080008009), f(0x000000008000000A),
            f(0x000000008000808B), f(0x800000000000008B), f(0x8000000000008089), f(0x8000000000008003),
            f(0x8000000000008002), f(0x8000000000000080), f(0x000000000000800A), f(0x800000008000000A),
            f(0x8000000080008081), f(0x8000000000008080), f(0x0000000080000001), f(0x8000000080008008),
        ];

        Ok(KeccakGadget {
            binary_to_first_base_converter_table,
            first_to_second_base_converter_table,
            of_first_to_second_base_converter_table,
            ternary_range_table,
            from_second_base_converter_table,
    
            binary_base_num_of_chunks,
            first_base_num_of_chunks,
            of_first_base_num_of_chunks,
            range_table_lower_bound,
            range_table_upper_bound,
            second_base_num_of_chunks,

            allocated_cnsts,
            offsets,
            round_cnsts,
        })
    }

    // returns closets upper integer to a / b
    fn round_up(a: usize, b : usize) -> usize {
        let additional_chunks : usize = if a % b > 0 {1} else {0};
        a/b + additional_chunks
    }

    // for row of the form [x, f(x), g(x), acc] do:
    // table query x => f(x), g(x)
    // running sum for input: acc_next = acc - coef * x
    // if is_final is set, simply check: acc = coef * x
    // returns (f(x), g(x), acc_next)
    fn query_table_accumulate<CS: ConstraintSystem<E>>(
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

    fn rotate_and_convert(&self, fr: &E::Fr, rot: usize) -> E::Fr
    {
        let mut input = BigUint::default();
        let fr_repr = fr.into_repr();
        for n in fr_repr.as_ref().iter().rev() {
            input <<= 64;
            input += *n;
        }

        let mut acc = BigUint::default(); 
        let init_base = biguint_pow(KECCAK_FIRST_SPARSE_BASE as usize, KECCAK_LANE_WIDTH - rot);
        let mut base = init_base;
        let mut iter_n = 0;
        let mut special_chunk = 0;

        for (is_first, is_last, i) in (0..(KECCAK_LANE_WIDTH + 1)).identify_first_last() {
            let remainder = (input.clone() % BigUint::from(KECCAK_FIRST_SPARSE_BASE)).to_u64().unwrap();
            if is_first || is_last {
                special_chunk += remainder;
            }
            else {
                let output_chunk = keccak_u64_second_converter(remainder);
                acc += base.clone() * output_chunk;
            }
            
            input /= KECCAK_FIRST_SPARSE_BASE;
            base *= KECCAK_SECOND_SPARSE_BASE;
            iter_n += 1;

            if iter_n == rot {
                base = BigUint::one();
            } 
        }

        acc += keccak_u64_second_converter(special_chunk) * init_base;
        let res = E::Fr::from_str(&acc.to_str_radix(10)).expect("should parse");
        res
    }

    fn theta<CS: ConstraintSystem<E>>(&self, cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut C = Vec::with_capacity(KECCAK_LANE_WIDTH);
        // calculate C[x] for each column:
        for i in 0..KECCAK_LANE_WIDTH {
            C.push(Num::sum(cs, &state.0[i])?);
        }

        // recalculate state
        let coeffs = [E::Fr::one(), E::Fr::one(), u64_to_ff(KECCAK_FIRST_SPARSE_BASE)];
        let mut new_state = KeccakState::default();
        for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            let inputs = [state[(i, j)].clone(), C[(i-1) % KECCAK_LANE_WIDTH].clone(), C[(i+1) % KECCAK_LANE_WIDTH].clone()];
            new_state[(i, j)] = Num::lc(cs, &coeffs, &inputs[..])?;
        }
        Ok(new_state)   
    }

    fn pi<CS: ConstraintSystem<E>>(&self, _cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut new_state = KeccakState::default();
        for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            new_state[(i, j)] = state[((i + 3*j) % KECCAK_LANE_WIDTH, i)].clone();
        }
        Ok(new_state)
    }

    fn xi_i<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: KeccakState<E>, round: usize, elems_to_squeeze: usize, is_final: bool,
    ) -> Result<(KeccakState<E>, Vec<Num<E>>)> 
    {
        let mut new_state = KeccakState::default();
        let mut iter_count = 0;
        let coeffs = [u64_to_ff(2), E::Fr::one(), u64_to_ff(3), E::Fr::one()];
        let mut squeezed = Vec::with_capacity(elems_to_squeeze);
        
        let num_of_chunks = self.second_base_num_of_chunks;
        let num_slices = Self::round_up(KECCAK_LANE_WIDTH, num_of_chunks);
                    
        let input_slice_modulus = pow(KECCAK_SECOND_SPARSE_BASE as usize, num_of_chunks);
        let output1_slice_modulus = pow(KECCAK_FIRST_SPARSE_BASE as usize, num_of_chunks);
        let output2_slice_modulus = pow(BINARY_BASE as usize, num_of_chunks);

        let input_slice_modulus_fr = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, num_of_chunks as u64);
        let output1_slice_modulus_fr = u64_exp_to_ff(KECCAK_FIRST_SPARSE_BASE, num_of_chunks as u64);
        let output2_slice_modulus_fr = u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, num_of_chunks as u64);

        for (j, i) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
            // A′[x, y,z] = A[x, y,z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) ⋅ A[(x+2) mod 5, y, z]).
            // the corresponding algebraic transform is y = 2a + b + 3c +2d
            // d is always constant and nonzero only for lane[0][0]
            let d = if i == 0  && j == 0 { Num::Constant(self.round_cnsts[round].clone()) } else { Num::default() };
            let b = state[((i+1 % KECCAK_STATE_WIDTH), j)].clone();
            let c = state[((i+2 % KECCAK_STATE_WIDTH), j)].clone();
            let inputs = [state[(i, j)].clone(), b, c, d];
            let lc = Num::lc(cs, &coeffs, &inputs)?;

            match lc {
                Num::Constant(fr) => {
                    new_state[(i, j)] = Num::Constant(keccak_ff_second_converter(fr, KECCAK_FIRST_SPARSE_BASE));
                    if iter_count < elems_to_squeeze {
                        squeezed.push(Num::Constant(keccak_ff_second_converter(fr, BINARY_BASE)));
                    }
                }
                Num::Allocated(var) => {
                    let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    let mut output1_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    let mut output2_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);

                    match var.get_value() {
                        None => {
                            for _ in 0..num_slices {
                                let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
                                input_slices.push(tmp);
                            }
                        },
                        Some(f) => {
                            // here we have to operate on row biguint number
                            let mut big_f = BigUint::default();
                            let f_repr = f.into_repr();
                            for n in f_repr.as_ref().iter().rev() {
                                big_f <<= 64;
                                big_f += *n;
                            } 

                            for _ in 0..num_slices {
                                let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
                                let new_val = u64_to_ff(remainder);
                                big_f /= input_slice_modulus;
                                let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
                                input_slices.push(tmp);
                            }

                            assert!(big_f.is_zero());
                        }
                    }

                    let mut coef = E::Fr::one();
                    let mut acc = var.clone();
                    for (_is_first, is_last, input_chunk) in input_slices.iter().identify_first_last() {
                        let (output1, output2, new_acc) = self.query_table_accumulate(
                            cs, &self.from_second_base_converter_table, input_chunk, &acc, &coef, is_last
                        )?; 

                        coef.mul_assign(&input_slice_modulus_fr);
                        acc = new_acc;
                    }

                    if !is_final {
                        let mut output1_total = AllocatedNum::alloc(cs, || {
                            let fr = var.get_value().grab()?;
                            Ok(keccak_ff_second_converter(fr, KECCAK_FIRST_SPARSE_BASE))
                        })?;

                        AllocatedNum::long_weighted_sum_eq(cs, &output1_slices[..], &output1_slice_modulus_fr, &output1_total)?;
                        new_state[(i, j)] = Num::Allocated(output1_total);
                    }

                    if iter_count < elems_to_squeeze {
                        let mut output2_total = AllocatedNum::alloc(cs, || {
                            let fr = var.get_value().grab()?;
                            Ok(keccak_ff_second_converter(fr, BINARY_BASE))
                        })?;

                        AllocatedNum::long_weighted_sum_eq(cs, &output2_slices[..], &output2_slice_modulus_fr, &output2_total)?;
                        squeezed.push(Num::Allocated(output2_total));
                    }
                }
            }
        }

        Ok((new_state, squeezed))
    }

    fn check_offset(&self, cur_offset: usize, max_offset: usize, is_first_iter: bool) -> Option<usize> {
        if is_first_iter && (cur_offset < max_offset) && (cur_offset + self.of_first_base_num_of_chunks > max_offset) {
            return Some(max_offset - cur_offset);
        }
        if !is_first_iter && (cur_offset < max_offset) && (cur_offset + self.first_base_num_of_chunks > max_offset) {
            return Some(max_offset - cur_offset);
        }
        if (cur_offset < KECCAK_LANE_WIDTH) && (cur_offset + self.first_base_num_of_chunks > KECCAK_LANE_WIDTH) {
            return Some(max_offset - cur_offset);
        }
        return None;
    }

    //we unite /rho (rotate) and conversion (FIRST_SPARSE_BASE -> SECOND_SPARSE_BASE) in one function
    // fn rho<CS: ConstraintSystem<E>>(&self, state: KeccakState<E>) -> Result<KeccakState<E>> {
    //     let mut new_state = KeccakState::default();
    //     let mut of_map : std::collections::HashMap<usize, Vec<AllocatedNum<E>>> = HashMap::new();
    //     let num_slices = Self::round_up(KECCAK_LANE_WIDTH - self.of_first_base_num_of_chunks -1, self.first_base_num_of_chunks) + 3;  
        
    //     let input_slice_modulus = pow(KECCAK_FIRST_SPARSE_BASE as usize, self.first_base_num_of_chunks);
    //     let output_slice_modulus = pow(KECCAK_SECOND_SPARSE_BASE as usize, self.second_base_num_of_chunks);

    //     for (i, j) in (0..KECCAK_LANE_WIDTH).cartesian_product(0..KECCAK_LANE_WIDTH) {
    //         let offset = self.offsets[i][j];

    //         match state[(i, j)] {
    //             Num::Constant(fr) => {
    //                 new_state[(i, j)] = self.rotate_and_convert(fr, offset);
    //             }
    //             Num::Allocated(var) => {
    //                 let mut input_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
    //                 let mut output_slices : Vec<AllocatedNum<E>> = Vec::with_capacity(num_slices);
                    
    //                 let mut big_f = BigUint::default();
    //                 let mut cur_offset = 0;

    //                 let total_output = match var.get_value() {
    //                     None => AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?,
    //                     Some(fr) => {
    //                         let fr_repr = fr.into_repr();
    //                         for n in fr_repr.as_ref().iter().rev() {
    //                             big_f <<= 64;
    //                             big_f += *n;
    //                         } 
    //                         AllocatedNum::alloc(cs, || fr)
    //                     }
    //                 };
    //                 let mut cur_acc = total_output;

    //                 // first iterator: work on it separately
    //                 let offset_ic = self.check_offset(cur_offset, offset, true);
    //                 match 

    //                 let mut is_first_iter = true;
    //                 while cur_offset < KECCAK_LANE_WIDTH {
                        
    //                     is_first_iter = false; 
    //                 }

    //                 match var.get_value() {
    //                     None => {
    //                         while cur_offset < KECCAK_LANE_WIDTH {

    //                         }
    //                         for _ in 0..num_slices {
    //                             let tmp = AllocatedNum::alloc(cs, || Err(SynthesisError::AssignmentMissing))?;
    //                             input_slices.push(tmp);
    //                         }
    //                     },
    //                     Some(f) => {
    //                         // here we have to operate on row biguint number
    //                         let mut big_f = BigUint::default();
    //                         let f_repr = f.into_repr();
    //                         for n in f_repr.as_ref().iter().rev() {
    //                             big_f <<= 64;
    //                             big_f += *n;
    //                         } 

    //                         for _ in 0..num_slices {
    //                             let remainder = (big_f.clone() % BigUint::from(input_slice_modulus)).to_u64().unwrap();
    //                             let new_val = u64_to_ff(remainder);
    //                             big_f /= input_slice_modulus;
    //                             let tmp = AllocatedNum::alloc(cs, || Ok(new_val))?;
    //                             input_slices.push(tmp);
    //                         }

    //                         assert!(big_f.is_zero());
    //                     }
    //                 }

    //                 let mut coef = E::Fr::one();
    //                 let mut acc = var.clone();
    //                 for (_is_first, is_last, input_chunk) in input_slices.iter().identify_first_last() {
    //                     let (output1, output2, new_acc) = self.query_table_accumulate(
    //                         cs, &self.from_second_base_converter_table, input_chunk, &acc, &coef, is_last
    //                     )?; 

    //                     coef.mul_assign(&input_slice_modulus_fr);
    //                     acc = new_acc;
    //                 }
    //         ;


            
    //         let mut coef = if offset > 0 { 
    //             u64_exp_to_ff(KECCAK_SECOND_SPARSE_BASE, KECCAK_LANE_WIDTH - offset) 
    //         } else 
    //         { 
    //             E::Fr::one() 
    //         };

    //         let mut cur_offset = 0;
            
    //     }

    //     Ok(new_state) 
    // }

    // we assume that data is split into 64-bit words
    pub fn digest<CS: ConstraintSystem<E>>(&self, cs: &mut CS, data: &[Num<E>]) -> Result<Vec<Num<E>>> {
        
    } 

    fn keccak_f<CS: ConstraintSystem<E>>(
        &self, cs: &mut CS, state: KeccakState<E>, elems_to_squeeze: usize, is_final: bool,
    ) -> Result<(KeccakState<E>, Vec<Num<E>>)>
    {
        let mut state = KeccakState::default();
        for (_is_first, is_last, _i) in 0..KECCAK_NUM_ROUNDS {

        }
    } 



}