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

type Result<T> = std::result::Result<T, SynthesisError>;


// keccak full_width = 1600 bits = 200 bytes
// rate = 136 byte = 1088 bits
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
            [0, 28, 61, 46, 23], 
            [63, 20, 54, 19, 62], 
            [2, 58, 21, 49, 3], 
            [36, 9, 39, 43, 8], 
            [37, 44, 25, 56, 50]
        ];

        let f = |input: u64| -> E::Fr {
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
        let round_constants = [
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
            round_constants,
        })
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
        for (i, j) in (0..KECCAK_LANE_WIDTH).zip(0..KECCAK_LANE_WIDTH) {
            let inputs = [state[(i, j)].clone(), C[(i-1) % KECCAK_LANE_WIDTH].clone(), C[(i+1) % KECCAK_LANE_WIDTH].clone()];
            new_state[(i, j)] = Num::lc(cs, &coeffs, &inputs[..])?;
        }
        Ok(new_state)   
    }

    fn pi<CS: ConstraintSystem<E>>(&self, _cs: &mut CS, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut new_state = KeccakState::default();
        for (i, j) in (0..KECCAK_LANE_WIDTH).zip(0..KECCAK_LANE_WIDTH) {
            new_state[(i, j)] = state[((i + 3*j) % KECCAK_LANE_WIDTH, i)].clone();
        }
        Ok(new_state)
    }

    fn xi_i<CS>(&self, state: KeccakState<E>, round: usize, squeeze: u64, is_final: bool) -> Result<(KeccakState<E>, Vec<Num<E>>)> 
    where CS: ConstraintSystem<E>
    {
        let mut new_state = KeccakState::default();
        let mut iter_count = 0;
        let coeffs = [u64_to_ff(2), E::Fr::one(), u64_to_ff(3), E::Fr::one()];

        for (i, j) in (0..KECCAK_LANE_WIDTH).zip(0..KECCAK_LANE_WIDTH) {
            // A′[x, y,z] = A[x, y,z] ⊕ ((A[(x+1) mod 5, y, z] ⊕ 1) ⋅ A[(x+2) mod 5, y, z]).
            // the corresponding algebraic transform is y = 2a + b + 3c +2d
            // d is always constant and nonzero only for lane[0][0]
            let d = if i == 0  && j == 0 { self.round_cnsts } else { Num::default() };
            let inputs = [state[(i, j)].clone(), state[((i+1 % KECCAK_STATE_WIDTH), y)], state[((i+2 % KECCAK_STATE_WIDTH), y)], d];
            let lc = Num::lc(cs, &coeffs, &inputs)?;

            match lc {
                Num::Constant(fr)
            }
        }
    }

    // we unite /rho (rotate) and conversion (FIRST_SPARSE_BASE -> SECOND_SPARSE_BASE) in one function
    fn rho<CS: ConstraintSystem<E>>(&self, state: KeccakState<E>) -> Result<KeccakState<E>> {
        let mut new_state = KeccakState::default();
        let mut arr1 
        let mut arr2
        let mut arr3

        for (i, j) in (0..KECCAK_LANE_WIDTH).zip(0..KECCAK_LANE_WIDTH) {
            let offset = self.offsets[i][j];

        } 
    }

}