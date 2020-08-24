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

use super::utils::*;
use super::tables::*;
use super::custom_gates::*;
use std::sync::Arc;


type Result<T> = std::result::Result<T, SynthesisError>;


pub struct SparseChValue<E: Engine> {
    normal: Num<E>,
    sparse: Num<E>,
    // all rots are in sparse representation as well
    rot6: Num<E>,
    rot11: Num<E>,
    rot25: Num<E>,
}


pub struct SparseMajValue<E: Engine> {
    normal: Num<E>,
    sparse: Num<E>,
    rot2: Num<E>,
    rot13: Num<E>,
    rot22: Num<E>,
}


pub struct Sha256GadgetParams<E: Engine> {
    //num_of_blocks: usize,
    sha256_base7_rot6_table: Arc<LookupTableApplication<E>>,
    sha256_base7_rot3_extr10_table: Arc<LookupTableApplication<E>>,
    _marker: std::marker::PhantomData<E>,
}

const CH_GADGET_CHUNK_SIZE : usize = 11; 


impl<E: Engine> Sha256GadgetParams<E> {

    pub fn new<CS: ConstraintSystem<E>>(cs: &mut CS) -> Result<Self> {

        let columns = vec![
            PolyIdentifier::VariablesPolynomial(0), 
            PolyIdentifier::VariablesPolynomial(1), 
            PolyIdentifier::VariablesPolynomial(2)
        ];

        let name1: &'static str = "sha256_base7_rot6_table";
        let sha256_base7_rot6_table = LookupTableApplication::new(
            name1,
            Sha256SparseRotateTable::new(CH_GADGET_CHUNK_SIZE, 6, 0, SHA256_CHOOSE_BASE, name1),
            columns.clone(),
            true
        );

        let name2 : &'static str = "sha256_base7_rot3_extr10_table";
        let sha256_base7_rot3_extr10_table = LookupTableApplication::new(
            name2,
            Sha256SparseRotateTable::new(CH_GADGET_CHUNK_SIZE, 3, CH_GADGET_CHUNK_SIZE-1, SHA256_CHOOSE_BASE, name2),
            columns.clone(),
            true
        );

        let sha256_base7_rot6_table = cs.add_table(sha256_base7_rot6_table)?;
        let sha256_base7_rot3_extr10_table = cs.add_table(sha256_base7_rot3_extr10_table)?;
    
        Ok(Sha256GadgetParams {
            sha256_base7_rot6_table,
            sha256_base7_rot3_extr10_table,
            _marker : std::marker::PhantomData,
        })
    }

    // here we assume that maximal overflow is not more than 2 bits
    // we return both the extracted 32bit value and the overflow
    fn extract_32_from_constant(x: &E::Fr) -> (E::Fr, E::Fr) {
        let mut repr = x.into_repr();
        let mut of_repr = repr.clone();
        
        repr.as_mut()[0] &= (1 << 32) - 1; 
        let extracted = E::Fr::from_repr(repr).expect("should decode");

        of_repr.as_mut()[0] >>= 32;
        let of = E::Fr::from_repr(repr).expect("should decode");

        (extracted, of)
    } 
        
    fn extact_32_from_overflowed_num<CS: ConstraintSystem<E>>(cs: &mut CS, var: &Num<E>) -> Result<Num<E>> {
        let res = match var {
            Num::Constant(x) => {
                Num::Constant(Self::extract_32_from_constant(x).0)
            },
            Num::Alocated(x) => {
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
                    cs.new_single_gate_for_trace_step(
                        &RangeCheck32ConstraintGate::default(), 
                        &[], 
                        &[vars[4*i].get_variable(), vars[4*i+1].get_variable(), vars[4*i+2].get_variable(), vars[4*i+3].get_variable()], 
                        &[]
                    )?;
                }

                let of_value = x.get_value().map( |elem | {
                    Self::extract_32_from_constant(&elem).1
                });

                let of_var = AllocatedNum::alloc(cs, || of_value.grab())?;

                cs.begin_gates_batch_for_step()?;
                
                cs.new_gate_in_batch( 
                    &In04BRangeGate::default(),
                    &[],
                    &[x.get_variable(), of_var.get_variable(), CS::get_dummy_variable(), vars[15].get_variable()],
                    &[],
                )?;

                // the selectors in the main gate go in the following order:
                // [q_a, q_b, q_c, q_d, q_m, q_const, q_d_next]
                // we constraint the equation: q_a - 2^32 q_b - q_d = 0;
                // so in our case: q_a = -1, q_b = 2^32; q_d = 1; q_c = q_m = q_const = q_d_next = 0;

                let zero = E::Fr::zero();
                let one = E::Fr::one();
                let mut minus_one = E::Fr::one();
                minus_one.negate();

                let mut temp_repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
                temp_repr.as_mut()[0] = 1 << 32;
                let coef = E::Fr::from_repr(temp_repr).expect("should parse");

                cs.new_gate_in_batch(
                    &CS::MainGate::default(),
                    &[minus_one, coef, zero.clone(), one, zero.clone(), zero.clone(), zero],
                    &[x.get_variable(), of_var.get_variable(), CS::get_dummy_variable(), vars[15].get_variable()],
                    &[],
                )?;

                cs.end_gates_batch_for_step()?;

                Num::Alocated(vars.pop().expect("top element exists"))
            }
        };

        Ok(res)
    }

    fn converter_helper(n: u64, sparse_base: usize, rotation: usize, extraction: usize) -> E::Fr {
        
        let t = map_into_sparse_form(rotate_extract(n as usize, rotation, extraction), sparse_base);
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = t as u64;
        E::Fr::from_repr(repr).expect("should parse")
    }

    fn allocated_converted_num<CS: ConstraintSystem<E>>(
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
            let mut repr = fr.into_repr();
            let n = (repr.as_ref()[0] >> (chunk_bitlen * chunk_num)) & ((1 << chunk_bitlen) - 1);
            Self::converter_helper(n, sparse_base, rotation, extraction)
        });

        AllocatedNum::alloc(cs, || new_val.grab())
    }

    pub fn query_table1<CS>(cs: &mut CS, table: Arc<LookupTableApplication<E>>, key: &AllocatedNum<E>) -> Result<AllocatedNum<E>> 
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
        cs.apply_single_lookup_gate(&vars[..table.width()], table)?;

        cs.end_gates_batch_for_step()?;

        Ok(res)
    }

    pub fn query_table2<CS: ConstraintSystem<E>>(
        cs: &mut CS, 
        table: Arc<LookupTableApplication<E>>, 
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
        cs.apply_single_lookup_gate(&vars[..table.width()], table)?;

        cs.end_gates_batch_for_step()?;
        Ok(res)
    }

    fn u64_to_ff(n: u64) -> E::Fr {
        let mut repr : <E::Fr as PrimeField>::Repr = E::Fr::zero().into_repr();
        repr.as_mut()[0] = n;
        E::Fr::from_repr(repr).expect("should parse")
    }

    pub fn convert_into_sparse_chooser_form<CS : ConstraintSystem<E>>(
        &self, 
        cs: &mut CS, 
        input: &Num<E>, 
        overflow_check: bool
    ) -> Result<SparseChValue<E>> 
    { 
        let var = if overflow_check { Self::extact_32_from_overflowed_num(cs, input)? } else { *input };
        
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
                
                let low = Self::allocated_converted_num(cs, var, CH_GADGET_CHUNK_SIZE, 0, 0, 0, 0)?;
                let mid = Self::allocated_converted_num(cs, var, CH_GADGET_CHUNK_SIZE, 1, 0, 0, 0)?;
                let high = Self::allocated_converted_num(cs, var, CH_GADGET_CHUNK_SIZE, 2, 0, 0, CH_GADGET_CHUNK_SIZE - 1)?;

                let (sparse_low, sparse_low_rot6) = Self::query_table2(cs, self.sha256_base7_rot6_table, &low)?;
                let (sparse_mid, sparse_mid_rot6) = Self::query_table2(cs, self.sha256_base7_rot6_table, &mid)?;
                let (sparse_high, sparse_high_rot3) = Self::query_table2(cs, self.sha256_base7_rot3_extr10_table, &high)?;

                // compose full normal = low + 2^11 * mid + 2^22 * high
                AllocatedNum::ternary_lc_eq(
                    cs, 
                    &[E::Fr::one(), Self::u64_to_ff(1 << 11), Self::u64_to_ff(1 << 22)],
                    &[low, mid, high],
                    var,
                )?;

                // compose sparse = low_sparse + 7^11 * mid + 7^22 * high
                constexpr fr limb_1_shift = uint256_t(7).pow(11);
    constexpr fr limb_2_shift = uint256_t(7).pow(22);
                fn allocated_converted_num<CS: ConstraintSystem<E>>(
        cs: &mut CS,
        var: &AllocatedNum<E>, 
        chunk_bitlen: usize, 
        chunk_num: usize, 
        sparse_base: usize,
        rotation: usize, 
        extraction: usize

                constexpr fr limb_1_shift = uint256_t(4).pow(11);
                constexpr fr limb_2_shift = uint256_t(4).pow(22);

                constexpr fr rot2_limb_1_shift = uint256_t(4).pow(11 - 2);
                constexpr fr rot2_limb_2_shift = uint256_t(4).pow(22 - 2);

                constexpr fr rot13_limb_0_shift = uint256_t(4).pow(32 - 11 - 2);
                constexpr fr rot13_limb_2_shift = uint256_t(4).pow(22 - 11 - 2);

                constexpr fr rot22_limb_0_shift = uint256_t(4).pow(32 - 22);
                constexpr fr rot22_limb_1_shift = uint256_t(4).pow(32 - 22 + 11);

//     result.normal = input_slices[0].add_two(input_slices[1] * field_t<waffle::PLookupComposer>(ctx, fr(1 << 11)),
//                                             input_slices[2] * field_t<waffle::PLookupComposer>(ctx, fr(1 << 22)));

//     // TODO: USE RANGE PROOF TO CONSTRAIN INPUT
//     // result.normal.assert_equal(a);

//     result.sparse = s[0].add_two(s[1] * limb_1_shift, s[2] * limb_2_shift);

//     // a >>> 6 = (s0 + s1 * (2^11-6) + s2 * 2^(22 - 6))
//     result.rot2 = s_rot[0].add_two(s[1] * rot2_limb_1_shift, s[2] * rot2_limb_2_shift);

//     result.rot13 = s_rot[1].add_two(s[0] * rot13_limb_0_shift, s[2] * rot13_limb_2_shift);

//     result.rot22 = s[2].add_two(s[0] * rot22_limb_0_shift, s[1] * rot22_limb_1_shift);

//     return result;
// }

            }
        }
    }
}
   






