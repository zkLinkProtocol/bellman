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
    num_of_blocks: usize,
    _marker: std::marker::PhantomData<E>,
}


impl<E: Engine> Sha256GadgetParams<E> {

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

    pub fn convert_into_sparse_chooser_form<CS>(cs: mut &CS, input: &Num<E>, overflow_check: bool) -> Result<SparseChValue<E>> 
    where CS: ConstraintSystem<E>
    { 
        let var = if overflow_check { Self::extact_32_from_overflowed_num(cs, input) } else { *input };
        
        match var {
            Num::Constant(x) => {
                let repr = x.into_repr();
                let n = repr.as_ref()[0]; 
                
                let res = SparseChValue {
                    normal: Num::Constant(x),
                    sparse: Num::Constant(map_into_sparse_form(n, SHA256_CHOOSE_BASE)),
                    rot6: Num::Constant(map_from_sparse_form(rotate_extract(n, 6, 0), SHA256_CHOOSE_BASE)),
                    rot11: Num::Constant(map_from_sparse_form(rotate_extract(n, 11, 0), SHA256_CHOOSE_BASE)),
                    rot25: Num::Constant(map_from_sparse_form(rotate_extract(n, 25, 0), SHA256_CHOOSE_BASE)),
                };

                return Ok(res)
            },
            AllocatedNum(var) => {
                
                // split our 32bit variable into 11-bit chunks

                const CH_GADGET_CHUNK_SIZE : usize = 11; 

                //     const uint64_t slice_maximum = (1 << 11) - 1;
//     const uint64_t slice_values[3]{
//         input & slice_maximum,
//         (input >> 11) & slice_maximum,
//         (input >> 22) & slice_maximum,
//     };

//     if (a.witness_index == UINT32_MAX) {
//         result.normal = field_t<waffle::PLookupComposer>(ctx, input);
//         result.sparse = field_t<waffle::PLookupComposer>(ctx, fr(numeric::map_into_sparse_form<4>(input)));
//         result.rot2 = field_t<waffle::PLookupComposer>(
//             ctx, fr(numeric::map_into_sparse_form<4>(numeric::rotate32((uint32_t)input, 2))));
//         result.rot13 = field_t<waffle::PLookupComposer>(
//             ctx, fr(numeric::map_into_sparse_form<4>(numeric::rotate32((uint32_t)input, 13))));
//         result.rot22 = field_t<waffle::PLookupComposer>(
//             ctx, fr(numeric::map_into_sparse_form<4>(numeric::rotate32((uint32_t)input, 22))));
//         return result;
//     }

//     std::array<field_t<waffle::PLookupComposer>, 3> input_slices;
//     for (size_t i = 0; i < 3; ++i) {
//         input_slices[i] = field_t<waffle::PLookupComposer>(ctx);
//         input_slices[i].witness_index = ctx->add_variable(barretenberg::fr(slice_values[i]));
//     }

//     std::array<field_t<waffle::PLookupComposer>, 3> s{
//         witness_t<waffle::PLookupComposer>(ctx, numeric::map_into_sparse_form<4>(slice_values[0])),
//         witness_t<waffle::PLookupComposer>(ctx, numeric::map_into_sparse_form<4>(slice_values[1])),
//         witness_t<waffle::PLookupComposer>(ctx, numeric::map_into_sparse_form<4>(slice_values[2])),
//     };
//     std::array<field_t<waffle::PLookupComposer>, 3> s_rot{
//         field_t<waffle::PLookupComposer>(ctx),
//         field_t<waffle::PLookupComposer>(ctx),
//         field_t<waffle::PLookupComposer>(ctx),
//     };

//     const std::array<uint32_t, 3> slice_indices{
//         ctx->read_from_table(
//             waffle::PLookupTableId::SHA256_BASE4_ROTATE2, input_slices[0].witness_index, s[0].witness_index),
//         ctx->read_from_table(
//             waffle::PLookupTableId::SHA256_BASE4_ROTATE2, input_slices[1].witness_index, s[1].witness_index),
//         ctx->read_from_table(
//             waffle::PLookupTableId::SHA256_BASE4_ROTATE2, input_slices[2].witness_index, s[2].witness_index),
//     };

//     s_rot[0].witness_index = slice_indices[0];
//     s_rot[1].witness_index = slice_indices[1];
//     s_rot[2].witness_index = slice_indices[2];

//     constexpr fr limb_1_shift = uint256_t(4).pow(11);
//     constexpr fr limb_2_shift = uint256_t(4).pow(22);

//     constexpr fr rot2_limb_1_shift = uint256_t(4).pow(11 - 2);
//     constexpr fr rot2_limb_2_shift = uint256_t(4).pow(22 - 2);

//     constexpr fr rot13_limb_0_shift = uint256_t(4).pow(32 - 11 - 2);
//     constexpr fr rot13_limb_2_shift = uint256_t(4).pow(22 - 11 - 2);

//     constexpr fr rot22_limb_0_shift = uint256_t(4).pow(32 - 22);
//     constexpr fr rot22_limb_1_shift = uint256_t(4).pow(32 - 22 + 11);

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
   


// {
//     waffle::PLookupComposer* ctx = a.get_context();

//     sparse_maj_value result;

//     const uint64_t input_full = uint256_t(a.get_value()).data[0];

//     // TODO: USE RANGE PROOF TO CONSTRAIN INPUT
//     const uint64_t input = (input_full & 0xffffffffUL);



// }





