#[cfg(test)]
mod test {
    use crate::plonk::better_better_cs::cs::*;
    use crate::pairing::ff::*;
    use crate::SynthesisError;
    use crate::Engine;
    use crate::sha2::{Sha256, Digest};
    use crate::plonk::better_better_cs::gadgets::num::{
        AllocatedNum,
        Num,
    };
    use crate::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use super::super::custom_gates::*;
    use rand::Rng;


    struct TestSha256Circuit<E:Engine>{
        input: [E::Fr; 16],
        output: [E::Fr; 8],
        majority_strategy: MajorityStrategy,
        ch_base_num_of_chunks: Option<usize>,
        maj_base_num_of_chunks: Option<usize>,
    }

    impl<E: Engine> Circuit<E> for TestSha256Circuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                    RangeCheck32ConstraintGate::default().into_internal(),
                    SparseRangeGate::new(1).into_internal(),
                    SparseRangeGate::new(2).into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {

            let mut input_vars = Vec::with_capacity(16);
            for value in self.input.iter() {
                let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                input_vars.push(Num::Allocated(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(16);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let sha256_gadget = Sha256GadgetParams::new(
                cs, self.majority_strategy, self.ch_base_num_of_chunks, self.maj_base_num_of_chunks
            )?;

            let supposed_output_vars = sha256_gadget.sha256(cs, &input_vars[..])?;

            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                let a = match a {
                    Num::Allocated(x) => x,
                    Num::Constant(_) => unreachable!(),
                };

                a.eq(cs, b)?;
            }

            Ok(())
        }
    }

    fn slice_to_ff<Fr: PrimeField>(slice: &[u8]) -> Fr {
        assert_eq!(slice.len(), 4);
        let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
        repr.as_mut()[0] = slice[0] as u64 + ((slice[1] as u64) << 8) + ((slice[2] as u64) << 16) + ((slice[3] as u64) << 24);
        Fr::from_repr(repr).expect("should parse")
    }

    fn sha256_gadget_test() 
    {
        // SHA256 Pre-processing (Padding):
        // begin with the original message of length L bits
        // append a single '1' bit
        // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
        // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
        
        // our current impementation of SHA256 does not support padding for now, 
        // and the gadget awaits 16 well formed chunks (of 32-bit numbers)
        // so we deal with padding here explicitely and craft the following message: 
        // 13 - randomly generated blocks of 32-bit numbers => 13 * 4 = 52 8-but number
        // we take L = 13 * 32 = 416 
        // 13-th chunk holds the 1 << 31 => bytes will be 01, 00, 00, 00
        // the last two chunks (14-th and 15-th) haol big-endian representation of 416 = 0x1a0 
        // => the bytes will be  00, 00, 00, 00, 00, 00, 01, a0 
        let mut rng = rand::thread_rng();

        let mut input = [0u8; 64];
        for i in 0..13 {
            input[i] = rng.gen();
        }
        input[52] = 01;
        // 53, 54, 55 are zero
        // as well as 56, 57, 58, 59, 60, 61, 
        input[62] = 01;
        input[63] = 0xa0;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.update(&input[..]);
        // read hash digest and consume hasher
        let output = hasher.finalize();

        let mut input_fr_arr = [Fr::zero(); 16];
        let mut output_fr_arr = [Fr::zero(); 8];

        for (i, block) in input.chunks(4).enumerate() {
            input_fr_arr[i] = slice_to_ff::<Fr>(block);
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
            majority_strategy: MajorityStrategy::UseTwoTables,
            ch_base_num_of_chunks: None,
            maj_base_num_of_chunks: None,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}


            
