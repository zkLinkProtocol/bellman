#[cfg(test)]
mod test {
    use crate::plonk::better_better_cs::cs::*;
    use crate::pairing::ff::*;
    use crate::SynthesisError;
    use crate::Engine;
    use blake2::{Blake2s, Digest};
    use crate::plonk::better_better_cs::gadgets::num::{
        AllocatedNum,
        Num,
    };
    use crate::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use rand::{Rng, SeedableRng, StdRng};


    struct TestBlake2sCircuit<E:Engine>{
        input: Vec<E::Fr>,
        output: [E::Fr; 8],
    }

    impl<E: Engine> Circuit<E> for TestBlake2sCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> 
        {
            let mut input_vars = Vec::with_capacity(16);
            for value in self.input.iter() {
                let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                input_vars.push(Num::Allocated(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(8);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let blake2s_gadget = Blake2sGadget::new(cs)?;

            let supposed_output_vars = blake2s_gadget.digest(cs, &input_vars[..])?;

            for (a, b) in supposed_output_vars.iter().zip(actual_output_vars.into_iter()) {
                let a = match a {
                    Num::Allocated(x) => x,
                    Num::Constant(_) => unreachable!(),
                };

                //a.eq(cs, b)?;
            }

            Ok(())
        }
    }

    fn slice_to_ff<Fr: PrimeField>(slice: &[u8]) -> Fr {
        assert_eq!(slice.len(), 4);
        let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
        repr.as_mut()[0] = slice[3] as u64 + ((slice[2] as u64) << 8) + ((slice[1] as u64) << 16) + ((slice[0] as u64) << 24);
        Fr::from_repr(repr).expect("should parse")
    }

    #[test]
    fn blake2s_gadget_test() 
    {
        // SHA256 Pre-processing (Padding):
        // begin with the original message of length L bits
        // append a single '1' bit
        // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
        // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
        let seed: &[_] = &[1, 2, 3, 4, 5];
        let mut rng: StdRng = SeedableRng::from_seed(seed);

        let mut input = [0u8; 64];
        for i in 0..55 {
            input[i] = rng.gen();
        }

        let mut hasher = Blake2s::new();
        hasher.update(&input[..]);
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16);
        let mut output_fr_arr = [Fr::zero(); 8];

        for (i, block) in input.chunks(4).enumerate() {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestBlake2sCircuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}