#[cfg(test)]
mod test {
    use crate::plonk::better_better_cs::cs::*;
    use crate::pairing::ff::*;
    use crate::SynthesisError;
    use crate::Engine;
    use crate::keccak;
    use crate::plonk::better_better_cs::gadgets::num::{
        AllocatedNum,
        Num,
    };
    use crate::pairing::bn256::{Bn256, Fr};

    use super::super::gadgets::*;
    use super::super::utils::*;
    use rand::{Rng, SeedableRng, StdRng};


    struct TestKeccakCircuit<E:Engine>{
        input: Vec<E::Fr>,
        output: [E::Fr; DEFAULT_KECCAK_DIGEST_WORDS_SIZE],
    }

    impl<E: Engine> Circuit<E> for TestKeccakCircuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                ]
            )
        }

        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {

            let mut input_vars = Vec::with_capacity(self.input.len());
            for value in self.input.iter() {
                let new_var = AllocatedNum::alloc(cs, || Ok(value.clone()))?;
                input_vars.push(Num::Allocated(new_var));
            }

            let mut actual_output_vars = Vec::with_capacity(DEFAULT_KECCAK_DIGEST_WORDS_SIZE);
            for value in self.output.iter() {
                let new_var = AllocatedNum::alloc_input(cs, || Ok(value.clone()))?;
                actual_output_vars.push(new_var);
            }

            let keccak_gadget = KeccakGadget::new(cs, None, None, None, None, None)?; 
            let supposed_output_vars = keccak_gadget.digest(cs, &input_vars[..])?;

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

    #[test]
    fn keccak_gadget_test() 
    {
        const NUM_OF_BLOCKS: usize = 1;
        let mut rng = rand::thread_rng();

        let mut input = [0u64; KECCAK_RATE_WORDS_SIZE * NUM_OF_BLOCKS];
        for i in 0..(input - 1) {
            input[i] = rng.gen();
        }
        input.last_mut().unwrap() = 0x8000000000000001;

        
        keccak::f1600(&mut data);
assert_eq!(data, [
    0xF1258F7940E1DDE7, 0x84D5CCF933C0478A, 0xD598261EA65AA9EE, 0xBD1547306F80494D,
    0x8B284E056253D057, 0xFF97A42D7F8E6FD4, 0x90FEE5A0A44647C4, 0x8C5BDA0CD6192E76,
    0xAD30A6F71B19059C, 0x30935AB7D08FFC64, 0xEB5AA93F2317D635, 0xA9A6E6260D712103,
    0x81A57C16DBCF555F, 0x43B831CD0347C826, 0x01F22F1A11A5569F, 0x05E5635A21D9AE61,
    0x64BEFEF28CC970F2, 0x613670957BC46611, 0xB87C5A554FD00ECB, 0x8C3EE88A1CCF32C8,
    0x940C7922AE3A2614, 0x1841F924A2C509E4, 0x16F53526E70465C2, 0x75F644E97F30A13B,
    0xEAF1FF7B5CECA249,
]);

keccak::f1600(&mut data);

        
        
        let total_number_of_bits = (64 * (NUM_OF_BLOCKS-1) + 55) * 8;
        input[64 * (NUM_OF_BLOCKS-1) + 60] = (total_number_of_bits >> 24) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 61] = (total_number_of_bits >> 16) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 62] = (total_number_of_bits >> 8) as u8;
        input[64 * (NUM_OF_BLOCKS-1) + 63] = total_number_of_bits as u8;

        // create a Sha256 object
        let mut hasher = Sha256::new();
        // write input message
        hasher.update(&input[0..(64 * (NUM_OF_BLOCKS-1) + 55)]);
        // read hash digest and consume hasher
        let output = hasher.finalize();

        let mut input_fr_arr = Vec::with_capacity(16 * NUM_OF_BLOCKS);
        let mut output_fr_arr = [Fr::zero(); 8];

        for (i, block) in input.chunks(4).enumerate() {
            input_fr_arr.push(slice_to_ff::<Fr>(block));
        }

        for (i, block) in output.chunks(4).enumerate() {
            output_fr_arr[i] = slice_to_ff::<Fr>(block);
        }
        
        let circuit = TestSha256Circuit::<Bn256>{
            input: input_fr_arr,
            output: output_fr_arr,

            // Note: this parameters may be played with!
            // for now, the only testes versions are the following combinations
            // global_strategy: Use_8_1_2_split, majority_strategy: NaiveApproach
            // global_strategy: UseRangeTable(16), majority_strategy: NaiveApproach
            global_strategy: GlobalStrategy::Use_8_1_2_SplitTable,
            majority_strategy: Strategy::UseCustomTable,

            ch_base_num_of_chunks: None,
            maj_base_num_of_chunks: None,
            sheduler_base_num_of_chunks: None,
        };

        let mut assembly = TrivialAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNext>::new();

        circuit.synthesize(&mut assembly).expect("must work");
        println!("Assembly contains {} gates", assembly.n());
        println!("Total length of all tables: {}", assembly.total_length_of_all_tables);
        assert!(assembly.is_satisfied());
    }
}



