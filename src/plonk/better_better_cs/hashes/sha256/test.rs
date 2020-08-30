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

    use super::super::gadgets::*;
    use super::super::custom_gates::*;
    use rand::Rng;


    struct TestSha256Circuit<E:Engine>{
        input: [E::Fr; 16],
        output: [E::Fr; 8],
        majority_strategy: MajorityStrategy,
        ch_base_num_of_chunks: usize,
        maj_base_num_of_chunks: usize,
    }

    impl<E: Engine> Circuit<E> for TestSha256Circuit<E> {
        type MainGate = Width4MainGateWithDNext;

        fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
            Ok(
                vec![
                    Width4MainGateWithDNext::default().into_internal(),
                    RangeCheck32ConstraintGate::default().into_internal(),
                    In04RangeGate::new(1).into_internal(),
                    In04RangeGate::new(2).into_internal(),
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

            for (a, b) supposed_output_vars.into_iter().zip(actual_output_vars.into_iter()) {
                let a = match a {
                    Num::Allocated(x) => x,
                    Num::Constant(_) => unreachable!(),
                };

                a.eq(b)?;
            }
        }
    }

    fn u32_to_ff<Fr: PrimeField>(n: u32) -> Fr {
        let mut repr : <Fr as PrimeField>::Repr = Fr::zero().into_repr();
        repr.as_mut()[0] = n as u64;
        Fr::from_repr(repr).expect("should parse")
    }

    fn sha256_gadget_test_impl<E: Engine>() 
    {
        // SHA256 Pre-processing (Padding):
        // begin with the original message of length L bits
        // append a single '1' bit
        // append K '0' bits, where K is the minimum number >= 0 such that L + 1 + K + 64 is a multiple of 512
        // append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits
        
        // our current impementation of SHA256 does not support padding for now, 
        // and the gadget awaits 16 well formed chunks (of 32-bit numbers)
        // so we deal with padding here explicitely and craft the following message: 
        // 13 - randomly generated blocks of 32-bit numbers 
        // we take L = 13 * 32 = 416 = 0x1a0
        // 13-th chunk holds the 1 << 31
        // the last two chunks (14-th and 15-th) haol big-endian representation of 416
        let mut input = [0u32; 16];
        for i in 0..13 {
            input[i] = rng.gen();
        }
        input[13] = 1 << 13;
        input[14] = 0xa0010000;

        // create a Sha256 object
        let mut hasher = Sha256::new();

// write input message
hasher.update(b"hello world");

// read hash digest and consume hasher
let result = hasher.finalize();

assert_eq!(result[..], hex!("
    b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
")[..]);

// same for Sha512
let mut hasher = Sha512::new();
hasher.update(b"hello world");
let result = hasher.finalize();

assert_eq!(result[..], hex!("
    309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f
    989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f
")[..]);
    }


            
