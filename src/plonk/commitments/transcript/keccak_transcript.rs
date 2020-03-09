use tiny_keccak::Keccak;
use crate::pairing::ff::{PrimeField, PrimeFieldRepr};

use super::*;

#[derive(Clone)]
pub struct RollingKeccakTranscript<F: PrimeField> {
    state: Keccak,
    fresh: bool,
    _marker: std::marker::PhantomData<F>
}

impl<F: PrimeField> RollingKeccakTranscript<F> {
    const SHAVE_BITS: u32 = 256 - F::CAPACITY;
    // const REPR_SIZE: usize = std::mem::size_of::<F::Repr>();
    const REPR_SIZE: usize = (((F::NUM_BITS as usize)/ 64) + 1) * 8;

    fn roll_update(&mut self, bytes: &[u8]) -> [u8; 32] {
        if self.fresh {
            self.fresh = false;
            self.state.update(&bytes);

            return [0; 32];
        }
        let mut value: [u8; 32] = [0; 32];
        let old_state = std::mem::replace(&mut self.state, Keccak::new_keccak256());
        old_state.finalize(&mut value);

        self.state.update(&value);
        self.state.update(&bytes);

        value
    }
}

impl<F: PrimeField> Prng<F> for RollingKeccakTranscript<F> {
    type Input = [u8; 32];

    fn new() -> Self {
        assert!(F::NUM_BITS < 256);
        let state = Keccak::new_keccak256();
        Self {
            state,
            fresh: true,
            _marker: std::marker::PhantomData
        }
    }

    fn commit_input(&mut self, input: &Self::Input) {
        self.commit_bytes(input)
    }

    fn get_challenge(&mut self) -> F {
        let value = self.roll_update(&[]);

        // let mut value: [u8; 32] = [0; 32];
        // self.state.finalize(&mut value);

        // self.state = Keccak::new_keccak256();
        // self.state.update(&value);
        
        let mut repr = F::Repr::default();
        let shaving_mask: u64 = 0xffffffffffffffff >> (Self::SHAVE_BITS % 64);
        repr.read_be(&value[..]).expect("will read");
        let last_limb_idx = repr.as_ref().len() - 1;
        repr.as_mut()[last_limb_idx] &= shaving_mask;
        let value = F::from_repr(repr).expect("in a field");

        // println!("Outputting {}", value);

        value
    }
}

impl<F: PrimeField> Transcript<F> for RollingKeccakTranscript<F> {
    fn commit_bytes(&mut self, bytes: &[u8]) {
        // println!("Committing bytes {:?}", bytes);
        // self.state.update(&bytes);
        self.roll_update(&bytes);
    }

    fn commit_field_element(&mut self, element: &F) {
        // println!("Committing field element {:?}", element);
        let repr = element.into_repr();
        let mut bytes: Vec<u8> = vec![0u8; Self::REPR_SIZE];
        repr.write_be(&mut bytes[..]).expect("should write");
        
        // self.state.update(&bytes[..]);
        self.roll_update(&bytes);
    }

    fn get_challenge_bytes(&mut self) -> Vec<u8> {
        let value = self.roll_update(&[]);
        // let value = *(self.state.finalize().as_array());
        // self.state.update(&value[..]);

        // println!("Outputting {:?}", value);

        Vec::from(&value[..])
    }

    fn commit_fe<FF: PrimeField>(&mut self, element: &FF) {
        let repr = element.into_repr();
        let mut bytes: Vec<u8> = vec![0u8; Self::REPR_SIZE];
        repr.write_be(&mut bytes[..]).expect("should write");
        self.roll_update(&bytes);
    }
}
