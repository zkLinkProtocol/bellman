use pairing::{Engine, bn256};
use pairing::ff::{Field, PrimeField, PrimeFieldRepr};

use super::{PoseidonHashParams};


#[macro_export]
macro_rules! construct_poseidon_params {
	( $(#[$attr:meta])* $visibility:vis struct $name:ident (
        $t_Fr: ty, 
        $n_capacity : tt, 
        $n_rate: tt,
        $n_partial_rounds: tt,
        $n_full_rounds: tt,
        $n_security_level: tt,
        $e_sbox_type: expr
    ); ) => {
		/// Little-endian large integer type
		$(#[$attr])* $visibility struct $name 
        {
            round_constants: Vec<$t_Fr>,
            mds_matrix: Vec<$t_Fr>,
        }
        
        impl $name {

            pub fn new<H: GroupHasher>() -> Self {
                Self::new_for_params::<H>($n_capacity, $n_rate, $n_partial_rounds, $n_full_rounds, $n_security_level)
            }
            
            pub fn new_for_params<H: GroupHasher>(
                c: u32, 
                r: u32, 
                partial_rounds: u32, 
                full_rounds: u32, 
                _security_level: u32
            ) -> Self {
                
                use byteorder::{WriteBytesExt, ReadBytesExt, BigEndian};

                let state_width = c + r;
                let num_round_constants = (full_rounds + partial_rounds) * state_width;
                let num_round_constants = num_round_constants as usize;

                // generate round constants based on some seed and hashing
                let round_constants = {
                    let tag = b"Poseidon_f";
                    let mut round_constants = Vec::with_capacity(num_round_constants);
                    let mut nonce = 0u32;
                    let mut nonce_bytes = [0u8; 4];

                    loop {
                        (&mut nonce_bytes[0..4]).write_u32::<BigEndian>(nonce).unwrap();
                        let mut h = H::new(&tag[..]);
                        h.update(GH_FIRST_BLOCK);
                        h.update(&nonce_bytes[..]);
                        let h = h.finalize();
                        assert!(h.len() == 32);

                        let mut constant_repr = <$t_Fr as PrimeField>::Repr::default();
                        constant_repr.read_le(&h[..]).unwrap();

                        if let Ok(constant) = <$t_Fr>::from_repr(constant_repr) {
                            if !constant.is_zero() {
                                round_constants.push(constant);
                            }
                        }

                        if round_constants.len() == num_round_constants {
                            break;
                        }

                        nonce += 1;
                    }

                    round_constants
                };

                let mds_matrix = {
                    use rand::{SeedableRng};
                    use rand::chacha::ChaChaRng;
                    // Create an RNG based on the outcome of the random beacon
                    let mut rng = {
                        // that produces MDS matrix without eigenvalues
                        // if we use Blake hasher
                        let tag = b"PosM0003";
                        let mut h = H::new(&tag[..]);
                        h.update(GH_FIRST_BLOCK);
                        let h = h.finalize();
                        assert!(h.len() == 32);
                        let mut seed = [0u32; 8];
                        for i in 0..8 {
                            seed[i] = (&h[..]).read_u32::<BigEndian>().expect("digest is large enough for this to work");
                        }

                        ChaChaRng::from_seed(&seed)
                    };

                    generate_mds_matrix::<$t_Fr, _>(state_width, &mut rng)
                };

                Self {
                    round_constants: round_constants,
                    mds_matrix: mds_matrix,
                }
            }
        }

        impl PoseidonHashParams for $name {
            type Fr = $t_Fr;

            fn capacity(&self) -> u32 {
                $n_capacity
            }

            fn rate(&self) -> u32 {
                $n_rate
            }

            fn num_full_rounds(&self) -> u32 {
                $n_full_rounds
            }

            fn num_partial_rounds(&self) -> u32 {
                $n_partial_rounds
            }

            fn round_constants(&self, round: u32) -> &[Self::Fr] {
                let t = $n_capacity + $n_rate;
                let start = (t*round) as usize;
                let end = (t*(round+1)) as usize;

                &self.round_constants[start..end]
            }

            fn mds_matrix_row(&self, row: u32) -> &[Self::Fr] {
                let t = $n_capacity + $n_rate;
                let start = (t*row) as usize;
                let end = (t*(row+1)) as usize;

                &self.mds_matrix[start..end]
            }

            fn security_level(&self) -> u32 {
                $n_security_level
            }

            fn output_len(&self) -> u32 {
                self.capacity()
            }

            fn absorbtion_cycle_len(&self) -> u32 {
                self.rate()
            }

            fn compression_rate(&self) -> u32 {
                self.absorbtion_cycle_len() / self.output_len()
            }

            fn sbox_type(&self) -> SBoxType {
                $e_sbox_type
            }
        }
    }
}
