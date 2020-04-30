use pairing::{Engine, bn256};
use pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use rand::Rng;

use super::{SBox, QuinticSBox, PoseidonHashParams};
use super::group_hash::*;


#[derive(Clone)]
pub struct Bn256PoseidonParams {
    pub(crate) c: u32,
    pub(crate) r: u32,
    pub(crate) full_rounds: u32,
    pub(crate) partial_rounds: u32,
    pub(crate) round_constants: Vec<bn256::Fr>,
    pub(crate) mds_matrix: Vec<bn256::Fr>,
    pub(crate) security_level: u32,
    pub(crate) sbox: QuinticSBox<bn256::Bn256>,
}


pub const GH_FIRST_BLOCK: &'static [u8; 64]
          = b"096b36a5804bfacef1691e173c366a47ff5ba84a44f26ddd7e8d9f79d5b42df0";


fn batch_inversion<E: Engine>(v: &mut [E::Fr]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = E::Fr::one();
    for g in v.iter()
        // Ignore zero elements
        .filter(|g| !g.is_zero())
    {
        tmp.mul_assign(&g);
        prod.push(tmp);
    }

    // Invert `tmp`.
    tmp = tmp.inverse().unwrap(); // Guaranteed to be nonzero.

    // Second pass: iterate backwards to compute inverses
    for (g, s) in v.iter_mut()
                    // Backwards
                    .rev()
                    // Ignore normalized elements
                    .filter(|g| !g.is_zero())
                    // Backwards, skip last element, fill in one for last term.
                    .zip(prod.into_iter().rev().skip(1).chain(Some(E::Fr::one())))
    {
        // tmp := tmp * g.z; g.z := tmp * s = 1/z
        let mut newtmp = tmp;
        newtmp.mul_assign(&g);
        *g = tmp;
        g.mul_assign(&s);
        tmp = newtmp;
    }
}


// For simplicity we'll not generate a matrix using a way from the paper and sampling
// an element with some zero MSBs and instead just sample and retry
fn generate_mds_matrix<E: Engine, R: Rng>(t: u32, rng: &mut R) -> Vec<E::Fr> {
    loop {
        let x: Vec<E::Fr> = (0..t).map(|_| rng.gen()).collect();
        let y: Vec<E::Fr> = (0..t).map(|_| rng.gen()).collect();

        let mut invalid = false;

        // quick and dirty check for uniqueness of x
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in x[(i+1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of y
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = y[i];
            for other in y[(i+1)..].iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // quick and dirty check for uniqueness of x vs y
        for i in 0..(t as usize) {
            if invalid {
                continue;
            }
            let el = x[i];
            for other in y.iter() {
                if el == *other {
                    invalid = true;
                    break;
                }
            }
        }

        if invalid {
            continue;
        }

        // by previous checks we can be sure in uniqueness and perform subtractions easily
        let mut mds_matrix = vec![E::Fr::zero(); (t*t) as usize];
        for (i, x) in x.into_iter().enumerate() {
            for (j, y) in y.iter().enumerate() {
                let place_into = i*(t as usize) + j;
                let mut element = x;
                element.sub_assign(y);
                mds_matrix[place_into] = element;
            }
        }

        // now we need to do the inverse
        batch_inversion::<E>(&mut mds_matrix[..]);

        return mds_matrix;
    }
}


impl Bn256PoseidonParams {
    pub fn new_2_into_1<H: GroupHasher>() -> Self {
        let c = 1u32;
        let r = 2u32;
        let partial_rounds = 83u32;
        let full_rounds = 8u32;
        let security_level = 126u32;

        Self::new_for_params::<H>(c, r, partial_rounds, full_rounds, security_level)
    }

    pub fn new_for_params<H: GroupHasher>(c: u32, r: u32, partial_rounds: u32, full_rounds: u32, security_level: u32) -> Self {
        use byteorder::{WriteBytesExt, ReadBytesExt, BigEndian};

        let state_width = c + r;
        let num_round_constants = (full_rounds + partial_rounds) * state_width;
        let num_round_constants = num_round_constants as usize;

        // generate round constants based on some seed and hashing
        let round_constants = {
            let tag = b"Rescue_f";
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

                let mut constant_repr = <bn256::Fr as PrimeField>::Repr::default();
                constant_repr.read_le(&h[..]).unwrap();

                if let Ok(constant) = bn256::Fr::from_repr(constant_repr) {
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
                // This tag is a first one in a sequence of b"ResMxxxx"
                // that produces MDS matrix without eigenvalues
                // if we use Blake hasher
                let tag = b"ResM0003";
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

            generate_mds_matrix::<bn256::Bn256, _>(state_width, &mut rng)
        };

        Self {
            c: c,
            r: r,
            full_rounds,
            partial_rounds,
            round_constants: round_constants,
            mds_matrix: mds_matrix,
            security_level: security_level,
            sbox: QuinticSBox { _marker: std::marker::PhantomData },
        }
    }
}


impl PoseidonHashParams<bn256::Bn256> for Bn256PoseidonParams {
    type SBox = QuinticSBox<bn256::Bn256>;

    fn capacity(&self) -> u32 {
        self.c
    }

    fn rate(&self) -> u32 {
        self.r
    }

    fn num_full_rounds(&self) -> u32 {
        self.full_rounds
    }

    fn num_partial_rounds(&self) -> u32 {
        self.partial_rounds
    }

    fn round_constants(&self, round: u32) -> &[bn256::Fr] {
        let t = self.c + self.r;
        let start = (t*round) as usize;
        let end = (t*(round+1)) as usize;

        &self.round_constants[start..end]
    }

    fn mds_matrix_row(&self, row: u32) -> &[bn256::Fr] {
        let t = self.c + self.r;
        let start = (t*row) as usize;
        let end = (t*(row+1)) as usize;

        &self.mds_matrix[start..end]
    }

    fn security_level(&self) -> u32 {
        self.security_level
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

    fn sbox(&self) -> &Self::SBox {
        &self.sbox
    }
}
