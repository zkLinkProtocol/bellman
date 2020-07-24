use crate::pairing::Engine;
use std::marker::PhantomData;
use pairing::ff::{Field, PrimeField, PrimeFieldRepr};
use pairing::bn256::Fr as bn256_Fr;
use pairing::bls12_381::Fr as bls12_381_Fr;
use rand::Rng;

pub mod group_hash;
use group_hash::GroupHasher;

#[macro_use]
mod params;

#[macro_use]
mod specialization;

pub enum SBoxType {
    CubicSxox,
    QuinticSBox,
}


pub fn apply<Fr: PrimeField>(elements: &mut[Fr], sbox_type: SBoxType) {
    match sbox_type {
        SBoxType::CubicSxox => {
            for element in elements.iter_mut() {
                let mut squared = *element;
                squared.square();
                element.mul_assign(&squared);
            }
        }
        SBoxType::QuinticSBox => {
            for element in elements.iter_mut() {
                let mut quad = *element;
                quad.square();
                quad.square();
                element.mul_assign(&quad);
            }
        }
        _ => unimplemented!()
    }
}


pub trait PoseidonHashParams : Sync {

    type Fr: PrimeField;

    fn capacity(&self) -> u32;
    fn rate(&self) -> u32;
    fn state_width(&self) -> u32 {
        self.capacity() + self.rate()
    }

    fn num_full_rounds(&self) -> u32;
    fn num_partial_rounds(&self) -> u32;
    fn round_constants(&self, round: u32) -> &[Self::Fr];
    fn mds_matrix_row(&self, row: u32) -> &[Self::Fr];
    fn security_level(&self) -> u32;
    fn output_len(&self) -> u32 {
        self.capacity()
    }
    fn absorbtion_cycle_len(&self) -> u32 {
        self.rate()
    }
    fn compression_rate(&self) -> u32 {
        self.absorbtion_cycle_len() / self.output_len()
    }

    fn sbox_type(&self) -> SBoxType;
}


#[inline]
pub fn scalar_product<Fr: PrimeField> (input: &[Fr], by: &[Fr]) -> Fr {
    debug_assert!(input.len() == by.len());
    let mut result = Fr::zero();
    for (a, b) in input.iter().zip(by.iter()) {
        let mut tmp = *a;
        tmp.mul_assign(b);
        result.add_assign(&tmp);
    }

    result
}

pub const GH_FIRST_BLOCK: &'static [u8; 64]
     = b"096b36a5804bfacef1691e173c366a47ff5ba84a44f26ddd7e8d9f79d5b42df0";


pub fn batch_inversion<F: PrimeField>(v: &mut [F]) {
    // Montgomery’s Trick and Fast Implementation of Masked AES
    // Genelle, Prouff and Quisquater
    // Section 3.2

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(v.len());
    let mut tmp = F::one();
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
                    .zip(prod.into_iter().rev().skip(1).chain(Some(F::one())))
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
pub fn generate_mds_matrix<Fr: PrimeField, R: Rng>(t: u32, rng: &mut R) -> Vec<Fr> {
    loop {
        let x: Vec<Fr> = (0..t).map(|_| rng.gen()).collect();
        let y: Vec<Fr> = (0..t).map(|_| rng.gen()).collect();

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
        let mut mds_matrix = vec![Fr::zero(); (t*t) as usize];
        for (i, x) in x.into_iter().enumerate() {
            for (j, y) in y.iter().enumerate() {
                let place_into = i*(t as usize) + j;
                let mut element = x;
                element.sub_assign(y);
                mds_matrix[place_into] = element;
            }
        }

        // now we need to do the inverse
        batch_inversion::<Fr>(&mut mds_matrix[..]);

        return mds_matrix;
    }
}


// construct different versions of hashes
// parameters: (field, capacity, rate, num_partial_rounds, num_full_rounds, security_level, sbox_type)

#[derive(PrimeField)]
#[PrimeFieldModulus = "3618502788666131213697322783095070105623107215331596699973092056135872020481"]
#[PrimeFieldGenerator = "3"]
pub struct StarkFr(FrRepr);


construct_poseidon_params! {
    pub struct Bn256_2_to_1_128s(bn256_Fr, 1, 2, 8, 8, 126, SBoxType::QuinticSBox);
}

construct_poseidon_params! {
    pub struct Bn256_2_to_1_80s(bn256_Fr, 1, 2, 13, 26, 80, SBoxType::QuinticSBox);
}

construct_poseidon_params! {
    pub struct Bn256_4_to_1_80s(bn256_Fr, 1, 4, 13, 26, 80, SBoxType::QuinticSBox);
}

construct_poseidon_params! {
    pub struct BLS_2_to_1_80s(bls12_381_Fr, 1, 2, 13, 26, 80, SBoxType::QuinticSBox);
}

construct_poseidon_params! {
    pub struct BLS_4_to_1_80s(bls12_381_Fr, 1, 4, 13, 26, 80, SBoxType::QuinticSBox);
}

construct_poseidon_params! {
    pub struct Stark_2_to_1_80s(StarkFr, 1, 2, 19, 38, 80, SBoxType::CubicSxox);
}

construct_poseidon_params! {
    pub struct Stark_4_to_1_80s(StarkFr, 1, 4, 19, 38, 80, SBoxType::CubicSxox);
}

construct_sponge! {
    pub struct PoseidonR2C1(2, 1, OpModeR2C1);
}

construct_sponge! {
    pub struct PoseidonR4C1(4, 1, OpModeR4C1);
}


#[cfg(test)]
mod test {
    use rand::{Rng, thread_rng};
    use crate::pairing::bn256::{Bn256, Fr};
    use super::*;
    use group_hash::BlakeHasher;

    #[test]
    fn test_generate_bn256_params() {
        let _params = Bn256_2_to_1_128s::new::<BlakeHasher>();
    }

    #[test]
    fn test_bn256_poseidon_hash() {
        let rng = &mut thread_rng();
        let params = Bn256_2_to_1_128s::new::<BlakeHasher>();
        let mut poseidon = PoseidonR2C1::new(&params);

        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        for e in input.into_iter() {
            poseidon.absorb(e);
        }

        let _ = poseidon.squeeze();
    }

    #[test]
    fn print_mds() {
        let params = Bn256_2_to_1_128s::new::<BlakeHasher>();
        println!("MDS MATRIX");
        let mut vec = vec![];
        for i in 0..params.state_width() {
            vec.push(format!("{:?}", params.mds_matrix_row(i)));
        }

        println!("[ {} ]", vec.join(","));
    }
}
