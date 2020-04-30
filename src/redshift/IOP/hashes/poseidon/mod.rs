use crate::pairing::Engine;
use std::marker::PhantomData;
use pairing::ff::{Field, PrimeField, PrimeFieldRepr};

pub mod group_hash;
pub mod params;

#[macro_use]
mod specialization;


pub trait SBox<Fr: PrimeField>: Sized + Clone {
    fn apply(&self, elements: &mut [Fr]);
}

#[derive(Clone)]
pub struct CubicSBox<Fr: PrimeField> {
    pub _marker: PhantomData<Fr>
}

impl<Fr: PrimeField> SBox<Fr> for CubicSBox<Fr> {
    fn apply(&self, elements: &mut [Fr]) {
        for element in elements.iter_mut() {
            let mut squared = *element;
            squared.square();
            element.mul_assign(&squared);
        }
    }
}

#[derive(Clone)]
pub struct QuinticSBox<Fr: PrimeField> {
    pub _marker: PhantomData<Fr>
}

impl<Fr: PrimeField> SBox<Fr> for QuinticSBox<Fr> {
    fn apply(&self, elements: &mut [Fr]) {
        for element in elements.iter_mut() {
            let mut quad = *element;
            quad.square();
            quad.square();
            element.mul_assign(&quad);
        }
    }
}


pub trait PoseidonHashParams<Fr: PrimeField> {
    type SBox: SBox<Fr>;
    fn capacity(&self) -> u32;
    fn rate(&self) -> u32;
    fn state_width(&self) -> u32 {
        self.capacity() + self.rate()
    }
    fn num_full_rounds(&self) -> u32;
    fn num_partial_rounds(&self) -> u32;
    fn round_constants(&self, round: u32) -> &[Fr];
    fn mds_matrix_row(&self, row: u32) -> &[Fr];
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

    fn sbox(&self) -> &Self::SBox;
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


construct_sponge! {
    pub struct PoseidonR2C1(2, 1);
}

#[cfg(test)]
mod test {
    use rand::{Rng, thread_rng};
    use crate::pairing::bn256::{Bn256, Fr};
    use super::*;
    use group_hash::BlakeHasher;
    use params::Bn256PoseidonParams;

    #[test]
    fn test_generate_bn256_params() {
        let _params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
    }

    #[test]
    fn test_bn256_poseidon_hash() {
        let rng = &mut thread_rng();
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
        let mut poseidon = PoseidonR2C1::new(&params);

        let input: Vec<Fr> = (0..params.rate()).map(|_| rng.gen()).collect();
        for e in input.into_iter() {
            poseidon.absorb(e);
        }

        let _ = poseidon.squeeze();
    }

    #[test]
    fn print_mds() {
        let params = Bn256PoseidonParams::new_2_into_1::<BlakeHasher>();
        println!("MDS MATRIX");
        let mut vec = vec![];
        for i in 0..params.state_width() {
            vec.push(format!("{:?}", params.mds_matrix_row(i)));
        }

        println!("[ {} ]", vec.join(","));
    }
}
