mod prover;

pub use prover::{create_proof, create_random_proof, prepare_prover};

use crate::{
    SynthesisError
};

use crate::pairing::{
    Engine,
    CurveAffine
};

use crate::groth16::Parameters;

pub trait BasesSource<E: Engine> {
    type G1Bases: AsRef<[E::G1Affine]>;
    // type G2Bases: &[E::G2Affine];

    fn get_h_bases(
        &mut self,
        num_h: usize
    ) -> Result<Self::G1Bases, SynthesisError>;
    // fn get_l(
    //     &mut self,
    //     num_l: usize
    // ) -> Result<&[E::G1Affine], SynthesisError>;
    // fn get_a(
    //     &mut self,
    //     num_inputs: usize,
    //     num_aux: usize
    // ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    // fn get_b_g1(
    //     &mut self,
    //     num_inputs: usize,
    //     num_aux: usize
    // ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>;
    // fn get_b_g2(
    //     &mut self,
    //     num_inputs: usize,
    //     num_aux: usize
    // ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

impl<'a, E: Engine> BasesSource<E> for &'a Parameters<E> {
    type G1Bases = &'a [E::G1Affine];
    // type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_h_bases(
        &mut self,
        size: usize
    ) -> Result<Self::G1Bases, SynthesisError>
    {
        if size > self.h.len() {
            return Err(SynthesisError::AssignmentMissing);
        }
        Ok(&self.h[..size])
    }

    // fn get_l(
    //     &mut self,
    //     _: usize
    // ) -> Result<Self::G1Builder, SynthesisError>
    // {
    //     Ok((self.l.clone(), 0))
    // }

    // fn get_a(
    //     &mut self,
    //     num_inputs: usize,
    //     _: usize
    // ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
    // {
    //     Ok(((self.a.clone(), 0), (self.a.clone(), num_inputs)))
    // }

    // fn get_b_g1(
    //     &mut self,
    //     num_inputs: usize,
    //     _: usize
    // ) -> Result<(Self::G1Builder, Self::G1Builder), SynthesisError>
    // {
    //     Ok(((self.b_g1.clone(), 0), (self.b_g1.clone(), num_inputs)))
    // }

    // fn get_b_g2(
    //     &mut self,
    //     num_inputs: usize,
    //     _: usize
    // ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>
    // {
    //     Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    // }
}