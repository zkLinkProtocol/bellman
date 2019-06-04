mod prover;

pub use prover::{
    create_proof, 
    create_random_proof, 
    prepare_prover,
    create_proof_cpu_fft,
    create_random_proof_cpu_fft
};

use std::sync::Arc;
use std::io::Write;
use crate::source::SourceBuilder;
use crate::pairing::RawEncodable;

use crate::{
    SynthesisError
};

use crate::pairing::{
    Engine,
    CurveAffine
};

use crate::groth16::Parameters;
use crate::groth16::VerifyingKey;

pub trait GpuParametersSource<E: Engine> {
    // type G1Reference: AsRef<E::G1Affine>;
    type G1Builder: SourceBuilder<E::G1Affine>;
    type G2Builder: SourceBuilder<E::G2Affine>;

    fn get_vk(
        &mut self,
        num_ic: usize
    ) -> Result<VerifyingKey<E>, SynthesisError>;
    fn get_h_bases(
        &mut self,
        num_h: usize
    ) -> Result<Arc<Vec<u8>>, SynthesisError>;
    fn get_l(
        &mut self,
        num_l: usize
    ) -> Result<Arc<Vec<u8>>, SynthesisError>;
    fn get_a(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G1Builder, Arc<& [E::G1Affine]>), SynthesisError>;
    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G1Builder, Arc<& [E::G1Affine]>), SynthesisError>;
    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        num_aux: usize
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>;
}

#[derive(Clone)]
pub struct GpuParameters<E: Engine> {
    pub vk: VerifyingKey<E>,

    // for GPU we only need H and L in pre-endoded form
    pub h: Arc<Vec<u8>>,
    pub l: Arc<Vec<u8>>,

    pub a: Arc<Vec<E::G1Affine>>,
    pub b_g1: Arc<Vec<E::G1Affine>>,
    pub b_g2: Arc<Vec<E::G2Affine>>
}

impl<E: Engine> PartialEq for GpuParameters<E> {
    fn eq(&self, other: &Self) -> bool {
        self.vk == other.vk &&
        self.h == other.h &&
        self.l == other.l &&
        self.a == other.a &&
        self.b_g1 == other.b_g1 &&
        self.b_g2 == other.b_g2
    }
}

// impl<E: Engine> Parameters<E> {
//     pub fn write<W: Write>(
//         &self,
//         mut writer: W
//     ) -> io::Result<()>
//     {
//         self.vk.write(&mut writer)?;

//         writer.write_u32::<BigEndian>(self.h.len() as u32)?;
//         for g in &self.h[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.l.len() as u32)?;
//         for g in &self.l[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.a.len() as u32)?;
//         for g in &self.a[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.b_g1.len() as u32)?;
//         for g in &self.b_g1[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         writer.write_u32::<BigEndian>(self.b_g2.len() as u32)?;
//         for g in &self.b_g2[..] {
//             writer.write_all(g.into_uncompressed().as_ref())?;
//         }

//         Ok(())
//     }

//     pub fn read<R: Read>(
//         mut reader: R,
//         checked: bool
//     ) -> io::Result<Self>
//     {
//         let read_g1 = |reader: &mut R| -> io::Result<E::G1Affine> {
//             let mut repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
//             reader.read_exact(repr.as_mut())?;

//             if checked {
//                 repr
//                 .into_affine()
//             } else {
//                 repr
//                 .into_affine_unchecked()
//             }
//             .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//             .and_then(|e| if e.is_zero() {
//                 Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
//             } else {
//                 Ok(e)
//             })
//         };

//         let read_g2 = |reader: &mut R| -> io::Result<E::G2Affine> {
//             let mut repr = <E::G2Affine as CurveAffine>::Uncompressed::empty();
//             reader.read_exact(repr.as_mut())?;

//             if checked {
//                 repr
//                 .into_affine()
//             } else {
//                 repr
//                 .into_affine_unchecked()
//             }
//             .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
//             .and_then(|e| if e.is_zero() {
//                 Err(io::Error::new(io::ErrorKind::InvalidData, "point at infinity"))
//             } else {
//                 Ok(e)
//             })
//         };

//         let vk = VerifyingKey::<E>::read(&mut reader)?;

//         let mut h = vec![];
//         let mut l = vec![];
//         let mut a = vec![];
//         let mut b_g1 = vec![];
//         let mut b_g2 = vec![];

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 h.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 l.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 a.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 b_g1.push(read_g1(&mut reader)?);
//             }
//         }

//         {
//             let len = reader.read_u32::<BigEndian>()? as usize;
//             for _ in 0..len {
//                 b_g2.push(read_g2(&mut reader)?);
//             }
//         }

//         Ok(Parameters {
//             vk: vk,
//             h: Arc::new(h),
//             l: Arc::new(l),
//             a: Arc::new(a),
//             b_g1: Arc::new(b_g1),
//             b_g2: Arc::new(b_g2)
//         })
//     }
// }

impl<'a, E: Engine> GpuParametersSource<E> for &'a GpuParameters<E> {
    // type G1Reference = Arc<&'a [E::G1Affine]>;
    type G1Builder = (Arc<Vec<E::G1Affine>>, usize);
    type G2Builder = (Arc<Vec<E::G2Affine>>, usize);

    fn get_vk(
        &mut self,
        _: usize
    ) -> Result<VerifyingKey<E>, SynthesisError>
    {
        Ok(self.vk.clone())
    }

    fn get_h_bases(
        &mut self,
        size: usize
    ) -> Result<Arc<Vec<u8>>, SynthesisError>
    {
        use crate::pairing::EncodedPoint;

        let representation_size = <E::G1Affine as CurveAffine>::Uncompressed::size();
        if size != self.h.len() / representation_size  {
            return Err(SynthesisError::AssignmentMissing);
        }
        Ok(self.h.clone())
    }

    fn get_l(
        &mut self,
        size: usize
    ) -> Result<Arc<Vec<u8>>, SynthesisError>
    {
        use crate::pairing::EncodedPoint;

        let representation_size = <E::G1Affine as CurveAffine>::Uncompressed::size();
        if size != self.l.len() / representation_size  {
            return Err(SynthesisError::AssignmentMissing);
        }
        Ok(self.l.clone())
    }

    fn get_a(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G1Builder, Arc<&[E::G1Affine]>), SynthesisError>
    {
        Ok(((self.a.clone(), 0), Arc::new(&self.a[num_inputs..])))
    }

    fn get_b_g1(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G1Builder, Arc<&[E::G1Affine]>), SynthesisError>
    {
        Ok(((self.b_g1.clone(), 0), Arc::new(&self.b_g1[num_inputs..])))
    }

    fn get_b_g2(
        &mut self,
        num_inputs: usize,
        _: usize
    ) -> Result<(Self::G2Builder, Self::G2Builder), SynthesisError>
    {
        Ok(((self.b_g2.clone(), 0), (self.b_g2.clone(), num_inputs)))
    }
}

impl<E: Engine> GpuParameters<E> {
    pub fn from_parameters(params: Parameters<E>) -> Self {
        let mut h_representation: Vec<u8> = vec![];
        for base in params.h.iter() {
                // for base in h_bases.iter() {
            // let base = h_bases.as_ref()[i];
            let g1_representation = base.into_raw_uncompressed_le();
            (&mut h_representation).write(g1_representation.as_ref()).expect("must write representation");
        }

        let mut l_representation: Vec<u8> = vec![];
        for base in params.l.iter() {
                // for base in h_bases.iter() {
            // let base = h_bases.as_ref()[i];
            let g1_representation = base.into_raw_uncompressed_le();
            (&mut l_representation).write(g1_representation.as_ref()).expect("must write representation");
        }

        Self {
            vk: params.vk,
            h: Arc::from(h_representation),
            l: Arc::from(l_representation),

            a: params.a,
            b_g1: params.b_g1,
            b_g2: params.b_g2
        }
    }
}