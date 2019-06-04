use crate::log::Stopwatch;

use rand::Rng;

use std::io::Read;
use std::io::Write;
use std::sync::Arc;

use futures::Future;

use crate::pairing::{
    Engine,
    CurveProjective,
    CurveAffine,
    RawEncodable,
    EncodedPoint
};

use crate::source::QueryDensity;

use crate::pairing::ff::{
    PrimeField,
    Field,
    PrimeFieldRepr,
    ScalarEngine
};

use crate::groth16::{
    Proof
};

use crate::groth16::scalars_into_representations;

use crate::groth16_gpu::GpuParametersSource;

use crate::{
    SynthesisError,
    Circuit,
    ConstraintSystem,
    LinearCombination,
    Variable,
    Index
};

use crate::domain::{
    EvaluationDomain,
    Scalar
};

use crate::source::{
    DensityTracker,
    FullDensity
};

use crate::multiexp::multiexp;

use crate::worker::{
    Worker
};

fn eval<E: Engine>(
    lc: &LinearCombination<E>,
    mut input_density: Option<&mut DensityTracker>,
    mut aux_density: Option<&mut DensityTracker>,
    input_assignment: &[E::Fr],
    aux_assignment: &[E::Fr]
) -> E::Fr
{
    let mut acc = E::Fr::zero();

    for &(index, coeff) in lc.0.iter() {
        let mut tmp;

        match index {
            Variable(Index::Input(i)) => {
                tmp = input_assignment[i];
                if let Some(ref mut v) = input_density {
                    v.inc(i);
                }
            },
            Variable(Index::Aux(i)) => {
                tmp = aux_assignment[i];
                if let Some(ref mut v) = aux_density {
                    v.inc(i);
                }
            }
        }

        if coeff == E::Fr::one() {
           acc.add_assign(&tmp);
        } else {
           tmp.mul_assign(&coeff);
           acc.add_assign(&tmp);
        }
    }

    acc
}

// This is a proving assignment with densities precalculated
pub struct PreparedProver<E: Engine>{
    assignment: ProvingAssignment<E>,
}

fn encode_scalars_into_montgommery_representations<E: Engine>(
    worker: &Worker,
    scalars: Vec<Scalar<E>>
) -> Result<Vec<u8>, SynthesisError>
{   
    let representation_size = {
        std::mem::size_of::<<E::Fr as PrimeField>::Repr>()
    };

    let mut representation = vec![0u8; scalars.len() * representation_size];
    worker.scope(scalars.len(), |scope, chunk| {
        for (scalar, repr) in scalars.chunks(chunk)
                    .zip(representation.chunks_mut(chunk*representation_size)) {
            scope.spawn(move |_| {
                for (j, scalar) in scalar.iter()
                                            .enumerate() {
                    let start = j *representation_size;
                    let end = (j + 1)*representation_size;
                    let write_to = &mut repr[start..end];
                    let scalar_repr = scalar.0.into_raw_repr();
                    scalar_repr.write_le(write_to).expect("must encode");
                }
            });
        }
    });

    Ok(representation)
}

fn representations_to_encoding<E: Engine> (
    worker: &Worker,
    scalars: &[<E::Fr as PrimeField>::Repr]
) -> Result<Vec<u8>, SynthesisError>
{   
    let representation_size = {
        std::mem::size_of::<<E::Fr as PrimeField>::Repr>()
    };
    let mut representation = vec![0u8; scalars.len() * representation_size];
    worker.scope(scalars.len(), |scope, chunk| {
        for (scalar, repr) in scalars.chunks(chunk)
                    .zip(representation.chunks_mut(chunk*representation_size)){
            scope.spawn(move |_| {
                for (j, scalar) in scalar.iter()
                                            .enumerate() {
                    let start = (j)*representation_size;
                    let end = (j + 1)*representation_size;
                    let write_to = &mut repr[start..end];
                    scalar.write_le(write_to).expect("must encode");
                }
            });
        }
    });

    Ok(representation)
}

// fn filter_and_encode_bases_and_scalars<E: Engine>(
//     worker: &Worker,
//     bases: Arc<&[E::G1Affine]>,
//     density_map: Arc<DensityTracker>,
//     exponents: Arc<Vec<<E::Fr as PrimeField>::Repr>> 
// ) -> Result<(Vec<u8>, Vec<u8>), SynthesisError>
// {   
//     let num_cpus = worker.cpus;
//     // temporary
//     let mut top_level_bases_representation: Vec<Vec<u8>> = vec![vec![]; num_cpus];
//     let mut top_level_scalar_representation: Vec<Vec<u8>> = vec![vec![]; num_cpus];
//     let representation_size = {
//         std::mem::size_of::<<E::Fr as PrimeField>::Repr>()
//     };

//     let g1_representation_size = <E::G1Affine as CurveAffine>::Uncompressed::size();
//     worker.scope(exponents.len(), |scope, chunk| {
//         for (i, (((exponents, bases), bases_res), scalars_res)) in exponents.chunks(chunk)
//                     .zip(bases.chunks(chunk))
//                     .zip(top_level_bases_representation.chunks_mut(1))
//                     .zip(top_level_scalar_representation.chunks_mut(1))
//                     .enumerate() {
            
//             let density_map = density_map.clone();
//             scope.spawn(move |_| {
//                 let density_iter = density_map.as_ref().iter().skip(i*chunk);
//                 let mut bases_repr_per_worker: Vec<u8> = Vec::with_capacity(chunk * g1_representation_size);
//                 let mut scalars_repr_per_worker: Vec<u8> = Vec::with_capacity(chunk * representation_size);
//                 let mut base_idx = 0;
//                 for ((exponent, base), density) in exponents.iter()
//                                 .zip(bases.iter())
//                                 .zip(density_iter) {
//                     if density {
//                         if exponent.is_zero() {
//                             continue;
//                         }
//                         exponent.write_le(&mut scalars_repr_per_worker).expect("must encode");
//                         let base_repr = base.into_raw_uncompressed_le();
//                         (&mut bases_repr_per_worker).write(base_repr.as_ref()).expect("must encode");
//                     }
//                 }

//                 bases_res[0] = bases_repr_per_worker;
//                 scalars_res[0] = scalars_repr_per_worker;
//             });
//         }
//     });

//     let bases = top_level_bases_representation.into_iter().flatten().collect();
//     let scalars = top_level_scalar_representation.into_iter().flatten().collect();

//     Ok((scalars, bases))
// }

fn filter_and_encode_bases_and_scalars<E: Engine>(
    worker: &Worker,
    bases: Arc<&[E::G1Affine]>,
    density_map: Arc<DensityTracker>,
    exponents: Arc<Vec<<E::Fr as PrimeField>::Repr>> 
) -> Result<(Vec<u8>, Vec<u8>, usize), SynthesisError>
{   
    // println!("Total bases = {}, exponents = {}", bases.len(), exponents.len());
    let num_cpus = worker.cpus;
    let mut top_level_scalar_representation: Vec<Vec<u8>> = vec![vec![]; num_cpus];
    let representation_size = {
        std::mem::size_of::<<E::Fr as PrimeField>::Repr>()
    };
    println!("Num bases = {}", bases.len());
    println!("Total density = {}", density_map.get_total_density());
    worker.scope(exponents.len(), |scope, chunk| {
        for (i, (exponents, scalars_res)) in exponents.chunks(chunk)
                    .zip(top_level_scalar_representation.chunks_mut(1))
                    .enumerate() {
            
            let density_map = density_map.clone();
            scope.spawn(move |_| {
                println!("Skipping {}", i*chunk);
                let density_iter = density_map.as_ref().iter().skip(i*chunk);
                let mut scalars_repr_per_worker: Vec<u8> = Vec::with_capacity(chunk * representation_size);
                for (exponent, density) in exponents.iter()
                                .zip(density_iter) {
                    if density {
                        exponent.write_le(&mut scalars_repr_per_worker).expect("must encode");
                    } else {
                        println!("Skipping for i = {}", i);
                    }
                }
                scalars_res[0] = scalars_repr_per_worker;
            });
        }
    });

    let g1_representation_size = <E::G1Affine as CurveAffine>::Uncompressed::size();
    let mut bases_representation: Vec<u8> = vec![0u8; g1_representation_size * bases.len()];
    
    worker.scope(bases.len(), |scope, chunk| {
        for (bases, bases_repr) in bases.chunks(chunk)
                    .zip(bases_representation.chunks_mut(chunk * g1_representation_size)) {

            scope.spawn(move |_| {
                for (j, base) in bases.iter().enumerate() {
                    let start = j * g1_representation_size;
                    let end = (j + 1)*g1_representation_size;
                    let mut write_to = &mut bases_repr[start..end];
                    let base_repr = base.into_raw_uncompressed_le();
                    (&mut write_to).write(base_repr.as_ref()).expect("must encode");
                }
            });
        }
    });

    let scalars: Vec<u8> = top_level_scalar_representation.into_iter().flatten().collect();
    let num_scalars = scalars.len() / representation_size;
    bases_representation.truncate(num_scalars * g1_representation_size);
    // println!("Scalars encoding len = {}, for element {}", scalars.len(), scalars.len() / representation_size);
    // println!("Bases encoding len = {}, for element {}", bases_representation.len(), bases_representation.len() / g1_representation_size);
    // assert!(scalars.len() / representation_size == bases_representation.len() / g1_representation_size);

    Ok((bases_representation, scalars, num_scalars))
}

#[derive(Clone)]
struct ProvingAssignment<E: Engine> {
    // Density of queries
    a_aux_density: DensityTracker,
    b_input_density: DensityTracker,
    b_aux_density: DensityTracker,

    // Evaluations of A, B, C polynomials
    a: Vec<Scalar<E>>,
    b: Vec<Scalar<E>>,
    c: Vec<Scalar<E>>,

    // Assignments of variables
    input_assignment: Vec<E::Fr>,
    aux_assignment: Vec<E::Fr>
}

pub fn prepare_prover<E, C>(
    circuit: C,
) -> Result<PreparedProver<E>, SynthesisError>
    where E: Engine, C: Circuit<E> 
{
    let mut prover = ProvingAssignment {
        a_aux_density: DensityTracker::new(),
        b_input_density: DensityTracker::new(),
        b_aux_density: DensityTracker::new(),
        a: vec![],
        b: vec![],
        c: vec![],
        input_assignment: vec![],
        aux_assignment: vec![]
    };

    prover.alloc_input(|| "", || Ok(E::Fr::one()))?;

    circuit.synthesize(&mut prover)?;

    for i in 0..prover.input_assignment.len() {
        prover.enforce(|| "",
            |lc| lc + Variable(Index::Input(i)),
            |lc| lc,
            |lc| lc,
        );
    }

    let prepared = PreparedProver {
        assignment: prover
    };

    return Ok(prepared)
}

fn calculate_evaluation_domain_params<E: Engine>(length: usize) 
    -> Result<(usize, E::Fr, E::Fr), SynthesisError> {
    // m is a size of domain where Z polynomial does vanish
    // in normal domain Z is in a form of (X-1)(X-2)...(X-N)
    let mut m = 1;
    let mut exp = 0;
    let max_degree = (1 << E::Fr::S) - 1;

    if length > max_degree {
        return Err(SynthesisError::PolynomialDegreeTooLarge)
    }

    while m < length {
        m *= 2;
        exp += 1;

        // The pairing-friendly curve may not be able to support
        // large enough (radix2) evaluation domains.
        if exp > E::Fr::S {
            return Err(SynthesisError::PolynomialDegreeTooLarge)
        }
    }

    let z = {
        let mut tmp = E::Fr::multiplicative_generator().pow(&[m as u64]);
        tmp.sub_assign(&E::Fr::one());

        tmp
    };

    let z_inv = z.inverse().unwrap();

    let m_inv = E::Fr::from_str(&format!("{}", m)).unwrap().inverse().unwrap();

    Ok((m, z_inv, m_inv))
}

extern "C"{
    fn evaluate_h(
        a_len: u64, 
        b_len: u64, 
        c_len: u64, 
        h_len: u64,
        a_repr: *const u8,
        b_repr: *const u8,
        c_repr: *const u8,
        h_repr: *const u8,
        z_inv: *const u8,
        m_inv: *const u8,
        result_ptr: *mut u8
    ) -> u32;

    fn dense_multiexp(
        len: u64, 
        scalars_repr: *const u8,
        bases_repr: *const u8,
        convert_from_montgommery: bool,
        result_ptr: *mut u8
    ) -> u32;
}

impl<E:Engine> PreparedProver<E> {
    pub fn create_random_proof<R, P: GpuParametersSource<E>>(
        self,
        params: P,
        rng: &mut R
    ) -> Result<Proof<E>, SynthesisError>
        where R: Rng
    {
        let r = rng.gen();
        let s = rng.gen();

        self.create_proof(params, r, s)
    }

    pub fn create_proof<P: GpuParametersSource<E>>(
        self,
        mut params: P,
        r: E::Fr,
        s: E::Fr
    ) -> Result<Proof<E>, SynthesisError>
    {        
        let prover = self.assignment;
        let worker = Worker::new();

        let vk = params.get_vk(prover.input_assignment.len())?;

        let stopwatch = Stopwatch::new();

        let a_len = prover.a.len();
        let b_len = prover.b.len();
        let c_len = prover.c.len();

        let a_representation = encode_scalars_into_montgommery_representations(&worker, prover.a)?;
        let b_representation = encode_scalars_into_montgommery_representations(&worker, prover.b)?;
        let c_representation = encode_scalars_into_montgommery_representations(&worker, prover.c)?;

        let (mut expected_h_len, z_inv, m_inv) = calculate_evaluation_domain_params::<E>(a_len)?;

        elog_verbose!("H query domain size is {}", expected_h_len);
        expected_h_len = expected_h_len - 1;

        let h_bases_representation = params.get_h_bases(expected_h_len)?;

        let h = worker.compute(move || { 
            let m_inv_repr = {
                let mut repr = vec![];
                m_inv.into_raw_repr().write_le(&mut repr)?;

                repr
            };

            let z_inv_repr = {
                let mut repr = vec![];
                z_inv.into_raw_repr().write_le(&mut repr)?;

                repr
            };

            let h_affine = unsafe {

                let mut empty_repr_bytes = vec![0u8; <E::G1Affine as CurveAffine>::Uncompressed::size()];
                let mut empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();

                let result = evaluate_h(
                    a_len as u64,
                    b_len as u64,
                    c_len as u64,
                    expected_h_len as u64,
                    a_representation.as_ptr(),
                    b_representation.as_ptr(),
                    c_representation.as_ptr(),
                    h_bases_representation.as_ref().as_ptr(),
                    z_inv_repr.as_ptr(),
                    m_inv_repr.as_ptr(),
                    empty_repr_bytes.as_mut_ptr()
                );

                if result != 0 {
                    elog_verbose!("Error in CUDA routine");
                    return Err(SynthesisError::AssignmentMissing);
                }

                (&empty_repr_bytes[..]).read_exact(&mut empty_repr.as_mut())?;

                let h_affine = E::G1Affine::from_raw_uncompressed_le(&empty_repr, false);
                if h_affine.is_err() {
                    elog_verbose!("Error parsing point {}", h_affine.unwrap_err());
                    return Err(SynthesisError::AssignmentMissing);
                }

                let h_affine = h_affine.unwrap();


                h_affine
            };

            Ok(h_affine.into_projective())
        });

        elog_verbose!("{} seconds for prover to convert to start H evaluation on GPU", stopwatch.elapsed());

        let stopwatch = Stopwatch::new();

        let input_len = prover.input_assignment.len();
        let aux_len = prover.aux_assignment.len();

        let input_assignment = Arc::new(scalars_into_representations::<E>(&worker, prover.input_assignment)?);
        let aux_assignment = Arc::new(scalars_into_representations::<E>(&worker, prover.aux_assignment)?);

        elog_verbose!("H query is dense in G1,\nOther queries are {} elements in G1 and {} elements in G2",
            2*(input_len + aux_len) + aux_len, input_len + aux_len);

        let scalars_encoding = representations_to_encoding::<E>(&worker, &aux_assignment[..])?;
        let l_bases_representation = params.get_l(aux_assignment.len())?;

        let l = worker.compute(move || {
            let mut empty_repr_bytes = vec![0u8; <E::G1Affine as CurveAffine>::Uncompressed::size()];
            let mut empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();

            let result = unsafe { dense_multiexp(
                aux_len as u64,
                scalars_encoding.as_ptr(),
                l_bases_representation.as_ref().as_ptr(),
                false,
                empty_repr_bytes.as_mut_ptr()
            ) };

            if result != 0 {
                elog_verbose!("Error in CUDA routine");
                return Err(SynthesisError::AssignmentMissing);
            }

            (&empty_repr_bytes[..]).read_exact(&mut empty_repr.as_mut())?;

            let l_affine = E::G1Affine::from_raw_uncompressed_le(&empty_repr, false);
            if l_affine.is_err() {
                elog_verbose!("Error parsing point {}", l_affine.unwrap_err());

                return Err(SynthesisError::AssignmentMissing);
            }

            Ok(l_affine.unwrap().into_projective())
        });

        // Run a dedicated process for dense vector
        // let l = multiexp(&worker, params.get_l(aux_assignment.len())?, FullDensity, aux_assignment.clone());

        let a_aux_density_total = prover.a_aux_density.get_total_density();

        println!("A aux total density = {}", a_aux_density_total);

        let (a_inputs_source, a_aux_source) = params.get_a(input_assignment.len(), a_aux_density_total)?;

        // G1 for A on inputs stays on CPU
        let a_inputs = multiexp(&worker, a_inputs_source, FullDensity, input_assignment.clone());

        // let a_aux = multiexp(&worker, a_aux_source, Arc::new(prover.a_aux_density), aux_assignment.clone());

        let (a_bases, a_scalars, a_len) = filter_and_encode_bases_and_scalars::<E>(
            &worker,
            a_aux_source,
            Arc::new(prover.a_aux_density),
            aux_assignment.clone()
        )?;
        println!("A len = {}", a_len);

        let a_aux = worker.compute(move || {
            let mut empty_repr_bytes = vec![0u8; <E::G1Affine as CurveAffine>::Uncompressed::size()];
            let mut empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();

            let result = unsafe { dense_multiexp(
                a_len as u64,
                a_scalars.as_ptr(),
                a_bases.as_ptr(),
                false,
                empty_repr_bytes.as_mut_ptr()
            ) };

            if result != 0 {
                elog_verbose!("Error in CUDA routine");
                return Err(SynthesisError::AssignmentMissing);
            }

            (&empty_repr_bytes[..]).read_exact(&mut empty_repr.as_mut())?;

            let affine = E::G1Affine::from_raw_uncompressed_le(&empty_repr, false);
            if affine.is_err() {
                elog_verbose!("Error parsing point {}", affine.unwrap_err());
                println!("Missing final");
                return Err(SynthesisError::AssignmentMissing);
            }
            let affine = affine.unwrap();
            println!("A = {}", affine);
            Ok(affine.into_projective())
        });
        
                println!("End3!");
        // let a_aux = multiexp(&worker, a_aux_source, Arc::new(prover.a_aux_density), aux_assignment.clone());

        let b_input_density = Arc::new(prover.b_input_density);
        let b_input_density_total = b_input_density.get_total_density();
        let b_aux_density = Arc::new(prover.b_aux_density);
        let b_aux_density_total = b_aux_density.get_total_density();
        println!("B aux density = {}", b_aux_density_total);


        let (b_g1_inputs_source, b_g1_aux_source) = params.get_b_g1(b_input_density_total, b_aux_density_total)?;
        println!("End4!");
        let b_g1_inputs = multiexp(&worker, b_g1_inputs_source, b_input_density.clone(), input_assignment.clone());
        println!("End6!");

        let (b_bases, b_scalars, b_len) = filter_and_encode_bases_and_scalars::<E>(
            &worker,
            b_g1_aux_source,
            b_aux_density.clone(),
            aux_assignment.clone()
        )?;
        println!("B len = {}", b_len);
        println!("End7!");

        let b_g1_aux = worker.compute(move || {
            println!("End8!");
            let mut empty_repr_bytes = vec![0u8; <E::G1Affine as CurveAffine>::Uncompressed::size()];
            let mut empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();

            let result = unsafe { dense_multiexp(
                b_len as u64,
                b_scalars.as_ptr(),
                b_bases.as_ptr(),
                false,
                empty_repr_bytes.as_mut_ptr()
            ) };

            if result != 0 {
                elog_verbose!("Error in CUDA routine");
                println!("Missing5");
                return Err(SynthesisError::AssignmentMissing);
            }

            (&empty_repr_bytes[..]).read_exact(&mut empty_repr.as_mut())?;

            let affine = E::G1Affine::from_raw_uncompressed_le(&empty_repr, false);
            if affine.is_err() {
                elog_verbose!("Error parsing point {}", affine.unwrap_err());
                println!("Missing6");
                return Err(SynthesisError::AssignmentMissing);
            }

            println!("End!");

            Ok(affine.unwrap().into_projective())
        });

        println!("End9!");
        // let b_g1_aux = multiexp(&worker, b_g1_aux_source, b_aux_density.clone(), aux_assignment.clone());

        // G2 operations stay on CPU
        let (b_g2_inputs_source, b_g2_aux_source) = params.get_b_g2(b_input_density_total, b_aux_density_total)?;
        
        let b_g2_inputs = multiexp(&worker, b_g2_inputs_source, b_input_density, input_assignment);
        let b_g2_aux = multiexp(&worker, b_g2_aux_source, b_aux_density, aux_assignment);

        if vk.delta_g1.is_zero() || vk.delta_g2.is_zero() {
            // If this element is zero, someone is trying to perform a
            // subversion-CRS attack.
            println!("Missing7");
            return Err(SynthesisError::UnexpectedIdentity);
        }

        let mut g_a = vk.delta_g1.mul(r);
        g_a.add_assign_mixed(&vk.alpha_g1);
        let mut g_b = vk.delta_g2.mul(s);
        g_b.add_assign_mixed(&vk.beta_g2);
        let mut g_c;
        {
            let mut rs = r;
            rs.mul_assign(&s);

            g_c = vk.delta_g1.mul(rs);
            g_c.add_assign(&vk.alpha_g1.mul(s));
            g_c.add_assign(&vk.beta_g1.mul(r));
        }
        let mut a_answer = a_inputs.wait()?;
        a_answer.add_assign(&a_aux.wait()?);
        g_a.add_assign(&a_answer);
        a_answer.mul_assign(s);
        g_c.add_assign(&a_answer);

        let mut b1_answer = b_g1_inputs.wait()?;
        b1_answer.add_assign(&b_g1_aux.wait()?);
        let mut b2_answer = b_g2_inputs.wait()?;
        b2_answer.add_assign(&b_g2_aux.wait()?);

        g_b.add_assign(&b2_answer);
        b1_answer.mul_assign(r);
        g_c.add_assign(&b1_answer);
        g_c.add_assign(&h.wait()?);
        g_c.add_assign(&l.wait()?);

        elog_verbose!("{} seconds for prover for point multiplication", stopwatch.elapsed());

        Ok(Proof {
            a: g_a.into_affine(),
            b: g_b.into_affine(),
            c: g_c.into_affine()
        })
    }
}


impl<E: Engine> ConstraintSystem<E> for ProvingAssignment<E> {
    type Root = Self;

    fn alloc<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.aux_assignment.push(f()?);
        self.a_aux_density.add_element();
        self.b_aux_density.add_element();

        Ok(Variable(Index::Aux(self.aux_assignment.len() - 1)))
    }

    fn alloc_input<F, A, AR>(
        &mut self,
        _: A,
        f: F
    ) -> Result<Variable, SynthesisError>
        where F: FnOnce() -> Result<E::Fr, SynthesisError>, A: FnOnce() -> AR, AR: Into<String>
    {
        self.input_assignment.push(f()?);
        self.b_input_density.add_element();

        Ok(Variable(Index::Input(self.input_assignment.len() - 1)))
    }

    fn enforce<A, AR, LA, LB, LC>(
        &mut self,
        _: A,
        a: LA,
        b: LB,
        c: LC
    )
        where A: FnOnce() -> AR, AR: Into<String>,
              LA: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LB: FnOnce(LinearCombination<E>) -> LinearCombination<E>,
              LC: FnOnce(LinearCombination<E>) -> LinearCombination<E>
    {
        let a = a(LinearCombination::zero());
        let b = b(LinearCombination::zero());
        let c = c(LinearCombination::zero());

        self.a.push(Scalar(eval(
            &a,
            // Inputs have full density in the A query
            // because there are constraints of the
            // form x * 0 = 0 for each input.
            None,
            Some(&mut self.a_aux_density),
            &self.input_assignment,
            &self.aux_assignment
        )));
        self.b.push(Scalar(eval(
            &b,
            Some(&mut self.b_input_density),
            Some(&mut self.b_aux_density),
            &self.input_assignment,
            &self.aux_assignment
        )));
        self.c.push(Scalar(eval(
            &c,
            // There is no C polynomial query,
            // though there is an (beta)A + (alpha)B + C
            // query for all aux variables.
            // However, that query has full density.
            None,
            None,
            &self.input_assignment,
            &self.aux_assignment
        )));
    }

    fn push_namespace<NR, N>(&mut self, _: N)
        where NR: Into<String>, N: FnOnce() -> NR
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn pop_namespace(&mut self)
    {
        // Do nothing; we don't care about namespaces in this context.
    }

    fn get_root(&mut self) -> &mut Self::Root {
        self
    }
}

pub fn create_random_proof<E, C, R, P: GpuParametersSource<E>>(
    circuit: C,
    params: P,
    rng: &mut R
) -> Result<Proof<E>, SynthesisError>
    where E: Engine, C: Circuit<E>, R: Rng
{
    let r = rng.gen();
    let s = rng.gen();

    create_proof::<E, C, P>(circuit, params, r, s)
}

pub fn create_proof<E, C, P: GpuParametersSource<E>>(
    circuit: C,
    params: P,
    r: E::Fr,
    s: E::Fr
) -> Result<Proof<E>, SynthesisError>
    where E: Engine, C: Circuit<E>
{
    let prover = prepare_prover(circuit)?;

    prover.create_proof(params, r, s)
}
