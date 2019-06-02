use crate::log::Stopwatch;

use rand::Rng;

use std::sync::Arc;

use futures::Future;

use crate::pairing::{
    Engine,
    CurveProjective,
    CurveAffine,
    RawEncodable,
    EncodedPoint
};

use crate::pairing::ff::{
    PrimeField,
    Field,
    PrimeFieldRepr
};

use crate::groth16::{
    ParameterSource,
    Proof
};

use crate::groth16_gpu::BasesSource;

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

use crate::multiexp::*;

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
        result_ptr: *mut u8,
        check_ptr: *const u8
    ) -> u32;
}

impl<E:Engine> PreparedProver<E> {
    pub fn create_random_proof<R, P: BasesSource<E> + ParameterSource<E>>(
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

    pub fn create_proof<P: BasesSource<E> + ParameterSource<E>>(
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

        // Kostya: here you start
        let h = {
            use std::io::Write;

            let a_len = prover.a.len();
            let b_len = prover.b.len();
            let c_len = prover.c.len();

            let (mut expected_h_len, z_inv, m_inv) = calculate_evaluation_domain_params::<E>(a_len)?;
            println!("H query domain size is {}", expected_h_len);
            expected_h_len = expected_h_len - 1;
            // TODO: all these can be parallelized

            let mut a_representation: Vec<u8> = vec![];
            for element in prover.a.iter() {
                let scalar_repr = element.0.into_raw_repr();
                scalar_repr.write_le(&mut a_representation)?;
            }

            let mut b_representation: Vec<u8> = vec![];
            for element in prover.b.iter() {
                let scalar_repr = element.0.into_raw_repr();
                scalar_repr.write_le(&mut b_representation)?;
            }

            let mut c_representation: Vec<u8> = vec![];
            for element in prover.c.iter() {
                let scalar_repr = element.0.into_raw_repr();
                scalar_repr.write_le(&mut c_representation)?;
            }


            println!("Encoded A length = {} bytes", a_representation.len());

            use crate::groth16_gpu::BasesSource;

            let h_bases = params.get_h_bases(expected_h_len)?;
            let mut bases_representation: Vec<u8> = vec![];
            for i in 0..h_bases.as_ref().len() {
                // for base in h_bases.iter() {
                let base = h_bases.as_ref()[i];
                let g1_representation = base.into_raw_uncompressed_le();
                (&mut bases_representation).write(g1_representation.as_ref())?;
            }

            println!("Encoded bases length = {} bytes", bases_representation.len());

            let m_inv_repr = {
                let mut repr = vec![];
                m_inv.into_raw_repr().write_le(&mut repr);

                repr
            };

            let z_inv_repr = {
                let mut repr = vec![];
                z_inv.into_raw_repr().write_le(&mut repr);

                repr
            };


            let g1_repr_length = {
                let mut empty_repr_bytes = vec![];
                let empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
                (&mut empty_repr_bytes).write(empty_repr.as_ref())?;

                empty_repr_bytes.len() 
            };


            let mut a = EvaluationDomain::from_coeffs(prover.a)?;
            let mut b = EvaluationDomain::from_coeffs(prover.b)?;
            let mut c = EvaluationDomain::from_coeffs(prover.c)?;

            // here a coset is a domain where denominator (z) does not vanish
            // inverse FFT is an interpolation
            a.ifft(&worker);
            a.coset_fft(&worker);

            // same is for B and C
            b.ifft(&worker);
            b.coset_fft(&worker);
            c.ifft(&worker);
            c.coset_fft(&worker);

            // do A*B-C in coset
            // a.mul_assign(&worker, &b);
 
            // a.sub_assign(&worker, &c);
            drop(c);
            // z does not vanish in coset, so we divide by non-zero
            //a.divide_by_z_on_coset(&worker);
            // // interpolate back in coset
            //a.icoset_fft(&worker);
            let mut a = a.into_coeffs();
            // let a_len = a.len() - 1;
            // a.truncate(a_len);

            let mut check_representation: Vec<u8> = vec![];
            for element in a.into_iter() {
                let scalar_repr = element.0.into_raw_repr();
                scalar_repr.write_le(&mut check_representation)?;
            }

            println!("G1 uncompressed representation length = {}", g1_repr_length);
            let h_point_vector = unsafe {

                let mut empty_repr_bytes = vec![];
                let empty_repr = <E::G1Affine as CurveAffine>::Uncompressed::empty();
                (&mut empty_repr_bytes).write(empty_repr.as_ref())?;


                let result = evaluate_h(
                    a_len as u64,
                    b_len as u64,
                    c_len as u64,
                    expected_h_len as u64,
                    a_representation.as_ptr(),
                    b_representation.as_ptr(),
                    c_representation.as_ptr(),
                    bases_representation.as_ptr(),
                    z_inv_repr.as_ptr(),
                    m_inv_repr.as_ptr(),
                    empty_repr_bytes.as_mut_ptr(),
                    check_representation.as_ptr()
                );

                empty_repr_bytes
            };
        };

        let h = E::G1Affine::zero().into_projective();

        elog_verbose!("{} seconds for prover for H evaluation (mostly FFT)", stopwatch.elapsed());

        let stopwatch = Stopwatch::new();

        // TODO: Check that difference in operations for different chunks is small

        // TODO: parallelize if it's even helpful
        // TODO: in large settings it may worth to parallelize
        let input_assignment = Arc::new(prover.input_assignment.into_iter().map(|s| s.into_repr()).collect::<Vec<_>>());
        let aux_assignment = Arc::new(prover.aux_assignment.into_iter().map(|s| s.into_repr()).collect::<Vec<_>>());

        let input_len = input_assignment.len();
        let aux_len = aux_assignment.len();
        elog_verbose!("H query is dense in G1,\nOther queries are {} elements in G1 and {} elements in G2",
            2*(input_len + aux_len) + aux_len, input_len + aux_len);

        // Run a dedicated process for dense vector
        let l = multiexp(&worker, params.get_l(aux_assignment.len())?, FullDensity, aux_assignment.clone());

        let a_aux_density_total = prover.a_aux_density.get_total_density();

        let (a_inputs_source, a_aux_source) = params.get_a(input_assignment.len(), a_aux_density_total)?;

        let a_inputs = multiexp(&worker, a_inputs_source, FullDensity, input_assignment.clone());
        let a_aux = multiexp(&worker, a_aux_source, Arc::new(prover.a_aux_density), aux_assignment.clone());

        let b_input_density = Arc::new(prover.b_input_density);
        let b_input_density_total = b_input_density.get_total_density();
        let b_aux_density = Arc::new(prover.b_aux_density);
        let b_aux_density_total = b_aux_density.get_total_density();

        let (b_g1_inputs_source, b_g1_aux_source) = params.get_b_g1(b_input_density_total, b_aux_density_total)?;

        let b_g1_inputs = multiexp(&worker, b_g1_inputs_source, b_input_density.clone(), input_assignment.clone());
        let b_g1_aux = multiexp(&worker, b_g1_aux_source, b_aux_density.clone(), aux_assignment.clone());

        let (b_g2_inputs_source, b_g2_aux_source) = params.get_b_g2(b_input_density_total, b_aux_density_total)?;
        
        let b_g2_inputs = multiexp(&worker, b_g2_inputs_source, b_input_density, input_assignment);
        let b_g2_aux = multiexp(&worker, b_g2_aux_source, b_aux_density, aux_assignment);

        if vk.delta_g1.is_zero() || vk.delta_g2.is_zero() {
            // If this element is zero, someone is trying to perform a
            // subversion-CRS attack.
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
        g_c.add_assign(&h);
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

pub fn create_random_proof<E, C, R, P: BasesSource<E> + ParameterSource<E>>(
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

pub fn create_proof<E, C, P: BasesSource<E> + ParameterSource<E>>(
    circuit: C,
    mut params: P,
    r: E::Fr,
    s: E::Fr
) -> Result<Proof<E>, SynthesisError>
    where E: Engine, C: Circuit<E>
{
    let prover = prepare_prover(circuit)?;

    prover.create_proof(params, r, s)
}
