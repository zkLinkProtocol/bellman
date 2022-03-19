use super::async_prover_new::*;
use super::data_structures_new::*;
use super::main_gate_with_d_next_new::*;
use super::polynomials_new::*;
use crate::multicore::Worker as OldWorker;
use crate::pairing::bn256::{Bn256, Fr};
use crate::plonk::better_better_cs::proof::cs::{
    ensure_in_map_or_create_async, Circuit, ConstraintSystem, Gate, GateInternal,
};
use crate::plonk::better_better_cs::proof::cs::*;
use crate::plonk::better_better_cs::proof::setup::VerificationKey;
use crate::plonk::better_better_cs::proof::verifier::*;
use crate::plonk::domains::Domain;
use crate::plonk::fft::cooley_tukey_ntt::{
    BitReversedOmegas, CTPrecomputations, OmegasInvBitreversed,
};
use crate::SynthesisError;
use futures::executor::{block_on, ThreadPool, ThreadPoolBuilder};
use futures::task::SpawnExt;
use heavy_ops_service::{get_chunk_size, AsyncWorkManager, ResourceManagerProxy, Worker};
use pairing::ff::{Field, PrimeField, ScalarEngine};
use pairing::Engine;
use rand::*;
use std::{marker::PhantomData, sync::Arc};

use super::main_gate_with_d_next_new::*;

pub fn domain_generator<E: ScalarEngine>(degree: usize) -> E::Fr {
    let n = degree.next_power_of_two();

    let mut k = n;
    let mut power_of_two = 0;
    while k != 1 {
        k >>= 1;
        power_of_two += 1;
    }

    let max_power_of_two = E::Fr::S;

    assert!(power_of_two <= max_power_of_two);

    let mut generator = E::Fr::root_of_unity();

    for _ in power_of_two..max_power_of_two {
        generator.square()
    }

    generator
}

pub fn precompute_bitreversed_half_size_twiddles<F: PrimeField>(
    omega: F,
    domain_size: usize,
) -> Vec<F> {
    debug_assert!(domain_size.is_power_of_two());
    debug_assert_eq!(omega.pow(&[domain_size as u64]), F::one());
    let mut twiddles = vec![F::zero(); domain_size / 2];
    let cpus = num_cpus::get_physical();
    let chunk_size = get_chunk_size(twiddles.len(), cpus);
    crossbeam::scope(|scope| {
        for (chunk_idx, twiddles) in twiddles.chunks_mut(chunk_size).enumerate() {
            scope.spawn(move |_| {
                let mut power_of_omega = omega.pow(&[(chunk_idx * chunk_size) as u64]);
                for twiddle in twiddles.iter_mut() {
                    *twiddle = power_of_omega;

                    power_of_omega.mul_assign(&omega);
                }
            });
        }
    })
    .expect("must run");
    bitreverse_enumeration(&mut twiddles);

    twiddles
}

pub fn bitreverse_enumeration<T: Sized>(v: &mut [T]) {
    let n = v.len();
    for i in 0..n {
        let j = bitreverse_index(n, i);
        if j > i {
            v.swap(i, j);
        }
    }
}

pub const fn bitreverse_index(size: usize, index: usize) -> usize {
    const USIZE_BITS: usize = 0_usize.count_zeros() as usize;
    // debug_assert!(index < size);
    if size == 1 {
        0
    } else {
        // debug_assert!(size.is_power_of_two());
        let bits = size.trailing_zeros() as usize;
        index.reverse_bits() >> (USIZE_BITS - bits)
    }
}

#[test]
fn test_circuit_setup_and_async_prove() {
    block_on(run_test_circuit_setup_and_async_prove())
}

async fn run_test_circuit_setup_and_async_prove() {
    let mut assembly =
        SetupAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextNew>::new();

    let circuit = TestCircuit4WithLookups::<Bn256> {
        log_degree: 10,
        _marker: PhantomData,
    };

    circuit.synthesize(&mut assembly).expect("must work");

    println!("Assembly contains {} gates", assembly.n());
    assert!(assembly.is_satisfied());

    assembly.finalize();

    println!("Finalized assembly contains {} gates", assembly.n());

    // let worker = Worker::new();
    let old_worker = OldWorker::new();
    let manager = ResourceManagerProxy::new(num_cpus::get_physical(), 0, 1);
    let worker = manager.create_worker();

    let setup = assembly
        .create_setup::<TestCircuit4WithLookups<Bn256>>(&old_worker, worker.child(), false)
        .await
        .unwrap();

    let mut assembly =
        ProvingAssembly::<Bn256, PlonkCsWidth4WithNextStepParams, Width4MainGateWithDNextNew>::new(
        );
    circuit.synthesize(&mut assembly).expect("must work");
    assembly.finalize();

    let size = assembly.n().next_power_of_two();

    use crate::kate_commitment::*;
    use crate::plonk::commitments::transcript::keccak_transcript::RollingKeccakTranscript;

    let mon_crs = Crs::<Bn256, CrsForMonomialForm>::crs_42(size, &old_worker);
    let thread_pool = ThreadPool::new().unwrap();
    println!("managers initializing");

    let domain = Domain::new_for_size(size as u64).unwrap();
    let omega: Fr = domain.generator;
    let omega_inv = omega.clone().inverse().expect("inverse of omega");

    let twiddles = precompute_bitreversed_half_size_twiddles(omega, size);

    // init gpu mexp manager
    let thread_pool = None; // some for fpga

    let bases = Arc::try_unwrap(mon_crs.g1_bases).unwrap();

    let async_manager = AsyncWorkManager::init(
        Some(bases),
        Some((omega, twiddles)),
        thread_pool,
    );
    let async_manager = Arc::new(async_manager);

    println!("managers initialized");
    let proof = assembly
        .async_create_proof_new::<TestCircuit4WithLookups<Bn256>, RollingKeccakTranscript<Fr>>(
            &old_worker,
            worker.child(),
            async_manager.clone(),
            &setup,
            // &mon_crs,
            None,
        )
        .await
        .unwrap();

    let first = mon_crs.g2_monomial_bases[0].clone();
    let second = mon_crs.g2_monomial_bases[1].clone();

    println!("1");
    let vk = VerificationKey::from_setup(
        &setup,
        &worker.child(),
        async_manager.clone(),
        [first, second],
    )
    .await
    .unwrap();

    println!("1");
    let valid = verify::<Bn256, TestCircuit4WithLookups<Bn256>, RollingKeccakTranscript<Fr>>(
        &vk, &proof, None,
    )
    .unwrap();

    dbg!(valid);
}

struct TestCircuit4WithLookups<E: Engine> {
    log_degree: usize,
    _marker: PhantomData<E>,
}

impl<E: Engine> Circuit<E> for TestCircuit4WithLookups<E> {
    type MainGate = Width4MainGateWithDNextNew;

    fn declare_used_gates() -> Result<Vec<Box<dyn GateInternal<E>>>, SynthesisError> {
        Ok(vec![
            Width4MainGateWithDNextNew::default().into_internal(),
            TestBitGate::default().into_internal(),
        ])
    }

    fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
        let columns = vec![
            PolyIdentifier::VariablesPolynomial(0),
            PolyIdentifier::VariablesPolynomial(1),
            PolyIdentifier::VariablesPolynomial(2),
        ];
        let range_table = LookupTableApplication::new_range_table_of_width_3(2, columns.clone())?;
        let range_table_name = range_table.functional_name();

        let xor_table = LookupTableApplication::new_xor_table(2, columns.clone())?;
        let xor_table_name = xor_table.functional_name();

        let and_table = LookupTableApplication::new_and_table(2, columns)?;
        let and_table_name = and_table.functional_name();

        cs.add_table(range_table)?;
        cs.add_table(xor_table)?;
        cs.add_table(and_table)?;

        let a = cs.alloc(|| Ok(E::Fr::from_str("10").unwrap()))?;

        println!("A = {:?}", a);

        let b = cs.alloc(|| Ok(E::Fr::from_str("20").unwrap()))?;

        println!("B = {:?}", b);

        let c = cs.alloc(|| Ok(E::Fr::from_str("200").unwrap()))?;

        println!("C = {:?}", c);

        let d = cs.alloc(|| Ok(E::Fr::from_str("100").unwrap()))?;

        println!("D = {:?}", d);

        let e = cs.alloc(|| Ok(E::Fr::from_str("2").unwrap()))?;

        let binary_x_value = E::Fr::from_str("3").unwrap();
        let binary_y_value = E::Fr::from_str("1").unwrap();

        let binary_x = cs.alloc(|| Ok(binary_x_value))?;

        let binary_y = cs.alloc(|| Ok(binary_y_value))?;

        let one = E::Fr::one();

        let mut two = one;
        two.double();

        let mut negative_one = one;
        negative_one.negate();

        // 2a - b = 0

        let two_a = ArithmeticTerm::from_variable_and_coeff(a, two);
        let minus_b = ArithmeticTerm::from_variable_and_coeff(b, negative_one);
        let mut term = MainGateTerm::new();
        term.add_assign(two_a);
        term.add_assign(minus_b);

        cs.allocate_main_gate(term)?;

        // c - a*b == 0

        let mut ab_term = ArithmeticTerm::from_variable(a).mul_by_variable(b);
        ab_term.scale(&negative_one);
        let c_term = ArithmeticTerm::from_variable(c);
        let mut term = MainGateTerm::new();
        term.add_assign(c_term);
        term.add_assign(ab_term);

        cs.allocate_main_gate(term)?;

        let dummy = CS::get_dummy_variable();

        // and table (gate #2 zero enumerated)
        {
            let table = cs.get_table(&and_table_name)?;
            let num_keys_and_values = table.width();

            let and_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

            let binary_z = cs.alloc(|| Ok(and_result_value))?;

            cs.begin_gates_batch_for_step()?;

            let vars = [binary_x, binary_y, binary_z, dummy];
            cs.allocate_variables_without_gate(&vars, &[])?;

            cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

            cs.end_gates_batch_for_step()?;
        }

        let rng = &mut thread_rng();

        // d - 100 == 0
        let degree = 1 << self.log_degree;
        for _ in 0..degree{
            let a = ArithmeticTerm::constant(E::Fr::rand(rng));
            let b = ArithmeticTerm::from_variable(d);
            let mut term = MainGateTerm::new();
            term.add_assign(a);
            term.sub_assign(b);
    
            cs.allocate_main_gate(term)?;    
        }

        let hundred = ArithmeticTerm::constant(E::Fr::from_str("100").unwrap());
        let d_term = ArithmeticTerm::from_variable(d);
        let mut term = MainGateTerm::new();
        term.add_assign(d_term);
        term.sub_assign(hundred);

        cs.allocate_main_gate(term)?;

        let var_zero = cs.get_explicit_zero()?;

        // range table (gate #4 zero enumerated)
        {
            let table = cs.get_table(&range_table_name)?;
            let num_keys_and_values = table.width();

            cs.begin_gates_batch_for_step()?;

            let mut term = MainGateTerm::<E>::new();
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(e, E::Fr::zero()));
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(
                var_zero,
                E::Fr::zero(),
            ));
            term.add_assign(ArithmeticTerm::from_variable_and_coeff(
                var_zero,
                E::Fr::zero(),
            ));

            let (vars, coeffs) = CS::MainGate::format_linear_term_with_duplicates(term, dummy)?;

            cs.new_gate_in_batch(&CS::MainGate::default(), &coeffs, &vars, &[])?;

            cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

            cs.end_gates_batch_for_step()?;
        }

        // xor table (gate #5 zero enumerated)
        {
            let table = cs.get_table(&xor_table_name)?;
            let num_keys_and_values = table.width();

            let xor_result_value = table.query(&[binary_x_value, binary_y_value])?[0];

            let binary_z = cs.alloc(|| Ok(xor_result_value))?;

            cs.begin_gates_batch_for_step()?;

            let vars = [binary_x, binary_y, binary_z, dummy];
            cs.allocate_variables_without_gate(&vars, &[])?;

            cs.apply_single_lookup_gate(&vars[..num_keys_and_values], table)?;

            cs.end_gates_batch_for_step()?;
        }

        let one = cs.get_explicit_one()?;

        cs.new_single_gate_for_trace_step(&TestBitGate::default(), &[], &[one], &[])?;

    
        Ok(())
    }
}

#[derive(Clone, Debug, Hash, Default)]
pub struct TestBitGate;

impl<E: Engine> GateInternal<E> for TestBitGate {
    fn name(&self) -> &'static str {
        "Test bit gate on A"
    }

    fn degree(&self) -> usize {
        2
    }

    fn can_include_public_inputs(&self) -> bool {
        false
    }

    fn all_queried_polynomials(&self) -> Vec<PolynomialInConstraint> {
        vec![PolynomialInConstraint::from_id(
            PolyIdentifier::VariablesPolynomial(0),
        )]
    }

    fn setup_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![]
    }

    fn variable_polynomials(&self) -> Vec<PolyIdentifier> {
        vec![PolyIdentifier::VariablesPolynomial(0)]
    }

    fn benefits_from_linearization(&self) -> bool {
        false
    }

    fn linearizes_over(&self) -> Vec<PolynomialInConstraint> {
        vec![]
    }

    fn needs_opened_for_linearization(&self) -> Vec<PolynomialInConstraint> {
        vec![]
    }

    fn num_quotient_terms(&self) -> usize {
        1
    }

    fn verify_on_row(
        &self,
        row: usize,
        poly_storage: &AssembledPolynomialStorage<E>,
        _last_row: bool,
    ) -> E::Fr {
        let q_a = poly_storage.get_poly_at_step(PolyIdentifier::VariablesPolynomial(0), row);

        // (A - 1) * A
        let mut tmp = q_a;
        tmp.sub_assign(&E::Fr::one());
        tmp.mul_assign(&q_a);

        tmp
    }

    fn contribute_into_quotient(
        &self,
        domain_size: usize,
        poly_storage: &mut AssembledPolynomialStorage<E>,
        monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
        challenges: &[E::Fr],
        omegas_bitreversed: &BitReversedOmegas<E::Fr>,
        _omegas_inv_bitreversed: &OmegasInvBitreversed<E::Fr>,
        worker: &OldWorker,
    ) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
        // assert!(domain_size.is_power_of_two());
        // assert_eq!(
        //     challenges.len(),
        //     <Self as GateInternal<E>>::num_quotient_terms(&self)
        // );

        // let lde_factor = poly_storage.lde_factor;
        // assert!(lde_factor.is_power_of_two());

        // assert!(poly_storage.is_bitreversed);

        // let coset_factor = E::Fr::multiplicative_generator();

        // for p in <Self as GateInternal<E>>::all_queried_polynomials(&self).into_iter() {
        //     ensure_in_map_or_create_new(
        //         &worker,
        //         p,
        //         domain_size,
        //         omegas_bitreversed,
        //         lde_factor,
        //         coset_factor,
        //         monomials_storage,
        //         poly_storage,
        //     )?;
        // }

        // let ldes_storage = &*poly_storage;

        // // (A - 1) * A
        // let a_ref = get_from_map_unchecked(
        //     PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
        //     ldes_storage,
        // );

        // let mut tmp = a_ref.clone();
        // drop(a_ref);

        // let one = E::Fr::one();

        // tmp.map(&worker, |el| {
        //     let mut tmp = *el;
        //     tmp.sub_assign(&one);
        //     tmp.mul_assign(&*el);

        //     *el = tmp;
        // });

        // tmp.scale(&worker, challenges[0]);

        // Ok(tmp)

        todo!();
    }

    fn contribute_into_linearization(
        &self,
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
        _challenges: &[E::Fr],
        _worker: &OldWorker,
    ) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
    fn contribute_into_verification_equation(
        &self,
        _domain_size: usize,
        _at: E::Fr,
        queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        challenges: &[E::Fr],
    ) -> Result<E::Fr, SynthesisError> {
        assert_eq!(challenges.len(), 1);
        // (A-1) * A
        let a_value = *queried_values
            .get(&PolynomialInConstraint::from_id(
                PolyIdentifier::VariablesPolynomial(0),
            ))
            .ok_or(SynthesisError::AssignmentMissing)?;
        let mut result = a_value;
        result.sub_assign(&E::Fr::one());
        result.mul_assign(&a_value);
        result.mul_assign(&challenges[0]);

        Ok(result)
    }

    fn put_public_inputs_into_selector_id(&self) -> Option<usize> {
        None
    }

    fn box_clone(&self) -> Box<dyn GateInternal<E>> {
        Box::from(self.clone())
    }
    fn contribute_into_linearization_commitment(
        &self,
        _domain_size: usize,
        _at: E::Fr,
        _queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
        _commitments_storage: &std::collections::HashMap<PolyIdentifier, E::G1Affine>,
        _challenges: &[E::Fr],
    ) -> Result<E::G1, SynthesisError> {
        unreachable!("this gate does not contribute into linearization");
    }
}

impl<E: Engine> Gate<E> for TestBitGate {}
