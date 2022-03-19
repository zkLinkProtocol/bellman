use crate::kate_commitment::divide_single;
use crate::multicore::Worker as OldWorker;
use crate::SynthesisError;
use futures::future::join_all;
use futures::task::SpawnExt;
use futures_locks::RwLock;
use heavy_ops_service::*;
use heavy_ops_service::{AsyncWorkManager, Worker};
// use new_polynomials::domains::Domain;
use pairing::{
    ff::{Field, PrimeField},
    Engine,
    CurveAffine,
    CurveProjective,
};
use std::sync::Arc;

use crate::plonk::better_better_cs::proof::utils::*;

use super::data_structures_new::*;
use super::setup::Setup;
use crate::plonk::better_better_cs::proof::cs::*;
use crate::plonk::better_better_cs::proof::sort_queries_for_linearization;
use crate::plonk::better_better_cs::utils::{binop_over_slices_async, BinopAddAssignScaled};
use crate::plonk::commitments::transcript::Transcript;
use crate::plonk::domains::{materialize_domain_elements_with_natural_enumeration, Domain};
// use new_polynomials::polynomials::*;
use super::polynomials_new::*;
use crate::plonk::better_better_cs::proof::lookup_tables::*;

pub fn get_from_map_unchecked_<E: Engine>(
    key_with_dilation: PolynomialInConstraint,
    ldes_map: &AssembledPolynomialStorage<E>,
) -> &Polynomial<E::Fr, Values> {
    let (key, dilation_value) = key_with_dilation.into_id_and_raw_dilation();

    let r = if dilation_value == 0 {
        match key {
            k @ PolyIdentifier::VariablesPolynomial(..) => ldes_map
                .state_map
                .get(&k)
                .expect(&format!("Must get poly {:?} from ldes storage", &k)),
            k @ PolyIdentifier::WitnessPolynomial(..) => ldes_map
                .witness_map
                .get(&k)
                .expect(&format!("Must get poly {:?} from ldes storage", &k)),
            k @ PolyIdentifier::GateSetupPolynomial(..) => ldes_map
                .setup_map
                .get(&k)
                .expect(&format!("Must get poly {:?} from ldes storage", &k)),
            _ => {
                unreachable!();
            }
        }
    } else {
        ldes_map
            .scratch_space
            .get(&key_with_dilation)
            .expect(&format!(
                "Must get poly {:?} from lde storage",
                &key_with_dilation
            ))
    };

    r
}

async fn test_bit_gate_contribute_into_quotient<E: Engine>(
    gate: &Box<dyn GateInternal<E>>,
    domain_size: usize,
    poly_storage: &mut AssembledPolynomialStorage<E>,
    monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
    challenges: &[E::Fr],
    async_manager: Arc<AsyncWorkManager<E>>,
    old_worker: &OldWorker,
    worker: Worker,
    is_background: bool,
) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
    assert!(domain_size.is_power_of_two());
    assert_eq!(challenges.len(), gate.num_quotient_terms());

    let lde_factor = poly_storage.lde_factor;
    assert!(lde_factor.is_power_of_two());

    assert!(poly_storage.is_bitreversed);

    let coset_factor = E::Fr::multiplicative_generator();

    for p in gate.all_queried_polynomials().into_iter() {
        // ensure_in_map_or_create(
        //     &old_worker,
        //     p,
        //     domain_size,
        //     omegas_bitreversed,
        //     lde_factor,
        //     coset_factor,
        //     monomials_storage,
        //     poly_storage,
        // )?;
        ensure_in_map_or_create_async(
            p,
            domain_size,
            lde_factor,
            coset_factor,
            monomials_storage,
            poly_storage,
            async_manager.clone(),
            worker.child(),
            is_background,
        )
        .await?;
    }

    let ldes_storage = &*poly_storage;

    // (A - 1) * A
    let a_ref = get_from_map_unchecked_(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
        ldes_storage,
    );

    let mut tmp = a_ref.clone();
    drop(a_ref);

    let one = E::Fr::one();

    let num_cpus = worker.num_cpus();

    let chunk_size = domain_size / num_cpus;

    let mut handles = vec![];
    for (chunk_id, (worker, coeffs, chunk_len)) in tmp.arc_coeffs().chunks(chunk_size).map(|chunk| (worker.child(), tmp.arc_coeffs().clone(), chunk.len())).enumerate(){
        let fut = async move{
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;

            let coeffs = unsafe{std::slice::from_raw_parts_mut(coeffs[start..end].as_ptr() as *mut E::Fr, chunk_len)};
            for el in coeffs.iter_mut(){
                let mut tmp = *el;
                tmp.sub_assign(&one);
                tmp.mul_assign(&*el);

                *el = tmp;
            }
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle);
    }
    let _ = join_all(handles).await;

    tmp.scale(worker.child(), false, challenges[0]);

    Ok(tmp)
}


async fn main_gate_contribute_into_quotient_for_public_inputs<E: Engine, MG: MainGate<E>>(
    gate: &MG,
    domain_size: usize,
    public_inputs: &[E::Fr],
    poly_storage: &mut AssembledPolynomialStorage<E>,
    monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
    challenges: &[E::Fr],
    async_manager: Arc<AsyncWorkManager<E>>,
    worker: Worker,
    is_background: bool,
) -> Result<Polynomial<E::Fr, Values>, SynthesisError> {
    assert!(domain_size.is_power_of_two());
    assert_eq!(challenges.len(), <MG as GateInternal<E>>::num_quotient_terms(gate));

    let lde_factor = poly_storage.lde_factor;
    assert!(lde_factor.is_power_of_two());

    assert!(poly_storage.is_bitreversed);

    let coset_factor = E::Fr::multiplicative_generator();
    // Include the public inputs
    let mut inputs_poly = Polynomial::<E::Fr, Values>::new_for_size(domain_size)?;
    for (idx, &input) in public_inputs.iter().enumerate() {
        inputs_poly.as_mut()[idx] = input;
    }
    // go into monomial form

    // let mut inputs_poly = inputs_poly.ifft_using_bitreversed_ntt(&worker, omegas_inv_bitreversed, &E::Fr::one())?;
    let inputs_poly_coeffs = async_manager.ifft(inputs_poly.arc_coeffs(), worker.child(), false).await;
    let inputs_poly = Polynomial::from_coeffs(inputs_poly_coeffs).unwrap();

    // add constants selectors vector
    let name = <MG as GateInternal<E>>::name(gate);

    let key = PolyIdentifier::GateSetupPolynomial(name, 5);
    let constants_poly_ref = monomials_storage.get_poly(key);
    inputs_poly.add_assign(worker.child(), false, constants_poly_ref).await;
    drop(constants_poly_ref);

    // LDE
    let t_1_values = async_manager.coset_lde(inputs_poly.arc_coeffs(),lde_factor, &coset_factor, worker.child(), false).await;
    let mut t_1 =  Polynomial::from_values(t_1_values).unwrap();

    for p in <MG as GateInternal<E>>::all_queried_polynomials(gate).into_iter() {
        // skip public constants poly (was used in public inputs)
        if p == PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 5)) {
            continue;
        }
        ensure_in_map_or_create_async(
            p,
            domain_size,
            lde_factor,
            coset_factor,
            monomials_storage,
            poly_storage,
            async_manager.clone(),
            worker.child(),
            false,
        ).await?;
    }

    let ldes_storage = &*poly_storage;

    // Q_A * A
    let q_a_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 0)),
        ldes_storage
    );
    let a_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
        ldes_storage
    );
    let mut tmp = q_a_ref.clone();
    tmp.mul_assign(worker.child(), false, a_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_a_ref);
    drop(a_ref);

    // Q_B * B
    let q_b_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 1)),
        ldes_storage
    );
    let b_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
        ldes_storage
    );
    tmp.reuse_allocation(q_b_ref);
    tmp.mul_assign(worker.child(), false, b_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_b_ref);
    drop(b_ref);

    // // Q_C * C
    let q_c_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 2)),
        ldes_storage
    );
    let c_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
        ldes_storage
    );
    tmp.reuse_allocation(q_c_ref);
    tmp.mul_assign(worker.child(), false, c_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_c_ref);
    drop(c_ref);

    // // Q_D * D
    let q_d_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 3)),
        ldes_storage
    );
    let d_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)),
        ldes_storage
    );
    tmp.reuse_allocation(q_d_ref);
    tmp.mul_assign(worker.child(), false, d_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_d_ref);
    drop(d_ref);

    // Q_M * A * B
    let q_m_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 4)),
        ldes_storage
    );
    let a_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
        ldes_storage
    );
    let b_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
        ldes_storage
    );
    tmp.reuse_allocation(q_m_ref);
    tmp.mul_assign(worker.child(), false, a_ref).await;
    tmp.mul_assign(worker.child(), false, b_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_m_ref);
    drop(a_ref);
    drop(b_ref);

    // Q_D_next * D_next
    let q_d_next_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id(PolyIdentifier::GateSetupPolynomial(name, 6)),
        ldes_storage
    );
    let d_next_ref = get_from_map_unchecked(
        PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1),
        ldes_storage
    );
    tmp.reuse_allocation(q_d_next_ref);
    tmp.mul_assign(worker.child(), false, d_next_ref).await;
    t_1.add_assign(worker.child(), false, &tmp).await;
    drop(q_d_next_ref);
    drop(d_next_ref);

    t_1.scale(worker.child(), false, challenges[0]).await;

    Ok(t_1)
}


async fn main_gate_contribute_into_linearization_for_public_inputs<E: Engine, G: Gate<E>>(
    gate: &G,
    _domain_size: usize,
    _public_inputs: &[E::Fr],
    _at: E::Fr,
    queried_values: &std::collections::HashMap<PolynomialInConstraint, E::Fr>,
    monomials_storage: &AssembledPolynomialStorageForMonomialForms<E>,
    challenges: &[E::Fr],
    worker: Worker,
    is_background: bool,
) -> Result<Polynomial<E::Fr, Coefficients>, SynthesisError> {
    // we actually do not depend on public inputs, but we use this form for consistency
    assert_eq!(challenges.len(), 1);

    let a_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)))
    .ok_or(SynthesisError::AssignmentMissing)?;
    let b_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)))
    .ok_or(SynthesisError::AssignmentMissing)?;
    let c_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)))
    .ok_or(SynthesisError::AssignmentMissing)?;
    let d_value = *queried_values.get(&PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(3)))
    .ok_or(SynthesisError::AssignmentMissing)?;
    let d_next_value = *queried_values.get(&PolynomialInConstraint::from_id_and_dilation(PolyIdentifier::VariablesPolynomial(3), 1))
    .ok_or(SynthesisError::AssignmentMissing)?;

    let name = <G as GateInternal<E>>::name(&gate);

    // Q_a * A
    let mut result = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 0)).clone();
    result.scale(worker.child(), false, a_value).await;

    // Q_b * B
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 1));
    result.add_assign_scaled(worker.child(), false, poly_ref, &b_value).await;

    // Q_c * C
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 2));
    result.add_assign_scaled(worker.child(), false, poly_ref, &c_value).await;

    // Q_d * D
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 3));
    result.add_assign_scaled(worker.child(), false, poly_ref, &d_value).await;

    // Q_m * A*B
    let mut tmp = a_value;
    tmp.mul_assign(&b_value);
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 4));
    result.add_assign_scaled(worker.child(), false, poly_ref, &tmp).await;

    // Q_const
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 5));
    result.add_assign(worker.child(), false, poly_ref).await;

    // Q_dNext * D_next
    let poly_ref = monomials_storage.get_poly(PolyIdentifier::GateSetupPolynomial(name, 6));
    result.add_assign_scaled(worker.child(), false, poly_ref, &d_next_value).await;

    result.scale(worker.child(), false, challenges[0]).await;

    Ok(result)

}


fn main_gate_add_inputs_into_quotient<E: Engine, MG: MainGate<E>>(
    gate: &MG,
    domain_size: usize,
    public_inputs: &[E::Fr],
    at: E::Fr,
    challenges: &[E::Fr],
) -> Result<E::Fr, SynthesisError> {
        if public_inputs.len() == 0 {
            return Ok(E::Fr::zero());
        }
        assert_eq!(challenges.len(), 1);
        // just evaluate L_{i}(z) * value
        let mut contribution = E::Fr::zero();
        let domain = Domain::<E::Fr>::new_for_size(domain_size as u64)?;
        for (idx, inp) in public_inputs.iter().enumerate() {
            let mut tmp = evaluate_lagrange_poly_at_point(idx, &domain, at)?;
            tmp.mul_assign(&inp);

            contribution.add_assign(&tmp);
        }

        contribution.mul_assign(&challenges[0]);

        Ok(contribution)
}

#[derive(Clone, PartialEq, Eq)]
pub struct Proof<E: Engine, C: Circuit<E>> {
    pub n: usize,
    pub inputs: Vec<E::Fr>,
    pub state_polys_commitments: Vec<E::G1Affine>,
    pub witness_polys_commitments: Vec<E::G1Affine>,
    pub copy_permutation_grand_product_commitment: E::G1Affine,

    pub lookup_s_poly_commitment: Option<E::G1Affine>,
    pub lookup_grand_product_commitment: Option<E::G1Affine>,

    pub quotient_poly_parts_commitments: Vec<E::G1Affine>,

    pub state_polys_openings_at_z: Vec<E::Fr>,
    pub state_polys_openings_at_dilations: Vec<(usize, usize, E::Fr)>,
    pub witness_polys_openings_at_z: Vec<E::Fr>,
    pub witness_polys_openings_at_dilations: Vec<(usize, usize, E::Fr)>,

    pub gate_setup_openings_at_z: Vec<(usize, usize, E::Fr)>,
    pub gate_selectors_openings_at_z: Vec<(usize, E::Fr)>,

    pub copy_permutation_polys_openings_at_z: Vec<E::Fr>,
    pub copy_permutation_grand_product_opening_at_z_omega: E::Fr,

    pub lookup_s_poly_opening_at_z_omega: Option<E::Fr>,
    pub lookup_grand_product_opening_at_z_omega: Option<E::Fr>,

    pub lookup_t_poly_opening_at_z: Option<E::Fr>,
    pub lookup_t_poly_opening_at_z_omega: Option<E::Fr>,

    pub lookup_selector_poly_opening_at_z: Option<E::Fr>,
    pub lookup_table_type_poly_opening_at_z: Option<E::Fr>,

    pub quotient_poly_opening_at_z: E::Fr,

    pub linearization_poly_opening_at_z: E::Fr,

    pub opening_proof_at_z: E::G1Affine,
    pub opening_proof_at_z_omega: E::G1Affine,

    _marker: std::marker::PhantomData<C>
}

impl<E: Engine, C: Circuit<E>> Proof<E, C> {
    pub fn empty() -> Self {
        Self {
            n: 0,
            inputs: vec![],
            state_polys_commitments: vec![],
            witness_polys_commitments: vec![],
            copy_permutation_grand_product_commitment: E::G1Affine::zero(),

            lookup_s_poly_commitment: None,
            lookup_grand_product_commitment: None,

            quotient_poly_parts_commitments: vec![],

            state_polys_openings_at_z: vec![],
            state_polys_openings_at_dilations: vec![],
            witness_polys_openings_at_z: vec![],
            witness_polys_openings_at_dilations: vec![],

            gate_setup_openings_at_z: vec![],
            gate_selectors_openings_at_z: vec![],

            copy_permutation_polys_openings_at_z: vec![],
            copy_permutation_grand_product_opening_at_z_omega: E::Fr::zero(),

            lookup_s_poly_opening_at_z_omega: None,
            lookup_grand_product_opening_at_z_omega: None,

            lookup_t_poly_opening_at_z: None,
            lookup_t_poly_opening_at_z_omega: None,
        
            lookup_selector_poly_opening_at_z: None,
            lookup_table_type_poly_opening_at_z: None,

            quotient_poly_opening_at_z: E::Fr::zero(),

            linearization_poly_opening_at_z: E::Fr::zero(),

            opening_proof_at_z: E::G1Affine::zero(),
            opening_proof_at_z_omega: E::G1Affine::zero(),

            _marker: std::marker::PhantomData
        }
    }
}

impl<E: Engine, P: PlonkConstraintSystemParams<E>, MG: MainGate<E>, S: SynthesisMode>
    Assembly<E, P, MG, S>
{
    pub async fn async_create_proof_new<C: Circuit<E>, T: Transcript<E::Fr>>(
        self,
        old_worker: &OldWorker,
        worker: Worker,
        async_manager: Arc<AsyncWorkManager<E>>,
        setup: &Setup<E, C>,
        // mon_crs: &Crs<E, CrsForMonomialForm>,
        transcript_params: Option<T::InitializationParameters>,
    ) -> Result<Proof<E, C>, SynthesisError> {
    // ) -> Result<(), SynthesisError> {
        assert!(S::PRODUCE_WITNESS);
        assert!(self.is_finalized);

        let mut transcript = if let Some(params) = transcript_params {
            T::new_from_params(params)
        } else {
            T::new()
        };

        let mut proof = Proof::<E, C>::empty();

        let input_values = self.input_assingments.clone();

        proof.n = self.n();
        println!("DEGREE {}", proof.n);
        proof.inputs = input_values.clone();

        for inp in input_values.iter() {
            transcript.commit_field_element(inp);
        }

        let num_state_polys = <Self as ConstraintSystem<E>>::Params::STATE_WIDTH;
        let num_witness_polys = <Self as ConstraintSystem<E>>::Params::WITNESS_WIDTH;

        let mut values_storage = self.make_assembled_poly_storage(&old_worker, true)?;

        let required_domain_size = self.n() + 1;
        assert!(required_domain_size.is_power_of_two());


        println!("proving started");

        // let new_values_storage = Arc::new(RwLock::new(values_storage.clone()));

        // let mon_crs = vec![];

        // if we simultaneously produce setup then grab permutation polys in values forms

        let old_worker = OldWorker::new();
        if S::PRODUCE_SETUP {
            let permutation_polys = self.make_permutations(&old_worker, worker.child(), false).await?;
            assert_eq!(permutation_polys.len(), num_state_polys);

            for (idx, poly) in permutation_polys.into_iter().enumerate() {
                let key = PolyIdentifier::PermutationPolynomial(idx);
                // let poly = PolynomialProxy::from_owned(poly);
                values_storage.setup_map.insert(key, poly);
            }
        } else {
            // compute from setup
            for idx in 0..num_state_polys {
                let key = PolyIdentifier::PermutationPolynomial(idx);
                let vals = async_manager.fft(setup.permutation_monomials[idx].arc_coeffs(), worker.child(), false).await;

                let mut poly = Polynomial::from_values_unpadded(vals)?;
                // poly.bitreverse_enumeration(worker);
                // let poly = PolynomialProxy::from_owned(poly);
                values_storage.setup_map.insert(key, poly);
            }
        }

        let mut ldes_storage = AssembledPolynomialStorage::<E>::new(
            true,
            self.max_constraint_degree.next_power_of_two(),
        );


        dbg!("creating monomial storage");
        let mut monomials_storage =
            Self::create_monomial_storage_async(&old_worker, worker.child(), async_manager.clone(), &values_storage, true, false).await?;
        dbg!("done");



        monomials_storage.extend_from_setup(&setup)?; // TODO



        // step 1 - commit state and witness, enumerated. Also commit sorted polynomials for table arguments
        let mut num_commitments = 0;
        for i in 0..num_witness_polys {
            let key = PolyIdentifier::VariablesPolynomial(i);
            let poly_ref = monomials_storage.get_poly(key);
            // let commitment = commit_using_monomials(poly_ref, mon_crs, &old_worker)?;
            let commitment = async_manager.multiexp(poly_ref.arc_coeffs(), worker.child(), false).await;

            commit_point_as_xy::<E, T>(&mut transcript, &commitment);
            num_commitments += 1;
            num_commitments += 1;

            proof.witness_polys_commitments.push(commitment);
        }


        // step 1.5 - if there are lookup tables then draw random "eta" to linearlize over tables
        let mut lookup_data: Option<LookupDataHolder<E>> = if self.tables.len() > 0
        {
            let eta = transcript.get_challenge();
            // let eta = E::Fr::from_str("987").unwrap();

            // these are selected rows from witness (where lookup applies)

            let (selector_poly, table_type_mononial, table_type_values) = if S::PRODUCE_SETUP {
                let selector_for_lookup_values = self.calculate_lookup_selector_values()?;
                let table_type_values = self.calculate_table_type_values()?;
                
                let table_type_poly_values = Polynomial::from_values(table_type_values)?;                
                let coeffs = async_manager.ifft(table_type_poly_values.arc_coeffs(), worker.child(), false).await;
                let table_type_poly_monomial = Polynomial::from_coeffs(coeffs).unwrap();
                
                let selector_coeffs = async_manager.ifft(Arc::new(selector_for_lookup_values), worker.child(), false).await;
                let selector_poly = Polynomial::from_coeffs(selector_coeffs).unwrap();

                // let selector_poly = PolynomialProxy::from_owned(selector_poly);
                // let table_type_poly = PolynomialProxy::from_owned(table_type_poly_monomial);

                (selector_poly, table_type_poly_monomial, table_type_poly_values.into_coeffs())
            } else {
                let selector_poly_ref = setup
                    .lookup_selector_monomial
                    .as_ref()
                    .expect("setup must contain lookup selector poly");
                // let selector_poly = PolynomialProxy::from_borrowed(selector_poly_ref);

                let table_type_poly_ref = setup
                    .lookup_table_type_monomial
                    .as_ref()
                    .expect("setup must contain lookup table type poly");
                // let table_type_poly = PolynomialProxy::from_borrowed(table_type_poly_ref);
                
                let mut table_type_values = async_manager.fft(table_type_poly_ref.arc_coeffs(), worker.child(), false).await;
                let mut table_type_values = Polynomial::from_values(table_type_values).unwrap();
                // table_type_values.bitreverse_enumeration(&old_worker);
                let mut table_type_values = table_type_values.into_coeffs();
                table_type_values.pop().unwrap();

                (selector_poly_ref.arc_clone(), table_type_poly_ref.arc_clone(), table_type_values)
            };
            dbg!("Setup for Lookup polys done");

            let witness_len = required_domain_size - 1;

            let f_poly_values_aggregated = {
                let mut table_contributions_values = if S::PRODUCE_SETUP {
                    self.calculate_masked_lookup_entries(&values_storage)?
                } else {
                    let selector_values = async_manager.fft(selector_poly.arc_coeffs(), worker.child(), false).await;
                    let mut selector_values = Polynomial::from_values(selector_values).unwrap();
                    // selector_values.bitreverse_enumeration(&old_worker);

                    let selector_values = PolynomialProxy::from_owned(selector_values);

                    self.calculate_masked_lookup_entries_using_selector(
                        &values_storage,
                        &selector_values,
                    )?
                };

                assert_eq!(table_contributions_values.len(), 3);

                assert_eq!(witness_len, table_contributions_values[0].len());

                let f_poly_values_aggregated = Arc::new(table_contributions_values
                    .drain(0..1)
                    .collect::<Vec<_>>()
                    .pop()
                    .unwrap());

                let mut current = eta;
                for t in table_contributions_values.into_iter() {
                    let op = BinopAddAssignScaled::new(current);
                    // FIXME
                    binop_over_slices_async(worker.child(), false, op, f_poly_values_aggregated.clone(), Arc::new(t)).await;

                    current.mul_assign(&eta);
                }

                // add table type marker
                let op = BinopAddAssignScaled::new(current);
                binop_over_slices_async(
                    worker.child(),
                    false,
                    op,
                    f_poly_values_aggregated.clone(),
                    Arc::new(table_type_values),
                ).await;

                Polynomial::from_arc_values_unpadded(f_poly_values_aggregated)?
            };

            let (t_poly_values, t_poly_values_shifted, t_poly_monomial) = if S::PRODUCE_SETUP {
                // these are unsorted rows of lookup tables
                let mut t_poly_ends =
                    self.calculate_t_polynomial_values_for_single_application_tables()?;

                assert_eq!(t_poly_ends.len(), 4);

                let mut t_poly_values_aggregated =
                    t_poly_ends.drain(0..1).collect::<Vec<_>>().pop().unwrap();
                let mut current = eta;
                for t in t_poly_ends.into_iter() {
                    let op = BinopAddAssignScaled::new(current);
                    binop_over_slices(&old_worker, &op, &mut t_poly_values_aggregated, &t);

                    current.mul_assign(&eta);
                }

                let copy_start = witness_len - t_poly_values_aggregated.len();
                let mut full_t_poly_values = vec![E::Fr::zero(); witness_len];
                let mut full_t_poly_values_shifted = full_t_poly_values.clone();

                full_t_poly_values[copy_start..].copy_from_slice(&t_poly_values_aggregated);
                full_t_poly_values_shifted[(copy_start - 1)..(witness_len - 1)]
                    .copy_from_slice(&t_poly_values_aggregated);

                assert!(full_t_poly_values[0].is_zero());

                let t_poly_monomial = {
                    let mon = Polynomial::from_values(full_t_poly_values.clone())?;
                    // let mon = mon.ifft_using_bitreversed_ntt(
                    //     &old_worker,
                    //     &omegas_inv_bitreversed,
                    //     &E::Fr::one(),
                    // )?;
                    let coeffs = async_manager.ifft(selector_poly.arc_coeffs(), worker.child(), false).await;
                    let mut mon = Polynomial::from_coeffs(coeffs).unwrap();
                    mon.bitreverse_enumeration(worker.child(), false).await;

                    mon
                };

                (
                    Polynomial::from_values_unpadded(
                        full_t_poly_values,
                    )?,
                    Polynomial::from_values_unpadded(
                        full_t_poly_values_shifted,
                    )?,
                    t_poly_monomial,
                )
            } else {
                let mut t_poly_values_monomial_aggregated =
                    setup.lookup_tables_monomials[0].clone();
                let mut current = eta;
                for idx in 1..4 {
                    let to_aggregate_ref = &setup.lookup_tables_monomials[idx];
                    t_poly_values_monomial_aggregated.add_assign_scaled(
                        worker.child(),
                        false,
                        to_aggregate_ref,
                        &current,
                    ).await;

                    current.mul_assign(&eta);
                }

                // let mut t_poly_values = t_poly_values_monomial_aggregated.clone().fft(&old_worker);
                // let mut t_poly_values = t_poly_values_monomial_aggregated
                //     .clone()
                //     .fft_using_bitreversed_ntt(&old_worker, &omegas_bitreversed, &E::Fr::one())?;
                let t_poly_values = async_manager.fft(t_poly_values_monomial_aggregated.arc_coeffs(), worker.child(), false).await;
                let mut t_poly_values = Polynomial::from_values(t_poly_values).unwrap();
                // t_poly_values.bitreverse_enumeration(&old_worker);
                let mut t_values_shifted_coeffs = t_poly_values.clone().into_coeffs();

                let _ = t_poly_values.pop_last()?;

                let _: Vec<_> = t_values_shifted_coeffs.drain(0..1).collect();

                let t_poly_values_shifted =
                    Polynomial::from_values_unpadded(t_values_shifted_coeffs)?;

                assert_eq!(witness_len, t_poly_values.size());
                assert_eq!(witness_len, t_poly_values_shifted.size());

                (
                    t_poly_values,
                    t_poly_values_shifted,
                    t_poly_values_monomial_aggregated,
                )
            };

            let (s_poly_monomial, s_poly_unpadded_values, s_shifted_unpadded_values) = {
                let mut s_poly_ends = self.calculate_s_poly_contributions_from_witness()?;
                assert_eq!(s_poly_ends.len(), 4);

                let mut s_poly_values_aggregated =
                    s_poly_ends.drain(0..1).collect::<Vec<_>>().pop().unwrap();
                let mut current = eta;
                for t in s_poly_ends.into_iter() {
                    let op = BinopAddAssignScaled::new(current);
                    binop_over_slices(&old_worker, &op, &mut s_poly_values_aggregated, &t);

                    current.mul_assign(&eta);
                }

                let sorted_copy_start = witness_len - s_poly_values_aggregated.len();

                let mut full_s_poly_values = vec![E::Fr::zero(); witness_len];
                let mut full_s_poly_values_shifted = full_s_poly_values.clone();

                full_s_poly_values[sorted_copy_start..].copy_from_slice(&s_poly_values_aggregated);
                full_s_poly_values_shifted[(sorted_copy_start - 1)..(witness_len - 1)]
                    .copy_from_slice(&s_poly_values_aggregated);

                assert!(full_s_poly_values[0].is_zero());

                let s_poly_monomial = {
                    let mon = Polynomial::from_values(full_s_poly_values.clone())?;
                    // let mon = mon.ifft_using_bitreversed_ntt(
                    //     &old_worker,
                    //     &omegas_inv_bitreversed,
                    //     &E::Fr::one(),
                    // )?;

                    let coeffs = async_manager.ifft(mon.arc_coeffs(), worker.child(), false).await;
                    let mut mon = Polynomial::from_coeffs(coeffs).unwrap();
                    mon.bitreverse_enumeration(worker.child(), false).await;
                    mon
                };

                (
                    s_poly_monomial,
                    Polynomial::from_values_unpadded(full_s_poly_values)?,
                    Polynomial::from_values_unpadded(full_s_poly_values_shifted)?,
                )
            };

            // let s_poly_commitment = commit_using_monomials(&s_poly_monomial, mon_crs, &old_worker)?;
            let s_poly_commitment = async_manager.multiexp(s_poly_monomial.arc_coeffs(), worker.child(), false).await;
            

            commit_point_as_xy::<E, T>(&mut transcript, &s_poly_commitment);
            num_commitments += 1;


            proof.lookup_s_poly_commitment = Some(s_poly_commitment);

            let data = LookupDataHolder::<E> {
                eta,
                f_poly_unpadded_values: Some(f_poly_values_aggregated),
                t_poly_unpadded_values: Some(t_poly_values),
                t_shifted_unpadded_values: Some(t_poly_values_shifted),
                s_poly_unpadded_values: Some(s_poly_unpadded_values),
                s_shifted_unpadded_values: Some(s_shifted_unpadded_values),
                t_poly_monomial: Some(t_poly_monomial),
                s_poly_monomial: Some(s_poly_monomial),
                selector_poly_monomial: Some(selector_poly),
                table_type_poly_monomial: Some(table_type_mononial),
            };

            Some(data)
        } else {
            None
        };

        if self.multitables.len() > 0 {
            unimplemented!("do not support multitables yet")
        }


        if self.multitables.len() > 0 {
            unimplemented!("do not support multitables yet")
        }

        // step 2 - grand product arguments

        let beta_for_copy_permutation = transcript.get_challenge();
        let gamma_for_copy_permutation = transcript.get_challenge();

        // let beta_for_copy_permutation = E::Fr::from_str("123").unwrap();
        // let gamma_for_copy_permutation = E::Fr::from_str("456").unwrap();

        // copy permutation grand product argument

        let mut grand_products_protos_with_gamma = vec![];

        for i in 0..num_state_polys {
            let id = PolyIdentifier::VariablesPolynomial(i);

            let p = values_storage.state_map.get(&id).unwrap(); // FIXME
            p.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;

            grand_products_protos_with_gamma.push(p);
        }

        let required_domain_size = required_domain_size;

        let domain = Domain::new_for_size(required_domain_size as u64)?;

        let mut domain_elements =
            materialize_domain_elements_with_natural_enumeration(&domain, &old_worker);

        domain_elements
            .pop()
            .expect("must pop last element for omega^i");

        let non_residues = make_non_residues::<E::Fr>(num_state_polys - 1);

        let mut domain_elements_poly_by_beta = Polynomial::from_values_unpadded(domain_elements)?;
        domain_elements_poly_by_beta.scale(worker.child(), false, beta_for_copy_permutation).await;

        // we take A, B, C, ... values and form (A + beta * X * non_residue + gamma), etc and calculate their grand product

        let mut z_num = {
            let mut grand_products_proto_it = grand_products_protos_with_gamma.iter();

            let mut z_1 = grand_products_proto_it.next().unwrap();
            z_1.add_assign(worker.child(), false, &domain_elements_poly_by_beta).await;

            for (mut p, non_res) in grand_products_proto_it.zip(non_residues.iter()) {
                p.add_assign_scaled(worker.child(), false, &domain_elements_poly_by_beta, non_res).await;
                z_1.mul_assign(worker.child(), false, &p).await;
            }

            z_1
        };

        // we take A, B, C, ... values and form (A + beta * perm_a + gamma), etc and calculate their grand product

        let mut permutation_polynomials_values_of_size_n_minus_one = vec![];

        for idx in 0..num_state_polys {
            let key = PolyIdentifier::PermutationPolynomial(idx);

            let mut coeffs = values_storage.get_poly(key).clone().into_coeffs();
            coeffs.pop().unwrap();

            let p = Polynomial::from_values_unpadded(coeffs)?;
            permutation_polynomials_values_of_size_n_minus_one.push(p);
        }

        let z_den = {
            assert_eq!(
                permutation_polynomials_values_of_size_n_minus_one.len(),
                grand_products_protos_with_gamma.len()
            );
            let mut grand_products_proto_it = grand_products_protos_with_gamma.iter();
            let mut permutation_polys_it =
                permutation_polynomials_values_of_size_n_minus_one.iter();

            let mut z_2 = grand_products_proto_it.next().unwrap();
            z_2.add_assign_scaled(
                worker.child(), false,
                permutation_polys_it.next().unwrap(),
                &beta_for_copy_permutation,
            ).await;

            for (mut p, perm) in grand_products_proto_it.zip(permutation_polys_it) {
                // permutation polynomials
                p.add_assign_scaled(worker.child(), false, &perm, &beta_for_copy_permutation).await;
                z_2.mul_assign(worker.child(), false, &p).await;
            }

            z_2.arc_clone().batch_inversion(worker.child(), false).await?;

            z_2
        };

        z_num.mul_assign(worker.child(), false, &z_den).await;
        drop(z_den);

        let z = z_num.calculate_shifted_grand_product(worker.child(), false).await?;
        drop(z_num);

        assert!(z.size().is_power_of_two());

        assert!(z.as_ref()[0] == E::Fr::one());

        // let copy_permutation_z_in_monomial_form =
        //     z.ifft_using_bitreversed_ntt(worker.child(), false, &omegas_inv_bitreversed, &E::Fr::one())?;

        let copy_permutation_z_in_monomial_form_coeffs = async_manager.ifft(z.arc_coeffs(), worker.child(), false).await;
        let mut copy_permutation_z_in_monomial_form = Polynomial::from_coeffs(copy_permutation_z_in_monomial_form_coeffs).unwrap();
        copy_permutation_z_in_monomial_form.bitreverse_enumeration(worker.child(), false).await;
        // let copy_permutation_z_poly_commitment = commit_using_monomials(&copy_permutation_z_in_monomial_form, mon_crs, worker.child(), false)?;
        let copy_permutation_z_poly_commitment = async_manager.multiexp(copy_permutation_z_in_monomial_form.arc_coeffs(), worker.child(), false).await;

        commit_point_as_xy::<E, T>(&mut transcript, &copy_permutation_z_poly_commitment);
        num_commitments += 1;

        proof.copy_permutation_grand_product_commitment = copy_permutation_z_poly_commitment;

        let mut beta_for_lookup = None;
        let mut gamma_for_lookup = None;


        let lookup_z_poly_in_monomial_form = if let Some(data) = lookup_data.as_mut() {
            let beta_for_lookup_permutation = transcript.get_challenge();
            let gamma_for_lookup_permutation = transcript.get_challenge();

            // let beta_for_lookup_permutation = E::Fr::from_str("789").unwrap();
            // let gamma_for_lookup_permutation = E::Fr::from_str("1230").unwrap();

            beta_for_lookup = Some(beta_for_lookup_permutation);
            gamma_for_lookup = Some(gamma_for_lookup_permutation);

            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);

            let expected = gamma_beta.pow([(required_domain_size - 1) as u64]);

            let f_poly_unpadded_values = data.f_poly_unpadded_values.take().unwrap();
            let t_poly_unpadded_values = data.t_poly_unpadded_values.take().unwrap();
            let t_shifted_unpadded_values = data.t_shifted_unpadded_values.take().unwrap();
            let s_poly_unpadded_values = data.s_poly_unpadded_values.take().unwrap();
            let s_shifted_unpadded_values = data.s_shifted_unpadded_values.take().unwrap();

            // Z(x*omega) = Z(x) *
            // (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) /
            // (\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

            let mut z_num = {
                // (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))

                let mut t = t_poly_unpadded_values;
                t.add_assign_scaled(
                    worker.child(),
                    false,
                    &t_shifted_unpadded_values,
                    &beta_for_lookup_permutation,
                ).await;
                t.add_constant(worker.child(), false, &gamma_beta).await;

                let mut tmp = f_poly_unpadded_values.clone();
                tmp.add_constant(worker.child(), false, &gamma_for_lookup_permutation).await;
                tmp.scale(worker.child(), false, beta_plus_one).await;

                t.mul_assign(worker.child(), false, &tmp).await;
                drop(tmp);

                t
            };

            let z_den = {
                // (\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

                let mut t = s_poly_unpadded_values.clone();
                t.add_assign_scaled(
                    worker.child(),
                    false,
                    &s_shifted_unpadded_values,
                    &beta_for_lookup_permutation,
                ).await;
                t.add_constant(worker.child(), false, &gamma_beta).await;

                t.batch_inversion(worker.child(), false).await?;

                t
            };

            z_num.mul_assign(worker.child(), false, &z_den).await;
            drop(z_den);

            let z = z_num.calculate_shifted_grand_product(worker.child(), false).await?;
            drop(z_num);

            assert!(z.size().is_power_of_two());

            assert_eq!(z.as_ref()[0], E::Fr::one());
            // FIXME
            // assert_eq!(*z.as_ref().last().unwrap(), expected);


            let z_coeffs = async_manager.ifft(z.arc_coeffs(), worker.child(), false).await;
            let mut z = Polynomial::from_coeffs(z_coeffs).unwrap();
            z.bitreverse_enumeration(worker.child(), false).await;
            
            let lookup_z_poly_commitment = async_manager.multiexp(z.arc_coeffs(), worker.child(), false).await;

            commit_point_as_xy::<E, T>(&mut transcript, &lookup_z_poly_commitment);
            num_commitments += 1;

            proof.lookup_grand_product_commitment = Some(lookup_z_poly_commitment);

            Some(z)
        } else {
            None
        };

        // now draw alpha and add all the contributions to the quotient polynomial

        let alpha = transcript.get_challenge();
        // let alpha = E::Fr::from_str("1234567890").unwrap();

        let mut total_powers_of_alpha_for_gates = 0;
        for g in self.sorted_gates.iter() {
            total_powers_of_alpha_for_gates += g.num_quotient_terms();
        }

        // println!("Have {} terms from {} gates", total_powers_of_alpha_for_gates, self.sorted_gates.len());

        let mut current_alpha = E::Fr::one();
        let mut powers_of_alpha_for_gates = Vec::with_capacity(total_powers_of_alpha_for_gates);
        powers_of_alpha_for_gates.push(current_alpha);
        for _ in 1..total_powers_of_alpha_for_gates {
            current_alpha.mul_assign(&alpha);
            powers_of_alpha_for_gates.push(current_alpha);
        }

        assert_eq!(
            powers_of_alpha_for_gates.len(),
            total_powers_of_alpha_for_gates
        );

        let mut all_gates = self.sorted_gates.clone();
        let num_different_gates = self.sorted_gates.len();

        let mut challenges_slice = &powers_of_alpha_for_gates[..];

        let mut lde_factor = num_state_polys;
        for g in self.sorted_gates.iter() {
            let degree = g.degree();
            if degree > lde_factor {
                lde_factor = degree;
            }
        }

        assert!(lde_factor <= 4);

        let coset_factor = E::Fr::multiplicative_generator();

        let mut t_poly = {
            let gate = all_gates.drain(0..1).into_iter().next().unwrap();
            assert!(<Self as ConstraintSystem<E>>::MainGate::default().into_internal() == gate);
            let gate = <Self as ConstraintSystem<E>>::MainGate::default();
            assert_eq!(gate.name(), "main gate of width 4 with D_next");
            let num_challenges = gate.num_quotient_terms();
            let (for_gate, rest) = challenges_slice.split_at(num_challenges);
            challenges_slice = rest;

            let input_values = self.input_assingments.clone();
            let mut t = main_gate_contribute_into_quotient_for_public_inputs(
                &gate,
                required_domain_size,
                &input_values,
                &mut ldes_storage,
                &monomials_storage,
                for_gate,
                async_manager.clone(),
                worker.child(),
                false,
            ).await?;

            if num_different_gates > 1 {
                // we have to multiply by the masking poly (selector)
                let key = PolyIdentifier::GateSelector(gate.name());
                let monomial_selector =
                    monomials_storage.gate_selectors.get(&key).unwrap();
                let selector_lde_values = async_manager.coset_lde(
                    monomial_selector.clone_padded_to_domain()?.arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let selector_lde = Polynomial::from_values(selector_lde_values).unwrap();

                t.mul_assign(worker.child(), false, &selector_lde).await;
                drop(selector_lde);
            }

            t
        };

        let non_main_gates = all_gates;

        for gate in non_main_gates.into_iter() {
            assert_eq!(gate.name(), "Test bit gate on A");
            let num_challenges = gate.num_quotient_terms();
            let (for_gate, rest) = challenges_slice.split_at(num_challenges);
            challenges_slice = rest;

            let mut contribution = test_bit_gate_contribute_into_quotient(
                &gate,
                required_domain_size,
                &mut ldes_storage,
                &monomials_storage,
                for_gate,
                async_manager.clone(),
                &old_worker,
                worker.child(),
                false,
            ).await?;


            {
                // we have to multiply by the masking poly (selector)
                let key = PolyIdentifier::GateSelector(gate.name());
                let monomial_selector =
                    monomials_storage.gate_selectors.get(&key).unwrap();
    
                let selector_lde_values = async_manager.coset_lde(
                    monomial_selector.clone_padded_to_domain()?.arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let selector_lde = Polynomial::from_values(selector_lde_values).unwrap();

                contribution.mul_assign(worker.child(), false, &selector_lde).await;
                drop(selector_lde);
            }

            t_poly.add_assign(worker.child(), false, &contribution).await;
        }

        assert_eq!(challenges_slice.len(), 0);

        println!(
            "Power of alpha for a start of normal permutation argument = {}",
            total_powers_of_alpha_for_gates
        );


        // perform copy-permutation argument

        // we precompute L_{0} here cause it's necessary for both copy-permutation and lookup permutation

        // z(omega^0) - 1 == 0
        let l_0 =
            calculate_lagrange_poly::<E>(async_manager.clone(), worker.child(), false, required_domain_size.next_power_of_two(), 0).await?;        
        let l_0_coset_lde_bitreversed_values = async_manager.coset_lde(
            l_0.arc_coeffs(),
            lde_factor,
            &coset_factor,
            worker.child(),
            false,
        ).await;
        let l_0_coset_lde_bitreversed = Polynomial::from_values(l_0_coset_lde_bitreversed_values).unwrap();

        let mut copy_grand_product_alphas = None;
        let x_poly_lde_bitreversed = {
            // now compute the permutation argument

            // bump alpha
            current_alpha.mul_assign(&alpha);
            let alpha_0 = current_alpha;
            
            let z_coset_lde_bitreversed_values = async_manager.coset_lde(
                copy_permutation_z_in_monomial_form.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let z_coset_lde_bitreversed = Polynomial::from_values(z_coset_lde_bitreversed_values).unwrap();

            assert!(z_coset_lde_bitreversed.size() == required_domain_size * lde_factor);

            let z_shifted_coset_lde_bitreversed =
                z_coset_lde_bitreversed.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size * lde_factor);

            // For both Z_1 and Z_2 we first check for grand products
            // z*(X)(A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma) -
            // - (A + beta*perm_a(X) + gamma)(B + beta*perm_b(X) + gamma)(C + beta*perm_c(X) + gamma)*Z(X*Omega)== 0

            // we use evaluations of the polynomial X and K_i * X on a large domain's coset
            let mut contrib_z = z_coset_lde_bitreversed.clone();

            // precompute x poly
            let mut x_poly =
                Polynomial::from_values(vec![coset_factor; required_domain_size * lde_factor])?;
            x_poly.distribute_powers(worker.child(), false, z_shifted_coset_lde_bitreversed.omega).await;
            x_poly.bitreverse_enumeration(worker.child(), false).await;

            assert_eq!(x_poly.size(), required_domain_size * lde_factor);

            // A + beta*X + gamma

            let mut tmp = ldes_storage
                .state_map
                .get(&PolyIdentifier::VariablesPolynomial(0))
                .unwrap().arc_clone();
            tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;
            tmp.add_assign_scaled(worker.child(), false, &x_poly, &beta_for_copy_permutation).await;
            contrib_z.mul_assign(worker.child(), false, &tmp).await;

            assert_eq!(non_residues.len() + 1, num_state_polys);

            for (poly_idx, non_res) in (1..num_state_polys).zip(non_residues.iter()) {
                let mut factor = beta_for_copy_permutation;
                factor.mul_assign(&non_res);

                let key = PolyIdentifier::VariablesPolynomial(poly_idx);
                tmp.reuse_allocation(ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;
                tmp.add_assign_scaled(worker.child(), false, &x_poly, &factor).await;
                contrib_z.mul_assign(worker.child(), false, &tmp).await;
            }

            t_poly.add_assign_scaled(worker.child(), false, &contrib_z, &current_alpha).await;

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            for idx in 0..num_state_polys {
                let key = PolyIdentifier::VariablesPolynomial(idx);

                tmp.reuse_allocation(&ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;

                let key = PolyIdentifier::PermutationPolynomial(idx);                
                let perm_points = async_manager.coset_lde(
                    monomials_storage.get_poly(key).arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let perm = Polynomial::from_values(perm_points).unwrap();
                tmp.add_assign_scaled(worker.child(), false, &perm, &beta_for_copy_permutation).await;
                contrib_z.mul_assign(worker.child(), false, &tmp).await;
                drop(perm);
            }

            t_poly.sub_assign_scaled(worker.child(), false, &contrib_z, &current_alpha).await;

            drop(contrib_z);

            drop(tmp);

            // Z(x) * L_{0}(x) - 1 == 0
            current_alpha.mul_assign(&alpha);

            let alpha_1 = current_alpha;

            {
                let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
                z_minus_one_by_l_0.sub_constant(worker.child(), false, &E::Fr::one()).await;

                z_minus_one_by_l_0.mul_assign(worker.child(), false, &l_0_coset_lde_bitreversed).await;

                t_poly.add_assign_scaled(worker.child(), false, &z_minus_one_by_l_0, &current_alpha).await;
            }

            copy_grand_product_alphas = Some([alpha_0, alpha_1]);

            x_poly
        };

        // add contribution from grand product for loopup polys if there is one

        let mut lookup_grand_product_alphas = None;
        if let Some(z_poly_in_monomial_form) = lookup_z_poly_in_monomial_form.as_ref() {
            let beta_for_lookup_permutation = beta_for_lookup.unwrap();
            let gamma_for_lookup_permutation = gamma_for_lookup.unwrap();

            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);

            let expected = gamma_beta.pow([(required_domain_size - 1) as u64]);

            current_alpha.mul_assign(&alpha);

            let alpha_0 = current_alpha;

            let z_lde_values = async_manager.coset_lde(
                z_poly_in_monomial_form.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let z_lde = Polynomial::from_values(z_lde_values).unwrap();

            let z_lde_shifted = z_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            // We make an small ad-hoc modification here and instead of dividing some contributions by
            // (X^n - 1)/(X - omega^{n-1}) we move (X - omega^{n-1}) to the numerator and join the divisions

            // Numerator degree is at max 4n, so it's < 4n after division

            // ( Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
            // - Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) )*(X - omega^{n-1})

            let data = lookup_data.as_ref().unwrap();
            
            let s_lde_values = async_manager.coset_lde(
                data.s_poly_monomial.as_ref().unwrap().arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let s_lde = Polynomial::from_values(s_lde_values).unwrap();

            let s_lde_shifted = s_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

            let mut contribution = s_lde;
            contribution.add_assign_scaled(worker.child(), false, &s_lde_shifted, &beta_for_lookup_permutation).await;
            contribution.add_constant(worker.child(), false, &gamma_beta).await;
            contribution.mul_assign(worker.child(), false, &z_lde_shifted).await;

            drop(s_lde_shifted);
            drop(z_lde_shifted);

            // let t_lde = data
            //     .t_poly_monomial
            //     .as_ref()
            //     .unwrap()
            //     .as_ref()
            //     .clone()
            //     .bitreversed_lde_using_bitreversed_ntt(
            //         &old_worker,
            //         lde_factor,
            //         &omegas_bitreversed,
            //         &coset_factor,
            //     )?;
            let t_lde_values = async_manager.coset_lde(
                data.t_poly_monomial.as_ref().unwrap().arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let t_lde = Polynomial::from_values(t_lde_values).unwrap();

            let t_lde_shifted = t_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            let f_lde = {
                // add up ldes of a,b,c and table_type poly and multiply by selector

                let a_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
                    &ldes_storage,
                );
                let mut tmp = a_ref.clone();
                drop(a_ref);

                let eta = lookup_data.as_ref().unwrap().eta;

                let mut current = eta;

                let b_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
                    &ldes_storage,
                );

                tmp.add_assign_scaled(worker.child(), false, b_ref, &current).await;

                drop(b_ref);
                current.mul_assign(&eta);

                let c_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
                    &ldes_storage,
                );

                tmp.add_assign_scaled(worker.child(), false, c_ref, &current).await;

                drop(c_ref);
                current.mul_assign(&eta);

                let table_type_lde_values = async_manager.coset_lde(
                    lookup_data.as_ref().unwrap().table_type_poly_monomial.as_ref().unwrap().arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let table_type_lde = Polynomial::from_values(table_type_lde_values).unwrap();

                tmp.add_assign_scaled(worker.child(), false, &table_type_lde, &current).await;

                drop(table_type_lde);
              
                let lookup_selector_lde_values = async_manager.coset_lde(
                    lookup_data.as_ref().unwrap().selector_poly_monomial.as_ref().unwrap().arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let lookup_selector_lde = Polynomial::from_values(lookup_selector_lde_values).unwrap();

                tmp.mul_assign(worker.child(), false, &lookup_selector_lde).await;

                drop(lookup_selector_lde);

                tmp
            };

            //  - Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))

            let mut tmp = f_lde;
            tmp.add_constant(worker.child(), false, &gamma_for_lookup_permutation).await;
            tmp.mul_assign(worker.child(), false, &z_lde).await;
            tmp.scale(worker.child(), false, beta_plus_one).await;

            let mut t = t_lde;
            t.add_assign_scaled(worker.child(), false, &t_lde_shifted, &beta_for_lookup_permutation).await;
            t.add_constant(worker.child(), false, &gamma_beta).await;

            tmp.mul_assign(worker.child(), false, &t).await;

            drop(t);
            drop(t_lde_shifted);

            contribution.sub_assign(worker.child(), false, &tmp).await;

            contribution.scale(worker.child(), false, current_alpha).await;

            // multiply by (X - omega^{n-1})

            let last_omega = domain.generator.pow(&[(required_domain_size - 1) as u64]);
            let mut x_minus_last_omega = x_poly_lde_bitreversed;
            x_minus_last_omega.sub_constant(worker.child(), false, &last_omega).await;

            contribution.mul_assign(worker.child(), false, &x_minus_last_omega).await;
            drop(x_minus_last_omega);

            // we do not need to do addition multiplications for terms below cause multiplication by lagrange poly
            // does everything for us

            // check that (Z(x) - 1) * L_{0} == 0
            current_alpha.mul_assign(&alpha);

            let alpha_1 = current_alpha;

            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(worker.child(), false, &E::Fr::one()).await;
            tmp.mul_assign(worker.child(), false, &l_0_coset_lde_bitreversed).await;

            drop(l_0_coset_lde_bitreversed);

            contribution.add_assign_scaled(worker.child(), false, &tmp, &current_alpha).await;

            // check that (Z(x) - expected) * L_{n-1}  == 0

            current_alpha.mul_assign(&alpha);

            let alpha_2 = current_alpha;

            let l_last = calculate_lagrange_poly::<E>(
                async_manager.clone(),
                worker.child(), 
                false,
                required_domain_size.next_power_of_two(),
                required_domain_size - 1,
            ).await?;

            let l_last_coset_lde_bitreversed_values = async_manager.coset_lde(
                l_last.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let l_last_coset_lde_bitreversed = Polynomial::from_values(l_last_coset_lde_bitreversed_values).unwrap();

            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(worker.child(), false, &expected).await;
            tmp.mul_assign(worker.child(), false, &l_last_coset_lde_bitreversed).await;

            drop(l_last_coset_lde_bitreversed);

            contribution.add_assign_scaled(worker.child(), false, &tmp, &current_alpha).await;

            drop(tmp);
            drop(z_lde);

            t_poly.add_assign(worker.child(), false, &contribution).await;

            drop(contribution);

            lookup_grand_product_alphas = Some([alpha_0, alpha_1, alpha_2]);
        } else {
            drop(x_poly_lde_bitreversed);
            drop(l_0_coset_lde_bitreversed);
        }

        
        // perform copy-permutation argument

        // we precompute L_{0} here cause it's necessary for both copy-permutation and lookup permutation

        // z(omega^0) - 1 == 0
        let l_0 =
            calculate_lagrange_poly::<E>(async_manager.clone(), worker.child(), false, required_domain_size.next_power_of_two(), 0).await?;

        let l_0_coset_lde_bitreversed_values = async_manager.coset_lde(
            l_0.arc_coeffs(),
            lde_factor,
            &coset_factor,
            worker.child(),
            false,
        ).await;
        let l_0_coset_lde_bitreversed = Polynomial::from_values(l_0_coset_lde_bitreversed_values).unwrap();

        let mut copy_grand_product_alphas = None;
        let x_poly_lde_bitreversed = {
            // now compute the permutation argument

            // bump alpha
            current_alpha.mul_assign(&alpha);
            let alpha_0 = current_alpha;

            // let z_coset_lde_bitreversed = copy_permutation_z_in_monomial_form
            //     .clone()
            //     .bitreversed_lde_using_bitreversed_ntt(
            //         &worker,
            //         lde_factor,
            //         &omegas_bitreversed,
            //         &coset_factor,
            //     )?;
            let z_coset_lde_bitreversed_values = async_manager.coset_lde(
                copy_permutation_z_in_monomial_form.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let z_coset_lde_bitreversed = Polynomial::from_values(z_coset_lde_bitreversed_values).unwrap();

            assert!(z_coset_lde_bitreversed.size() == required_domain_size * lde_factor);

            let z_shifted_coset_lde_bitreversed =
                z_coset_lde_bitreversed.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            assert!(z_shifted_coset_lde_bitreversed.size() == required_domain_size * lde_factor);

            // For both Z_1 and Z_2 we first check for grand products
            // z*(X)(A + beta*X + gamma)(B + beta*k_1*X + gamma)(C + beta*K_2*X + gamma) -
            // - (A + beta*perm_a(X) + gamma)(B + beta*perm_b(X) + gamma)(C + beta*perm_c(X) + gamma)*Z(X*Omega)== 0

            // we use evaluations of the polynomial X and K_i * X on a large domain's coset
            let mut contrib_z = z_coset_lde_bitreversed.clone();

            // precompute x poly
            let mut x_poly =
                Polynomial::from_values(vec![coset_factor; required_domain_size * lde_factor])?;
            x_poly.distribute_powers(worker.child(), false, z_shifted_coset_lde_bitreversed.omega).await;
            x_poly.bitreverse_enumeration(worker.child(), false).await;

            assert_eq!(x_poly.size(), required_domain_size * lde_factor);

            // A + beta*X + gamma

            let mut tmp = ldes_storage
                .state_map
                .get(&PolyIdentifier::VariablesPolynomial(0))
                .unwrap().arc_clone();
            tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;
            tmp.add_assign_scaled(worker.child(), false, &x_poly, &beta_for_copy_permutation).await;
            contrib_z.mul_assign(worker.child(), false, &tmp).await;

            assert_eq!(non_residues.len() + 1, num_state_polys);

            for (poly_idx, non_res) in (1..num_state_polys).zip(non_residues.iter()) {
                let mut factor = beta_for_copy_permutation;
                factor.mul_assign(&non_res);

                let key = PolyIdentifier::VariablesPolynomial(poly_idx);
                tmp.reuse_allocation(&ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;
                tmp.add_assign_scaled(worker.child(), false, &x_poly, &factor).await;
                contrib_z.mul_assign(worker.child(), false, &tmp).await;
            }

            t_poly.add_assign_scaled(worker.child(), false, &contrib_z, &current_alpha).await;

            drop(contrib_z);

            let mut contrib_z = z_shifted_coset_lde_bitreversed;

            // A + beta*perm_a + gamma

            for idx in 0..num_state_polys {
                let key = PolyIdentifier::VariablesPolynomial(idx);

                tmp.reuse_allocation(&ldes_storage.state_map.get(&key).unwrap());
                tmp.add_constant(worker.child(), false, &gamma_for_copy_permutation).await;

                let key = PolyIdentifier::PermutationPolynomial(idx);
                // let perm = monomials_storage
                //     .get_poly(key)
                //     .clone()
                //     .bitreversed_lde_using_bitreversed_ntt(
                //         &worker,
                //         lde_factor,
                //         &omegas_bitreversed,
                //         &coset_factor,
                //     )?;
                let perm_points = async_manager.coset_lde(
                    monomials_storage.get_poly(key).arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let perm = Polynomial::from_values(perm_points).unwrap();
                tmp.add_assign_scaled(worker.child(), false, &perm, &beta_for_copy_permutation).await;
                contrib_z.mul_assign(worker.child(), false, &tmp).await;
                drop(perm);
            }

            t_poly.sub_assign_scaled(worker.child(), false, &contrib_z, &current_alpha).await;

            drop(contrib_z);

            drop(tmp);

            // Z(x) * L_{0}(x) - 1 == 0
            current_alpha.mul_assign(&alpha);

            let alpha_1 = current_alpha;

            {
                let mut z_minus_one_by_l_0 = z_coset_lde_bitreversed;
                z_minus_one_by_l_0.sub_constant(worker.child(), false, &E::Fr::one()).await;

                z_minus_one_by_l_0.mul_assign(worker.child(), false, &l_0_coset_lde_bitreversed).await;

                t_poly.add_assign_scaled(worker.child(), false, &z_minus_one_by_l_0, &current_alpha).await;
            }

            copy_grand_product_alphas = Some([alpha_0, alpha_1]);

            x_poly
        };

        // add contribution from grand product for loopup polys if there is one

        let mut lookup_grand_product_alphas = None;
        if let Some(z_poly_in_monomial_form) = lookup_z_poly_in_monomial_form.as_ref() {
            let beta_for_lookup_permutation = beta_for_lookup.unwrap();
            let gamma_for_lookup_permutation = gamma_for_lookup.unwrap();

            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);

            let expected = gamma_beta.pow([(required_domain_size - 1) as u64]);

            current_alpha.mul_assign(&alpha);

            let alpha_0 = current_alpha;

            // same grand product argument for lookup permutation except divisor is now with one point cut

            // let z_lde = z_poly_in_monomial_form
            //     .clone()
            //     .bitreversed_lde_using_bitreversed_ntt(
            //         &worker,
            //         lde_factor,
            //         &omegas_bitreversed,
            //         &coset_factor,
            //     )?;
            let z_lde_values = async_manager.coset_lde(
                z_poly_in_monomial_form.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let z_lde = Polynomial::from_values(z_lde_values).unwrap();

            let z_lde_shifted = z_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            // We make an small ad-hoc modification here and instead of dividing some contributions by
            // (X^n - 1)/(X - omega^{n-1}) we move (X - omega^{n-1}) to the numerator and join the divisions

            // Numerator degree is at max 4n, so it's < 4n after division

            // ( Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
            // - Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) )*(X - omega^{n-1})

            let data = lookup_data.as_ref().unwrap();

            // let s_lde = data
            //     .s_poly_monomial
            //     .as_ref()
            //     .unwrap()
            //     .clone()
            //     .bitreversed_lde_using_bitreversed_ntt(
            //         &worker,
            //         lde_factor,
            //         &omegas_bitreversed,
            //         &coset_factor,
            //     )?;
            let s_lde_values = async_manager.coset_lde(
                data.s_poly_monomial.as_ref().unwrap().arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let s_lde = Polynomial::from_values(s_lde_values).unwrap();

            let s_lde_shifted = s_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))

            let mut contribution = s_lde;
            contribution.add_assign_scaled(worker.child(), false, &s_lde_shifted, &beta_for_lookup_permutation).await;
            contribution.add_constant(worker.child(), false, &gamma_beta).await;
            contribution.mul_assign(worker.child(), false, &z_lde_shifted).await;

            drop(s_lde_shifted);
            drop(z_lde_shifted);

            
            let t_lde_values = async_manager.coset_lde(
                data.t_poly_monomial.as_ref().unwrap().arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let t_lde = Polynomial::from_values(t_lde_values).unwrap();

            let t_lde_shifted = t_lde.clone_shifted_assuming_bitreversed(lde_factor, worker.child(), false).await?;

            let f_lde = {
                // add up ldes of a,b,c and table_type poly and multiply by selector

                let a_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(0)),
                    &ldes_storage,
                );
                let mut tmp = a_ref.clone();
                drop(a_ref);

                let eta = lookup_data.as_ref().unwrap().eta;

                let mut current = eta;

                let b_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(1)),
                    &ldes_storage,
                );

                tmp.add_assign_scaled(worker.child(), false, b_ref, &current).await;

                drop(b_ref);
                current.mul_assign(&eta);

                let c_ref = get_from_map_unchecked(
                    PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(2)),
                    &ldes_storage,
                );

                tmp.add_assign_scaled(worker.child(), false, c_ref, &current).await;

                drop(c_ref);
                current.mul_assign(&eta);

               
                let table_type_lde_values = async_manager.coset_lde(
                    lookup_data.as_ref().unwrap().table_type_poly_monomial.as_ref().unwrap().arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let table_type_lde = Polynomial::from_values(table_type_lde_values).unwrap();

                tmp.add_assign_scaled(worker.child(), false, &table_type_lde, &current).await;

                drop(table_type_lde);

                let lookup_selector_lde_values = async_manager.coset_lde(
                    lookup_data.as_ref().unwrap().selector_poly_monomial.as_ref().unwrap().arc_coeffs(),
                    lde_factor,
                    &coset_factor,
                    worker.child(),
                    false,
                ).await;
                let lookup_selector_lde = Polynomial::from_values(lookup_selector_lde_values).unwrap();

                tmp.mul_assign(worker.child(), false, &lookup_selector_lde).await;

                drop(lookup_selector_lde);

                tmp
            };

            //  - Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))

            let mut tmp = f_lde;
            tmp.add_constant(worker.child(), false, &gamma_for_lookup_permutation).await;
            tmp.mul_assign(worker.child(), false, &z_lde).await;
            tmp.scale(worker.child(), false, beta_plus_one).await;

            let mut t = t_lde;
            t.add_assign_scaled(worker.child(), false, &t_lde_shifted, &beta_for_lookup_permutation).await;
            t.add_constant(worker.child(), false, &gamma_beta).await;

            tmp.mul_assign(worker.child(), false, &t).await;

            drop(t);
            drop(t_lde_shifted);

            contribution.sub_assign(worker.child(), false, &tmp).await;

            contribution.scale(worker.child(), false, current_alpha).await;

            // multiply by (X - omega^{n-1})

            let last_omega = domain.generator.pow(&[(required_domain_size - 1) as u64]);
            let mut x_minus_last_omega = x_poly_lde_bitreversed;
            x_minus_last_omega.sub_constant(worker.child(), false, &last_omega).await;

            contribution.mul_assign(worker.child(), false, &x_minus_last_omega).await;
            drop(x_minus_last_omega);

            // we do not need to do addition multiplications for terms below cause multiplication by lagrange poly
            // does everything for us

            // check that (Z(x) - 1) * L_{0} == 0
            current_alpha.mul_assign(&alpha);

            let alpha_1 = current_alpha;

            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(worker.child(), false, &E::Fr::one()).await;
            tmp.mul_assign(worker.child(), false, &l_0_coset_lde_bitreversed).await;

            drop(l_0_coset_lde_bitreversed);

            contribution.add_assign_scaled(worker.child(), false, &tmp, &current_alpha).await;

            // check that (Z(x) - expected) * L_{n-1}  == 0

            current_alpha.mul_assign(&alpha);

            let alpha_2 = current_alpha;

            let l_last = calculate_lagrange_poly::<E>(
                async_manager.clone(),
                worker.child(), 
                false,
                required_domain_size.next_power_of_two(),
                required_domain_size - 1,
            ).await?;

            // let l_last_coset_lde_bitreversed = l_last.bitreversed_lde_using_bitreversed_ntt(
            //     &worker,
            //     lde_factor,
            //     &omegas_bitreversed,
            //     &coset_factor,
            // )?;
            let l_last_coset_lde_bitreversed_values = async_manager.coset_lde(
                l_last.arc_coeffs(),
                lde_factor,
                &coset_factor,
                worker.child(),
                false,
            ).await;
            let l_last_coset_lde_bitreversed = Polynomial::from_values(l_last_coset_lde_bitreversed_values).unwrap();

            tmp.reuse_allocation(&z_lde);
            tmp.sub_constant(worker.child(), false, &expected).await;
            tmp.mul_assign(worker.child(), false, &l_last_coset_lde_bitreversed).await;

            drop(l_last_coset_lde_bitreversed);

            contribution.add_assign_scaled(worker.child(), false, &tmp, &current_alpha).await;

            drop(tmp);
            drop(z_lde);

            t_poly.add_assign(worker.child(), false, &contribution).await;

            drop(contribution);

            lookup_grand_product_alphas = Some([alpha_0, alpha_1, alpha_2]);
        } else {
            drop(x_poly_lde_bitreversed);
            drop(l_0_coset_lde_bitreversed);
        }

        // perform the division

        let inverse_divisor_on_coset_lde_natural_ordering = {
            let mut vanishing_poly_inverse_bitreversed =
                evaluate_vanishing_polynomial_of_degree_on_domain_size::<E::Fr>(
                    required_domain_size as u64,
                    &E::Fr::multiplicative_generator(),
                    (required_domain_size * lde_factor) as u64,
                    worker.child(), false,
                ).await?;
            vanishing_poly_inverse_bitreversed.batch_inversion(worker.child(), false).await?;
            // vanishing_poly_inverse_bitreversed.bitreverse_enumeration(&worker)?;

            vanishing_poly_inverse_bitreversed
        };

        // don't forget to bitreverse

        t_poly.bitreverse_enumeration(worker.child(), false).await;

        t_poly.mul_assign(worker.child(), false, &inverse_divisor_on_coset_lde_natural_ordering).await;

        drop(inverse_divisor_on_coset_lde_natural_ordering);

        let t_poly = t_poly.icoset_fft_for_generator(&old_worker,worker.child(), false, &coset_factor).await;

        println!("Lde factor = {}", lde_factor);

        // println!("Quotient poly = {:?}", t_poly.as_ref());

        {
            // degree is 4n-4
            let l = t_poly.as_ref().len();
            if &t_poly.as_ref()[(l - 4)..] != &[E::Fr::zero(); 4][..] {
                dbg!("quotient polynomial is invalid");
                // FIXME
                // return Err(SynthesisError::Unsatisfiable);
            }
            // assert_eq!(&t_poly.as_ref()[(l-4)..], &[E::Fr::zero(); 4][..], "quotient degree is too large");
        }

        // println!("Quotient poly degree = {}", get_degree::<E::Fr>(&t_poly));

        let mut t_poly_parts = t_poly.break_into_multiples(required_domain_size)?;

        for part in t_poly_parts.iter() {
            // let commitment = commit_using_monomials(part, mon_crs, &worker)?;
            let commitment = async_manager.multiexp(part.arc_coeffs(), worker.child(), false).await;

            commit_point_as_xy::<E, T>(&mut transcript, &commitment);
            num_commitments += 1;

            proof.quotient_poly_parts_commitments.push(commitment);
        }

        println!("num_commitments {}", num_commitments);
        // draw opening point
        let z = transcript.get_challenge();

        // let z = E::Fr::from_str("333444555").unwrap();
        let omega = domain.generator;

        // evaluate quotient at z

        let quotient_at_z = {
            let mut result = E::Fr::zero();
            let mut current = E::Fr::one();
            let z_in_domain_size = z.pow(&[required_domain_size as u64]);
            for p in t_poly_parts.iter() {
                let mut subvalue_at_z = p.evaluate_at(worker.child(), false, z).await;

                subvalue_at_z.mul_assign(&current);
                result.add_assign(&subvalue_at_z);
                current.mul_assign(&z_in_domain_size);
            }

            result
        };

        // commit quotient value
        transcript.commit_field_element(&quotient_at_z);

        proof.quotient_poly_opening_at_z = quotient_at_z;



        // Now perform the linearization.
        // First collect and evalute all the polynomials that are necessary for linearization
        // and construction of the verification equation

        const MAX_DILATION: usize = 1;

        let queries_with_linearization =
            crate::plonk::better_better_cs::proof::utils::sort_queries_for_linearization_new(&self.sorted_gates, MAX_DILATION);

        let mut query_values_map = std::collections::HashMap::new();

        // go over all required queries

        for (dilation_value, ids) in queries_with_linearization.state_polys.iter().enumerate() {
            for id in ids.into_iter() {
                let (poly_ref, poly_idx) = if let PolyIdentifier::VariablesPolynomial(idx) = id {
                    (monomials_storage.state_map.get(&id).unwrap(), idx)
                } else {
                    unreachable!();
                };

                let mut opening_point = z;
                for _ in 0..dilation_value {
                    opening_point.mul_assign(&omega);
                }

                let value = poly_ref.evaluate_at(worker.child(), false, opening_point).await;

                transcript.commit_field_element(&value);

                if dilation_value == 0 {
                    proof.state_polys_openings_at_z.push(value);
                } else {
                    proof.state_polys_openings_at_dilations.push((
                        dilation_value,
                        *poly_idx,
                        value,
                    ));
                }

                let key = PolynomialInConstraint::from_id_and_dilation(*id, dilation_value);

                query_values_map.insert(key, value);
            }
        }

        for (dilation_value, ids) in queries_with_linearization.witness_polys.iter().enumerate() {
            for id in ids.into_iter() {
                let (poly_ref, poly_idx) = if let PolyIdentifier::WitnessPolynomial(idx) = id {
                    (
                        monomials_storage.witness_map.get(&id).unwrap(),
                        idx,
                    )
                } else {
                    unreachable!();
                };

                let mut opening_point = z;
                for _ in 0..dilation_value {
                    opening_point.mul_assign(&omega);
                }

                let value = poly_ref.evaluate_at(worker.child(), false, opening_point).await;

                transcript.commit_field_element(&value);

                if dilation_value == 0 {
                    proof.witness_polys_openings_at_z.push(value);
                } else {
                    proof.witness_polys_openings_at_dilations.push((
                        dilation_value,
                        *poly_idx,
                        value,
                    ));
                }

                let key = PolynomialInConstraint::from_id_and_dilation(*id, dilation_value);

                query_values_map.insert(key, value);
            }
        }

        for (gate_idx, queries) in queries_with_linearization
            .gate_setup_polys
            .iter()
            .enumerate()
        {
            for (dilation_value, ids) in queries.iter().enumerate() {
                for id in ids.into_iter() {
                    let (poly_ref, poly_idx) =
                        if let PolyIdentifier::GateSetupPolynomial(_, idx) = id {
                            (monomials_storage.setup_map.get(&id).unwrap(), idx)
                        } else {
                            unreachable!();
                        };

                    let mut opening_point = z;
                    for _ in 0..dilation_value {
                        opening_point.mul_assign(&omega);
                    }

                    let value = poly_ref.evaluate_at(worker.child(), false, opening_point).await;

                    transcript.commit_field_element(&value);

                    if dilation_value == 0 {
                        proof
                            .gate_setup_openings_at_z
                            .push((gate_idx, *poly_idx, value));
                    } else {
                        unimplemented!("gate setup polynomials can not be time dilated");
                    }

                    let key = PolynomialInConstraint::from_id_and_dilation(*id, dilation_value);

                    query_values_map.insert(key, value);
                }
            }
        }

        // also open selectors

        let mut selector_values = vec![];
        for s in queries_with_linearization.gate_selectors.iter() {
            let gate_index = self.sorted_gates.iter().position(|r| r == s).unwrap();

            let key = PolyIdentifier::GateSelector(s.name());
            let poly_ref = monomials_storage.gate_selectors.get(&key).unwrap();
            let value = poly_ref.evaluate_at(worker.child(), false, z).await;

            transcript.commit_field_element(&value);

            proof.gate_selectors_openings_at_z.push((gate_index, value));

            selector_values.push(value);
        }

        // copy-permutation polynomials queries

        let mut copy_permutation_queries = vec![];

        for idx in 0..(num_state_polys - 1) {
            let key = PolyIdentifier::PermutationPolynomial(idx);
            let value = monomials_storage.get_poly(key).evaluate_at(worker.child(), false, z).await;

            transcript.commit_field_element(&value);

            proof.copy_permutation_polys_openings_at_z.push(value);

            copy_permutation_queries.push(value);
        }

        // copy-permutation grand product query

        let mut z_omega = z;
        z_omega.mul_assign(&domain.generator);
        let copy_permutation_z_at_z_omega =
            copy_permutation_z_in_monomial_form.evaluate_at(worker.child(), false, z_omega).await;
        transcript.commit_field_element(&copy_permutation_z_at_z_omega);
        proof.copy_permutation_grand_product_opening_at_z_omega = copy_permutation_z_at_z_omega;

        // we've computed everything, so perform linearization

        let mut challenges_slice = &powers_of_alpha_for_gates[..];

        let mut all_gates = self.sorted_gates.clone();

        let mut r_poly = {
            let gate = all_gates.drain(0..1).into_iter().next().unwrap();
            assert!(
                gate.benefits_from_linearization(),
                "main gate is expected to benefit from linearization!"
            );
            assert!(<Self as ConstraintSystem<E>>::MainGate::default().into_internal() == gate);
            let gate = <Self as ConstraintSystem<E>>::MainGate::default();
            let num_challenges = gate.num_quotient_terms();
            let (for_gate, rest) = challenges_slice.split_at(num_challenges);
            challenges_slice = rest;

            let input_values = self.input_assingments.clone();

            let mut r = main_gate_contribute_into_linearization_for_public_inputs(
                &gate,
                required_domain_size,
                &input_values,
                z,
                &query_values_map,
                &monomials_storage,
                for_gate,
                worker.child(),
                false,
            ).await?;

            let mut selectors_it = selector_values.clone().into_iter();

            if num_different_gates > 1 {
                // first multiply r by the selector value at z
                r.scale(worker.child(), false, selectors_it.next().unwrap()).await;
            }

            // now proceed per gate
            for gate in all_gates.into_iter() {
                let num_challenges = gate.num_quotient_terms();
                let (for_gate, rest) = challenges_slice.split_at(num_challenges);
                challenges_slice = rest;

                if gate.benefits_from_linearization() {
                    // gate benefits from linearization, so make temporary value
                    let tmp = gate.contribute_into_linearization(
                        required_domain_size,
                        z,
                        &query_values_map,
                        &monomials_storage,
                        for_gate,
                        &old_worker,
                    )?;

                    let selector_value = selectors_it.next().unwrap();

                    r.add_assign_scaled(worker.child(), false, &tmp, &selector_value).await;
                } else {
                    // we linearize over the selector, so take a selector and scale it
                    let gate_value_at_z = gate.contribute_into_verification_equation(
                        required_domain_size,
                        z,
                        &query_values_map,
                        for_gate,
                    )?;

                    let key = PolyIdentifier::GateSelector(gate.name());
                    let gate_selector_ref = monomials_storage
                        .gate_selectors
                        .get(&key)
                        .expect("must get monomial form of gate selector");

                    r.add_assign_scaled(worker.child(), false, gate_selector_ref, &gate_value_at_z).await;
                }
            }

            assert!(selectors_it.next().is_none());
            assert_eq!(challenges_slice.len(), 0);

            r
        };

        // add contributions from copy-permutation and lookup-permutation

        // copy-permutation linearization comtribution
        {
            // + (a(z) + beta*z + gamma)*()*()*()*Z(x)

            let [alpha_0, alpha_1] = copy_grand_product_alphas
                .expect("there must be powers of alpha for copy permutation");

            let some_one = Some(E::Fr::one());
            let mut non_residues_iterator = some_one.iter().chain(&non_residues);

            let mut factor = alpha_0;

            for idx in 0..num_state_polys {
                let key = PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(idx));
                let wire_value = query_values_map
                    .get(&key)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let mut t = z;
                let non_res = non_residues_iterator.next().unwrap();
                t.mul_assign(&non_res);
                t.mul_assign(&beta_for_copy_permutation);
                t.add_assign(&wire_value);
                t.add_assign(&gamma_for_copy_permutation);

                factor.mul_assign(&t);
            }

            assert!(non_residues_iterator.next().is_none());

            r_poly.add_assign_scaled(worker.child(), false, &copy_permutation_z_in_monomial_form, &factor).await;

            // - (a(z) + beta*perm_a + gamma)*()*()*z(z*omega) * beta * perm_d(X)

            let mut factor = alpha_0;
            factor.mul_assign(&beta_for_copy_permutation);
            factor.mul_assign(&copy_permutation_z_at_z_omega);

            for idx in 0..(num_state_polys - 1) {
                let key = PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(idx));
                let wire_value = query_values_map
                    .get(&key)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let permutation_at_z = copy_permutation_queries[idx];
                let mut t = permutation_at_z;

                t.mul_assign(&beta_for_copy_permutation);
                t.add_assign(&wire_value);
                t.add_assign(&gamma_for_copy_permutation);

                factor.mul_assign(&t);
            }

            let key = PolyIdentifier::PermutationPolynomial(num_state_polys - 1);
            let last_permutation_poly_ref = monomials_storage.get_poly(key);

            r_poly.sub_assign_scaled(worker.child(), false, last_permutation_poly_ref, &factor).await;

            // + L_0(z) * Z(x)

            let mut factor = evaluate_l0_at_point(required_domain_size as u64, z)?;
            factor.mul_assign(&alpha_1);

            r_poly.add_assign_scaled(worker.child(), false, &copy_permutation_z_in_monomial_form, &factor).await;
        }

        // lookup grand product linearization

        // due to separate divisor it's not obvious if this is beneficial without some tricks
        // like multiplication by (1 - L_{n-1}) or by (x - omega^{n-1})

        // Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
        // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) == 0
        // check that (Z(x) - 1) * L_{0} == 0
        // check that (Z(x) - expected) * L_{n-1} == 0, or (Z(x*omega) - expected)* L_{n-2} == 0

        // f(x) does not need to be opened as it's made of table selector and witnesses
        // if we pursue the strategy from the linearization of a copy-permutation argument
        // then we leave something like s(x) from the Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) term,
        // and Z(x) from Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) term,
        // with terms with lagrange polys as multipliers left intact

        let lookup_queries = if let Some(lookup_z_poly) = lookup_z_poly_in_monomial_form.as_ref() {
            let [alpha_0, alpha_1, alpha_2] = lookup_grand_product_alphas
                .expect("there must be powers of alpha for lookup permutation");

            let s_at_z_omega = lookup_data
                .as_ref()
                .unwrap()
                .s_poly_monomial
                .as_ref()
                .unwrap()
                .evaluate_at(worker.child(), false, z_omega).await;
            let grand_product_at_z_omega = lookup_z_poly.evaluate_at(worker.child(), false, z_omega).await;
            let t_at_z = lookup_data
                .as_ref()
                .unwrap()
                .t_poly_monomial
                .as_ref()
                .unwrap()
                .evaluate_at(worker.child(), false, z).await;
            let t_at_z_omega = lookup_data
                .as_ref()
                .unwrap()
                .t_poly_monomial
                .as_ref()
                .unwrap()
                .evaluate_at(worker.child(), false, z_omega).await;
            let selector_at_z = lookup_data
                .as_ref()
                .unwrap()
                .selector_poly_monomial
                .as_ref()
                .unwrap()
                .evaluate_at(worker.child(), false, z).await;
            let table_type_at_z = lookup_data
                .as_ref()
                .unwrap()
                .table_type_poly_monomial
                .as_ref()
                .unwrap()
                .evaluate_at(worker.child(), false, z).await;

            let l_0_at_z = evaluate_lagrange_poly_at_point(0, &domain, z)?;
            let l_n_minus_one_at_z =
                evaluate_lagrange_poly_at_point(required_domain_size - 1, &domain, z)?;

            let beta_for_lookup_permutation = beta_for_lookup.unwrap();
            let gamma_for_lookup_permutation = gamma_for_lookup.unwrap();

            let mut beta_plus_one = beta_for_lookup_permutation;
            beta_plus_one.add_assign(&E::Fr::one());
            let mut gamma_beta = gamma_for_lookup_permutation;
            gamma_beta.mul_assign(&beta_plus_one);

            // (Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega))) -
            // Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)))*(X - omega^{n-1})

            let last_omega = domain.generator.pow(&[(required_domain_size - 1) as u64]);
            let mut z_minus_last_omega = z;
            z_minus_last_omega.sub_assign(&last_omega);

            // s(x) from the Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))
            let mut factor = grand_product_at_z_omega; // we do not need to account for additive terms
            factor.mul_assign(&alpha_0);
            factor.mul_assign(&z_minus_last_omega);

            r_poly.add_assign_scaled(
                worker.child(), 
                false,
                lookup_data
                    .as_ref()
                    .unwrap()
                    .s_poly_monomial
                    .as_ref()
                    .unwrap(),
                &factor,
            ).await;

            // Z(x) from - alpha_0 * Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega))
            // + alpha_1 * Z(x) * L_{0}(z) + alpha_2 * Z(x) * L_{n-1}(z)

            // accumulate coefficient
            let mut factor = t_at_z_omega;
            factor.mul_assign(&beta_for_lookup_permutation);
            factor.add_assign(&t_at_z);
            factor.add_assign(&gamma_beta);

            // (\gamma + f(x))

            let mut f_reconstructed = E::Fr::zero();
            let mut current = E::Fr::one();
            let eta = lookup_data.as_ref().unwrap().eta;
            // a,b,c
            for idx in 0..(num_state_polys - 1) {
                let key = PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(idx));
                let mut value = *query_values_map
                    .get(&key)
                    .ok_or(SynthesisError::AssignmentMissing)?;

                value.mul_assign(&current);
                f_reconstructed.add_assign(&value);

                current.mul_assign(&eta);
            }

            // and table type
            let mut t = table_type_at_z;
            t.mul_assign(&current);
            f_reconstructed.add_assign(&t);

            f_reconstructed.mul_assign(&selector_at_z);
            f_reconstructed.add_assign(&gamma_for_lookup_permutation);

            // end of (\gamma + f(x)) part

            factor.mul_assign(&f_reconstructed);
            factor.mul_assign(&beta_plus_one);
            factor.negate(); // don't forget minus sign
            factor.mul_assign(&alpha_0);

            // Multiply by (z - omega^{n-1})

            factor.mul_assign(&z_minus_last_omega);

            // L_{0}(z) in front of Z(x)

            let mut tmp = l_0_at_z;
            tmp.mul_assign(&alpha_1);
            factor.add_assign(&tmp);

            // L_{n-1}(z) in front of Z(x)

            let mut tmp = l_n_minus_one_at_z;
            tmp.mul_assign(&alpha_2);
            factor.add_assign(&tmp);

            r_poly.add_assign_scaled(worker.child(), false, lookup_z_poly, &factor).await;

            let query = LookupQuery::<E> {
                s_at_z_omega,
                grand_product_at_z_omega,
                t_at_z,
                t_at_z_omega,
                selector_at_z,
                table_type_at_z,
            };

            Some(query)
        } else {
            None
        };

        if let Some(queries) = lookup_queries.as_ref() {
            // first commit values at z, and then at z*omega
            transcript.commit_field_element(&queries.t_at_z);
            transcript.commit_field_element(&queries.selector_at_z);
            transcript.commit_field_element(&queries.table_type_at_z);

            // now at z*omega
            transcript.commit_field_element(&queries.s_at_z_omega);
            transcript.commit_field_element(&queries.grand_product_at_z_omega);
            transcript.commit_field_element(&queries.t_at_z_omega);

            proof.lookup_s_poly_opening_at_z_omega = Some(queries.s_at_z_omega);
            proof.lookup_grand_product_opening_at_z_omega = Some(queries.grand_product_at_z_omega);
            proof.lookup_t_poly_opening_at_z = Some(queries.t_at_z);
            proof.lookup_t_poly_opening_at_z_omega = Some(queries.t_at_z_omega);
            proof.lookup_selector_poly_opening_at_z = Some(queries.selector_at_z);
            proof.lookup_table_type_poly_opening_at_z = Some(queries.table_type_at_z);
        }

        let linearization_at_z = r_poly.evaluate_at(worker.child(), false, z).await;

        transcript.commit_field_element(&linearization_at_z);
        proof.linearization_poly_opening_at_z = linearization_at_z;


        // linearization is done, now perform sanity check
        // this is effectively a verification procedure

        {
            let vanishing_at_z = evaluate_vanishing_for_size(&z, required_domain_size as u64);

            // first let's aggregate gates

            let mut t_num_on_full_domain = E::Fr::zero();

            let challenges_slice = &powers_of_alpha_for_gates[..];

            let mut all_gates = self.sorted_gates.clone();

            // we've suffered and linearization polynomial captures all the gates except the public input!

            {
                let mut tmp = linearization_at_z;
                // add input values

                let gate = all_gates.drain(0..1).into_iter().next().unwrap();
                assert!(
                    gate.benefits_from_linearization(),
                    "main gate is expected to benefit from linearization!"
                );
                assert!(<Self as ConstraintSystem<E>>::MainGate::default().into_internal() == gate);
                let gate = <Self as ConstraintSystem<E>>::MainGate::default();
                let num_challenges = gate.num_quotient_terms();
                let (for_gate, _) = challenges_slice.split_at(num_challenges);

                let input_values = self.input_assingments.clone();

                let mut inputs_term = gate.add_inputs_into_quotient(
                    required_domain_size,
                    &input_values,
                    z,
                    for_gate,
                )?;

                if num_different_gates > 1 {
                    let selector_value = selector_values[0];
                    inputs_term.mul_assign(&selector_value);
                }

                tmp.add_assign(&inputs_term);

                t_num_on_full_domain.add_assign(&tmp);
            }

            // now aggregate leftovers from grand product for copy permutation
            {
                // - alpha_0 * (a + perm(z) * beta + gamma)*()*(d + gamma) * z(z*omega)
                let [alpha_0, alpha_1] = copy_grand_product_alphas
                    .expect("there must be powers of alpha for copy permutation");

                let mut factor = alpha_0;
                factor.mul_assign(&copy_permutation_z_at_z_omega);

                for idx in 0..(num_state_polys - 1) {
                    let key =
                        PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(idx));
                    let wire_value = query_values_map
                        .get(&key)
                        .ok_or(SynthesisError::AssignmentMissing)?;
                    let permutation_at_z = copy_permutation_queries[idx];
                    let mut t = permutation_at_z;

                    t.mul_assign(&beta_for_copy_permutation);
                    t.add_assign(&wire_value);
                    t.add_assign(&gamma_for_copy_permutation);

                    factor.mul_assign(&t);
                }

                let key = PolynomialInConstraint::from_id(PolyIdentifier::VariablesPolynomial(
                    num_state_polys - 1,
                ));
                let mut tmp = *query_values_map
                    .get(&key)
                    .ok_or(SynthesisError::AssignmentMissing)?;
                tmp.add_assign(&gamma_for_copy_permutation);

                factor.mul_assign(&tmp);

                t_num_on_full_domain.sub_assign(&factor);

                // - L_0(z) * alpha_1

                let mut l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;
                l_0_at_z.mul_assign(&alpha_1);

                t_num_on_full_domain.sub_assign(&l_0_at_z);
            }

            // and if exists - grand product for lookup permutation

            {
                if lookup_queries.is_some() {
                    let [alpha_0, alpha_1, alpha_2] = lookup_grand_product_alphas
                        .expect("there must be powers of alpha for lookup permutation");

                    let lookup_queries =
                        lookup_queries.clone().expect("lookup queries must be made");

                    let beta_for_lookup_permutation = beta_for_lookup.unwrap();
                    let gamma_for_lookup_permutation = gamma_for_lookup.unwrap();
                    let mut beta_plus_one = beta_for_lookup_permutation;
                    beta_plus_one.add_assign(&E::Fr::one());
                    let mut gamma_beta = gamma_for_lookup_permutation;
                    gamma_beta.mul_assign(&beta_plus_one);

                    let expected = gamma_beta.pow([(required_domain_size - 1) as u64]);

                    // in a linearization we've taken terms:
                    // - s(x) from the alpha_0 * Z(x*omega)*(\gamma*(1 + \beta) + s(x) + \beta * s(x*omega)))
                    // - and Z(x) from - alpha_0 * Z(x) * (\beta + 1) * (\gamma + f(x)) * (\gamma(1 + \beta) + t(x) + \beta * t(x*omega)) (term in full) +
                    // + alpha_1 * (Z(x) - 1) * L_{0}(z) + alpha_2 * (Z(x) - expected) * L_{n-1}(z)

                    // first make alpha_0 * Z(x*omega)*(\gamma*(1 + \beta) + \beta * s(x*omega)))

                    let mut tmp = lookup_queries.s_at_z_omega;
                    tmp.mul_assign(&beta_for_lookup_permutation);
                    tmp.add_assign(&gamma_beta);
                    tmp.mul_assign(&lookup_queries.grand_product_at_z_omega);
                    tmp.mul_assign(&alpha_0);

                    // (z - omega^{n-1}) for this part
                    let last_omega = domain.generator.pow(&[(required_domain_size - 1) as u64]);
                    let mut z_minus_last_omega = z;
                    z_minus_last_omega.sub_assign(&last_omega);

                    tmp.mul_assign(&z_minus_last_omega);

                    t_num_on_full_domain.add_assign(&tmp);

                    // // - alpha_1 * L_{0}(z)

                    let mut l_0_at_z = evaluate_l0_at_point(required_domain_size as u64, z)?;
                    l_0_at_z.mul_assign(&alpha_1);

                    t_num_on_full_domain.sub_assign(&l_0_at_z);

                    // // - alpha_2 * expected L_{n-1}(z)

                    let mut l_n_minus_one_at_z =
                        evaluate_lagrange_poly_at_point(required_domain_size - 1, &domain, z)?;
                    l_n_minus_one_at_z.mul_assign(&expected);
                    l_n_minus_one_at_z.mul_assign(&alpha_2);

                    t_num_on_full_domain.sub_assign(&l_n_minus_one_at_z);
                }
            }

            let mut lhs = quotient_at_z;
            lhs.mul_assign(&vanishing_at_z);

            let rhs = t_num_on_full_domain;

            if lhs != rhs {
                // FIXME
                dbg!("Circuit is not satisfied");
                // return Err(SynthesisError::Unsatisfiable);
            }
        }

        let v = transcript.get_challenge();


         // now construct two polynomials that are opened at z and z*omega

         let mut multiopening_challenge = E::Fr::one();

         let mut poly_to_divide_at_z = t_poly_parts.drain(0..1).collect::<Vec<_>>().pop().unwrap();
         let z_in_domain_size = z.pow(&[required_domain_size as u64]);
         let mut power_of_z = z_in_domain_size;
         for t_part in t_poly_parts.into_iter() {
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, &t_part, &power_of_z).await;
             power_of_z.mul_assign(&z_in_domain_size);
         }
 
         // linearization polynomial
         multiopening_challenge.mul_assign(&v);
         poly_to_divide_at_z.add_assign_scaled(worker.child(), false, &r_poly, &multiopening_challenge).await;
 
         debug_assert_eq!(multiopening_challenge, v.pow(&[1 as u64]));
 
         // now proceed over all queries
 
         const THIS_STEP_DILATION: usize = 0;
         for id in queries_with_linearization.state_polys[THIS_STEP_DILATION].iter() {
             multiopening_challenge.mul_assign(&v);
             let poly_ref = monomials_storage.get_poly(*id);
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         for id in queries_with_linearization.witness_polys[THIS_STEP_DILATION].iter() {
             multiopening_challenge.mul_assign(&v);
             let poly_ref = monomials_storage.get_poly(*id);
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         for queries in queries_with_linearization.gate_setup_polys.iter() {
             for id in queries[THIS_STEP_DILATION].iter() {
                 multiopening_challenge.mul_assign(&v);
                 let poly_ref = monomials_storage.get_poly(*id);
                 poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
             }
         }
 
         // also open selectors at z
         for s in queries_with_linearization.gate_selectors.iter() {
             multiopening_challenge.mul_assign(&v);
             let key = PolyIdentifier::GateSelector(s.name());
             let poly_ref = monomials_storage.get_poly(key);
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         for idx in 0..(num_state_polys - 1) {
             multiopening_challenge.mul_assign(&v);
             let key = PolyIdentifier::PermutationPolynomial(idx);
             let poly_ref = monomials_storage.get_poly(key);
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         // if lookup is present - add it
         if let Some(data) = lookup_data.as_ref() {
             // we need to add t(x), selector(x) and table type(x)
             multiopening_challenge.mul_assign(&v);
             let poly_ref = data.t_poly_monomial.as_ref().unwrap();
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
 
             multiopening_challenge.mul_assign(&v);
             let poly_ref = data.selector_poly_monomial.as_ref().unwrap();
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
 
             multiopening_challenge.mul_assign(&v);
             let poly_ref = data.table_type_poly_monomial.as_ref().unwrap();
             poly_to_divide_at_z.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         // now proceed at z*omega
         multiopening_challenge.mul_assign(&v);
         let mut poly_to_divide_at_z_omega = copy_permutation_z_in_monomial_form;
         poly_to_divide_at_z_omega.scale(worker.child(), false, multiopening_challenge).await;
 
         // {
         //     let tmp = commit_using_monomials(
         //         &poly_to_divide_at_z_omega,
         //         &mon_crs,
         //         &worker
         //     )?;
 
         //     dbg!(tmp);
 
         //     let tmp = poly_to_divide_at_z_omega.evaluate_at(&worker, z_omega);
 
         //     dbg!(tmp);
         // }
 
         const NEXT_STEP_DILATION: usize = 1;
 
         for id in queries_with_linearization.state_polys[NEXT_STEP_DILATION].iter() {
             multiopening_challenge.mul_assign(&v);
             let poly_ref = monomials_storage.get_poly(*id);
             poly_to_divide_at_z_omega.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         for id in queries_with_linearization.witness_polys[NEXT_STEP_DILATION].iter() {
             multiopening_challenge.mul_assign(&v);
             let poly_ref = monomials_storage.get_poly(*id);
             poly_to_divide_at_z_omega.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         for queries in queries_with_linearization.gate_setup_polys.iter() {
             for id in queries[NEXT_STEP_DILATION].iter() {
                 multiopening_challenge.mul_assign(&v);
                 let poly_ref = monomials_storage.get_poly(*id);
                 poly_to_divide_at_z_omega.add_assign_scaled(
                    worker.child(), 
                    false,
                     poly_ref,
                     &multiopening_challenge,
                 ).await;
             }
         }
 
         if let Some(data) = lookup_data {
             // we need to add s(x), grand_product(x) and t(x)
             multiopening_challenge.mul_assign(&v);
             let poly_ref = data.s_poly_monomial.as_ref().unwrap();
             poly_to_divide_at_z_omega.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
 
             multiopening_challenge.mul_assign(&v);
             let poly_ref = lookup_z_poly_in_monomial_form.as_ref().unwrap();
             poly_to_divide_at_z_omega.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
 
             multiopening_challenge.mul_assign(&v);
             let poly_ref = data.t_poly_monomial.as_ref().unwrap();
             poly_to_divide_at_z_omega.add_assign_scaled(worker.child(), false, poly_ref, &multiopening_challenge).await;
         }
 
         // division in monomial form is sequential, so we parallelize the divisions
 
         let mut z_by_omega = z;
         z_by_omega.mul_assign(&domain.generator);
 
        //  let mut polys = vec![
        //      (poly_to_divide_at_z, z),
        //      (poly_to_divide_at_z_omega, z_by_omega),
        //  ];

         let poly_to_divide_at_z = divide_single_async::<E>(worker.child(), false, poly_to_divide_at_z.arc_coeffs(), z).await;
         let open_at_z_omega = Polynomial::from_coeffs(poly_to_divide_at_z).unwrap();
         let poly_to_divide_at_z_omega = divide_single_async::<E>(worker.child(), false, poly_to_divide_at_z_omega.arc_coeffs(), z).await;
         let open_at_z = Polynomial::from_coeffs(poly_to_divide_at_z_omega).unwrap();
 
        //  worker.scope(polys.len(), |scope, chunk| {
        //      for p in polys.chunks_mut(chunk) {
        //          scope.spawn(move |_| {
        //              let (poly, at) = &p[0];
        //              let at = *at;
        //              let result = divide_single::<E>(poly.as_ref(), at);
        //              p[0] = (Polynomial::from_coeffs(result).unwrap(), at);
        //          });
        //      }
        //  });
 
        //  let open_at_z_omega = polys.pop().unwrap().0;
        //  let open_at_z = polys.pop().unwrap().0;
 
         // let opening_at_z = commit_using_monomials(&open_at_z, &mon_crs, &worker)?;
         let opening_at_z = async_manager.multiexp(open_at_z.arc_coeffs(), worker.child(), false).await;
 
         // let opening_at_z_omega = commit_using_monomials(&open_at_z_omega, &mon_crs, &worker)?;
         let opening_at_z_omega = async_manager.multiexp(open_at_z_omega.arc_coeffs(), worker.child(), false).await;
 
         proof.opening_proof_at_z = opening_at_z;
         proof.opening_proof_at_z_omega = opening_at_z_omega;
 
         Ok(proof)
    }
}
