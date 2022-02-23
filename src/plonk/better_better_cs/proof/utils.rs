use std::sync::Arc;

use futures::future::join_all;
use heavy_ops_service::{AsyncWorkManager, Worker};

use crate::pairing::{Engine, CurveAffine, ff::{Field, PrimeField}};
use crate::worker::Worker as OldWorker;
use crate::SynthesisError;
use crate::plonk::domains::Domain;
use crate::plonk::better_better_cs::proof::polynomials_new::*;
use crate::plonk::better_better_cs::proof::data_structures_new::*;
use crate::plonk::commitments::transcript::Transcript;


pub(crate) async fn calculate_inverse_vanishing_polynomial_in_a_coset<F: PrimeField>(
    worker: Worker, 
    is_background: bool,
    poly_size: usize, 
    vahisning_size: usize
) -> Result<Polynomial::<F, Values>, SynthesisError> {
    assert!(poly_size.is_power_of_two());
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

    let domain = Domain::<F>::new_for_size(vahisning_size as u64)?;
    let n_domain_omega = domain.generator;
    let mut root = n_domain_omega.pow([(vahisning_size - 1) as u64]);
    root.negate();

    let multiplicative_generator = F::multiplicative_generator();

    let mut negative_one = F::one();
    negative_one.negate();

    let mut numerator = Polynomial::<F, Values>::from_values(vec![multiplicative_generator; poly_size])?;
    // evaluate X in linear time

    numerator.distribute_powers(worker.child(), false, numerator.omega).await;
    numerator.add_constant(worker.child(), false, &root).await;

    // numerator.add_constant(&worker, &negative_one);
    // now it's a series of values in a coset

    // now we should evaluate X^(n+1) - 1 in a linear time

    let shift = multiplicative_generator.pow([vahisning_size as u64]);
    
    let mut denominator = Polynomial::<F, Values>::from_values(vec![shift; poly_size])?;

    // elements are h^size - 1, (hg)^size - 1, (hg^2)^size - 1, ...

    denominator.distribute_powers(worker.child(), false, denominator.omega.pow([vahisning_size as u64])).await;
    denominator.add_constant(worker.child(), false, &negative_one).await;

    denominator.batch_inversion(worker.child(), false).await?;

    numerator.mul_assign(worker.child(), false, &denominator).await;

    Ok(numerator)
}

pub(crate) fn evaluate_inverse_vanishing_poly_with_last_point_cut<F: PrimeField>(
    vahisning_size: usize, 
    point: F
) -> F {
    assert!(vahisning_size.is_power_of_two());

    // update from the paper - it should not hold for the last generator, omega^(n) in original notations

    // Z(X) = (X^(n+1) - 1) / (X - omega^(n)) => Z^{-1}(X) = (X - omega^(n)) / (X^(n+1) - 1)

    let domain = Domain::<F>::new_for_size(vahisning_size as u64).expect("should fit");
    let n_domain_omega = domain.generator;
    let root = n_domain_omega.pow([(vahisning_size - 1) as u64]);

    let mut numerator = point;
    numerator.sub_assign(&root);

    let mut denominator = point.pow([vahisning_size as u64]);
    denominator.sub_assign(&F::one());

    let denominator = denominator.inverse().expect("must exist");

    numerator.mul_assign(&denominator);

    numerator
}

pub(crate) async fn calculate_lagrange_poly<E: Engine>(
    async_manager: Arc<AsyncWorkManager<E>>,
    worker: Worker, 
    is_background: bool,
    poly_size:usize, 
    poly_number: usize
) -> Result<Polynomial::<E::Fr, Coefficients>, SynthesisError> {
    assert!(poly_size.is_power_of_two());
    assert!(poly_number < poly_size);

    let mut poly = Polynomial::<E::Fr, Values>::from_values(vec![E::Fr::zero(); poly_size])?;

    poly.as_mut()[poly_number] = E::Fr::one();

    let result = async_manager.ifft(poly.arc_coeffs(), worker.child(), false).await;

    Polynomial::from_coeffs(result)
}

pub(crate) async fn evaluate_vanishing_polynomial_of_degree_on_domain_size<F: PrimeField>(
    vanishing_degree: u64,
    coset_factor: &F,
    domain_size: u64,
    worker: Worker, 
    is_background: bool,
) -> Result<Polynomial<F, Values>, SynthesisError> {
    let domain = Domain::<F>::new_for_size(domain_size)?;
    let domain_generator = domain.generator;

    let coset_factor = coset_factor.pow(&[vanishing_degree]);

    let domain_generator_in_vanishing_power = domain_generator.pow(&[vanishing_degree]);

    let mut minus_one = F::one();
    minus_one.negate();

    let mut result = vec![minus_one; domain.size as usize];
    let result = Arc::new(result);

    let num_cpus = worker.num_cpus();
    let num_items = domain.size as usize;
    let grand_products = Arc::new(vec![F::one(); num_items]);
    let sub_products = Arc::new(vec![F::one(); num_cpus]);
    let chunk_size = num_items / num_cpus;
    let mut handles = vec![];
    for (chunk_id, (child_worker, result, chunk_len)) in result
        .chunks(chunk_size)
        .map(|chunk| {
            (
                worker.child(),
                result.clone(),
                chunk.len(),
            )
        })
        .enumerate()
    {


        let fut = async move{
            let start = chunk_id * chunk_size;
            let end = start + chunk_len;
            let range = start..end;
            let chunk = unsafe{std::slice::from_raw_parts_mut(result[range].as_ptr() as *mut F, chunk_len)};

            let mut pow = domain_generator_in_vanishing_power.pow(&[start as u64]);
            pow.mul_assign(&coset_factor);
            for el in chunk.iter_mut() {
                el.add_assign(&pow);
                pow.mul_assign(&domain_generator_in_vanishing_power);
            }
        };
        let handle = worker.spawn_with_handle(fut).unwrap();
        handles.push(handle)
    }
    let _ = join_all(handles).await;


    // worker.scope(result.len(), |scope, chunk_size| {
    //     for (chunk_id, chunk) in result.chunks_mut(chunk_size).enumerate() {
    //         scope.spawn(move |_| {
    //             let start = chunk_id * chunk_size;
    //             let mut pow = domain_generator_in_vanishing_power.pow(&[start as u64]);
    //             pow.mul_assign(&coset_factor);
    //             for el in chunk.iter_mut() {
    //                 el.add_assign(&pow);
    //                 pow.mul_assign(&domain_generator_in_vanishing_power);
    //             }
    //         });
    //     }
    // });

    let result = Arc::try_unwrap(result).unwrap();

    Polynomial::from_values(result)
}

pub(crate) fn evaluate_vanishing_for_size<F: PrimeField>(point: &F, vanishing_domain_size: u64) -> F {
    let mut result = point.pow(&[vanishing_domain_size]);
    result.sub_assign(&F::one());

    result
}

pub(crate) fn evaluate_l0_at_point<F: PrimeField>(
    domain_size: u64,
    point: F
) -> Result<F, SynthesisError> {
    let size_as_fe = F::from_str(&format!("{}", domain_size)).unwrap();

    let mut den = point;
    den.sub_assign(&F::one());
    den.mul_assign(&size_as_fe);

    let den = den.inverse().ok_or(SynthesisError::DivisionByZero)?;

    let mut num = point.pow(&[domain_size]);
    num.sub_assign(&F::one());
    num.mul_assign(&den);

    Ok(num)
}

pub(crate) fn evaluate_lagrange_poly_at_point<F: PrimeField>(
    poly_number: usize, 
    domain: &Domain<F>,
    point: F
) -> Result<F, SynthesisError> {
    // lagrange polynomials have a form
    // (omega^i / N) / (X - omega^i) * (X^N - 1)

    let mut num = evaluate_vanishing_for_size(&point, domain.size);
    let omega_power = domain.generator.pow(&[poly_number as u64]);
    num.mul_assign(&omega_power);

    let size_as_fe = F::from_str(&format!("{}", domain.size)).unwrap();

    let mut den = point;
    den.sub_assign(&omega_power);
    den.mul_assign(&size_as_fe);

    let den = den.inverse().ok_or(SynthesisError::DivisionByZero)?;

    num.mul_assign(&den);

    Ok(num)
}

use crate::ff::SqrtField;

use super::{SortedGateQueries, lookup_tables::PolyIdentifier, cs::GateInternal};


pub fn make_non_residues<F: PrimeField + SqrtField>(num: usize) -> Vec<F> {
    // create largest domain possible
    assert!(F::S < 63);
    let domain_size = 1u64 << (F::S as u64);

    let domain = Domain::<F>::new_for_size(domain_size).expect("largest domain must exist");

    make_non_residues_for_domain(num, &domain)
}

pub fn make_non_residues_for_domain<F: PrimeField + SqrtField>(num: usize, domain: &Domain<F>) -> Vec<F> {
    use crate::ff::LegendreSymbol;
    
    // we need to check that 
    // - some k is not a residue
    // - it's NOT a part of coset formed as other_k * {1, omega^1, ...}

    let mut non_residues = vec![];
    let mut current = F::one();
    let one = F::one();
    for _ in 0..num {
        loop {
            if current.legendre() != LegendreSymbol::QuadraticNonResidue {
                current.add_assign(&one);
            } else {
                let mut is_unique = true;
                {
                    // first pow into the domain size 
                    let tmp = current.pow(&[domain.size]);
                    // then check: if it's in some other coset, then
                    // X^N == other_k ^ N
                    for t in Some(one).iter().chain(non_residues.iter()) {
                        if !is_unique {
                            break;
                        }
                        let t_in_domain_size = t.pow(&[domain.size]);
                        if tmp == t_in_domain_size {
                            is_unique = false;
                        }
                    }
                }
                if is_unique {
                    non_residues.push(current);
                    current.add_assign(&one);
                    break;
                }
            }
        }
    }

    non_residues
}

pub fn commit_point_as_xy<E: Engine, T: Transcript<E::Fr>>(
    transcript: &mut T,
    point: &E::G1Affine
) {
    use crate::ff::Field;

    if point.is_zero() {
        transcript.commit_fe(&E::Fq::zero());
        transcript.commit_fe(&E::Fq::zero());
    } else {
        let (x, y) = point.into_xy_unchecked();
        transcript.commit_fe(&x);
        transcript.commit_fe(&y);
    }
}



#[derive(Debug)]
pub struct SortedGateQueriesNew<E: Engine>{
    pub state_polys: Vec<Vec<PolyIdentifier>>,
    pub witness_polys: Vec<Vec<PolyIdentifier>>,
    pub gate_selectors: Vec<Box<dyn GateInternal<E>>>,
    pub gate_setup_polys: Vec<Vec<Vec<PolyIdentifier>>>,
}

/// we sort queries by:
/// - witness first
/// - gate selectors
/// - gate setups in order of gates appearing
/// - additionally we split them into buckets of different dilation
pub fn sort_queries_for_linearization_new<E: Engine>(gates: & Vec<Box<dyn crate::plonk::better_better_cs::proof::cs::GateInternal<E>>>, max_dilation: usize) -> SortedGateQueriesNew<E>{
    let state_polys_sorted_by_dilation = vec![vec![]; max_dilation+1];
    let witness_polys_sorted_by_dilation = vec![vec![]; max_dilation+1];
    let gate_setup_polys_by_gate_and_dilation = vec![vec![vec![]; max_dilation+1]; gates.len()];

    let mut queries = SortedGateQueriesNew::<E> {
        state_polys: state_polys_sorted_by_dilation,
        witness_polys: witness_polys_sorted_by_dilation,
        gate_selectors: vec![],
        gate_setup_polys: gate_setup_polys_by_gate_and_dilation,
    };

    let mut opening_requests_before_linearization = std::collections::HashSet::new();
    let mut all_queries = std::collections::HashSet::new();
    let mut sorted_opening_requests = vec![];
    let mut sorted_selector_for_opening = vec![];
    let mut polys_in_linearization = std::collections::HashSet::new();

    let num_gate_types = gates.len();

    for (gate_idx, gate) in gates.iter().enumerate() {
        for q in gate.all_queried_polynomials().into_iter() {
            all_queries.insert(q);
        }
        let queries_to_add = if gate.benefits_from_linearization() {
            if num_gate_types > 1 {
                // there are various gates, so we need to query the selector
                sorted_selector_for_opening.push(gate.box_clone());
            }

            // it's better to linearize the gate
            for q in gate.linearizes_over().into_iter() {
                polys_in_linearization.insert(q);
            }

            gate.needs_opened_for_linearization()
        } else {
            // we will linearize over the selector, so we do not need to query it
            // and instead have to query all other polynomials

            // we blindly add all queried polys
            gate.all_queried_polynomials()
        };

        for q in queries_to_add.into_iter() {
            if !opening_requests_before_linearization.contains(&q) {
                opening_requests_before_linearization.insert(q.clone());

                // push into the corresponding bucket

                let (id, dilation_value) = q.into_id_and_raw_dilation();
                match id {
                    p @ PolyIdentifier::VariablesPolynomial(..) => {
                        queries.state_polys[dilation_value].push(p);
                    },
                    p @ PolyIdentifier::WitnessPolynomial(..) => {
                        queries.witness_polys[dilation_value].push(p);
                    },
                    p @ PolyIdentifier::GateSetupPolynomial(..) => {
                        queries.gate_setup_polys[gate_idx][dilation_value].push(p);
                    },
                    _ => {
                        unreachable!();
                    }
                };


                sorted_opening_requests.push(q);

            }
        }
    }

    // Sanity check: we open everything either in linearization or in plain text! 
    {
        let must_open_without_linearization: Vec<_> = all_queries.difference(&polys_in_linearization).collect();

        for p in must_open_without_linearization.into_iter() {
            assert!(opening_requests_before_linearization.contains(&p));
        }
    }

    // gate selectors are always sorted by the gate order
    queries.gate_selectors = sorted_selector_for_opening;

    queries
}



pub(crate) async fn divide_single_async<E: Engine>(
    worker: Worker, 
    is_background: bool,
    poly: Arc<Vec<E::Fr>>,
    opening_point: E::Fr,
) -> Vec<E::Fr> {
    // we are only interested in quotient without a reminder, so we actually don't need opening value
    let mut b = opening_point;
    b.negate();

    let mut q = vec![E::Fr::zero(); poly.len()];

    let mut tmp = E::Fr::zero();
    let mut found_one = false;
    for (q, r) in q.iter_mut().rev().skip(1).zip(poly.iter().rev()) {
        if !found_one {
            if r.is_zero() {
                continue
            } else {
                found_one = true;
            }
        }

        let mut lead_coeff = *r;
        lead_coeff.sub_assign(&tmp);
        *q = lead_coeff;
        tmp = lead_coeff;
        tmp.mul_assign(&b);
    }

    q
}

#[cfg(test)]
    mod test {
    #[test]
    fn test_lagrange_poly_explicit_multicore_validity() {
        // use crate::pairing::bn256::Fr;
        // use crate::ff::{Field, PrimeField};
        // use super::*;

        // if cfg!(debug_assertions) {
        //     println!("Will be too slow to run in test mode, abort");
        //     return;
        // }

        // use rand::{XorShiftRng, SeedableRng, Rand, Rng};
        // use crate::worker::Worker;

        // let size: usize = 1 << 21;
        // let worker = Worker::new();

        // let mut reference: Option<Polynomial<_, _>> = None;

        // for _ in 0..100 {
        //     for num_cpus in 1..=32 {
        //         let subworker = Worker::new_with_cpus(num_cpus);
        //         let candidate = calculate_lagrange_poly::<Fr>(&subworker, size.next_power_of_two(), 0).unwrap();

        //         if let Some(to_compare) = reference.take() {
        //             assert_eq!(candidate.as_ref(), to_compare.as_ref(), "mismatch for {} cpus", num_cpus);
        //         } else {
        //             reference = Some(candidate);
        //         }

        //         println!("Completed for {} cpus", num_cpus);
        //     }
        // }

        todo!()
    }
}

