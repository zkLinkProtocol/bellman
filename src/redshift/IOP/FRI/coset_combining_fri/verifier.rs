use crate::pairing::ff::PrimeField;
use crate::redshift::polynomials::*;
use crate::redshift::domains::*;
use crate::multicore::*;
use crate::SynthesisError;
use super::*;
use crate::redshift::fft::cooley_tukey_ntt::log2_floor;
use crate::redshift::IOP::oracle::*;
use super::coset_combiner::*;
use crate::redshift::fft::cooley_tukey_ntt::bitreverse;
use std::ops::Range;

//TODO: it is also very important to understand how do values are located inside coset

impl<F: PrimeField, O: Oracle<F>, C: Channel<F, Input = O::Commitment>> FriIop<F, O, C> {
    
    pub fn verify_proof_queries<Func: Fn(Vec<(Label, &F)>) -> Option<F>>(
        proof: &FriProof<F, O>,
        upper_layer_commitments: Vec<(Label, O::Commitment)>,
        natural_element_indexes: Vec<usize>,
        fri_challenges: &[F],
        params: &FriParams,
        oracle_params: &O::Params,
        upper_layer_combiner: Func,
    ) -> Result<bool, SynthesisError> {
        
        assert!(fri_challenges.len() == proof.commitments.len() + 1);
        assert!(proof.queries.len() == params.R);
        assert!(natural_element_indexes.len() == proof.queries.len());

        let mut two = F::one();
        two.double();

        let two_inv = two.inverse().ok_or(
            SynthesisError::DivisionByZero
        )?;

        let domain = Domain::<F>::new_for_size((params.initial_degree_plus_one.get() * params.lde_factor) as u64)?;

        let omega = domain.generator;
        let omega_inv = omega.inverse().ok_or(
            SynthesisError::DivisionByZero
        )?;

        let collapsing_factor = params.collapsing_factor;
        let coset_size = 1 << collapsing_factor;
        let initial_domain_size = domain.size as usize;
        let log_initial_domain_size = log2_floor(initial_domain_size);

        if natural_element_indexes.len() != params.R || proof.final_coefficients.len() > params.final_degree_plus_one {
            return Ok(false);
        }

        let num_steps = 
            log2_floor(params.initial_degree_plus_one.get() / params.final_degree_plus_one) / params.collapsing_factor as u32;
        
        for ((round, natural_first_element_index), upper_layer_query) in 
            proof.queries.iter().zip(natural_element_indexes.into_iter()).zip(proof.upper_layer_queries.iter()) {
            
            let valid = FriIop::<F, O, C>::verify_single_proof_round::<Func>(
                &upper_layer_query,
                &upper_layer_commitments,
                &upper_layer_combiner,
                round,
                &proof.commitments,
                &proof.final_coefficients,
                natural_first_element_index,
                fri_challenges,
                num_steps as usize,
                initial_domain_size,
                log_initial_domain_size,
                collapsing_factor,
                coset_size,
                &oracle_params,
                &omega,
                &omega_inv,
                &two_inv,
            )?;

            if !valid {
                return Ok(false);
            }
        }

        return Ok(true);
    }

    pub fn verify_single_proof_round<Func: Fn(Vec<(Label, &F)>) -> Option<F>>(
        upper_layer_queries: &Vec<(Label, O::Query)>,
        upper_layer_commitments: &Vec<(Label, O::Commitment)>, 
        upper_layer_combiner: &Func,
        queries: &Vec<O::Query>,
        commitments: &Vec<O::Commitment>,
        final_coefficients: &Vec<F>,
        natural_first_element_index: usize,
        fri_challenges: &[F],
        _num_steps: usize,
        initial_domain_size: usize,
        log_initial_domain_size: u32,
        collapsing_factor: u32,
        coset_size: usize,
        oracle_params: &O::Params,
        omega: &F,
        omega_inv: &F,
        two_inv: &F,
    ) -> Result<bool, SynthesisError>
    {
        let mut coset_idx_range = CosetCombiner::get_coset_idx_for_natural_index(
            natural_first_element_index, initial_domain_size, log_initial_domain_size, collapsing_factor);

        println!("coset: {}-{}", coset_idx_range.start, coset_idx_range.end);

        

        //check query cardinality here!
        if upper_layer_queries.iter().any(|x| x.1.indexes() != coset_idx_range) {
            return Ok(false);
        }
        if !BatchedOracle::<F, O>::verify_query(upper_layer_commitments, upper_layer_queries, oracle_params) {
            return Ok(false);
        }

        let mut values = Vec::with_capacity(coset_size);
        for (i, coset_idx) in coset_idx_range.clone().enumerate() {
            let mut argument : Vec<(Label, &F)> = upper_layer_queries.iter().map(|x| (x.0, &x.1.values()[i])).collect();
            let natural_idx = CosetCombiner::get_natural_idx_for_coset_index(
                coset_idx, initial_domain_size, log_initial_domain_size, collapsing_factor);
            println!("natural index: {}", natural_idx);

            let mut evaluation_point = omega.pow([natural_idx as u64]);
            evaluation_point.mul_assign(&F::multiplicative_generator());
            println!("verifier ev-p: {}", evaluation_point);

            argument.push(("evaluation_point", &evaluation_point));
            let combined_value = upper_layer_combiner(argument).ok_or(SynthesisError::AssignmentMissing)?;
            values.push(combined_value);
        }

        let mut domain_size = initial_domain_size;
        let mut log_domain_size = log_initial_domain_size;

        let mut omega = omega.clone();
        let mut omega_inv = omega_inv.clone();

        let mut previous_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
            &values[..],
            &fri_challenges[0],
            coset_idx_range.clone(),
            collapsing_factor,
            coset_size,
            &mut domain_size,
            &mut log_domain_size,
            &mut omega,
            & mut omega_inv,
            two_inv);

        for ((query, commitment), challenge) 
            in queries.into_iter().zip(commitments.iter()).zip(fri_challenges.iter().skip(1)) 
        {
            // TODO: check query cardinality here!
            println!("On the next iteration!");

            //we do also need to check that coset_indexes are consistent with query
            let (temp, elem_tree_idx) = CosetCombiner::get_next_layer_coset_idx_extended(
                coset_idx_range.start, collapsing_factor);
            coset_idx_range = temp;

            assert_eq!(coset_idx_range.len(), coset_size);

            if query.indexes() != coset_idx_range {
                println!("quert index");
                return Ok(false);
            }

            if !<O as Oracle<F>>::verify_query(commitment, query, &oracle_params) {
                println!("verify query");
                return Ok(false);
            }
            
            //round consistency check
            let this_layer_element = FriIop::<F, O, C>::coset_interpolant_value(
                query.values(),
                &challenge,
                coset_idx_range.clone(),
                collapsing_factor,
                coset_size,
                &mut domain_size,
                &mut log_domain_size,
                &mut omega,
                &mut omega_inv,
                two_inv);

            println!("previous layer elem: {}", previous_layer_element);
            println!("current elem: {}", query.values()[elem_tree_idx]);

            if previous_layer_element != query.values()[elem_tree_idx] {
                println!("coset value wrong");
                return Ok(false);
            }
            previous_layer_element = this_layer_element;
        }

        println!("at th end of FRI!");

        // finally we need to get expected value from coefficients
        let (coset_idx_range, elem_tree_idx) = CosetCombiner::get_next_layer_coset_idx_extended(
            coset_idx_range.start, collapsing_factor);
        let elem_index = CosetCombiner::get_natural_idx_for_coset_index(
            coset_idx_range.start + elem_tree_idx, domain_size, log_domain_size, collapsing_factor);

        let mut expected_value_from_coefficients = F::zero();
        let mut power = F::one();
        let mut evaluation_point = omega.pow([(elem_index) as u64]);
        evaluation_point.mul_assign(&F::multiplicative_generator());

        for c in final_coefficients.iter() {
            let mut tmp = power;
            tmp.mul_assign(c);
            expected_value_from_coefficients.add_assign(&tmp);
            power.mul_assign(&evaluation_point);
        }
        Ok(expected_value_from_coefficients == previous_layer_element)
    }

    pub fn coset_interpolant_value(
        values: &[F],
        challenge: &F,
        coset_idx_range: Range<usize>,
        collapsing_factor: u32,
        coset_size: usize,
        domain_size: &mut usize,
        log_domain_size: &mut u32,
        omega: &mut F,
        omega_inv: &mut F,
        two_inv: &F,
    ) -> F
    {
        let mut challenge = challenge.clone();
        let mut this_level_values = Vec::with_capacity(coset_size/2);
        let mut next_level_values = vec![F::zero(); coset_size / 2];

        //let base_omega_idx = bitreverse(coset_idx_range.start, *log_domain_size as usize);
        let mut base_omega_idx = coset_idx_range.start;

        //*elem_index = ((*elem_index << collapsing_factor) % *domain_size) >> collapsing_factor;

        for wrapping_step in 0..collapsing_factor {
            let inputs = if wrapping_step == 0 {
                                values
                            } else {
                                &this_level_values[..(coset_size >> wrapping_step)]
                            };
            for (pair_idx, (pair, o)) in inputs.chunks(2).zip(next_level_values.iter_mut()).enumerate() 
            {
                
                let idx = bitreverse(base_omega_idx + 2*pair_idx, *log_domain_size as usize);
                let divisor = omega_inv.pow([idx as u64]);

                let f_at_omega = pair[0];
                let f_at_minus_omega = pair[1];
                let mut v_even_coeffs = f_at_omega;
                v_even_coeffs.add_assign(&f_at_minus_omega);

                let mut v_odd_coeffs = f_at_omega;
                v_odd_coeffs.sub_assign(&f_at_minus_omega);
                v_odd_coeffs.mul_assign(&divisor);

                let mut tmp = v_odd_coeffs;
                tmp.mul_assign(&challenge);
                tmp.add_assign(&v_even_coeffs);
                tmp.mul_assign(&two_inv);

                *o = tmp;
            }

            if wrapping_step != collapsing_factor - 1 {
                this_level_values.clear();
                this_level_values.clone_from(&next_level_values);
                challenge.square();
            }
            
            omega.square();
            omega_inv.square();

            *domain_size >>= 1;
            *log_domain_size -= 1;
            base_omega_idx >>= 1;
            
        }

    next_level_values[0]
    }
}


#[cfg(test)]
mod test {

    #[test]
    fn fri_queries() {

        use crate::ff::{Field, PrimeField};
        use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    
        use crate::redshift::polynomials::*;
        use crate::multicore::*;
        use crate::redshift::fft::cooley_tukey_ntt::{CTPrecomputations, BitReversedOmegas};

        use crate::redshift::IOP::FRI::coset_combining_fri::precomputation::*;
        use crate::redshift::IOP::FRI::coset_combining_fri::FriPrecomputations;
        use crate::redshift::IOP::FRI::coset_combining_fri::fri;
        use crate::redshift::IOP::FRI::coset_combining_fri::{FriParams, FriIop};

        use crate::redshift::IOP::channel::blake_channel::*;
        use crate::redshift::IOP::channel::*;

        use crate::redshift::IOP::oracle::coset_combining_blake2s_tree::*;
        use crate::redshift::IOP::oracle::{Oracle, BatchedOracle, Label};

        use crate::pairing::bn256::Fr as Fr;

        const SIZE: usize = 1024;
        let worker = Worker::new_with_cpus(1);
        let mut channel = Blake2sChannel::new(&());

        let params = FriParams {
            collapsing_factor: 2,
            R: 4,
            initial_degree_plus_one: std::cell::Cell::new(SIZE),
            lde_factor: 4,
            final_degree_plus_one: 4,
        };

        let oracle_params = FriSpecificBlake2sTreeParams {
            values_per_leaf: 1 << params.collapsing_factor
        };

        let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let coeffs = (0..SIZE).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
    
        let poly = Polynomial::<Fr, _>::from_coeffs(coeffs).unwrap();
        let precomp = BitReversedOmegas::<Fr>::new_for_domain_size(poly.size());

        let coset_factor = Fr::multiplicative_generator();
        let eval_result = poly.bitreversed_lde_using_bitreversed_ntt(&worker, 4, &precomp, &coset_factor).unwrap();

        // construct upper layer oracle from eval_result

        let upper_layer_oracle = FriSpecificBlake2sTree::create(eval_result.as_ref(), &oracle_params);
        let batched_oracle = BatchedOracle::create(vec![("starting oracle", &upper_layer_oracle)]);
        let upper_layer_commitments = batched_oracle.get_commitment();

        let fri_precomp = <OmegasInvBitreversed::<Fr> as FriPrecomputations<Fr>>::new_for_domain_size(eval_result.size());

        let fri_proto = FriIop::<Fr, FriSpecificBlake2sTree<Fr>, Blake2sChannel<Fr>>::proof_from_lde(
            eval_result.clone(), 
            &fri_precomp, 
            &worker, 
            &mut channel,
            &params,
            &oracle_params,
        ).expect("FRI must succeed");

        // upper layer combiner is trivial in our case

        println!("erer");

        let proof = FriIop::<Fr, FriSpecificBlake2sTree<Fr>, Blake2sChannel<Fr>>::prototype_into_proof(
            fri_proto,
            &batched_oracle,
            vec![eval_result.as_ref()],
            vec![6, 4, 127, 434],
            &params,
            &oracle_params,
        ).expect("Fri Proof must be constrcuted");

        channel.reset();
        let fri_challenges = FriIop::<Fr, FriSpecificBlake2sTree<Fr>, Blake2sChannel<Fr>>::get_fri_challenges(
            &proof,
            &mut channel,
            &params,
        );

        let upper_layer_combiner = |arr: Vec<(Label, &Fr)>| -> Option<Fr> {
            let res = arr.iter().find(|(l, _)| *l == "starting oracle").map(|(_, c)| (*c).clone());
            res
        };

        println!("Here");

        let result = FriIop::<Fr, FriSpecificBlake2sTree<Fr>, Blake2sChannel<Fr>>::verify_proof_queries(
            &proof,
            upper_layer_commitments,
            vec![6, 4, 127, 434],
            &fri_challenges,
            &params,
            &oracle_params,
            upper_layer_combiner,
        ).expect("Verification must be successful");

        assert_eq!(result, true);    
    }
}


