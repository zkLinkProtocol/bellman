#[cfg(test)]
mod test {
    use crate::redshift::redshift::cs::*;
    use crate::redshift::redshift::generators::*;
    use crate::redshift::redshift::prover::*;
    use crate::redshift::redshift::verifier::*;
    use crate::redshift::redshift::data_structures::*;
    use crate::redshift::redshift::utils::*;

    use crate::redshift::IOP::FRI::coset_combining_fri::*;
    use crate::redshift::IOP::FRI::coset_combining_fri::precomputation::*;
    use crate::redshift::partial_reduction_field::*;
    use crate::redshift::partial_reduction_field::proth_engine::Transparent252;
    use crate::redshift::partial_reduction_field::proth::Fr;
    use crate::redshift::IOP::oracle::*;
    use crate::redshift::IOP::channel::*;
    use crate::redshift::fft::cooley_tukey_ntt::*;

    use crate::pairing::ff::{Field, PrimeField};
    use crate::pairing::{Engine};

    use crate::{SynthesisError};
    use std::marker::PhantomData;
    use crate::multicore::*;

    use crate::redshift::redshift::test_assembly::*;
    use std::mem;

    #[derive(Clone)]
    struct BenchmarkCircuit<E: Engine>{
        num_steps: usize,
        a: E::Fr,
        b: E::Fr,
        output: E::Fr,
        _marker: std::marker::PhantomData<E>
    }

    fn fibbonacci<F: Field>(a: &F, b: &F, num_steps: usize) -> F {

        let mut a = a.clone();
        let mut b = b.clone();

        for _ in 0..num_steps {
            b.add_assign(&a);
            std::mem::swap(&mut a, &mut b);
        }

        a
    }

    impl<E: Engine> Circuit<E> for BenchmarkCircuit<E> {
        fn synthesize<CS: ConstraintSystem<E>>(&self, cs: &mut CS) -> Result<(), SynthesisError> {
            // yeah, fibonacci...

            let one = E::Fr::one();
            let mut negative_one = one;
            negative_one.negate();
            
            let mut a = cs.alloc_input(|| {
                Ok(self.a.clone())
            })?;

            let mut b = cs.alloc_input(|| {
                Ok(self.b.clone())
            })?;

            let mut a_value = self.a.clone();
            let mut b_value = self.b.clone();

            for _ in 0..self.num_steps {

                b_value.add_assign(&a_value);
               
                let temp = cs.alloc(|| {
                    Ok(b_value.clone())
                })?;

                cs.enforce_zero_3((a, b, temp), (one, one, negative_one))?;
                std::mem::swap(&mut a_value, &mut b_value);

                b = a;
                a = temp;
            }

            let output = cs.alloc_input(|| {
                Ok(self.output.clone())
            })?;

            cs.enforce_zero_2((a, output), (one, negative_one))?;

            Ok(())
        }
    }

    fn test_redshift_template<E: Engine, I: Oracle<E::Fr>, T: Channel<E::Fr, Input = I::Commitment>>(
        a: E::Fr,
        b: E::Fr,
        num_steps: usize,
        fri_params: FriParams,
        oracle_params: I::Params,
        channel_params: T::Params,
    ) -> Result<bool, SynthesisError>
    {

        let output = fibbonacci(&a, &b, num_steps);
        
        let circuit = BenchmarkCircuit::<E> {
            num_steps,
            a,
            b,
            output,
            _marker: std::marker::PhantomData::<E>
        };

        // verify that circuit is satifiable
        let mut test_assembly = TestAssembly::new();
        circuit.synthesize(&mut test_assembly)?;
        println!("test circuit is satisfied: {}", test_assembly.is_satisfied(false));
        
        let (_setup, setup_precomp) = setup_with_precomputations::<E, BenchmarkCircuit<E>, I, T>(
            &circuit,
            &fri_params,
            &oracle_params,
            &channel_params,
        )?;

        println!("before proof");

        let proof = prove_with_setup_precomputed::<E, BenchmarkCircuit<E>, I, T> (
            &circuit,
            &setup_precomp, 
            &fri_params,
            &oracle_params,
            &channel_params, 
        )?;

        println!("before verification");

        let is_valid = verify_proof::<E, I, T>(
            proof,
            &[a, b, output],
            &setup_precomp,
            &fri_params,
            &oracle_params,
            &channel_params,
        );

        is_valid
    }

    #[test]
    fn test_redshift_with_blake() {

        use crate::redshift::IOP::oracle::coset_combining_blake2s_tree::*;
        use crate::redshift::IOP::channel::blake_channel::*;

        type E = Transparent252;
        type O = FriSpecificBlake2sTree<Fr>;
        type T = Blake2sChannel<Fr>;

        // prepare parameters
        let a = Fr::one();
        let b = Fr::one();
        let num_steps =1000;

        let fri_params = FriParams {
            lde_factor : 16,
            initial_degree_plus_one: std::cell::Cell::new(0),
            R : 20,
            collapsing_factor : 3,
            final_degree_plus_one : 2,
        };

        // note the consistency between collapsing_factor and num_elems_per_leaf!
        // we should always have num_elems_per_leaf = 1 << collapsing_factor

        let oracle_params = FriSpecificBlake2sTreeParams {
            values_per_leaf : 1 << fri_params.collapsing_factor
        };

        let channel_params = ();

        let res = test_redshift_template::<E, O, T>(
            a,
            b,
            num_steps,
            fri_params,
            oracle_params,
            channel_params,
        );

        match res {
            Ok(valid) => assert_eq!(valid, true),
            Err(_) => println!("Some error has been occured!"),
        };       
    }

    #[test]
    fn test_redshift_with_rescue() {

        use crate::redshift::IOP::oracle::coset_combining_rescue_tree::*;
        use crate::redshift::IOP::channel::rescue_channel::*;
        use crate::redshift::IOP::hashes::rescue::bn256_rescue_params::BN256Rescue;
        use crate::redshift::IOP::hashes::rescue::RescueParams;
        use crate::pairing::bn256::Fr as Fr;

        type E = crate::pairing::bn256::Bn256;
        type O<'a> = FriSpecificRescueTree<'a, Fr, BN256Rescue>;
        type T<'a> = RescueChannel<'a, Fr, BN256Rescue>;

        // prepare parameters
        let a = Fr::one();
        let b = Fr::one();
        let num_steps = 10;

        let fri_params = FriParams {
            initial_degree_plus_one: std::cell::Cell::new(0),
            lde_factor: 16,
            R: 4,
            collapsing_factor: 1,
            final_degree_plus_one: 1
        };

        let bn256_rescue_params = BN256Rescue::default();

        let oracle_params = RescueTreeParams {
            values_per_leaf: 1 << fri_params.collapsing_factor,
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let channel_params = RescueChannelParams {
            rescue_params: &bn256_rescue_params,
            _marker: std::marker::PhantomData::<Fr>,
        };

        let res = test_redshift_template::<E, O, T>(
            a,
            b,
            num_steps,
            fri_params,
            oracle_params,
            channel_params,
        );

        match res {
            Ok(valid) => assert_eq!(valid, true),
            Err(_) => println!("Some error has been occured!"),
        };       
    }
}