use rand::{Rand, Rng, thread_rng};
use super::new::Polynomial;
use super::old::Polynomial as OldPolynomial;
use crate::multicore::Worker;
use crate::pairing::bn256::Fr;
use crate::plonk::fft::cooley_tukey_ntt::{BitReversedOmegas, OmegasInvBitreversed, CTPrecomputations};
use crate::{Field, PrimeField};

#[test]
fn test_polynomial_arith(){
    let log_degree = if let Ok(log_degree) = std::env::var("LOG_DEGREE"){
        log_degree.parse().unwrap()
    }else{
        4usize
    };
    let rng = &mut thread_rng();
    let worker = Worker::new();
    let DEGREE = 1 << log_degree;
    let mut coeffs = vec![Fr::one(); DEGREE];
    for c in coeffs.iter_mut(){
        *c = Fr::rand(rng);
    }
    let mut values = vec![Fr::one(); DEGREE];
    for v in values.iter_mut(){
        *v = Fr::rand(rng);
    }

    {
       
        let old = OldPolynomial::from_coeffs(coeffs.clone()).unwrap();
        let new = Polynomial::from_coeffs(coeffs.clone()).unwrap();

        {
            let mut old = old.clone();
            let mut new = new.clone();
            let e = old.into_coeffs();
            let a = new.into_coeffs();
            assert_eq!(e, a);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let power = rng.gen::<Fr>();
            old.distribute_powers(&worker, power.clone());
            new.distribute_powers(&worker, power.clone());
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let power = rng.gen::<Fr>();
            let mut old = old.clone();
            let mut new = new.clone();
            old.bitreverse_enumeration(&worker);
            new.bitreverse_enumeration(&worker);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let scaler = rng.gen::<Fr>();
            let mut old = old.clone();
            let mut new = new.clone();

            old.scale(&worker, scaler);
            new.scale(&worker, scaler);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();

            old.negate(&worker);
            new.negate(&worker);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();

            old.pad_by_factor(2).unwrap();
            new.pad_by_factor(2).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();

            old.pad_to_size(2*DEGREE).unwrap();
            new.pad_to_size(2*DEGREE).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }   
        {            
            let mut old = OldPolynomial::from_coeffs(coeffs.clone()).unwrap();
            let mut new = Polynomial::from_coeffs(coeffs.clone()).unwrap();

            old.pad_to_domain().unwrap();
            new.pad_to_domain().unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut coeffs = coeffs[..DEGREE-1].to_vec();
            let mut old = OldPolynomial::from_coeffs(coeffs.clone()).unwrap();
            let mut new = Polynomial::from_coeffs(coeffs.clone()).unwrap();

            old.clone_padded_to_domain().unwrap();
            new.clone_padded_to_domain().unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            // let mut old = old.clone();
            // let mut new = new.clone();

            // old.trim_to_degree(15).unwrap();
            // new.trim_to_degree(15).unwrap();
            // assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            // let mut coeffs = vec![Fr::zero(); degree];
            // let mut old = OldPolynomial::from_roots(coeffs.clone(), &worker).unwrap();
            // let mut new = Polynomial::from_roots(coeffs.clone(), &worker).unwrap();
            // assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut coeffs = vec![Fr::rand(rng); 2];
            let mut old = OldPolynomial::from_coeffs(coeffs.clone()).unwrap();
            let mut new = Polynomial::from_coeffs(coeffs.clone()).unwrap();

            let domain_size = 32;
            old.evaluate_at_domain_for_degree_one(&worker, domain_size).unwrap();
            new.evaluate_at_domain_for_degree_one(&worker, domain_size).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);

            old.coset_evaluate_at_domain_for_degree_one(&worker, domain_size).unwrap();
            new.coset_evaluate_at_domain_for_degree_one(&worker, domain_size).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }   
        {
            let mut old = old.clone();
            let mut new = new.clone();

            let domain_size = 32;
            let e = old.break_into_multiples(4).unwrap();
            let a = new.break_into_multiples(4).unwrap();
            for (e, a) in e.iter().zip(a.iter()){
                assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            }
        }
        {
            let mut coeffs = vec![Fr::zero(); DEGREE];
            for c in coeffs.iter_mut(){
                *c = Fr::rand(rng);
            }
            let mut old = OldPolynomial::from_coeffs(coeffs.clone()).unwrap();
            let mut new = Polynomial::from_coeffs(coeffs.clone()).unwrap();

            let mut old = old.clone();
            let mut new = new.clone();

            let e = old.clone().lde(&worker, 4).unwrap();
            let a= new.clone().lde(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]); // TODO
            
            let e = old.clone().coset_lde(&worker, 4).unwrap();
            let a= new.clone().coset_lde(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);

            let e = old.clone().filtering_lde(&worker, 4).unwrap();
            let a = new.clone().filtering_lde(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().lde_using_multiple_cosets_naive(&worker, 4).unwrap();
            let a = new.clone().lde_using_multiple_cosets_naive(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().lde_using_multiple_cosets(&worker, 4).unwrap();
            let a = new.clone().lde_using_multiple_cosets(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().coset_filtering_lde(&worker, 4).unwrap();
            let a = new.clone().coset_filtering_lde(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().coset_lde_using_multiple_cosets_naive(&worker, 4).unwrap();
            let a = new.clone().coset_lde_using_multiple_cosets_naive(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().coset_lde_using_multiple_cosets(&worker, 4).unwrap();
            let a = new.clone().coset_lde_using_multiple_cosets(&worker, 4).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().fft(&worker);
            let a = new.clone().fft(&worker);
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().coset_fft(&worker);
            let a = new.clone().coset_fft(&worker);
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            
            let e = old.clone().coset_fft_for_generator(&worker, Fr::multiplicative_generator());
            let a = new.clone().coset_fft_for_generator(&worker, Fr::multiplicative_generator());
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();

            o0.add_assign(&worker, &o1);
            n0.add_assign(&worker, &n1);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            let s = Fr::rand(rng);
            o0.add_assign_scaled(&worker, &o1, &s);
            n0.add_assign_scaled(&worker, &n1, &s);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();

            o0.sub_assign(&worker, &o1);
            n0.sub_assign(&worker, &n1);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            let s = Fr::rand(rng);
            o0.sub_assign_scaled(&worker, &o1, &s);
            n0.sub_assign_scaled(&worker, &n1, &s);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let eval = Fr::rand(rng);
            old.evaluate_at(&worker, eval.clone());
            new.evaluate_at(&worker, eval);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(DEGREE);
            {
                let mut old = old.clone();
                let mut new = new.clone();
                let coset_factor = Fr::multiplicative_generator();
                let e = old.fft_using_bitreversed_ntt(&worker, &omegas_bitreversed, &coset_factor).unwrap();
                let a = new.fft_using_bitreversed_ntt(&worker, &omegas_bitreversed, &coset_factor).unwrap();
                assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            }
        }
    }
   {        
        let mut old = OldPolynomial::from_values(values.clone()).unwrap();
        let mut new = Polynomial::from_values(values.clone()).unwrap();
        {
            let mut old = old.clone();
            let mut new = new.clone();
            
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut values = values[..DEGREE-1].to_vec();
            let mut old = OldPolynomial::from_values_unpadded(values.clone()).unwrap();
            let mut new = Polynomial::from_values_unpadded(values).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let mut values = vec![Fr::zero(); DEGREE-2];
            let mut old = old.clone_subset_assuming_bitreversed(4).unwrap();
            let mut new = new.clone_subset_assuming_bitreversed(4).unwrap();
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();

            let pow = rng.gen::<u64>();
            assert!(pow != 2);
            old.pow(&worker, pow);
            new.pow(&worker, pow);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
        
            old.square(&worker);
            new.square(&worker);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
        
            let e = old.ifft(&worker);
            let a = new.ifft(&worker);
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
        
            let e = old.icoset_fft(&worker);
            let a = new.icoset_fft(&worker);
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
        
            let e = old.icoset_fft_for_generator(&worker, &Fr::multiplicative_generator());
            let a = new.icoset_fft_for_generator(&worker, &Fr::multiplicative_generator());
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();

            o0.add_assign(&worker, &o1);
            n0.add_assign(&worker, &n1);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            let s = Fr::rand(rng);
            o0.add_assign_scaled(&worker, &o1, &s);
            n0.add_assign_scaled(&worker, &n1, &s);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();

            o0.sub_assign(&worker, &o1);
            n0.sub_assign(&worker, &n1);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            let s = Fr::rand(rng);
            o0.sub_assign_scaled(&worker, &o1, &s);
            n0.sub_assign_scaled(&worker, &n1, &s);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            
            o0.mul_assign(&worker, &o1);
            n0.mul_assign(&worker, &n1);
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut o0 = old.clone();
            let mut o1 = old.clone();
            let mut n0 = new.clone();
            let mut n1 = new.clone();
            
            o0.batch_inversion(&worker).unwrap();
            n0.batch_inversion(&worker).unwrap();
            assert_eq!(&o0.coeffs[..], &n0.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let c = Fr::rand(rng);
            old.add_constant(&worker, &c);
            new.add_constant(&worker, &c);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let c = Fr::rand(rng);
            old.sub_constant(&worker, &c);
            new.sub_constant(&worker, &c);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let x = Fr::rand(rng);
            let e = old.barycentric_evaluate_at(&worker, x.clone()).unwrap();
            let a = new.barycentric_evaluate_at(&worker, x).unwrap();
            assert_eq!(e, a);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let x = Fr::rand(rng);
            let factor = Fr::multiplicative_generator();
            let e = old.barycentric_over_coset_evaluate_at(&worker, x.clone(), &factor).unwrap();
            let a = new.barycentric_over_coset_evaluate_at(&worker, x, &factor).unwrap();
            assert_eq!(e, a);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let start = std::time::Instant::now();
            let e = old.calculate_shifted_grand_product(&worker).unwrap();
            println!("old grand prod takes {}ms", start.elapsed().as_millis());
            let start = std::time::Instant::now();
            let a = new.calculate_shifted_grand_product(&worker).unwrap();
            println!("new grand prod takes {}ms", start.elapsed().as_millis());
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let e = old.calculate_grand_product(&worker).unwrap();
            let a = new.calculate_grand_product(&worker).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let e = old.calculate_grand_product_serial().unwrap();
            let a = new.calculate_grand_product_serial().unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let e = old.calculate_sum(&worker).unwrap();
            let a = new.calculate_sum(&worker).unwrap();
            assert_eq!(e, a);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let (e0, e1) = old.calculate_grand_sum(&worker).unwrap();
            let (a0, a1) = new.calculate_grand_sum(&worker).unwrap();
            assert_eq!(e0, a0);
            assert_eq!(&e1.coeffs[..], &a1.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let e = old.pop_last().unwrap();
            let a = new.pop_last().unwrap();
            assert_eq!(e, a);
            assert_eq!(&old.coeffs[..], &new.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let by = DEGREE/2;
            let e = old.clone_shifted_assuming_natural_ordering(by).unwrap();
            let a = new.clone_shifted_assuming_natural_ordering(by).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            let mut old = old.clone();
            let mut new = new.clone();
            let by = DEGREE/2;
            let e = old.clone_shifted_assuming_bitreversed(by, &worker).unwrap();
            let a = new.clone_shifted_assuming_bitreversed(by, &worker).unwrap();
            assert_eq!(&e.coeffs[..], &a.coeffs[..]);
        }
        {
            
            let omegas_bitreversed = BitReversedOmegas::<Fr>::new_for_domain_size(DEGREE);
            let omegas_bitreversed_inv = OmegasInvBitreversed::<Fr>::new_for_domain_size(DEGREE);
            {
                let mut old = old.clone();
                let mut new = new.clone();
                let coset_factor = Fr::multiplicative_generator();
                let e = old.ifft_using_bitreversed_ntt(&worker, &omegas_bitreversed_inv, &coset_factor).unwrap();
                let a = new.ifft_using_bitreversed_ntt(&worker, &omegas_bitreversed_inv, &coset_factor).unwrap();
                assert_eq!(&e.coeffs[..], &a.coeffs[..]);
            }
        }
   }
        
}