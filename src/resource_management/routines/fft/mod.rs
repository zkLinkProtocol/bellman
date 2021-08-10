mod transpose;
mod strided_fft;

pub use strided_fft::non_generic_radix_sqrt as fft;

#[cfg(test)]
mod test {
    use super::super::utils::*;
    use futures::task::SpawnExt;
    use rand::{self, Rand};
    use crate::pairing::bn256::Bn256;
    use crate::pairing::ff::*;
    use crate::pairing::{Engine, CurveProjective};
    use crate::plonk::domains::Domain;
    use futures::executor::{block_on};
    use super::*;
    use super::super::ResourceManagerProxy;
    use std::sync::Arc;

    use std::time::Instant;
    
    #[test]
    fn test_async_fft() {
        const SAMPLES: usize = 1 << 24;

        let rng = &mut rand::thread_rng();
        let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng)).collect::<Vec<_>>();

        let domain = Domain::<<Bn256 as ScalarEngine>::Fr>::new_for_size(SAMPLES as u64).unwrap();
        let omega = domain.generator;

        let twiddles = precompute_bitreversed_half_size_twiddles(omega, SAMPLES);
        let twiddles = Arc::from(twiddles);
        
        let manager = ResourceManagerProxy::new_simple();
        let worker = manager.create_worker();
        let now = Instant::now();
        let fut = fft::<<Bn256 as ScalarEngine>::Fr, 1024>(
            v.clone(), 
            omega, 
            twiddles,
            worker,
            false
        );
        let handle = manager.inner.thread_pool.spawn_with_handle(fut).unwrap();
        let result = block_on(handle);
        dbg!(now.elapsed());

        use crate::plonk::polynomials::Polynomial;

        let pool = crate::multicore::Worker::new();
        let poly = Polynomial::from_coeffs(v).unwrap();
        let now = Instant::now();
        let mut poly = poly.fft(&pool);
        dbg!(now.elapsed());
        poly.bitreverse_enumeration(&pool);
        let poly = poly.into_coeffs();

        assert_eq!(poly, result);
    }
}