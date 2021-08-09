use crate::ff::PrimeField;
use crate::resource_management::utils::get_chunk_size;
use super::bitreverse::bitreverse_enumeration;

pub fn precompute_bitreversed_half_size_twiddles<F: PrimeField>(omega: F, domain_size: usize) -> Vec<F>
{
    debug_assert!(domain_size.is_power_of_two());
    debug_assert_eq!(omega.pow(&[domain_size as u64]), F::one());
    let mut twiddles = vec![F::zero(); domain_size/2];
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
    }).expect("must run");
    bitreverse_enumeration(&mut twiddles);

    twiddles
}