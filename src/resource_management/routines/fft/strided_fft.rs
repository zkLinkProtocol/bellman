use futures::task::SpawnExt;

use super::transpose::*;
use super::super::utils::*;
use crate::ff::PrimeField;
use std::sync::Arc;
use crate::resource_management::*;
use crate::resource_management::utils::*;

#[inline(always)]
fn radix_2_butterfly<F: PrimeField>(values: &mut [F], offset: usize, stride: usize) {
    // a + b, a - b
    unsafe {
        let i = offset;
        let j = offset + stride;
        let i_el = *values.get_unchecked(i);
        let j_el = *values.get_unchecked(j);
        values.get_unchecked_mut(i).add_assign(&j_el);
        *values.get_unchecked_mut(j) = i_el;
        values.get_unchecked_mut(j).sub_assign(&j_el);
    }
}

#[inline(always)]
fn radix_2_butterfly_with_twiddle<F: PrimeField>(
    values: &mut [F],
    twiddle: &F,
    offset: usize,
    stride: usize,
) {
    // a + w*b, a - w*b

    // we can make use of partial reduction here:
    // a + w*b \in [0, 3p)
    // a + p - w*b \in [0, 2p)
    unsafe {
        let i = offset;
        let j = offset + stride;
        let i_el = *values.get_unchecked(i);
        let mut j_el = *values.get_unchecked(j);
        j_el.mul_assign(&twiddle);
        values.get_unchecked_mut(i).add_assign(&j_el);
        *values.get_unchecked_mut(j) = i_el;
        values.get_unchecked_mut(j).sub_assign(&j_el);
    }
}

async fn outer_serial_fft<F: PrimeField, const MAX_LOOP_UNROLL: usize, const TWIDDLE: bool>(
    mut values: SubVec<F>,
    omega: F,
    precomputed_twiddle_factors: Arc<Vec<F>>,
    inner_size: usize,
    outer_size: usize,
    absolute_position_offset: usize,
    offset: usize,
    count: usize,
    stride: usize,
    worker: Worker,
    is_background: bool,
) {
    let resources = worker.get_cpu_unit(is_background).await.await;
    let values = values.deref_mut();

    let precomputed_twiddle_factors: &[F] = &*precomputed_twiddle_factors;
    let start = absolute_position_offset;
    for (i, s) in values.chunks_mut(outer_size).enumerate() {
        if TWIDDLE {
            let idx = start + i;
            let i = bitreverse_index(inner_size, idx);
            let inner_twiddle = omega.pow(&[i as u64]);
            let mut outer_twiddle = inner_twiddle;
            for element in s.iter_mut().skip(1) {
                element.mul_assign(&outer_twiddle);
                outer_twiddle.mul_assign(&inner_twiddle);
            }
        }else{
            // TODO: we use here to distribute powers of coset generator
            // through all terms
            
        }

        non_generic_small_size_serial_fft::<F, MAX_LOOP_UNROLL>(
            s,
            precomputed_twiddle_factors,
            offset,
            count,
            stride
        );
    }

    worker.return_resources(resources).await;
}

 fn non_generic_small_size_serial_fft<F: PrimeField, const MAX_LOOP_UNROLL: usize>(
    values: &mut [F],
    precomputed_twiddle_factors: &[F],
    offset: usize,
    count: usize,
    stride: usize,
) {
    debug_assert_eq!(values.len() % stride, 0);
    // work size
    let size = values.len() / stride;
    debug_assert!(size.is_power_of_two(), "size {} is not a power of two. Supplied values length {}, stride {}", size, values.len(), stride);
    debug_assert!(offset < stride);
    if size > 1 {
        // Inner FFT radix size/2 without explicit splitting
        if stride == count && count < MAX_LOOP_UNROLL {
            non_generic_small_size_serial_fft::<F, MAX_LOOP_UNROLL>(
                values,
                precomputed_twiddle_factors,
                offset,
                2 * count,
                2 * stride,
            );
        } else {
            // we may parallelize this too as indexes do not overlap
            non_generic_small_size_serial_fft::<F, MAX_LOOP_UNROLL>(
                values,
                precomputed_twiddle_factors,
                offset,
                count,
                2 * stride,
            );
            non_generic_small_size_serial_fft::<F, MAX_LOOP_UNROLL>(
                values,
                precomputed_twiddle_factors,
                offset + stride,
                count,
                2 * stride,
            );
        }

        // unrolled loops
        // we expect them to be small enough in case of square root division strategy,
        // so we do not need to care about prefetches
        for i in offset..offset + count {
            radix_2_butterfly(values, i, stride);
        }
        for (offset, twiddle) in (offset..offset + size * stride)
            .step_by(2 * stride)
            .zip(precomputed_twiddle_factors.iter())
            .skip(1)
        {
            for i in offset..offset + count {
                radix_2_butterfly_with_twiddle(values, twiddle, i, stride)
            }
        }
    }
}

fn calcualate_inner_and_outer_sizes(size: usize) -> (usize, usize) {
    assert!(size.is_power_of_two());
    let log_n = size.trailing_zeros();
    let inner_size = 1 << (log_n / 2);
    let outer_size = size / inner_size;

    (inner_size, outer_size)
}

pub async fn non_generic_radix_sqrt<F: PrimeField, const MAX_LOOP_UNROLL: usize>(
    job_id: usize,
    values: SubVec<F>, // will be modified
    omega: F,
    precomputed_twiddle_factors: Arc<Vec<F>>,
    worker: Worker,
    is_background: bool,
) -> usize {
    if values.len() <= 1 {
        return job_id; // TODO
    }

    // let mut values = values;

    // Recurse by splitting along the square root
    // Round such that outer is larger.
    let length = values.len();

    let (inner_size, outer_size) = calcualate_inner_and_outer_sizes(length);
    // TODO
    let stretch = outer_size / inner_size;

    debug_assert_eq!(omega.pow(&[length as u64]), F::one());
    debug_assert!(outer_size == inner_size || outer_size == 2 * inner_size);
    debug_assert_eq!(outer_size * inner_size, length);



    // shuffle
    let mut values = values;
    transpose(values.deref_mut(), inner_size, stretch);

    const MAX_EFFICIENTLY_USED_CPUS: usize = 1;

    let max_available_resources = worker.max_available_resources();
    let max_available_cpus = max_available_resources.cpu_cores;
    let cpus_to_use = std::cmp::min(MAX_EFFICIENTLY_USED_CPUS, max_available_cpus);

    let mut all_futures = Vec::with_capacity(cpus_to_use);

    let num_inner_work_units_per_cpu = get_chunk_size(inner_size, cpus_to_use);
    let fft_chunk_size = outer_size * num_inner_work_units_per_cpu;
    // we need to split alligned, so use splitting by precomputed size
    // chunkable_vector
    // let mut_ref: &mut Vec<Vec<_>> = chunkable_vector.as_mut();

    let mut chunk = SubVec::new(vec![]);
    let mut values_copy = values.clone();

    for i in 0..cpus_to_use-1 {
        (chunk, values_copy) = values_copy.split_at(fft_chunk_size);

        let absolute_position_offset = i * num_inner_work_units_per_cpu;
        let fut = outer_serial_fft::<F, MAX_LOOP_UNROLL, false>(
            chunk, 
            omega,
            precomputed_twiddle_factors.clone(),
            inner_size,
            outer_size,
            absolute_position_offset,
            0,
            stretch,
            stretch,
            worker.child(),
            is_background,
        );
        let spawned_fut = worker.spawn_with_handle(fut).expect("must spawn a future");
        all_futures.push(spawned_fut);
    }

    let absolute_position_offset = (cpus_to_use - 1) * num_inner_work_units_per_cpu;
        let fut = outer_serial_fft::<F, MAX_LOOP_UNROLL, false>(
        values_copy, 
        omega,
        precomputed_twiddle_factors.clone(),
        inner_size,
        outer_size,
        absolute_position_offset,
        0,
        stretch,
        stretch,
        worker.child(),
        is_background,
    );
    let spawned_fut = worker.spawn_with_handle(fut).expect("must spawn a future");
    all_futures.push(spawned_fut);

    let _ = join_all(all_futures).await;
    let worker = worker.next();

    transpose(values.deref_mut(), inner_size, stretch);

    let mut all_futures = Vec::with_capacity(cpus_to_use);

    let mut chunk = SubVec::new(vec![]);
    let mut values_copy = values.clone();

    for i in 0..cpus_to_use-1 {
        (chunk, values_copy) = values_copy.split_at(fft_chunk_size);

        let absolute_position_offset = i * num_inner_work_units_per_cpu;
        let fut = outer_serial_fft::<F, MAX_LOOP_UNROLL, true>(
            chunk, 
            omega,
            precomputed_twiddle_factors.clone(),
            inner_size,
            outer_size,
            absolute_position_offset,
            0,
            1,
            1,
            worker.child(),
            is_background,
        );          
        let spawned_fut = worker.spawn_with_handle(fut).expect("must spawn a future");
        all_futures.push(spawned_fut);
    }

    let absolute_position_offset = (cpus_to_use - 1) * num_inner_work_units_per_cpu;
    let fut = outer_serial_fft::<F, MAX_LOOP_UNROLL, true>(
        values_copy, 
        omega,
        precomputed_twiddle_factors.clone(),
        inner_size,
        outer_size,
        absolute_position_offset,
        0,
        1,
        1,
        worker.child(),
        is_background,
    );          
    let spawned_fut = worker.spawn_with_handle(fut).expect("must spawn a future");
    all_futures.push(spawned_fut);

    let _ = join_all(all_futures).await;

    job_id
}