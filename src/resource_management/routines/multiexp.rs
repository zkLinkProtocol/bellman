use std::io::BufWriter;

use super::*;
use crate::pairing::Engine;
use crate::pairing::ff::PrimeField;
use futures::task::SpawnExt;

const WIDTH: u32 = 16;
const NUM_BUCKETS: usize = 1 << (WIDTH-1);
const MM: u64 = 1u64 << WIDTH;
const MIDPOINT: u64 = MM >> 1;
const MASK: u64 = MM - 1;
pub const NUM_WINDOWS: usize = 16;

pub async fn multiexp<E: Engine>(worker: Worker, scalars: Arc<Vec<E::Fr>>, bases: Arc<Vec<E::G1Affine>>, is_background: bool) -> E::G1 {
    let m1 = std::time::Instant::now();
    let windows = scalars_to_signed_digits::<E>(worker.child(), scalars, is_background).await;
    dbg!(m1.elapsed());
    // bump a priority
    let worker = worker.next();
    let num_windows = windows.len();
    let mut all_futures = Vec::with_capacity(num_windows);
    let m2 = std::time::Instant::now();
    for w in std::array::IntoIter::new(windows) {
        let fut = sort_into_buckets::<E>(worker.child(), w, bases.clone(), is_background);
        let spawned_fut = worker.inner.manager.thread_pool.spawn_with_handle(fut).expect("must spawn a future");
        all_futures.push(spawned_fut);
    }
    let join = join_all(all_futures).await;
    dbg!(m2.elapsed());

    // bump a priority
    let worker = worker.next();
    let mut all_futures = Vec::with_capacity(num_windows);
    let m3 = std::time::Instant::now();
    for buckets in join.into_iter() {
        let fut = sum_buckets::<E>(worker.child(), buckets, is_background);
        let spawned_fut = worker.inner.manager.thread_pool.spawn_with_handle(fut).expect("must spawn a future");
        all_futures.push(spawned_fut);
    }
    let join = join_all(all_futures).await;
    dbg!(m3.elapsed());

    let mut it = join.into_iter().rev();
    let mut result = it.next().unwrap();
    use crate::pairing::CurveProjective;
    for p in it {
        for _ in 0..WIDTH {
            result.double();
        }
        result.add_assign(&p);
    }

    result
}

pub async fn sort_into_buckets<E: Engine>(worker_scope: Worker, digits: Vec<SignedDigit>, bases: Arc<Vec<E::G1Affine>>, is_background: bool) -> Vec<E::G1> {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;
    assert_eq!(digits.len(), bases.len());

    let granted_resources = worker_scope.get_cpu_unit(is_background).await.await;
    
    let mut all_buckets = vec![E::G1::zero(); NUM_BUCKETS];
    let s1 = std::time::Instant::now();
    for (digit, base) in digits.into_iter().zip(bases.iter()) {
        let mut base = *base;
        let (sign, abs) = digit.to_sign_and_abs();
        if abs == 0 {
            continue;
        }
        if sign {
            base.negate();
        }
        all_buckets[(abs-1) as usize].add_assign_mixed(&base);
    }
    dbg!(s1.elapsed());
    worker_scope.return_resources(granted_resources).await;

    all_buckets
}

pub async fn sum_buckets<E: Engine>(worker: Worker, mut buckets: Vec<E::G1>, is_background: bool) -> E::G1 {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;

    let granted_resources = worker.get_cpu_unit(is_background).await.await;

    E::G1::batch_normalization(&mut buckets);
    let buckets = buckets.into_iter().map(|el| el.into_affine());

    // let buckets = buckets.into_iter();

    let mut acc = E::G1::zero();
    let mut running_sum = E::G1::zero();
    for exp in buckets.rev() {
        running_sum.add_assign_mixed(&exp);
        // running_sum.add_assign(&exp);
        acc.add_assign(&running_sum);
    }
    worker.return_resources(granted_resources).await;
    
    acc
}

fn scalar_to_signed_digits<F: PrimeField>(scalar: &F) -> [SignedDigit; NUM_WINDOWS] {
    let mut repr = scalar.into_repr();
    let mut digits = [SignedDigit::new(); NUM_WINDOWS];
    for d in digits.iter_mut() {
        let mut part = repr.as_ref()[0] & MASK;
        sub_single_noborrow(repr.as_mut(), part);
        if part >= MIDPOINT {
            part = MM - part;
            add_single_nocarry(repr.as_mut(), MM);
            *d = SignedDigit::from_sign_and_abs(true, part as u16);
        } else {
            *d = SignedDigit::from_sign_and_abs(false, part as u16);
        }
        repr.shr(WIDTH);
    }

    debug_assert!(repr.is_zero());

    digits
}

async fn scalars_range_to_signed_digits<E: Engine>(worker: Worker, scalars: Arc<Vec<E::Fr>>, range: Range<usize>, is_background: bool) -> Vec<[SignedDigit; NUM_WINDOWS]> {
    let granted_resources = worker.get_cpu_unit(is_background).await.await;
    let mut result = Vec::with_capacity(range.len());
    let source = &scalars[range];
    for scalar in source.iter() {
        let digits = scalar_to_signed_digits(scalar);
        result.push(digits);
    }

    worker.return_resources(granted_resources).await;

    result
}

pub async fn scalars_to_signed_digits<E: Engine>(worker: Worker, scalars: Arc<Vec<E::Fr>>, is_background: bool) -> [Vec<SignedDigit>; NUM_WINDOWS] {
    let max_resources = worker.max_available_resources();
    let allocated_cpus = max_resources.cpu_cores;
    let num_scalars = scalars.len();
    // we have taken some cpus, now we can use them without futures, and just spawn threads
    let chunk_size = get_chunk_size(num_scalars, allocated_cpus);
    let ranges = get_ranges(num_scalars, chunk_size);
    assert_eq!(ranges.len(), allocated_cpus);
    let s1 = std::time::Instant::now();
    let mut all_futures = Vec::with_capacity(ranges.len());
    for range in ranges.into_iter() {
        let fut = scalars_range_to_signed_digits::<E>(worker.child(), scalars.clone(), range, is_background);
        let spawned_fut = worker.inner.manager.thread_pool.spawn_with_handle(fut).expect("must spawn a future");
        all_futures.push(spawned_fut);
    }

    let join = join_all(all_futures).await;
    dbg!(s1.elapsed());

    // now we need to transpose the results to sort into all the signed digits at the same place
    let s2 = std::time::Instant::now();
    // let mut final_result: [Vec<_>; NUM_WINDOWS] = (0..16).map(|_| Vec::with_capacity(num_scalars)).collect::<Vec<_>>().try_into().unwrap();
    let mut final_result: [Vec<_>; NUM_WINDOWS] = (0..16).map(|_| vec![SignedDigit::new(); num_scalars]).collect::<Vec<_>>().try_into().unwrap();
    let [mut w0, mut w1, mut w2, mut w3, mut w4, mut w5, mut w6, mut w7, mut w8, mut w9, mut w10, mut w11, mut w12, mut w13, mut w14, mut w15] = final_result;
    let mut results_iter = w0.iter_mut()
        .zip(w1.iter_mut())
        .zip(w2.iter_mut())
        .zip(w3.iter_mut())
        .zip(w4.iter_mut())
        .zip(w5.iter_mut())
        .zip(w6.iter_mut())
        .zip(w7.iter_mut())
        .zip(w8.iter_mut())
        .zip(w9.iter_mut())
        .zip(w10.iter_mut())
        .zip(w11.iter_mut())
        .zip(w12.iter_mut())
        .zip(w13.iter_mut())
        .zip(w14.iter_mut())
        .zip(w15.iter_mut());

    let mut src_iter = join.into_iter().map(|el| el.into_iter()).flatten();
    for (dst, src) in (&mut results_iter).zip(&mut src_iter) {
        let (((((((((((((((s0, s1), s2), s3), s4), s5), s6), s7), s8), s9), s10), s11), s12), s13), s14), s15) = dst;
        let [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15] = src;
        *s0 = t0;
        *s1 = t1;
        *s2 = t2;
        *s3 = t3;
        *s4 = t4;
        *s5 = t5;
        *s6 = t6;
        *s7 = t7;
        *s8 = t8;
        *s9 = t9;
        *s10 = t10;
        *s11 = t11;
        *s12 = t12;
        *s13 = t13;
        *s14 = t14;
        *s15 = t15;
    }
    assert!(results_iter.next().is_none());
    assert!(src_iter.next().is_none());

    dbg!(s2.elapsed());

    let final_result = [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15];

    final_result
}