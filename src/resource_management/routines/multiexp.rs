use super::*;
use crate::pairing::Engine;
use crate::pairing::ff::PrimeField;

const WIDTH: u32 = 16;
const MM: u64 = 1u64 << WIDTH;
const MIDPOINT: u64 = MM >> 1;
const MASK: u64 = MM - 1;
const NUM_WINDOWS: usize = 16;

pub async fn multiexp<E: Engine>(worker: Worker, scalars: Arc<Vec<E::Fr>>, bases: Arc<Vec<E::G1Affine>>, is_background: bool) -> E::G1 {
    let windows = scalars_to_signed_digits::<E>(worker.child(), scalars, is_background).await;
    // bump a priority
    let worker = worker.next();
    let num_windows = windows.len();
    let mut all_futures = Vec::with_capacity(num_windows);
    for w in std::array::IntoIter::new(windows) {
        let fut = sort_into_buckets::<E>(worker.child(), w, bases.clone(), is_background);
        all_futures.push(fut);
    }
    let join = join_all(all_futures).await;

    // bump a priority
    let worker = worker.next();
    let mut all_futures = Vec::with_capacity(num_windows);
    for buckets in join.into_iter() {
        let fut = sum_buckets::<E>(worker.child(), buckets, is_background);
        all_futures.push(fut);
    }

    let join = join_all(all_futures).await;

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

async fn sort_into_buckets<E: Engine>(worker_scope: Worker, digits: Vec<SignedDigit>, bases: Arc<Vec<E::G1Affine>>, is_background: bool) -> Vec<E::G1> {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;
    assert_eq!(digits.len(), bases.len());

    let granted_resources = worker_scope.get_cpu_unit(is_background).await.await;
    
    let mut all_buckets = vec![E::G1::zero(); (1<<WIDTH) + 1];
    for (digit, base) in digits.into_iter().zip(bases.iter()) {
        let (sign, abs) = digit.to_sign_and_abs();
        let mut base = *base;
        if abs == 0 {
            continue;
        }
        if sign {
            base.negate();
        }
        all_buckets[(abs-1) as usize].add_assign_mixed(&base);
    }

    worker_scope.return_resources(granted_resources).await;

    all_buckets
}

async fn sum_buckets<E: Engine>(worker: Worker, mut buckets: Vec<E::G1>, is_background: bool) -> E::G1 {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;

    let granted_resources = worker.get_cpu_unit(is_background).await.await;

    E::G1::batch_normalization(&mut buckets);
    let buckets = buckets.into_iter().map(|el| el.into_affine());

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

async fn scalars_to_signed_digits<E: Engine>(worker: Worker, scalars: Arc<Vec<E::Fr>>, is_background: bool) -> [Vec<SignedDigit>; NUM_WINDOWS] {
    let max_resources = worker.max_available_resources();
    println!("All resources in a future: {:?}", max_resources);
    let allocated_cpus = max_resources.cpu_cores;
    let num_scalars = scalars.len();
    // we have taken some cpus, now we can use them without futures, and just spawn threads
    let chunk_size = get_chunk_size(num_scalars, allocated_cpus);
    let ranges = get_ranges(num_scalars, chunk_size);
    dbg!(&ranges);
    assert_eq!(ranges.len(), allocated_cpus);
    let mut all_futures = Vec::with_capacity(ranges.len());
    for range in ranges.into_iter() {
        let fut = scalars_range_to_signed_digits::<E>(worker.child(), scalars.clone(), range, is_background);
        all_futures.push(fut);
    }
    println!("Spawning");

    let join = join_all(all_futures).await;

    println!("Done paraller work");

    // now we need to transpose the results to sort into all the signed digits at the same place

    let mut final_result: [Vec<_>; NUM_WINDOWS] = (0..16).map(|_| Vec::with_capacity(num_scalars)).collect::<Vec<_>>().try_into().unwrap();
    for r in join.into_iter() {
        for el in r.into_iter() {
            for (i, src) in std::array::IntoIter::new(el).enumerate() {
                final_result[i].push(src);
            }
        }
    }

    final_result
}