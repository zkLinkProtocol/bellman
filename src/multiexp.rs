use crate::pairing::{
    CurveAffine,
    CurveProjective,
    Engine
};

use crate::pairing::ff::{
    PrimeField,
    Field,
    PrimeFieldRepr,
    ScalarEngine};

use std::sync::Arc;
use super::source::*;
use std::future::{Future};
use std::task::{Context, Poll};
use std::pin::{Pin};

extern crate futures;

use self::futures::future::{join_all, JoinAll};
use self::futures::executor::block_on;

use super::worker::{Worker, WorkerFuture};

use super::SynthesisError;

use cfg_if;

/// This genious piece of code works in the following way:
/// - choose `c` - the bit length of the region that one thread works on
/// - make `2^c - 1` buckets and initialize them with `G = infinity` (that's equivalent of zero)
/// - there is no bucket for "zero" cause it's not necessary
/// - go over the pairs `(base, scalar)`
/// - for each scalar calculate `scalar % 2^c` and add the base (without any multiplications!) to the 
/// corresponding bucket
/// - at the end each bucket will have an accumulated value that should be multiplied by the corresponding factor
/// between `1` and `2^c - 1` to get the right value
/// - here comes the first trick - you don't need to do multiplications at all, just add all the buckets together
/// starting from the first one `(a + b + c + ...)` and than add to the first sum another sum of the form
/// `(b + c + d + ...)`, and than the third one `(c + d + ...)`, that will result in the proper prefactor infront of every
/// accumulator, without any multiplication operations at all
/// - that's of course not enough, so spawn the next thread
/// - this thread works with the same bit width `c`, but SKIPS lowers bits completely, so it actually takes values
/// in the form `(scalar >> c) % 2^c`, so works on the next region
/// - spawn more threads until you exhaust all the bit length
/// - you will get roughly `[bitlength / c] + 1` inaccumulators
/// - double the highest accumulator enough times, add to the next one, double the result, add the next accumulator, continue
/// 
/// Demo why it works:
/// ```text
///     a * G + b * H = (a_2 * (2^c)^2 + a_1 * (2^c)^1 + a_0) * G + (b_2 * (2^c)^2 + b_1 * (2^c)^1 + b_0) * H
/// ```
/// - make buckets over `0` labeled coefficients
/// - make buckets over `1` labeled coefficients
/// - make buckets over `2` labeled coefficients
/// - accumulators over each set of buckets will have an implicit factor of `(2^c)^i`, so before summing thme up
/// "higher" accumulators must be doubled `c` times
///
#[cfg(not(feature = "nightly"))]
fn multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    skip: u32,
    c: u32,
    handle_trivial: bool
) -> WorkerFuture< <G as CurveAffine>::Projective, SynthesisError>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    // Perform this region of the multiexp
    let this = {
        // let bases = bases.clone();
        // let exponents = exponents.clone();
        // let density_map = density_map.clone();

        // This is a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

            // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                // Go over density and exponents
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as 
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % (1 << c);

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    this
}

#[cfg(not(feature = "nightly"))]
fn affine_multiexp_inner<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    skip: u32,
    c: u32,
    handle_trivial: bool
) -> WorkerFuture< <G as CurveAffine>::Projective, SynthesisError>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: AccessableSourceBuilder<G>
{
    let reduction_size = 1 << 14;

    // Perform this region of the multiexp
    let this = {
        // let bases = bases.clone();
        // let exponents = exponents.clone();
        // let density_map = density_map.clone();

        // This is a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            let mut work_size = 0usize;

            // Build a source for the bases
            let mut bases = bases.new();
            let mut work_sizes: Vec<usize> = vec![0; (1 << c) - 1];

            // let mut bucket_sums = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let mut scratch_x_diff: Vec<Vec<G::Base>> = vec![Vec::with_capacity(reduction_size); (1 << c) - 1];
            let mut scratch_y_diff: Vec<Vec<G::Base>> = vec![Vec::with_capacity(reduction_size); (1 << c) - 1];
            let mut scratch_x0_x1_y0: Vec<Vec<(G::Base, G::Base, G::Base)>> = vec![Vec::with_capacity(reduction_size); (1 << c) - 1];

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets: Vec<Vec<(G::Base, G::Base)>> = vec![Vec::with_capacity(reduction_size*2); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

            // Sort the bases into buckets
            for (&exp, density) in exponents.iter().zip(density_map.as_ref().iter()) {
                // Go over density and exponents
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            buckets[0].push(bases.get_ref()?.into_xy_unchecked());
                            work_sizes[0] += 1;
                            if work_sizes[0] & 1 == 0 {
                                work_size += 1;
                            }
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as 
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % (1 << c);

                        if exp != 0 {
                            buckets[(exp-1) as usize].push(bases.get_ref()?.into_xy_unchecked());
                            work_sizes[(exp-1) as usize] += 1;
                            if work_sizes[(exp-1) as usize] & 1 == 0 {
                                work_size += 1;
                            }

                        } else {
                            bases.skip(1)?;
                        }
                    }
                }

                if work_size >= reduction_size {
                    work_size = reduce::<G>(&mut buckets, &mut scratch_x_diff, &mut scratch_y_diff, &mut scratch_x0_x1_y0, &mut work_sizes)?;
                    // {
                    //     for ((bucket, running_sum_per_bucket), size) in buckets.iter_mut()
                    //                                         .zip(bucket_sums.iter_mut())
                    //                                         .zip(work_sizes.iter_mut()) {
                    //         let mut subsum = G::Projective::zero();
                    //         for _ in 0..bucket.len() {
                    //             running_sum_per_bucket.add_assign_mixed(&bucket.pop().unwrap());
                    //         }
                    //         *size = 0;
                    //     }
                    //     work_size = 0;
                    // }
                }
            }

            work_size = reduce::<G>(&mut buckets, &mut scratch_x_diff, &mut scratch_y_diff, &mut scratch_x0_x1_y0, &mut work_sizes)?;
            // {
                // for ((bucket, running_sum_per_bucket), size) in buckets.iter_mut()
                //                                     .zip(bucket_sums.iter_mut())
                //                                     .zip(work_sizes.iter_mut()) {
                //     let mut subsum = G::Projective::zero();
                //     for _ in 0..bucket.len() {
                //         running_sum_per_bucket.add_assign_mixed(&bucket.pop().unwrap());
                //     }
                //     *size = 0;
                // }
                // work_size = 0;
            // }


            // // Summation by parts
            // // e.g. 3a + 2b + 1c = a +
            // //                    (a) + b +
            // //                    ((a) + b) + c
            // let mut running_sum = G::Projective::zero();
            // for exp in bucket_sums.into_iter().rev() {
            //     running_sum.add_assign(&exp);
            //     acc.add_assign(&running_sum);
            // }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                let mut subsum = G::Projective::zero();
                for b in exp.into_iter() {
                    let p = G::from_xy_unchecked(b.0, b.1);
                    subsum.add_assign_mixed(&p);
                }
                running_sum.add_assign(&subsum);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };

    this
}

fn total_len<G: CurveAffine>(buckets: &Vec<Vec<(G::Base, G::Base)>>) -> usize {
    let mut result = 0;
    for b in buckets.iter() {
        result += b.len();
    }

    result
}

fn reduce<G: CurveAffine>(
    buckets: &mut Vec<Vec<(G::Base, G::Base)>>, 
    scratch_pad_x_diff: &mut Vec<Vec<G::Base>>,
    scratch_pad_y_diff: &mut Vec<Vec<G::Base>>, 
    scratch_pad_x0_x1_y0: &mut Vec<Vec<(G::Base, G::Base, G::Base)>>,
    work_counters: &mut Vec<usize>
) -> Result<usize, SynthesisError> {
    let initial_size = total_len::<G>(&*buckets);

    // First pass: compute [a, ab, abc, ...]
    let mut prod = Vec::with_capacity(initial_size);

    let one = <G::Base as Field>::one();
    let mut tmp = one;

    for ((((b, scratch_y), scratch_x), scratch_x0_x1_y0), work_counter) in buckets.iter_mut()
                                    .zip(scratch_pad_y_diff.iter_mut())
                                    .zip(scratch_pad_x_diff.iter_mut())
                                    .zip(scratch_pad_x0_x1_y0.iter_mut())
                                    .zip(work_counters.iter()) {
        assert!(scratch_x.len() == 0);
        assert!(scratch_y.len() == 0);
        assert!(scratch_x0_x1_y0.len() == 0);

        let len = b.len();

        assert!(*work_counter == len);

        if len <= 1 {
            continue;
        }

        // println!("During merging bucket len = {}", len);

        // make windows of two
        let mut drain_iter = if len & 1 == 1 {
            b.drain(1..)
        } else {
            b.drain(0..)
        };

        // let mut iter = b.into_iter();
        for _ in 0..(len/2) {
            let (x0, y0) = drain_iter.next().unwrap();
            let (x1, y1) = drain_iter.next().unwrap();

            let mut y_diff = y1;
            y_diff.sub_assign(&y0);

            let mut x_diff = x1;
            x_diff.sub_assign(&x0);

            scratch_y.push(y_diff);
            scratch_x.push(x_diff);
            scratch_x0_x1_y0.push((x0, x1, y0));

            tmp.mul_assign(&x_diff);
            prod.push(tmp);

        }
    }

    tmp = tmp.inverse().unwrap();

    
    // [abcd..., ..., ab, a, 1]
    // this is just a batch inversion
    let mut prod_iter = prod.into_iter().rev().skip(1).chain(Some(one));

    for x_diff in scratch_pad_x_diff.iter_mut().rev() {
        for x_diff_value in x_diff.iter_mut().rev() {
            let p = prod_iter.next().unwrap();
            let mut newtmp = tmp;
            newtmp.mul_assign(&x_diff_value);
            *x_diff_value = tmp;
            x_diff_value.mul_assign(&p);
    
            tmp = newtmp;
        }
    }

    // assert!(prod_iter.next().is_none());

    for ((((b, scratch_y), scratch_x), scratch_x0_x1_y0), work_counter) in buckets.iter_mut()
                                        .zip(scratch_pad_y_diff.iter_mut())
                                        .zip(scratch_pad_x_diff.iter_mut())
                                        .zip(scratch_pad_x0_x1_y0.iter_mut())
                                        .zip(work_counters.iter_mut()) {
        if *work_counter <= 1 {
            continue;
        }

        // println!("During work bucket len = {}", b.len());

        for ((x_diff, y_diff), x0_x1_y0) in scratch_x.iter().zip(scratch_y.iter()).zip(scratch_x0_x1_y0.iter()) {
            let mut lambda = *y_diff;
            lambda.mul_assign(&x_diff);

            let mut x_new = lambda;
            x_new.square();

            x_new.sub_assign(&x0_x1_y0.0); // - x0
            x_new.sub_assign(&x0_x1_y0.1); // - x1

            let mut y_new = x0_x1_y0.1; // x1
            y_new.sub_assign(&x_new);
            y_new.mul_assign(&lambda);
            y_new.sub_assign(&x0_x1_y0.2);

            b.push((x_new, y_new));
        }


        *work_counter = b.len();

        scratch_x.truncate(0);
        scratch_y.truncate(0);
        scratch_x0_x1_y0.truncate(0);
    }

    let final_size = total_len::<G>(&*buckets);

    assert!(initial_size >= final_size, "initial size is {}, final is {}", initial_size, final_size);

    Ok(final_size)
}


cfg_if! {
    if #[cfg(feature = "nightly")] {
        #[inline(always)]
        fn multiexp_inner_impl<Q, D, G, S>(
            pool: &Worker,
            bases: S,
            density_map: D,
            exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
            skip: u32,
            c: u32,
            handle_trivial: bool
        ) -> WorkerFuture< <G as CurveAffine>::Projective, SynthesisError>
            where for<'a> &'a Q: QueryDensity,
                D: Send + Sync + 'static + Clone + AsRef<Q>,
                G: CurveAffine,
                S: SourceBuilder<G>
        {
            multiexp_inner_with_prefetch(pool, bases, density_map, exponents, skip, c, handle_trivial)
        }
    } else {
        #[inline(always)]
        fn multiexp_inner_impl<Q, D, G, S>(
            pool: &Worker,
            bases: S,
            density_map: D,
            exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
            skip: u32,
            c: u32,
            handle_trivial: bool
        ) -> WorkerFuture< <G as CurveAffine>::Projective, SynthesisError>
            where for<'a> &'a Q: QueryDensity,
                D: Send + Sync + 'static + Clone + AsRef<Q>,
                G: CurveAffine,
                S: SourceBuilder<G>
        {
            multiexp_inner(pool, bases, density_map, exponents, skip, c, handle_trivial)
        }
    }  
}



#[cfg(feature = "nightly")]
extern crate prefetch;

#[cfg(feature = "nightly")]
fn multiexp_inner_with_prefetch<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>,
    skip: u32,
    c: u32,
    handle_trivial: bool
) -> WorkerFuture< <G as CurveAffine>::Projective, SynthesisError>
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    use prefetch::prefetch::*;
    // Perform this region of the multiexp
    let this = {
        // This is a Pippenger’s algorithm
        pool.compute(move || {
            // Accumulate the result
            let mut acc = G::Projective::zero();

            // Build a source for the bases
            let mut bases = bases.new();

            // Create buckets to place remainders s mod 2^c,
            // it will be 2^c - 1 buckets (no bucket for zeroes)

            // Create space for the buckets
            let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];

            let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
            let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();
            let padding = Arc::new(vec![zero]);

            let mask = 1 << c;

            // Sort the bases into buckets
            for ((&exp, &next_exp), density) in exponents.iter()
                        .zip(exponents.iter().skip(1).chain(padding.iter()))
                        .zip(density_map.as_ref().iter()) {
                // no matter what happens - prefetch next bucket
                if next_exp != zero && next_exp != one {
                    let mut next_exp = next_exp;
                    next_exp.shr(skip);
                    let next_exp = next_exp.as_ref()[0] % mask;
                    if next_exp != 0 {
                        let p: *const <G as CurveAffine>::Projective = &buckets[(next_exp - 1) as usize];
                        prefetch::<Write, High, Data, _>(p);
                    }
                    
                }
                // Go over density and exponents
                if density {
                    if exp == zero {
                        bases.skip(1)?;
                    } else if exp == one {
                        if handle_trivial {
                            bases.add_assign_mixed(&mut acc)?;
                        } else {
                            bases.skip(1)?;
                        }
                    } else {
                        // Place multiplication into the bucket: Separate s * P as 
                        // (s/2^c) * P + (s mod 2^c) P
                        // First multiplication is c bits less, so one can do it,
                        // sum results from different buckets and double it c times,
                        // then add with (s mod 2^c) P parts
                        let mut exp = exp;
                        exp.shr(skip);
                        let exp = exp.as_ref()[0] % mask;

                        if exp != 0 {
                            bases.add_assign_mixed(&mut buckets[(exp - 1) as usize])?;
                        } else {
                            bases.skip(1)?;
                        }
                    }
                }
            }

            // Summation by parts
            // e.g. 3a + 2b + 1c = a +
            //                    (a) + b +
            //                    ((a) + b) + c
            let mut running_sum = G::Projective::zero();
            for exp in buckets.into_iter().rev() {
                running_sum.add_assign(&exp);
                acc.add_assign(&running_sum);
            }

            Ok(acc)
        })
    };
    
    this
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
pub fn multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>
) -> ChunksJoiner< <G as CurveAffine>::Projective >
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: SourceBuilder<G>
{
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.

        assert!(query_size == exponents.len());
    }

    let mut skip = 0;
    let mut futures = Vec::with_capacity((<G::Engine as ScalarEngine>::Fr::NUM_BITS / c + 1) as usize);

    while skip < <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        let chunk_future = if skip == 0 {
            multiexp_inner_impl(pool, bases.clone(), density_map.clone(), exponents.clone(), 0, c, true)
        } else {
            multiexp_inner_impl(pool, bases.clone(), density_map.clone(), exponents.clone(), skip, c, false)
        };

        futures.push(chunk_future);
        skip += c;
    }

    let join = join_all(futures);

    ChunksJoiner {
        join,
        c
    } 
}

/// Perform multi-exponentiation. The caller is responsible for ensuring the
/// query size is the same as the number of exponents.
pub fn affine_multiexp<Q, D, G, S>(
    pool: &Worker,
    bases: S,
    density_map: D,
    exponents: Arc<Vec<<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr>>
) -> ChunksJoiner< <G as CurveAffine>::Projective >
    where for<'a> &'a Q: QueryDensity,
          D: Send + Sync + 'static + Clone + AsRef<Q>,
          G: CurveAffine,
          S: AccessableSourceBuilder<G>
{
    // let c = if exponents.len() < 32 {
    //     3u32
    // } else {
    //     (f64::from(exponents.len() as u32)).ln().ceil() as u32
    // };

    let c = 8u32;

    if let Some(query_size) = density_map.as_ref().get_query_size() {
        // If the density map has a known query size, it should not be
        // inconsistent with the number of exponents.

        assert!(query_size == exponents.len());
    }

    let mut skip = 0;
    let mut futures = Vec::with_capacity((<G::Engine as ScalarEngine>::Fr::NUM_BITS / c + 1) as usize);

    while skip < <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        let chunk_future = if skip == 0 {
            affine_multiexp_inner(pool, bases.clone(), density_map.clone(), exponents.clone(), 0, c, true)
        } else {
            affine_multiexp_inner(pool, bases.clone(), density_map.clone(), exponents.clone(), skip, c, false)
        };

        futures.push(chunk_future);
        skip += c;
    }

    let join = join_all(futures);

    ChunksJoiner {
        join,
        c
    } 
}

pub struct ChunksJoiner<G: CurveProjective> {
    join: JoinAll< WorkerFuture<G, SynthesisError> >,
    c: u32
}

impl<G: CurveProjective> Future for ChunksJoiner<G> {
    type Output = Result<G, SynthesisError>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        let c = self.as_ref().c;
        let join = unsafe { self.map_unchecked_mut(|s| &mut s.join) };
        match join.poll(cx) {
            Poll::Ready(v) => {
                let v = join_chunks(v, c);
                return Poll::Ready(v);
            },
            Poll::Pending => {
                return Poll::Pending;
            }
        }
    }
}

impl<G: CurveProjective> ChunksJoiner<G> {
    pub fn wait(self) -> <Self as Future>::Output {
        block_on(self)
    }
}

fn join_chunks<G: CurveProjective>
    (chunks: Vec<Result<G, SynthesisError>>, c: u32) -> Result<G, SynthesisError> {
    if chunks.len() == 0 {
        return Ok(G::zero());
    }

    let mut iter = chunks.into_iter().rev();
    let higher = iter.next().expect("is some chunk result");
    let mut higher = higher?;

    for chunk in iter {
        let this = chunk?;
        for _ in 0..c {
            higher.double();
        }

        higher.add_assign(&this);
    }

    Ok(higher)
}


/// Perform multi-exponentiation. The caller is responsible for ensuring that
/// the number of bases is the same as the number of exponents.
#[allow(dead_code)]
pub fn dense_multiexp<G: CurveAffine>(
    pool: &Worker,
    bases: & [G],
    exponents: & [<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr]
) -> Result<<G as CurveAffine>::Projective, SynthesisError>
{
    if exponents.len() != bases.len() {
        return Err(SynthesisError::AssignmentMissing);
    }
    let c = if exponents.len() < 32 {
        3u32
    } else {
        (f64::from(exponents.len() as u32)).ln().ceil() as u32
    };

    dense_multiexp_inner(pool, bases, exponents, 0, c, true)
}

fn dense_multiexp_inner<G: CurveAffine>(
    pool: &Worker,
    bases: & [G],
    exponents: & [<<G::Engine as ScalarEngine>::Fr as PrimeField>::Repr],
    mut skip: u32,
    c: u32,
    handle_trivial: bool
) -> Result<<G as CurveAffine>::Projective, SynthesisError>
{   
    use std::sync::{Mutex};
    // Perform this region of the multiexp. We use a different strategy - go over region in parallel,
    // then over another region, etc. No Arc required
    let this = {
        // let mask = (1u64 << c) - 1u64;
        let this_region = Mutex::new(<G as CurveAffine>::Projective::zero());
        let arc = Arc::new(this_region);
        pool.scope(bases.len(), |scope, chunk| {
            for (base, exp) in bases.chunks(chunk).zip(exponents.chunks(chunk)) {
                let this_region_rwlock = arc.clone();
                // let handle = 
                scope.spawn(move |_| {
                    let mut buckets = vec![<G as CurveAffine>::Projective::zero(); (1 << c) - 1];
                    // Accumulate the result
                    let mut acc = G::Projective::zero();
                    let zero = <G::Engine as ScalarEngine>::Fr::zero().into_repr();
                    let one = <G::Engine as ScalarEngine>::Fr::one().into_repr();

                    for (base, &exp) in base.iter().zip(exp.iter()) {
                        // let index = (exp.as_ref()[0] & mask) as usize;

                        // if index != 0 {
                        //     buckets[index - 1].add_assign_mixed(base);
                        // }

                        // exp.shr(c as u32);

                        if exp != zero {
                            if exp == one {
                                if handle_trivial {
                                    acc.add_assign_mixed(base);
                                }
                            } else {
                                let mut exp = exp;
                                exp.shr(skip);
                                let exp = exp.as_ref()[0] % (1 << c);
                                if exp != 0 {
                                    buckets[(exp - 1) as usize].add_assign_mixed(base);
                                }
                            }
                        }
                    }

                    // buckets are filled with the corresponding accumulated value, now sum
                    let mut running_sum = G::Projective::zero();
                    for exp in buckets.into_iter().rev() {
                        running_sum.add_assign(&exp);
                        acc.add_assign(&running_sum);
                    }

                    let mut guard = match this_region_rwlock.lock() {
                        Ok(guard) => guard,
                        Err(_) => {
                            panic!("poisoned!"); 
                            // poisoned.into_inner()
                        }
                    };

                    (*guard).add_assign(&acc);
                });
        
            }
        });

        let this_region = Arc::try_unwrap(arc).unwrap();
        let this_region = this_region.into_inner().unwrap();

        this_region
    };

    skip += c;

    if skip >= <G::Engine as ScalarEngine>::Fr::NUM_BITS {
        // There isn't another region, and this will be the highest region
        return Ok(this);
    } else {
        // next region is actually higher than this one, so double it enough times
        let mut next_region = dense_multiexp_inner(
            pool, bases, exponents, skip, c, false).unwrap();
        for _ in 0..c {
            next_region.double();
        }

        next_region.add_assign(&this);

        return Ok(next_region);
    }
}

#[test]
fn test_new_multiexp_with_bls12() {
    fn naive_multiexp<G: CurveAffine>(
        bases: Arc<Vec<G>>,
        exponents: Arc<Vec<<G::Scalar as PrimeField>::Repr>>
    ) -> G::Projective
    {
        assert_eq!(bases.len(), exponents.len());

        let mut acc = G::Projective::zero();

        for (base, exp) in bases.iter().zip(exponents.iter()) {
            acc.add_assign(&base.mul(*exp));
        }

        acc
    }

    use rand::{self, Rand};
    use crate::pairing::bls12_381::Bls12;

    use self::futures::executor::block_on;

    const SAMPLES: usize = 1 << 14;

    let rng = &mut rand::thread_rng();
    let v = Arc::new((0..SAMPLES).map(|_| <Bls12 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>());
    let g = Arc::new((0..SAMPLES).map(|_| <Bls12 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

    let naive = naive_multiexp(g.clone(), v.clone());

    let pool = Worker::new();

    let fast = block_on(
        multiexp(
            &pool,
            (g, 0),
            FullDensity,
            v
        )
    ).unwrap();

    assert_eq!(naive, fast);
}

#[test]
#[ignore]
fn test_new_multexp_speed_with_bn256() {
    use rand::{self, Rand};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    let cpus = num_cpus::get();
    const SAMPLES: usize = 1 << 22;

    let rng = &mut rand::thread_rng();
    let v = Arc::new((0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>());
    let g = Arc::new((0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

    let pool = Worker::new();

    use self::futures::executor::block_on;

    let start = std::time::Instant::now();

    let _fast = block_on(
        multiexp(
            &pool,
            (g, 0),
            FullDensity,
            v
        )
    ).unwrap();


    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("Elapsed {} ns for {} samples", duration_ns, SAMPLES);
    let time_per_sample = duration_ns/(SAMPLES as f64);
    println!("Tested on {} samples on {} CPUs with {} ns per multiplication", SAMPLES, cpus, time_per_sample);
}


#[test]
fn test_dense_multiexp_vs_new_multiexp() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    // const SAMPLES: usize = 1 << 22;
    const SAMPLES: usize = 1 << 16;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

    println!("Done generating test points and scalars");

    let pool = Worker::new();

    let start = std::time::Instant::now();

    let dense = dense_multiexp(
        &pool, &g, &v.clone()).unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for dense for {} samples", duration_ns, SAMPLES);

    use self::futures::executor::block_on;

    let start = std::time::Instant::now();

    let sparse = block_on(
        multiexp(
            &pool,
            (Arc::new(g), 0),
            FullDensity,
            Arc::new(v)
        )
    ).unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for sparse for {} samples", duration_ns, SAMPLES);

    assert_eq!(dense, sparse);
}

#[test]
fn test_affine_multiexp() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    // const SAMPLES: usize = 1 << 20;
    const SAMPLES: usize = 1 << 10;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

    println!("Done generating test points and scalars");

    let pool = Worker::new_with_cpus(1);

    let bases = Arc::new(g);
    let scalars = Arc::new(v);

    use self::futures::executor::block_on;

    let _affine = block_on(
        affine_multiexp(
            &pool,
            (bases.clone(), 0),
            FullDensity,
            scalars.clone()
        )
    ).unwrap();
}


#[test]
fn test_multiexp_vs_affine_multiexp() {
    use rand::{XorShiftRng, SeedableRng, Rand, Rng};
    use crate::pairing::bn256::Bn256;
    use num_cpus;

    const SAMPLES: usize = 1 << 20;
    // const SAMPLES: usize = 1 << 16;
    let rng = &mut XorShiftRng::from_seed([0x3dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

    let v = (0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng).into_repr()).collect::<Vec<_>>();
    let g = (0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>();

    println!("Done generating test points and scalars");

    let pool = Worker::new();

    let bases = Arc::new(g);
    let scalars = Arc::new(v);

    use self::futures::executor::block_on;

    let start = std::time::Instant::now();

    let standard = block_on(
        multiexp(
            &pool,
            (bases.clone(), 0),
            FullDensity,
            scalars.clone()
        )
    ).unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for standard multiexp for {} samples", duration_ns, SAMPLES);

    // let pool = Worker::new_with_cpus(1);

    let start = std::time::Instant::now();

    let affine = block_on(
        affine_multiexp(
            &pool,
            (bases.clone(), 0),
            FullDensity,
            scalars.clone()
        )
    ).unwrap();

    let duration_ns = start.elapsed().as_nanos() as f64;
    println!("{} ns for affine multiexp for {} samples", duration_ns, SAMPLES);

    // assert_eq!(standard, affine);
}