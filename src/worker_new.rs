//! This is an interface for dealing with the kinds of
//! parallel computations involved in bellman. It's
//! currently just a thin wrapper around CpuPool and
//! crossbeam but may be extended in the future to
//! allow for various parallelism strategies.

extern crate num_cpus;
extern crate futures_new;
extern crate crossbeam;

use std::future::{Future};
use std::task::{Context, Poll};
use std::pin::{Pin};
use self::futures_new::future::{lazy};
use self::futures_new::channel::oneshot::{channel, Sender, Receiver};
use self::futures_new::executor::{ThreadPool};
// use self::futures_cpupool::{CpuPool, CpuFuture};
use self::crossbeam::thread::{Scope};

#[derive(Clone)]
pub struct Worker {
    cpus: usize,
    pool: ThreadPool
}

impl Worker {
    // We don't expose this outside the library so that
    // all `Worker` instances have the same number of
    // CPUs configured.
    pub(crate) fn new_with_cpus(cpus: usize) -> Worker {
        Worker {
            cpus: cpus,
            pool: ThreadPool::builder().pool_size(cpus).create().expect("should create a thread pool for futures execution")
        }
    }

    pub fn new() -> Worker {
        Self::new_with_cpus(num_cpus::get())
    }

    pub fn log_num_cpus(&self) -> u32 {
        log2_floor(self.cpus)
    }

    pub fn compute<F, T, E>(
        &self, f: F
    ) -> WorkerFuture<T, E>
        where F: FnOnce() -> Result<T, E> + Send + 'static,
              T: Send + 'static,
              E: Send + 'static
    {
        let (sender, receiver) = channel();
        let lazy_future = lazy(move |_| {
            let res = f(); 

            if !sender.is_canceled() {
                let _ = sender.send(res);
            }
        });

        let worker_future = WorkerFuture {
            receiver
        };

        self.pool.spawn_ok(lazy_future);

        worker_future
    }

    pub fn scope<'a, F, R>(
        &self,
        elements: usize,
        f: F
    ) -> R
        where F: FnOnce(&Scope<'a>, usize) -> R
    {
        let chunk_size = if elements < self.cpus {
            1
        } else {
            elements / self.cpus
        };

        crossbeam::scope(|scope| {
            f(scope, chunk_size)
        }).expect("must run")
    }
}

pub struct WorkerFuture<T, E> {
    receiver: Receiver<Result<T, E>>
}

impl<T: Send + 'static, E: Send + 'static> Future for WorkerFuture<T, E> {
    type Output = Result<T, E>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        let rec = unsafe { self.map_unchecked_mut(|s| &mut s.receiver) };
        match rec.poll(cx) {
            Poll::Ready(v) => {
                if let Ok(v) = v {
                    return Poll::Ready(v)
                } else {
                    panic!("Worker future can not have canceled sender");
                }
            },
            Poll::Pending => {
                return Poll::Pending;
            }
        }
    }
}

fn log2_floor(num: usize) -> u32 {
    assert!(num > 0);

    let mut pow = 0;

    while (1 << (pow+1)) <= num {
        pow += 1;
    }

    pow
}

#[test]
fn test_log2_floor() {
    assert_eq!(log2_floor(1), 0);
    assert_eq!(log2_floor(2), 1);
    assert_eq!(log2_floor(3), 1);
    assert_eq!(log2_floor(4), 2);
    assert_eq!(log2_floor(5), 2);
    assert_eq!(log2_floor(6), 2);
    assert_eq!(log2_floor(7), 2);
    assert_eq!(log2_floor(8), 3);
}

#[test]
fn test_trivial_spawning() {
    use self::futures_new::executor::block_on;

    fn long_fn() -> Result<usize, ()> {
        let mut i: usize = 1;
        println!("Start calculating long task");
        for _ in 0..1000000 {
            i = i.wrapping_mul(42);
        }

        Ok(i)
    }

    let worker = Worker::new();
    println!("Spawning");
    let fut = worker.compute(|| long_fn());
    println!("Done spawning");

    let _ = block_on(fut);
}
