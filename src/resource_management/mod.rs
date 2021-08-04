pub mod utils;

use core::num;
use std::ops::DerefMut;
use std::sync::atomic::AtomicU32;
use std::cmp::*;
use std::sync::Arc;
use std::convert::TryInto;

use futures_locks::RwLock;
use pairing::ff::PrimeFieldRepr;
use std::future::{Future};
use std::task::{Context, Poll};
use std::pin::{Pin};

use crossbeam::thread::{Scope};

use futures::future::{join_all, lazy};
use futures::channel::oneshot::{channel, Sender, Receiver};
use futures::executor::{block_on};
use futures::executor::{ThreadPool};

#[derive(Clone, Copy, Debug, Default)]
pub struct Resources {
    pub cpu_cores: usize,
    pub fpga_units: usize,
    pub fpga_memory: usize,
    pub gpu_units: usize,
    pub gpu_memory: usize
}

#[derive(Debug)]
struct ResourceManagerInner {
    resources: Resources,
    priority_requests: std::collections::BinaryHeap<ResourceResponse>,
    background_requests: std::collections::BinaryHeap<ResourceResponse>,
}

#[derive(Debug)]
pub struct ResourceManager {
    epoch: AtomicU32,
    thread_pool: ThreadPool,
    resources: RwLock<ResourceManagerInner>,
}

fn try_get(num_res: usize, available: &mut usize) -> Option<usize> {
    if *available >= num_res {
        let new_available = *available - num_res;
        *available = new_available;

        Some(num_res)
    } else {
        None
    }
}

fn try_get_res(all_res: &mut Resources, requested: Resources) -> bool {
    if all_res.cpu_cores < requested.cpu_cores {
        return false
    }

    all_res.cpu_cores -= requested.cpu_cores;
    all_res.fpga_units -= requested.fpga_units;
    all_res.fpga_memory -= requested.fpga_memory;
    all_res.gpu_units -= requested.gpu_units;
    all_res.gpu_memory -= requested.gpu_memory;

    true
}

fn return_res(all_res: &mut Resources, returned: Resources) {
    all_res.cpu_cores += returned.cpu_cores;
    all_res.fpga_units += returned.fpga_units;
    all_res.fpga_memory += returned.fpga_memory;
    all_res.gpu_units += returned.gpu_units;
    all_res.gpu_memory += returned.gpu_memory;
}

use pin_project::pin_project;

#[derive(Clone, Copy, Debug)]
pub struct ResourceRequest {
    priority: u32,
    resources: Resources,
}

#[derive(Debug)]
struct ResourceResponse {
    epoch: u32,
    id: u32,
    resources: Resources,
    sender: Sender<Resources>
}

#[pin_project]
pub struct ResourceResponseFuture {
    #[pin]
    receiver: Receiver<Resources>
}

impl PartialOrd for ResourceResponse {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ResourceResponse {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.epoch.cmp(&other.epoch) {
            Ordering::Equal => {
                self.id.cmp(&other.id)
            },
            o @ _ => {
                o
            }
        }
    }
}

impl PartialEq for ResourceResponse {
    fn eq(&self, other: &Self) -> bool {
        self.epoch == other.epoch && self.id == other.id
    }
}

impl Eq for ResourceResponse {}

impl Future for ResourceResponseFuture {
    type Output = Resources;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        println!("Polling `ResourceResponseFuture`");
        let this = self.project();
        let rec = this.receiver;
        match rec.poll(cx) {
            Poll::Ready(v) => {
                if let Ok(v) = v {
                    return Poll::Ready(v)
                } else {
                    panic!("Can not have canceled sender");
                }
            },
            Poll::Pending => {
                return Poll::Pending;
            }
        }
    }
}

pub struct Worker {
    inner: Arc<WorkerInner>,
}

struct WorkerInner {
    epoch: AtomicU32,
    manager: Arc<ResourceManager>,
}

impl Worker {
    fn scope(&self) -> WorkerScope {
        let epoch = self.inner.epoch.fetch_add(1u32, std::sync::atomic::Ordering::Acquire);

        WorkerScope {
            epoch,
            scope_id: AtomicU32::from(0u32),
            child_id: AtomicU32::from(0u32),
            request_id: AtomicU32::from(0u32),
            worker: self.inner.clone(),
        }
    }
}

pub struct WorkerScope {
    epoch: u32,
    scope_id: AtomicU32,
    child_id: AtomicU32,
    request_id: AtomicU32,
    worker: Arc<WorkerInner>,
}

impl WorkerScope {
    pub fn child(&self) -> WorkerScope {
        let old_id = self.child_id.fetch_add(1u32, std::sync::atomic::Ordering::Acquire);
        let child_id = self.child_id.swap(old_id, std::sync::atomic::Ordering::Acquire);

        let this_scope_id = self.scope_id.load(std::sync::atomic::Ordering::Acquire);

        WorkerScope {
            epoch: self.epoch,
            scope_id: AtomicU32::from(this_scope_id),
            child_id: AtomicU32::from(child_id),
            request_id: AtomicU32::from(0),
            worker: self.worker.clone(),
        }
    }
    pub async fn get_cpu_unit(&self, is_background: bool) -> ResourceResponseFuture {
        let id = self.request_id.fetch_add(1u32, std::sync::atomic::Ordering::Acquire);
        let mut resources = Resources::default();
        resources.cpu_cores = 1;
        let resp = self.worker.manager.get_resources(self.epoch, id, resources, is_background).await;

        resp
    }

    pub async fn return_resources(&self, resources: Resources) {
        self.worker.manager.return_resources(resources).await;
    }
}

pub struct ResourceManagerProxy {
    inner: Arc<ResourceManager>,
}

impl ResourceManagerProxy {
    pub fn new_simple() -> Self {
        let inner = ResourceManager::new_simple();
        Self {
            inner: Arc::new(inner)
        }
    }
    pub fn create_worker(&self) -> Worker {
        let epoch = self.inner.epoch.fetch_add(1u32, std::sync::atomic::Ordering::Acquire);

        let inner = WorkerInner {
            epoch: AtomicU32::from(epoch),
            manager: self.inner.clone(),
        };

        Worker {
            inner: Arc::new(inner)
        }
    }
    
    pub async fn return_resources(&self, resources: Resources) {
        self.inner.return_resources(resources).await;
    }
}

impl ResourceManager {
    pub(crate) fn new_simple() -> Self {
        Self::new_simple_with_cpus(num_cpus::get_physical())
    }

    pub(crate) fn new_simple_with_cpus(cpus: usize) -> Self {
        let pool = ThreadPool::builder().pool_size(cpus).create().expect("should create a thread pool for futures execution");
        let resources = Resources {
            cpu_cores: cpus,
            fpga_units: 0,
            fpga_memory: 0,
            gpu_units: 0,
            gpu_memory: 0
        };

        let inner = ResourceManagerInner {
            resources,
            priority_requests: std::collections::BinaryHeap::new(),
            background_requests: std::collections::BinaryHeap::new(),
        };

        Self {
            epoch: AtomicU32::from(0),
            thread_pool: pool,
            resources: RwLock::new(inner)
        }
    }

    fn get_resources_handler(manager: &mut ResourceManagerInner, epoch: u32, id: u32, resources: Resources, is_background: bool) -> ResourceResponseFuture {
        let (sender, receiver) = channel();
        let req = ResourceResponse {
            epoch: epoch,
            id,
            resources,
            sender,
        };

        let resp = ResourceResponseFuture {
            receiver
        };

        if is_background {
            manager.background_requests.push(req);
        } else {
            manager.priority_requests.push(req);
        }

        Self::try_yeild(manager);
        
        resp
    }

    fn try_yeild(manager: &mut ResourceManagerInner) {
        let available_resources = &mut manager.resources;
        let mut proceed_background = false;
        if let Some(req) = manager.priority_requests.pop() {
            println!("Trying to process priority request");
            let res = req.resources;
            let can_allocate = try_get_res(available_resources, res);
            if can_allocate {
                println!("Granted resources to priority request: {:?}", res);
                if !req.sender.is_canceled() {
                    let _ = req.sender.send(res);
                }
            } else {
                manager.priority_requests.push(req);
                proceed_background = true;
            }
        }

        if proceed_background {
            if let Some(req) = manager.background_requests.pop() {
                println!("Trying to process priority request");
                let res = req.resources;
                let can_allocate = try_get_res(available_resources, res);
                if can_allocate {
                    println!("Granted resources to background request: {:?}", res);
                    if !req.sender.is_canceled() {
                        let _ = req.sender.send(res);
                    }
                } else {
                    manager.background_requests.push(req);
                }
            }
        }
    }

    async fn get_resources(&self, epoch: u32, id: u32, resources: Resources, is_background: bool) -> ResourceResponseFuture {
        let mut lock = self.resources.write().await;
        let inner = lock.deref_mut();
        let resp = Self::get_resources_handler(inner, epoch, id, resources, is_background);
        drop(lock);

        resp
    }

    async fn return_resources(&self, resources: Resources) {
        let mut lock = self.resources.write().await;
        let inner = lock.deref_mut();
        return_res(&mut inner.resources, resources);
        drop(lock);
    }
}


#[pin_project]
pub struct WorkerFuture<T, E> {
    #[pin]
    receiver: Receiver<Result<T, E>>
}

impl<T: Send + 'static, E: Send + 'static> Future for WorkerFuture<T, E> {
    type Output = Result<T, E>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        let this = self.project();
        let rec = this.receiver;
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

impl<T: Send + 'static, E: Send + 'static> WorkerFuture<T, E> {
    pub fn wait(self) -> <Self as Future>::Output {
        block_on(self)
    }
}

impl Worker {
    pub fn compute<F, T, E>(
        &self, f: F
    ) -> WorkerFuture<T, E>
        where F: FnOnce(WorkerScope) -> Result<T, E> + Send + 'static,
              T: Send + 'static,
              E: Send + 'static
    {
        let scope = self.scope();
        scope.compute(f)
    }
}

impl WorkerScope {
    pub async fn get_max_cpus(&self, is_background: bool) -> ResourceResponseFuture {
        let epoch = self.epoch;
        let id = (self.child_id.load(std::sync::atomic::Ordering::Acquire) << 16) | self.request_id.load(std::sync::atomic::Ordering::Acquire);
        let mut resources = Resources::default();
        resources.cpu_cores = 4;
        let resp = self.worker.manager.get_resources(epoch, id, resources, is_background).await;

        resp
    }

    pub fn compute<F, T, E>(
        self, f: F
    ) -> WorkerFuture<T, E>
        where F: FnOnce(WorkerScope) -> Result<T, E> + Send + 'static,
              T: Send + 'static,
              E: Send + 'static
    {
        let thread_pool = (*self.worker.manager).thread_pool.clone();
        let (sender, receiver) = channel();
        let lazy_future = lazy(move |_| {
            let res = f(self); 

            if !sender.is_canceled() {
                let _ = sender.send(res);
            }
        });

        let worker_future = WorkerFuture {
            receiver
        };

        thread_pool.spawn_ok(lazy_future);

        worker_future
    }
}

use crate::pairing::Engine;
use crate::resource_management::utils::{ChunkableVector, get_chunk_size};

// fn multiexp_proto<E: Engine>(worker: Worker, bases: Arc<Vec<E::G1Affine>>, scalars: Vec<E::Fr>) -> WorkerFuture<E::G1Affine, ()> {

// }

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SignedDigit(u16);

impl SignedDigit {
    const SGN_MASK: u16 = 1u16 << 15;
    const SGN_SHIFT: u32 = 15;
    const ABS_MASK: u16 = !Self::SGN_MASK;
    const MAX_ABS: u16 = 1u16 << 15;

    fn from_sign_and_abs(sign: bool, abs: u16) -> Self {
        if sign {
            debug_assert!(abs != 0)
        }

        if abs == Self::MAX_ABS && sign {
            Self(Self::MAX_ABS)
        } else {
            Self((sign as u16) << Self::SGN_SHIFT | abs)
        }
    }

    fn to_sign_and_abs(self) -> (bool, u16) {
        let sgn = ((self.0 & Self::SGN_MASK) >> Self::SGN_SHIFT) != 0;
        let mut abs = self.0 & Self::ABS_MASK;
        if sgn && abs == 0 {
            abs = Self::MAX_ABS;
        }

        (sgn, abs)
    }
}

#[inline(always)]
fn add_single_nocarry(src: &mut [u64], value: u64) {
    let (r0, c) = src[0].overflowing_add(value);
    src[0] = r0;
    let mut carry = c;
    for s in src.iter_mut().skip(1) {
        let (res, c) = s.overflowing_add(carry as u64);
        carry = c;
    }
    debug_assert!(!carry);
}

#[inline(always)]
fn sub_single_noborrow(src: &mut [u64], value: u64) {
    let (r0, b) = src[0].overflowing_sub(value);
    src[0] = r0;
    let mut borrow = b;
    for s in src.iter_mut().skip(1) {
        let (res, b) = s.overflowing_sub(borrow as u64);
        borrow = b;
    }
    debug_assert!(!borrow);
}

async fn multiexp_proto<E: Engine>(worker_scope: WorkerScope, scalars: Arc<Vec<E::Fr>>, bases: Arc<Vec<E::G1Affine>>) -> E::G1 {
    let windows = scalars_to_signed_digits::<E>(worker_scope.child(), scalars).await;
    let num_windows = windows.len();
    let mut all_futures = Vec::with_capacity(num_windows);
    for w in std::array::IntoIter::new(windows) {
        let fut = sort_into_buckets::<E>(worker_scope.child(), w, bases.clone());
        all_futures.push(fut);
    }

    let join = join_all(all_futures).await;

    let mut all_futures = Vec::with_capacity(num_windows);
    for buckets in join.into_iter() {
        let fut = sum_buckets::<E>(worker_scope.child(), buckets);
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

const WIDTH: u32 = 16;

async fn sort_into_buckets<E: Engine>(worker_scope: WorkerScope, digits: Vec<SignedDigit>, bases: Arc<Vec<E::G1Affine>>) -> Vec<E::G1> {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;
    assert_eq!(digits.len(), bases.len());

    let granted_resources = worker_scope.get_cpu_unit(false).await.await;
    
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

async fn sum_buckets<E: Engine>(worker_scope: WorkerScope, mut buckets: Vec<E::G1>) -> E::G1 {
    use crate::pairing::CurveProjective;
    use crate::pairing::CurveAffine;

    let granted_resources = worker_scope.get_cpu_unit(false).await.await;

    E::G1::batch_normalization(&mut buckets);
    let buckets = buckets.into_iter().map(|el| el.into_affine());

    let mut acc = E::G1::zero();
    let mut running_sum = E::G1::zero();
    for exp in buckets.rev() {
        running_sum.add_assign_mixed(&exp);
        // running_sum.add_assign(&exp);
        acc.add_assign(&running_sum);
    }

    worker_scope.return_resources(granted_resources).await;
    
    acc
}

async fn scalars_to_signed_digits<E: Engine>(worker_scope: WorkerScope, scalars: Arc<Vec<E::Fr>>) -> [Vec<SignedDigit>; 16] {
    const MM: u64 = 1u64 << WIDTH;
    const MIDPOINT: u64 = MM >> 1;
    const MASK: u64 = MM - 1;

    const NUM_WINDOWS: usize = 16;

    let granted_resources = worker_scope.get_max_cpus(false).await.await;
    println!("Granted resources in a future: {:?}", granted_resources);
    let allocated_cpus = granted_resources.cpu_cores;
    let num_scalars = scalars.len();
    // we have taken some cpus, now we can use them without futures, and just spawn threads
    let chunk_size = get_chunk_size(num_scalars, allocated_cpus);
    let mut results: Vec<Vec<[SignedDigit; NUM_WINDOWS]>> = vec![vec![]; allocated_cpus];
    let results_ref = &mut results;
    println!("Spawning");
    crossbeam::scope(|scope| {
        for (c, dst) in scalars.chunks(chunk_size).zip(results_ref.iter_mut()) {
            scope.spawn(move |_| {
                let mut result = Vec::with_capacity(chunk_size);
                for scalar in c.iter() {
                    use crate::pairing::ff::PrimeField;
                    let mut repr = scalar.into_repr();
                    let mut digits = [SignedDigit(0); NUM_WINDOWS];
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
                    result.push(digits);
                }
                *dst = result;
            });
        }
    }).expect("must run");

    println!("Done paraller work");

    // now we need to transpose the results to sort into all the signed digits at the same place

    let mut final_result: [Vec<_>; NUM_WINDOWS] = (0..16).map(|_| Vec::with_capacity(num_scalars)).collect::<Vec<_>>().try_into().unwrap();
    for r in results.into_iter() {
        for el in r.into_iter() {
            for (i, src) in std::array::IntoIter::new(el).enumerate() {
                final_result[i].push(src);
            }
        }
    }

    worker_scope.return_resources(granted_resources).await;

    final_result
}

#[cfg(test)]
mod test {
    use std::thread::Thread;

    use super::*;

    use futures::task::SpawnExt;
    use rand::{self, Rand};
    use crate::pairing::bn256::Bn256;
    use crate::pairing::ff::*;
    use crate::pairing::CurveProjective;

    #[test]
    fn test_spawn_simple() {
        const SAMPLES: usize = 1 << 10;

        let rng = &mut rand::thread_rng();
        let v = Arc::new((0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng)).collect::<Vec<_>>());
        let g = Arc::new((0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

        let pool = ThreadPool::builder().pool_size(4).create().unwrap();
        let manager = ResourceManagerProxy::new_simple();
        let worker = manager.create_worker();
        let scope = worker.scope();
        drop(worker);
        let fut = multiexp_proto::<Bn256>(scope, v, g);
        let handle = manager.inner.thread_pool.spawn_with_handle(fut).unwrap();
        let result = block_on(handle);
        dbg!(result);

        let inner = manager.inner;
        dbg!(Arc::strong_count(&inner));
        let manager = Arc::try_unwrap(inner).unwrap();
        dbg!(manager.resources.try_unwrap().unwrap());
    }
}