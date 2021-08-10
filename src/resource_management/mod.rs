use core::num;
use std::ops::{DerefMut, Range};
use std::sync::atomic::{AtomicU32, AtomicUsize};
use std::cmp::*;
use std::sync::Arc;
use std::convert::TryInto;

use futures_locks::RwLock;
use pairing::ff::PrimeFieldRepr;
use std::future::{Future};
use std::task::{Context, Poll};
use std::pin::{Pin};

use crossbeam::thread::{Scope};

pub mod priority_modifier;
pub mod resources;
pub mod utils;
pub mod routines;

use self::priority_modifier::Priority;
use self::resources::*;
use self::utils::*;
pub use self::routines::*;

use futures::future::{join_all, lazy};
use futures::channel::oneshot::{channel, Sender, Receiver};
use futures::executor::{block_on};
use futures::executor::{ThreadPool};


#[derive(Debug)]
struct ResourceManagerInner {
    resources: Resources,
    priority_requests: std::collections::BinaryHeap<ResourceResponse>,
    background_requests: std::collections::BinaryHeap<ResourceResponse>,
}

#[derive(Debug)]
pub struct ResourceManager {
    epoch: AtomicU32,
    request_counter: AtomicUsize,
    thread_pool: ThreadPool,
    max_resources: Resources,
    resources: RwLock<ResourceManagerInner>,
}

const PRIORITY_DEPTH: usize = 8;

use pin_project::pin_project;

#[derive(Clone, Copy, Debug)]
pub struct ResourceRequest {
    priority: u32,
    resources: Resources,
}

#[derive(Debug)]
struct ResourceResponse {
    epoch: u32,
    priority: Priority<PRIORITY_DEPTH>,
    request_id: usize,
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
                match self.priority.cmp(&other.priority) {
                    Ordering::Equal => { 
                        self.request_id.cmp(&other.request_id)
                    },
                    o @ _ => {
                        o
                    }
                }
            },
            o @ _ => {
                o
            }
        }
    }
}

impl PartialEq for ResourceResponse {
    fn eq(&self, other: &Self) -> bool {
        self.epoch == other.epoch && self.priority == other.priority && self.request_id == other.request_id
    }
}

impl Eq for ResourceResponse {}

impl Future for ResourceResponseFuture {
    type Output = Resources;

    fn poll(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Self::Output>
    {
        // println!("Polling `ResourceResponseFuture`");
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

struct WorkerInner {
    manager: Arc<ResourceManager>,
}

pub struct Worker {
    epoch: u32,
    priority: Priority<PRIORITY_DEPTH>,
    inner: Arc<WorkerInner>,
}

impl Worker {
    pub fn child(&self) -> Self {
        let child = self.priority.child();

        Self {
            epoch: self.epoch,
            priority: child,
            inner: self.inner.clone(),
        }
    }
    pub fn next(self) -> Self {
        let priority = self.priority.next();
        Self {
            epoch: self.epoch,
            priority,
            inner: self.inner.clone(),
        }
    }
    pub async fn get_cpu_unit(&self, is_background: bool) -> ResourceResponseFuture {
        let priority = self.priority.clone();
        let mut resources = Resources::default();
        resources.cpu_cores = 1;
        let resp = self.inner.manager.get_resources(self.epoch, priority, resources, is_background).await;

        resp
    }

    pub async fn return_resources(&self, resources: Resources) {
        self.inner.manager.return_resources(resources).await;
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
            manager: self.inner.clone(),
        };

        Worker {
            epoch,
            priority: Priority::new(),
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
            max_resources: resources,
            epoch: AtomicU32::from(0),
            request_counter: AtomicUsize::from(0),
            thread_pool: pool,
            resources: RwLock::new(inner)
        }
    }

    fn get_resources_handler(manager: &mut ResourceManagerInner, epoch: u32, request_id: usize, priority: Priority<PRIORITY_DEPTH>, resources: Resources, is_background: bool) -> ResourceResponseFuture {
        let (sender, receiver) = channel();
        let req = ResourceResponse {
            epoch,
            request_id,
            priority,
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
            // println!("Trying to process priority request");
            let res = req.resources;
            let can_allocate = try_get_res(available_resources, res);
            if can_allocate {
                // println!("Granted resources to priority request: {:?}", res);
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
                // println!("Trying to process priority request");
                let res = req.resources;
                let can_allocate = try_get_res(available_resources, res);
                if can_allocate {
                    // println!("Granted resources to background request: {:?}", res);
                    if !req.sender.is_canceled() {
                        let _ = req.sender.send(res);
                    }
                } else {
                    manager.background_requests.push(req);
                }
            }
        }
    }

    async fn get_resources(&self, epoch: u32, priority: Priority<PRIORITY_DEPTH>, resources: Resources, is_background: bool) -> ResourceResponseFuture {
        let mut lock = self.resources.write().await;
        let inner = lock.deref_mut();
        let request_id = self.request_counter.fetch_add(1usize, std::sync::atomic::Ordering::Acquire);
        let resp = Self::get_resources_handler(inner, epoch, request_id, priority, resources, is_background);
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
    pub async fn get_max_cpus(&self, is_background: bool) -> ResourceResponseFuture {
        let epoch = self.epoch;
        let priority = self.priority.clone();
        let mut resources = Resources::default();
        resources.cpu_cores = 4;
        let resp = self.inner.manager.get_resources(epoch, priority, resources, is_background).await;

        resp
    }

    pub fn max_available_resources(&self) -> Resources {
        self.inner.manager.max_resources
    }
}

use crate::resource_management::utils::{ChunkableVector, get_chunk_size};

#[cfg(test)]
mod test {
    use std::thread::Thread;

    use super::*;

    use futures::task::SpawnExt;
    use rand::{self, Rand};
    use crate::pairing::bn256::Bn256;
    use crate::pairing::ff::*;
    use crate::pairing::{Engine, CurveProjective};

    use super::*;

    #[test]
    fn test_spawn_simple() {
        const SAMPLES: usize = 1 << 10;

        let rng = &mut rand::thread_rng();
        let v = Arc::new((0..SAMPLES).map(|_| <Bn256 as ScalarEngine>::Fr::rand(rng)).collect::<Vec<_>>());
        let g = Arc::new((0..SAMPLES).map(|_| <Bn256 as Engine>::G1::rand(rng).into_affine()).collect::<Vec<_>>());

        let pool = ThreadPool::builder().pool_size(4).create().unwrap();
        let manager = ResourceManagerProxy::new_simple();
        let worker = manager.create_worker();
        let fut = multiexp::<Bn256>(worker, v.clone(), g.clone(), false);
        let handle = manager.inner.thread_pool.spawn_with_handle(fut).unwrap();
        let result = block_on(handle);
        dbg!();

        let inner = manager.inner;
        dbg!(Arc::strong_count(&inner));
        let manager = Arc::try_unwrap(inner).unwrap();
        dbg!(manager.resources.try_unwrap().unwrap());

        let pool = crate::multicore::Worker::new();
        let vv = v.iter().map(|el| el.into_repr()).collect::<Vec<_>>();
        let g = Arc::try_unwrap(g).unwrap();
        let reference_result = crate::multiexp::dense_multiexp(&pool, &g, &vv).unwrap();
        assert_eq!(result.into_affine(), reference_result.into_affine());
    }
}