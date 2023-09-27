use fs2::FileExt;
use std::fs::File;
use std::path::PathBuf;
use std::ops::{Deref, DerefMut};

use ec_gpu_gen::fft::FftKernel;
use ec_gpu_gen::multiexp::MultiexpKernel;
use ec_gpu_gen::rust_gpu_tools::{Device, UniqueId};
use ec_gpu_gen::EcError;
use ec_gpu_gen::threadpool::Worker;

use crate::cs::SynthesisError::GpuError;
use crate::pairing::Engine;
use crate::pairing::ff::{PrimeField, Field};

const GPU_LOCK_NAME: &str = "bellman.gpu.lock";

fn tmp_path(filename: &str, id: Option<UniqueId>) -> PathBuf {
    let temp_file = match id {
        Some(id) => format!("{}.{}", filename, id),
        None => filename.to_string(),
    };
    std::env::temp_dir().join(temp_file)
}

/// `GPULock` prevents two kernel objects to be instantiated simultaneously.
#[derive(Debug)]
struct GPULock<'a> {
    file: File,
    path: PathBuf,
    device: &'a Device,
}

impl<'a> GPULock<'a> {
    fn lock() -> Option<Self> {
        if let Ok(bellman_no_gpu) = std::env::var("BELLMAN_NO_GPU") {
            if bellman_no_gpu != "0" {
                return None;
            }
        }

        let devices = Device::all();
        for (index, device) in devices.iter().enumerate() {
            // let memory = device.memory();
            // if memory < min_memory {
            //     continue;
            // }
            let uid = device.unique_id();
            let path = tmp_path(GPU_LOCK_NAME, Some(uid));
            let file = File::create(&path).unwrap_or_else(|_| {
                panic!("Cannot create GPU {:?} lock file at {:?}", uid, &path)
            });
            if file.lock_exclusive().is_err() {
                continue;
            }
            println!("GPU lock acquired at {:?}", path);
            return Some(GPULock {
                file,
                path,
                device: device,
            });
        }
        None
    }

    fn devices(&self) -> Vec<&'a Device> {
        vec! [self.device]
    }
}

impl Drop for GPULock<'_> {
    fn drop(&mut self) {
        self.file.unlock().unwrap();
        println!("GPU lock released at {:?}", &self.path);
    }
}

pub struct LockedFFTKernel<'a, E> where E: Engine {
    lock: GPULock<'a>,
    pub kern: FftKernel<'a, E::Fr>,
}

impl<'a, E> LockedFFTKernel<'a, E> where E: Engine {
    pub fn new() -> Option<Self> {
        match GPULock::lock() {
            Some(lock) => {
                let programs = lock.devices()
                    .iter()
                    .map(|device| ec_gpu_gen::program!(device))
                    .collect::<Result<_, _>>().ok();
                let mut fft_kern = match programs {
                    Some(p) => FftKernel::<E::Fr>::create(p).ok(),
                    _ => None
                };
                match fft_kern {
                    Some(kern) => {
                        return Some(LockedFFTKernel {
                            lock,
                            kern
                        });
                    },
                    _ => return None,
                }
            },
            _ => None
        }
    }
}

impl<'a, E> Deref for LockedFFTKernel<'a, E> where E: Engine {
    type Target = FftKernel<'a, E::Fr>;
    
    fn deref(&self) -> &Self::Target {
        &self.kern
    }
}

impl<'a, E> DerefMut for LockedFFTKernel<'a, E> where E: Engine {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kern
    }
}

pub struct LockedMSMKernel<'a, E> where E: Engine {
    lock: GPULock<'a>,
    pub kern: MultiexpKernel<'a, E::G1Affine>,
}

impl<'a, E> LockedMSMKernel<'a, E> where E: Engine {
    pub fn new() -> Option<Self> {
        match GPULock::lock() {
            Some(lock) => {
                let programs = lock.devices()
                    .iter()
                    .map(|device| ec_gpu_gen::program!(device))
                    .collect::<Result<_, _>>().ok();
                let mut g1_multiexp_kern = match programs {
                    Some(p) => MultiexpKernel::<E::G1Affine>::create(p, &lock.devices()).ok(),
                    _ => None
                };
                match g1_multiexp_kern {
                    Some(kern) => {
                        return Some(LockedMSMKernel {
                            lock,
                            kern
                        });
                    },
                    _ => return None,
                }
            },
            _ => None
        }
    }
}

impl<'a, E> Deref for LockedMSMKernel<'a, E> where E: Engine {
    type Target = MultiexpKernel<'a, E::G1Affine>;
    
    fn deref(&self) -> &Self::Target {
        &self.kern
    }
}

impl<'a, E> DerefMut for LockedMSMKernel<'a, E> where E: Engine {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kern
    }
}
