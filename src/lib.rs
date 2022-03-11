#![feature(adt_const_params)]
#![ allow( dead_code, unused_imports, unused_mut, unused_variables, unused_macros, unused_assignments, unreachable_patterns ) ]
#![feature(async_closure)]
#![feature(get_mut_unchecked)]
#[macro_use]

extern crate cfg_if;
pub extern crate pairing;
extern crate rand;
extern crate bit_vec;
extern crate byteorder;

pub use pairing::*;

use crate::pairing::ff as ff;
pub use ff::*;

#[macro_use]
mod log;

pub mod domain;
// pub mod resource_management;

#[cfg(feature = "plonk")]
pub mod plonk;

#[macro_use]
#[cfg(feature = "plonk")]
extern crate lazy_static;

#[cfg(any(feature = "marlin", feature = "plonk"))]
pub mod kate_commitment;

pub mod constants;
mod group;
mod source;
mod multiexp;
mod prefetch;

pub use heavy_ops_service;

#[cfg(test)]
mod tests;

cfg_if! {
    if #[cfg(feature = "multicore")] {
        #[cfg(feature = "wasm")]
        compile_error!("Multicore feature is not yet compatible with wasm target arch");

        mod multicore;
        pub mod worker {
            pub use super::multicore::*;
        }
    } else {
        mod singlecore;
        pub mod worker {
            pub use super::singlecore::*;
        }
    }
}

mod cs;
pub use self::cs::*;

use std::str::FromStr;
use std::env;

cfg_if!{
    if #[cfg(any(not(feature = "nolog"), feature = "sonic"))] {
        fn verbose_flag() -> bool {
            option_env!("BELLMAN_VERBOSE").unwrap_or("0") == "1"
        }
    }
}
