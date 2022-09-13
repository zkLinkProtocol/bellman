use cfg_if::*;

cfg_if!{
    if #[cfg(feature = "allocator")]{
        pub mod unstable;
        use self::unstable as data_structures;        
    }else{        
        pub mod stable;        
        use self::stable as data_structures;
    }
}

use super::*;
pub use self::data_structures::*;