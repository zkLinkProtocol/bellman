use cfg_if::*;

cfg_if!{
    if #[cfg(feature = "allocator")]{
        pub mod unstable;
        use self::unstable as cs;        
    }else{        
        pub mod stable;        
        use self::stable as cs;
    }
}

use super::*;
pub use self::cs::*;