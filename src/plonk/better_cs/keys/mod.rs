cfg_if!{
    if #[cfg(feature = "allocator")]{
        pub mod unstable;
        use self::unstable as keys;        
    }else{        
        pub mod stable;        
        use self::stable as keys;
    }
}

pub use keys::*;