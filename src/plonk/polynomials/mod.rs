cfg_if!{
    if #[cfg(feature = "allocator")]{
        pub mod unstable;
        use self::unstable as polynomials;        
    }else{        
        pub mod stable;        
        use self::stable as polynomials;
    }
}

pub use polynomials::*;