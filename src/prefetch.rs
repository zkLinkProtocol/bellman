// #[repr(i32)]
// pub(crate) enum Locality {
//     L1 = core::arch::x86_64::_MM_HINT_T0,
//     L2 = core::arch::x86_64::_MM_HINT_T1,
//     L3 = core::arch::x86_64::_MM_HINT_T2,
//     Somewhere = core::arch::x86_64::_MM_HINT_NTA,
// }

// #[cfg(
//     all(
//         any(target_arch = "x86", target_arch = "x86_64"),
//         target_feature = "sse"
//     )
// )]
// #[inline(always)]
// pub(crate) fn prefetch<T: Sized>(reference: &T, locality: Locality) {
//     #[cfg(target_arch = "x86")]
//     use std::arch::x86::_mm_prefetch;
//     #[cfg(target_arch = "x86_64")]
//     use std::arch::x86_64::_mm_prefetch;
    
//     unsafe {
//         _mm_prefetch(reference as *T, locality as i32);
//     }
// }

cfg_if! {
    if #[cfg(
        all(
            any(target_arch = "x86", target_arch = "x86_64"),
            target_feature = "sse"
        )
    )] {
        #[inline(always)]
        pub(crate) fn prefetch_l1_pointer<T: Sized>(pointer: *const T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(pointer as *const i8, core::arch::x86_64::_MM_HINT_T0);
            }
        }

        #[inline(always)]
        pub(crate) fn prefetch_l2_pointer<T: Sized>(pointer: *const T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(pointer as *const i8, core::arch::x86_64::_MM_HINT_T1);
            }
        }

        #[inline(always)]
        pub(crate) fn prefetch_l3_pointer<T: Sized>(pointer: *const T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(pointer as *const i8, core::arch::x86_64::_MM_HINT_T2);
            }
        }

        #[inline(always)]
        pub(crate) fn prefetch_l1<T: Sized>(reference: &T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(reference as *const T as *const i8, core::arch::x86_64::_MM_HINT_T0);
            }
        }

        #[inline(always)]
        pub(crate) fn prefetch_l2<T: Sized>(reference: &T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(reference as *const T as *const i8, core::arch::x86_64::_MM_HINT_T1);
            }
        }

        #[inline(always)]
        pub(crate) fn prefetch_l3<T: Sized>(reference: &T) {
            #[cfg(target_arch = "x86")]
            use std::arch::x86::_mm_prefetch;
            #[cfg(target_arch = "x86_64")]
            use std::arch::x86_64::_mm_prefetch;
            

            unsafe {
                _mm_prefetch(reference as *const T as *const i8, core::arch::x86_64::_MM_HINT_T2);
            }
        }
    } else {
        #[inline(always)]
        pub(crate) fn prefetch_l1_pointer<T: Sized>(pointer: *const T) {}

        #[inline(always)]
        pub(crate) fn prefetch_l2_pointer<T: Sized>(pointer: *const T) {}

        #[inline(always)]
        pub(crate) fn prefetch_l3_pointer<T: Sized>(pointer: *const T) {}

        #[inline(always)]
        pub(crate) fn prefetch_l1<T: Sized>(reference: &T) {}

        #[inline(always)]
        pub(crate) fn prefetch_l2<T: Sized>(reference: &T) {}

        #[inline(always)]
        pub(crate) fn prefetch_l3<T: Sized>(reference: &T) {}
    }
}
