
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedDigit(u16);

pub const SIGNED_DIGIT_ENCODING_LEN: usize = 2;

impl SignedDigit {
    const SGN_MASK: u16 = 1u16 << 15;
    const SGN_SHIFT: u32 = 15;
    const ABS_MASK: u16 = !Self::SGN_MASK;
    const MAX_ABS: u16 = 1u16 << 15;

    pub(crate) const fn new() -> Self {
        SignedDigit(0)
    }

    pub(crate) fn from_sign_and_abs(sign: bool, abs: u16) -> Self {
        if sign {
            debug_assert!(abs != 0)
        }

        if abs == Self::MAX_ABS && sign {
            Self(Self::MAX_ABS)
        } else {
            Self((sign as u16) << Self::SGN_SHIFT | abs)
        }
    }

    pub(crate) fn to_sign_and_abs(self) -> (bool, u16) {
        let sgn = ((self.0 & Self::SGN_MASK) >> Self::SGN_SHIFT) != 0;
        let mut abs = self.0 & Self::ABS_MASK;
        if sgn && abs == 0 {
            abs = Self::MAX_ABS;
        }

        (sgn, abs)
    }

    pub const fn serialize(self) -> [u8; SIGNED_DIGIT_ENCODING_LEN] {
        self.0.to_le_bytes()
    }
}

#[inline(always)]
pub(crate) fn add_single_nocarry(src: &mut [u64], value: u64) {
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
pub(crate) fn sub_single_noborrow(src: &mut [u64], value: u64) {
    let (r0, b) = src[0].overflowing_sub(value);
    src[0] = r0;
    let mut borrow = b;
    for s in src.iter_mut().skip(1) {
        let (res, b) = s.overflowing_sub(borrow as u64);
        borrow = b;
    }
    debug_assert!(!borrow);
}