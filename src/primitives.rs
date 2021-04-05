use core::ops::Shr;

use num_traits::sign::Unsigned;
use num_traits::One;
use subtle::{ConditionallySelectable, ConstantTimeEq};

pub trait PrimitiveUInt:
    Unsigned + Sized + Copy + PartialOrd + Default + Shr + ConditionallySelectable + ConstantTimeEq
{
    const BITS: Self;
    fn from_bool_ct(b: bool) -> Self;
    fn mulhilo(x: Self, y: Self) -> (Self, Self);
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self);
    /// Computes `a - (b + borrow)`, returning the result along with the new borrow.
    fn sbb(a: Self, b: Self, borrow: Self) -> (Self, Self);
    fn wrapping_add(self, other: Self) -> Self;
    fn wrapping_mul(self, other: Self) -> Self;
    fn wrapping_sub(self, other: Self) -> Self;
    fn as_u8(self) -> u8;
}

impl PrimitiveUInt for u64 {
    const BITS: Self = 64;
    #[inline(always)]
    fn from_bool_ct(b: bool) -> Self {
        b as Self
    }
    #[inline(always)]
    fn mulhilo(x: Self, y: Self) -> (Self, Self) {
        let prod = (x as u128).wrapping_mul(y as u128);
        (
            (prod >> <Self as PrimitiveUInt>::BITS) as Self,
            prod as Self,
        )
    }
    #[inline(always)]
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u128)
            .wrapping_add(b as u128)
            .wrapping_add(carry as u128);
        ((ret >> <Self as PrimitiveUInt>::BITS) as Self, ret as Self)
    }
    #[inline(always)]
    fn sbb(a: Self, b: Self, borrow: Self) -> (Self, Self) {
        let shift = (<Self as PrimitiveUInt>::BITS - Self::one()) as u128;
        let ret = (a as u128).wrapping_sub((b as u128).wrapping_add((borrow >> shift) as u128));
        ((ret >> <Self as PrimitiveUInt>::BITS) as Self, ret as Self)
    }
    #[inline(always)]
    fn wrapping_add(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
    #[inline(always)]
    fn wrapping_mul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }
    #[inline(always)]
    fn wrapping_sub(self, other: Self) -> Self {
        self.wrapping_sub(other)
    }
    #[inline(always)]
    fn as_u8(self) -> u8 {
        self as u8
    }
}

impl PrimitiveUInt for u32 {
    const BITS: Self = 32;
    #[inline(always)]
    fn from_bool_ct(b: bool) -> Self {
        b as Self
    }
    #[inline(always)]
    fn mulhilo(x: Self, y: Self) -> (Self, Self) {
        let prod = (x as u64) * (y as u64);
        (
            (prod >> <Self as PrimitiveUInt>::BITS) as Self,
            prod as Self,
        )
    }
    #[inline(always)]
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u64) + (b as u64) + (carry as u64);
        ((ret >> <Self as PrimitiveUInt>::BITS) as Self, ret as Self)
    }
    #[inline(always)]
    fn sbb(a: Self, b: Self, borrow: Self) -> (Self, Self) {
        let shift = (<Self as PrimitiveUInt>::BITS - Self::one()) as u64;
        let ret = (a as u64).wrapping_sub((b as u64).wrapping_add((borrow >> shift) as u64));
        ((ret >> <Self as PrimitiveUInt>::BITS) as Self, ret as Self)
    }
    #[inline(always)]
    fn wrapping_add(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
    #[inline(always)]
    fn wrapping_mul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }
    #[inline(always)]
    fn wrapping_sub(self, other: Self) -> Self {
        self.wrapping_sub(other)
    }
    #[inline(always)]
    fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Add a*b to the number defined by (c0,c1,c2). c2 must never overflow.
pub(crate) fn muladd<T: PrimitiveUInt>(a: T, b: T, c0: T, c1: T, c2: T) -> (T, T, T) {
    // `th` is at most 0xFFFFFFFFFFFFFFFE
    let (th, tl) = T::mulhilo(a, b);

    let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
    let new_th = th.wrapping_add(T::from_bool_ct(new_c0 < tl)); // at most 0xFFFFFFFFFFFFFFFF
    let new_c1 = c1.wrapping_add(new_th); // overflow is handled on the next line
    let new_c2 = c2.wrapping_add(T::from_bool_ct(new_c1 < new_th)); // never overflows by contract (verified in the next line)
    debug_assert!((new_c1 >= new_th) || (new_c2 != T::zero()));
    (new_c0, new_c1, new_c2)
}

/// Add a*b to the number defined by (c0,c1). c1 must never overflow.
pub(crate) fn muladd_fast<T: PrimitiveUInt>(a: T, b: T, c0: T, c1: T) -> (T, T) {
    // `th` is at most 0xFFFFFFFFFFFFFFFE
    let (th, tl) = T::mulhilo(a, b);

    let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
    let new_th = th.wrapping_add(T::from_bool_ct(new_c0 < tl)); // at most 0xFFFFFFFFFFFFFFFF
    let new_c1 = c1.wrapping_add(new_th); // never overflows by contract (verified in the next line)
    debug_assert!(new_c1 >= new_th);
    (new_c0, new_c1)
}

pub trait BigEndian: Copy {
    const SIZE: usize;
    fn to_bytes(self) -> [u8; Self::SIZE];
    fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self;
}

impl BigEndian for u64 {
    const SIZE: usize = 8;

    fn to_bytes(self) -> [u8; Self::SIZE] {
        self.to_be_bytes()
    }

    fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self {
        Self::from_be_bytes(*bytes)
    }
}

impl BigEndian for u32 {
    const SIZE: usize = 4;

    fn to_bytes(self) -> [u8; Self::SIZE] {
        self.to_be_bytes()
    }

    fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self {
        Self::from_be_bytes(*bytes)
    }
}
