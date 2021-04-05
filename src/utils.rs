use core::ops::{Sub, Shr};
use num_traits::{Zero, One};
use num_traits::sign::Unsigned;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/*
/// Adds a (little-endian) multi-limb number to another multi-limb number,
/// returning the result and the resulting carry as a sinle-limb value.
/// The carry can be either `0` or `1`.
pub(crate) fn adc_array<T: PrimitiveUInt, const N: usize>(
    x: &[T; N],
    y: &[T; N],
) -> ([T; N], T) {
    let mut res = [T::zero(); N];
    let mut carry = T::zero();
    for i in 0..N {
        let (c, r) = T::adc(x[i], y[i], carry);
        carry = c;
        res[i] = r;
    }
    (res, carry)
}

/// Adds a (little-endian) multi-limb number to another multi-limb number,
/// returning the result and the resulting carry as a constant-time `Choice`
/// (`0` if there was no carry and `1` if there was).
#[inline(always)]
pub(crate) fn adc_array_with_overflow<T: AddWithCarry>(x: &T, y: T) -> (Choice, T) {
    let (carry, res) = adc_array(x, y);
    (Choice::from(carry.as_u8()), res)
}

/// Subtracts a (little-endian) multi-limb number from another multi-limb number,
/// returning the result and the resulting borrow as a sinle-limb value.
/// The borrow can be either `0` or `<u64>::MAX`.
#[inline(always)]
pub(crate) fn sbb_array<T: PrimitiveUInt, const N: usize>(x: &[T; N], y: &[T; N]) -> ([T; N], T) {
    let mut res = [T::zero(); N];
    let mut borrow = T::zero();
    for i in 0..N {
        let (b, r) = T::sbb(x[i], y[i], borrow);
        borrow = b;
        res[i] = r;
    }
    (res, borrow)
}

/// Subtracts a (little-endian) multi-limb number from another multi-limb number,
/// returning the result and the resulting borrow as a constant-time `Choice`
/// (`0` if there was no borrow and `1` if there was).
#[inline(always)]
pub(crate) fn sbb_array_with_underflow<T: PrimitiveUInt, const N: usize>(x: &[T; N], y: &[T; N]) -> ([T; N], Choice) {
    let (res, borrow) = sbb_array(x, y);
    // `borrow` is either 0xFF... or 0.
    (res, Choice::from((borrow >> (T::BITS - T::one())).as_u8()))
}
*/

#[inline(always)]
pub(crate) fn conditional_select<T: ConditionallySelectable + Default, const N: usize>(x: &[T; N], y: &[T; N], choice: Choice) -> [T; N] {
    let mut res = [T::default(); N];
    for i in 0..N {
        res[i] = T::conditional_select(&x[i], &y[i], choice)
    }
    res
}
