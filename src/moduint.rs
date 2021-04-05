use core::marker::PhantomData;
use core::ops::{Add, Mul};

use num_traits::{One, Zero};
use subtle::{Choice, ConditionallySelectable};

use crate::mluint::{LimbType, MLUInt};
use crate::primitives::PrimitiveUInt;
use crate::traits::{AddWithCarry, SubWithBorrow};

trait Modulus<T>: Copy + Clone + PartialEq {
    const MODULUS: T;
}

trait ValueType: AddWithCarry + SubWithBorrow + ConditionallySelectable + Zero + One {}

impl<T: LimbType, const N: usize> ValueType for MLUInt<T, N> {}

#[derive(Copy, Clone, Debug, PartialEq)]
struct ModUInt<T: ValueType, V: Modulus<T>> {
    value: T,
    modulus: PhantomData<V>,
}

/// Adds a (little-endian) multi-limb number to another multi-limb number,
/// returning the result and the resulting carry as a constant-time `Choice`
/// (`0` if there was no carry and `1` if there was).
#[inline(always)]
fn adc_array_with_overflow<T: AddWithCarry>(x: &T, y: &T) -> (Choice, T) {
    let (carry, res) = T::add_with_carry(x, y);
    (Choice::from(carry.as_u8()), res)
}

/// Subtracts a (little-endian) multi-limb number from another multi-limb number,
/// returning the result and the resulting borrow as a constant-time `Choice`
/// (`0` if there was no borrow and `1` if there was).
#[inline(always)]
fn sbb_array_with_underflow<T: SubWithBorrow>(x: &T, y: &T) -> (Choice, T) {
    let (borrow, res) = T::sub_with_borrow(x, y);
    (
        Choice::from((T::BorrowType::zero().wrapping_sub(borrow)).as_u8()),
        res,
    )
}

impl<T: ValueType, V: Modulus<T>> Add for ModUInt<T, V> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let (overflow, res1) = adc_array_with_overflow(&self.value, &other.value);
        let (underflow, res2) = sbb_array_with_underflow(&res1, &V::MODULUS);
        Self {
            value: T::conditional_select(&res1, &res2, overflow | !underflow),
            modulus: PhantomData,
        }
    }
}

impl<T: ValueType, V: Modulus<T>> Zero for ModUInt<T, V> {
    fn zero() -> Self {
        Self {
            value: T::zero(),
            modulus: PhantomData,
        }
    }

    fn is_zero(&self) -> bool {
        self.value.is_zero()
    }
}

impl<T: ValueType, V: Modulus<T>> Mul for ModUInt<T, V> {
    type Output = Self;

    #[allow(dead_code)]
    fn mul(self, _other: Self) -> Self {
        Self::zero() // FIXME: temporary stub
    }
}

impl<T: ValueType, V: Modulus<T>> One for ModUInt<T, V> {
    fn one() -> Self {
        Self {
            value: T::one(),
            modulus: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {

    use num_traits::{One, Zero};

    use super::{ModUInt, Modulus};
    use crate::mluint::MLUInt;

    #[derive(Copy, Clone, Debug, PartialEq)]
    struct MyType;

    impl Modulus<MLUInt<u64, 4>> for MyType {
        const MODULUS: MLUInt<u64, 4> = MLUInt::<u64, 4>::new([251, 0, 0, 0]);
    }

    #[test]
    fn zero() {
        let x = ModUInt::<MLUInt<u64, 4>, MyType>::zero();
        assert!(x.is_zero());
    }

    #[test]
    fn one() {
        let x = ModUInt::<MLUInt<u64, 4>, MyType>::zero();
        let y = ModUInt::<MLUInt<u64, 4>, MyType>::one();
        assert!(x + y == y);
    }
}
