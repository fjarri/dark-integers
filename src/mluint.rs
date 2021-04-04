use core::ops::{Add, Mul};

use num_traits::sign::Unsigned;
use num_traits::{One, Zero};

use crate::utils::{muladd, muladd_fast, adc_array, BigEndian, PrimitiveUInt};

pub trait LimbType: Unsigned + Copy + BigEndian {}

impl LimbType for u64 {}
impl LimbType for u32 {}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct MLUInt<T: LimbType, const N: usize>([T; N]);

impl<T: LimbType, const N: usize> MLUInt<T, N> {
    pub const fn new(limbs: [T; N]) -> Self {
        Self(limbs)
    }

    // TODO: this is basically an implementation of BigEndian,
    // but the compiler is not smart enough (yet) to resolve the const generics
    // if we made it an actual implementation.

    pub fn from_be_bytes(bytes: [u8; N * T::SIZE]) -> Self {
        let mut res = [T::zero(); N];
        #[allow(clippy::needless_range_loop)]
        for i in 0..N {
            let idx = (N - 1 - i) * T::SIZE;
            let mut limb_bytes = [0u8; T::SIZE];
            limb_bytes.clone_from_slice(&bytes[idx..(T::SIZE + idx)]);
            res[i] = T::from_bytes(&limb_bytes);
        }
        Self(res)
    }

    pub fn to_be_bytes(self) -> [u8; N * T::SIZE] {
        let mut res = [0u8; N * T::SIZE];
        for i in 0..N {
            let idx = (N - 1 - i) * T::SIZE;
            res[idx..(T::SIZE + idx)].copy_from_slice(&self.0[i].to_bytes());
        }
        res
    }
}

impl<T: LimbType + PrimitiveUInt, const N: usize> Add for MLUInt<T, N> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let (res, _) = adc_array(&self.0, &other.0);
        Self(res)
    }
}

impl<T: LimbType + PrimitiveUInt, const N: usize> Zero for MLUInt<T, N> {
    fn zero() -> Self {
        Self([T::zero(); N])
    }

    fn is_zero(&self) -> bool {
        !self.0.iter().fold(false, |acc, x| acc | !x.is_zero())
    }
}

impl<T: LimbType + PrimitiveUInt, const N: usize> Mul for MLUInt<T, N> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let mut c0 = T::zero();
        let mut c1 = T::zero();
        let mut c2 = T::zero();

        let mut res = [T::zero(); N];

        (c0, c1) = muladd_fast(self.0[0], other.0[0], c0, c1);
        (res[0], c0, c1) = (c0, c1, T::zero());

        #[allow(clippy::needless_range_loop)]
        for i in 1..N {
            for j in 0..i + 1 {
                (c0, c1, c2) = muladd(self.0[j], other.0[i - j], c0, c1, c2);
            }
            (res[i], c0, c1, c2) = (c0, c1, c2, T::zero());
        }

        Self(res)
    }
}

impl<T: LimbType + PrimitiveUInt, const N: usize> One for MLUInt<T, N> {
    fn one() -> Self {
        let mut res = [T::zero(); N];
        res[0] = T::one();
        Self::new(res)
    }
}

#[cfg(test)]
mod tests {

    use super::{LimbType, MLUInt};
    use crate::dev::{biguint_to_bytes, bytes_to_biguint};
    use num_bigint::{BigUint, ToBigUint};
    use num_traits::{One, Zero};

    use proptest::prelude::*;

    impl<T: LimbType, const N: usize> From<&BigUint> for MLUInt<T, N>
    where
        [u8; N * T::SIZE]: Sized,
    {
        fn from(x: &BigUint) -> Self {
            let bytes = biguint_to_bytes(x);
            Self::from_be_bytes(bytes)
        }
    }

    impl<T: LimbType, const N: usize> From<BigUint> for MLUInt<T, N>
    where
        [u8; N * T::SIZE]: Sized,
    {
        fn from(x: BigUint) -> Self {
            Self::from(&x)
        }
    }

    impl<T: LimbType, const N: usize> ToBigUint for MLUInt<T, N>
    where
        [u8; N * T::SIZE]: Sized,
    {
        fn to_biguint(&self) -> Option<BigUint> {
            Some(bytes_to_biguint(&self.to_be_bytes()))
        }
    }

    #[test]
    fn zero() {
        let x = MLUInt::<u64, 4>::zero();
        assert!(x.is_zero());
    }

    #[test]
    fn add() {
        let x = MLUInt::<u64, 4>::zero();
        let y = MLUInt::<u64, 4>::one();
        let z = x + y;
        assert!(z == y)
    }

    #[test]
    fn roundtrip_to_bytes() {
        let bytes: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
        let x = MLUInt::<u64, 2>::from_be_bytes(bytes);
        let bytes_back = x.to_be_bytes();
        assert_eq!(bytes, bytes_back);
    }

    prop_compose! {
        fn mluint_4x64()(bytes in any::<[u8; 32]>()) -> MLUInt<u64, 4> {
            MLUInt::<u64, 4>::from_be_bytes(bytes)
        }
    }

    prop_compose! {
        fn mluint_8x32()(bytes in any::<[u8; 32]>()) -> MLUInt<u32, 8> {
            MLUInt::<u32, 8>::from_be_bytes(bytes)
        }
    }

    proptest! {
        #[test]
        fn fuzzy_roundtrip_to_bytes_u64(x in mluint_4x64()) {
            let x_back = MLUInt::<u64, 4>::from_be_bytes(x.to_be_bytes());
            assert_eq!(x, x_back);
        }

        #[test]
        fn fuzzy_add_u64(x in mluint_4x64(), y in mluint_4x64()) {
            let reference = MLUInt::<u64, 4>::from(x.to_biguint().unwrap() + y.to_biguint().unwrap());
            let test = x + y;
            assert_eq!(test, reference);
        }

        #[test]
        fn fuzzy_mul_u64(x in mluint_4x64(), y in mluint_4x64()) {
            let reference = MLUInt::<u64, 4>::from(x.to_biguint().unwrap() * y.to_biguint().unwrap());
            let test = x * y;
            assert_eq!(test, reference);
        }

        #[test]
        fn fuzzy_mul_u32(x in mluint_8x32(), y in mluint_8x32()) {
            let reference = MLUInt::<u32, 8>::from(x.to_biguint().unwrap() * y.to_biguint().unwrap());
            let test = x * y;
            assert_eq!(test, reference);
        }
    }
}
