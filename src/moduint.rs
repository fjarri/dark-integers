use core::ops::{Add, Mul};
use num_traits::{One, Zero};

trait Modulus: Copy + Clone + PartialEq {
    type Value: Zero + One + Add + Copy + Clone + PartialEq;
    const MODULUS: Self::Value;
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct ModUInt<V: Modulus>(V::Value);

impl<V> Add for ModUInt<V>
where
    V: Modulus,
{
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}

impl<V> Zero for ModUInt<V>
where
    V: Modulus,
{
    fn zero() -> Self {
        Self(V::Value::zero())
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl<V> Mul for ModUInt<V>
where
    V: Modulus,
{
    type Output = Self;

    #[allow(dead_code)]
    fn mul(self, _other: Self) -> Self {
        Self::zero() // FIXME: temporary stub
    }
}

impl<V> One for ModUInt<V>
where
    V: Modulus,
{
    fn one() -> Self {
        Self(V::Value::one())
    }
}

#[cfg(test)]
mod tests {

    use num_traits::{One, Zero};

    use super::{ModUInt, Modulus};
    use crate::mluint::MLUInt;

    #[derive(Copy, Clone, Debug, PartialEq)]
    struct MyType;

    impl Modulus for MyType {
        type Value = MLUInt<u64, 4>;
        const MODULUS: Self::Value = Self::Value::new([251, 0, 0, 0]);
    }

    #[test]
    fn zero() {
        let x = ModUInt::<MyType>::zero();
        assert!(x.is_zero());
    }

    #[test]
    fn one() {
        let x = ModUInt::<MyType>::zero();
        let y = ModUInt::<MyType>::one();
        assert!(x + y == y);
    }
}
