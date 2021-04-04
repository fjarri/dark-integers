use num_traits::Zero;

pub trait PrimitiveUInt: Sized + Copy + PartialEq + PartialOrd + Zero {
    fn from_bool_ct(b: bool) -> Self;
    fn mulhilo(x: Self, y: Self) -> (Self, Self);
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self);
    fn wrapping_add(self, other: Self) -> Self;
    fn wrapping_mul(self, other: Self) -> Self;
}

impl PrimitiveUInt for u64 {
    #[inline(always)]
    fn from_bool_ct(b: bool) -> Self {
        b as Self
    }
    #[inline(always)]
    fn mulhilo(x: Self, y: Self) -> (Self, Self) {
        let prod = (x as u128).wrapping_mul(y as u128);
        ((prod >> 64) as Self, prod as Self)
    }
    #[inline(always)]
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u128)
            .wrapping_add(b as u128)
            .wrapping_add(carry as u128);
        ((ret >> 64) as Self, ret as Self)
    }
    #[inline(always)]
    fn wrapping_add(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
    #[inline(always)]
    fn wrapping_mul(self, other: Self) -> Self {
        self.wrapping_mul(other)
    }
}

impl PrimitiveUInt for u32 {
    #[inline(always)]
    fn from_bool_ct(b: bool) -> Self {
        b as Self
    }
    #[inline(always)]
    fn mulhilo(x: Self, y: Self) -> (Self, Self) {
        let prod = (x as u64) * (y as u64);
        ((prod >> 32) as Self, prod as Self)
    }
    #[inline(always)]
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u64) + (b as u64) + (carry as u64);
        ((ret >> 32) as Self, ret as Self)
    }
    #[inline(always)]
    fn wrapping_add(self, other: Self) -> Self {
        self.wrapping_add(other)
    }
    #[inline(always)]
    fn wrapping_mul(self, other: Self) -> Self {
        self.wrapping_mul(other)
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

/// Adds a (little-endian) multi-limb number to another multi-limb number,
/// returning the result and the resulting carry as a sinle-limb value.
/// The carry can be either `0` or `1`.
pub(crate) fn adc_array<T: PrimitiveUInt, const N: usize>(
    lhs: &[T; N],
    rhs: &[T; N],
) -> ([T; N], T) {
    let mut res = [T::zero(); N];
    let mut carry = T::zero();
    for i in 0..N {
        let (c, r) = T::adc(lhs[i], rhs[i], carry);
        carry = c;
        res[i] = r;
    }
    (res, carry)
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
