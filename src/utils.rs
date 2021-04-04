pub trait CarryOperations: Sized {
    fn ct_less(a: Self, b: Self) -> Self;
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self);
    fn muladd(a: Self, b: Self, c0: Self, c1: Self, c2: Self) -> (Self, Self, Self);
    fn muladd_fast(a: Self, b: Self, c0: Self, c1: Self) -> (Self, Self);
}

impl CarryOperations for u64 {
    /// Constant-time comparison.
    #[inline(always)]
    fn ct_less(a: Self, b: Self) -> Self {
        // Do not convert to Choice since it is only used internally,
        // and we don't want loss of performance.
        (a < b) as Self
    }

    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u128) + (b as u128) + (carry as u128);
        (ret as Self, (ret >> 64) as Self)
    }

    /// Add a*b to the number defined by (c0,c1,c2). c2 must never overflow.
    fn muladd(a: Self, b: Self, c0: Self, c1: Self, c2: Self) -> (Self, Self, Self) {
        let t = (a as u128) * (b as u128);
        let th = (t >> 64) as Self; // at most 0xFFFFFFFFFFFFFFFE
        let tl = t as Self;

        let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
        let new_th = th + if new_c0 < tl { 1 } else { 0 }; // at most 0xFFFFFFFFFFFFFFFF
        let new_c1 = c1.wrapping_add(new_th); // overflow is handled on the next line
        let new_c2 = c2 + Self::ct_less(new_c1, new_th); // never overflows by contract (verified in the next line)
        debug_assert!((new_c1 >= new_th) || (new_c2 != 0));
        (new_c0, new_c1, new_c2)
    }

    /// Add a*b to the number defined by (c0,c1). c1 must never overflow.
    fn muladd_fast(a: Self, b: Self, c0: Self, c1: Self) -> (Self, Self) {
        let t = (a as u128) * (b as u128);
        let th = (t >> 64) as Self; // at most 0xFFFFFFFFFFFFFFFE
        let tl = t as Self;

        let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
        let new_th = th + Self::ct_less(new_c0, tl); // at most 0xFFFFFFFFFFFFFFFF
        let new_c1 = c1 + new_th; // never overflows by contract (verified in the next line)
        debug_assert!(new_c1 >= new_th);
        (new_c0, new_c1)
    }
}

impl CarryOperations for u32 {
    /// Constant-time comparison.
    #[inline(always)]
    fn ct_less(a: Self, b: Self) -> Self {
        // Do not convert to Choice since it is only used internally,
        // and we don't want loss of performance.
        (a < b) as Self
    }

    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u64) + (b as u64) + (carry as u64);
        (ret as Self, (ret >> 32) as Self)
    }

    /// Add a*b to the number defined by (c0,c1,c2). c2 must never overflow.
    fn muladd(a: Self, b: Self, c0: Self, c1: Self, c2: Self) -> (Self, Self, Self) {
        let t = (a as u64) * (b as u64);
        let th = (t >> 32) as Self; // at most 0xFFFFFFFFFFFFFFFE
        let tl = t as Self;

        let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
        let new_th = th + if new_c0 < tl { 1 } else { 0 }; // at most 0xFFFFFFFFFFFFFFFF
        let new_c1 = c1.wrapping_add(new_th); // overflow is handled on the next line
        let new_c2 = c2 + Self::ct_less(new_c1, new_th); // never overflows by contract (verified in the next line)
        debug_assert!((new_c1 >= new_th) || (new_c2 != 0));
        (new_c0, new_c1, new_c2)
    }

    /// Add a*b to the number defined by (c0,c1). c1 must never overflow.
    fn muladd_fast(a: Self, b: Self, c0: Self, c1: Self) -> (Self, Self) {
        let t = (a as u64) * (b as u64);
        let th = (t >> 32) as Self; // at most 0xFFFFFFFFFFFFFFFE
        let tl = t as Self;

        let new_c0 = c0.wrapping_add(tl); // overflow is handled on the next line
        let new_th = th + Self::ct_less(new_c0, tl); // at most 0xFFFFFFFFFFFFFFFF
        let new_c1 = c1 + new_th; // never overflows by contract (verified in the next line)
        debug_assert!(new_c1 >= new_th);
        (new_c0, new_c1)
    }
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
