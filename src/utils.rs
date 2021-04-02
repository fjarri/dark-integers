pub trait CarryOperations: Sized {
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self);
}

impl CarryOperations for u64 {
    fn adc(a: Self, b: Self, carry: Self) -> (Self, Self) {
        let ret = (a as u128) + (b as u128) + (carry as u128);
        (ret as Self, (ret >> 64) as Self)
    }
}

pub trait BigEndian {
    const SIZE: usize;
    fn to_bytes(&self) -> [u8; Self::SIZE];
    fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self;
}

impl BigEndian for u64 {
    const SIZE: usize = 8;

    fn to_bytes(&self) -> [u8; Self::SIZE] {
        self.to_be_bytes()
    }

    fn from_bytes(bytes: &[u8; Self::SIZE]) -> Self {
        Self::from_be_bytes(*bytes)
    }
}
