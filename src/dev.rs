//! Test helper functions.

use num_bigint::{BigUint, ToBigUint};
use num_traits::cast::ToPrimitive;

/// Converts a byte array (big-endian) to BigUint.
pub fn bytes_to_biguint<const N: usize>(bytes: &[u8; N]) -> BigUint {
    bytes
        .iter()
        .enumerate()
        .map(|(i, w)| w.to_biguint().unwrap() << ((N - 1 - i) * 8))
        .sum()
}

/// Converts a BigUint to a byte array (big-endian).
pub fn biguint_to_bytes<const N: usize>(x: &BigUint) -> [u8; N] {
    let mask = BigUint::from(u8::MAX);
    let mut bytes = [0u8; N];
    for i in 0..N {
        bytes[i] = ((x >> ((N - 1 - i) * 8)) as BigUint & &mask)
            .to_u8()
            .unwrap();
    }
    bytes
}
