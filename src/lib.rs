#![no_std]
#![allow(incomplete_features)]
#![feature(const_fn)]
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]
#![feature(destructuring_assignment)]

mod mluint;
mod moduint;
mod primitives;
mod traits;

#[cfg(test)]
mod dev;

pub use mluint::MLUInt;
