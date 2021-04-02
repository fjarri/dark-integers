#![no_std]
#![allow(incomplete_features)]
#![feature(const_fn)]
#![feature(const_generics)]
#![feature(const_evaluatable_checked)]

mod mluint;
mod moduint;
mod utils;

#[cfg(test)]
mod dev;

pub use mluint::MLUInt;
