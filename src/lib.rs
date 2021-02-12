#[cfg(test)]
#[macro_use]
extern crate quickcheck;

pub use self::base62::{decode, encode};
mod base62;
