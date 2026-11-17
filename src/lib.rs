//! Research implementation of the V6.1 repair, with explicit typed boundaries.
//! Test success is not a security proof or a claim of production hardening.
pub type Error = String;
pub type Result<T> = std::result::Result<T, Error>;

pub mod codec;
pub mod experiment;
pub mod gates;
pub mod general_mask;
pub mod index;
pub mod lookup;
pub mod multi;
pub mod native;
pub mod parallel;
pub mod pcs;
pub mod profile;
pub mod protocol;
#[cfg(test)]
mod protocol_zero_tests;
pub mod random;
pub mod resources;
pub mod tables;
pub mod trace;
pub mod trace_native;
pub mod trace_pcs;
pub mod trace_protocol;
pub mod transcript;
pub mod workload;
