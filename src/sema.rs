//! Semantic analysis passes for LibSL.

mod purity;

pub use purity::check_pure;
