mod hash;
pub use hash::{HashTree, Hasher};

#[cfg(feature = "digest_compat")]
pub mod compat;
