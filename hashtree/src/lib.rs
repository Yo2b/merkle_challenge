mod hash;
pub use hash::{HashProof, HashTree, Hasher};

#[cfg(feature = "digest_compat")]
pub mod compat;
