//! A simple crate providing hash tree features (aka. Merkle tree and Merkle proof).
//!
//! Its implementation aims to be both memory efficient and performant, relying on intrinsic
//! properties of a hash tree and making the most of Rust safety.
//!
//! # Pros of the current implementation
//! - No need for smart pointers to link parents and children together, eg. using `Rc` / `Weak` pointers.
//! - The only way to alter a hash tree is to have a mutable access onto it.
//!
//! # Known limitations of the current implementation
//! - Not suitable for straight concurrent access nor optimize to lock only the hash node requiring to be upgraded.
//! - Some computation is made recursively and could be greatly optimized, eg. to get the depth and the length of a hash tree.

mod hash;
pub use hash::{HashProof, HashTree, Hasher};

#[cfg(feature = "digest_compat")]
pub mod compat;
