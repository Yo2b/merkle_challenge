use std::fmt::Debug;

mod proof;
pub use proof::HashProof;

/// An enum to deal with errors.
#[derive(Debug)]
enum Error {
    NoHash,
    LeftNodeNotFull,
    RightNodeNotCompliant,
}

/// A hasher trait to produce hash values.
pub trait Hasher: Default {
    /// Type associated to this `Hasher` implemention.
    type Hash: AsRef<[u8]> + PartialEq + Debug;

    /// Feed the hasher with a new value to be hashed.
    fn write(&mut self, bytes: &[u8]);

    /// Finalize the hasher and return the final hash value.
    fn finish(self) -> Self::Hash;

    /// Helper method to compute the resulting hash value with exactly two input values.
    fn hash(first: impl AsRef<[u8]>, second: impl AsRef<[u8]>) -> Self::Hash
    where
        Self: Sized,
    {
        let mut hasher = Self::default();
        hasher.write(first.as_ref());
        hasher.write(second.as_ref());
        hasher.finish()
    }
}

/// A hash node in the hash tree.
///
/// A node can be either a leaf or a branch.
/// With current implementation, a leaf is made empty in only two transitional states when:
/// - the root node of a hash tree is empty,
/// - an underlying node of the hash tree is upgrading its subtree.
///
/// This latest state only occurs when mutably accessing the root node to push a new leaf.
///
/// A branch is made of two underlying nodes for left / right subtrees, and a hash precomputed from left / right hashes.
/// This means both a non-empty leaf and a branch always have a hash, and a branch always has underlying nodes.
///
/// A hash node is made to grow in a way that left subtrees of its recursive right nodes are always fully balanced.
/// Its implementation tries to make the most of this assertion.
#[derive(Debug)]
enum HashNode<H: Hasher> {
    Branch(H::Hash, Box<(HashNode<H>, HashNode<H>)>),
    Leaf(Option<H::Hash>),
}

impl<H: Hasher> Default for HashNode<H> {
    fn default() -> Self {
        Self::Leaf(None)
    }
}

impl<H: Hasher> TryFrom<(Self, Self)> for HashNode<H> {
    type Error = Error;

    fn try_from((left, right): (Self, Self)) -> Result<Self, Self::Error> {
        if !left.is_full() {
            return Err(Error::LeftNodeNotFull);
        }

        if left.max_depth() < right.max_depth() || !right.is_balanced() {
            return Err(Error::RightNodeNotCompliant);
        }

        Self::branch(left, right).ok_or(Error::NoHash)
    }
}

impl<H: Hasher> HashNode<H> {
    /// Create a new branch node from left/right subtrees.
    ///
    /// Be aware that no check is operated against left/right subtrees. Use [`HashNode::try_from()`] form instead if you need to ensure that:
    /// - the left subtree is full
    /// - the left subtree is deeper than the right one
    /// - the right subtree is correctly balanced
    fn branch(left: Self, right: Self) -> Option<Self> {
        Some(Self::Branch(H::hash(left.hash()?, right.hash()?), Box::new((left, right))))
    }

    /// Create a new leaf node.
    fn leaf(hash: impl Into<H::Hash>) -> Self {
        Self::Leaf(Some(hash.into()))
    }

    /// Check if a node is a leaf.
    fn is_leaf(&self) -> bool {
        matches!(self, Self::Leaf(Some(_)))
    }

    /// Check if a node is empty.
    ///
    /// Only happens when the tree is empty.
    fn is_empty(&self) -> bool {
        matches!(self, Self::Leaf(None))
    }

    /// Check that a node is a leaf with the given hash.
    fn match_leaf(&self, hash: &H::Hash) -> bool {
        matches!(self, Self::Leaf(Some(h)) if h == hash)
    }

    /// Check that a node is a branch with the given hash.
    #[allow(dead_code)]
    fn match_branch(&self, hash: &H::Hash) -> bool {
        matches!(self, Self::Branch(h, _) if h == hash)
    }

    /// Check if a node's subtree is correctly balanced.
    ///
    /// A subtree is balanced when its left branches are full and all deeper than right ones.
    fn is_balanced(&self) -> bool {
        self.visit_right().flat_map(Self::nodes).all(|(left, right)| {
            let left_max_depth = left.max_depth();
            left.min_depth() == left_max_depth && left_max_depth >= right.max_depth()
        })
    }

    /// Check if a node's subtree is full.
    ///
    /// A subtree is full when all its branches have the same exact depth.
    fn is_full(&self) -> bool {
        !self.is_empty() && self.min_depth() == self.max_depth()
    }

    /// Return the min. depth of this node's subtree, computed recursively.
    ///
    /// Note: min. depth is always right-handed.
    fn min_depth(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch(_, nodes) => 1 + nodes.1.min_depth(),
        }
    }

    /// Return the max. depth of this node's subtree, computed recursively.
    ///
    /// Note: max. depth is always left-handed.
    fn max_depth(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch(_, nodes) => 1 + nodes.0.max_depth(),
        }
    }

    /// Convenient method to aggregate min. / max. depth.
    ///
    /// If this node's subtree is not empty, `self.1.is_none()` means the subtree is full.
    #[allow(dead_code)]
    fn depth(&self) -> (usize, Option<usize>) {
        let min_depth = self.min_depth();
        let max_depth = self.max_depth();

        (max_depth, (min_depth != max_depth).then_some(min_depth))
    }

    /// Return the length of this node's subtree, computed recursively.
    ///
    /// Note: length is the number of non-empty leaves.
    fn len(&self) -> usize {
        match self {
            Self::Leaf(None) => 0,
            Self::Leaf(Some(_)) => 1,
            Self::Branch(_, nodes) => nodes.0.len() + nodes.1.len(),
        }
    }

    /// Get a reference to the hash part of this node.
    ///
    /// Note: it is safe to `.unwrap()` the returned `Option` as long as this node is not empty.
    fn hash(&self) -> Option<&H::Hash> {
        match self {
            Self::Leaf(opt) => opt.as_ref(),
            Self::Branch(hash, _) => Some(hash),
        }
    }

    /// Get references to the children parts of this node.
    ///
    /// Note: it is safe to `.unwrap()` the returned `Option` as long as this node is a branch.
    fn nodes(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((&nodes.0, &nodes.1)),
        }
    }

    /// Get mutable references to the children parts of this node.
    ///
    /// Note: it is safe to `.unwrap()` the returned `Option` as long as this node is a branch.
    #[allow(dead_code)]
    fn nodes_mut(&mut self) -> Option<(&mut Self, &mut Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((&mut nodes.0, &mut nodes.1)),
        }
    }

    /// Turn this node into its children parts.
    ///
    /// Note: it is safe to `.unwrap()` the returned `Option` as long as this node is a branch.
    fn into_nodes(self) -> Option<(Self, Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((nodes.0, nodes.1)),
        }
    }

    /// Upgrade this node and combine it with a new hash part.
    ///
    /// This method ensures the subtree grows as expected, ugrading:
    /// - an empty node to a leaf one,
    /// - then a leaf node to a branch one,
    /// - and finally completing the left subtree recursively before pushing right.
    fn upgrade(self, other: H::Hash) -> Self {
        // all `.unwrap()` calls below are safe cause we do have hash and nodes in each case and we handle tree growth cycle
        match self {
            Self::Leaf(None) => Self::leaf(other),
            leaf @ Self::Leaf(Some(_)) => Self::branch(leaf, Self::leaf(other)).unwrap(),
            branch @ Self::Branch(..) => {
                if branch.is_full() {
                    Self::branch(branch, Self::leaf(other)).unwrap()
                } else {
                    let (left, right) = branch.into_nodes().unwrap();
                    Self::branch(left, right.upgrade(other)).unwrap()
                }
            }
        }
    }

    /// A convenient method to upgrade this node in-place.
    fn push(&mut self, hash: impl Into<H::Hash>) {
        *self = std::mem::take(self).upgrade(hash.into());
    }

    /// A convenient iterator to visit only left child nodes.
    #[allow(dead_code)]
    fn visit_left(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |&node| node.nodes().map(|(left, _)| left))
    }

    /// A convenient iterator to visit only right child nodes.
    fn visit_right(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |&node| node.nodes().map(|(_, right)| right))
    }

    /// Iterate over subtree nodes.
    ///
    /// It browses all the subtree in a left-handed way.
    fn visit_nodes(&self) -> impl Iterator<Item = &Self> {
        let mut rights = Vec::with_capacity(self.max_depth());

        std::iter::successors(Some(self), move |&node| {
            if let Some((left, right)) = node.nodes() {
                rights.push(right);
                Some(left)
            } else {
                rights.pop()
            }
        })
    }

    /// Convenient method to iterate over leaves only (oldest to newest).
    fn leaves(&self) -> impl Iterator<Item = &Self> {
        self.visit_nodes().filter(|&node| node.is_leaf())
    }

    /// Compute the path traversing all required nodes to reach a leaf, starting from this root node.
    ///
    /// Returns `None` if `i` is out of range, rather than panicking.
    ///
    /// Note: only required nodes are lazily iterated very efficiently, at the minimal cost of the initial
    /// deterministic computation of the theoretical path (one recursion for each right-incomplete subtree).
    fn leaf_path(&self, i: usize) -> Option<impl Iterator<Item = &Self>> {
        let len = self.len();

        // This helper function recursively computes a theoritical path in right-incomplete subtrees.
        // 0 means go left, 1 means go right.
        fn bits(i: usize, len: usize) -> usize {
            let last_complete_index = 2usize.pow(len.ilog2());
            if i > last_complete_index {
                // incomplete subtree: we have to go right once, then compute the path in the right-handed subtree
                bits(i - last_complete_index, len - last_complete_index) << 1 | 0b1
            } else {
                // complete subtree: path is straightfully computed from the leaf index in the subtree
                i.reverse_bits().wrapping_shr(usize::BITS - len.next_power_of_two().ilog2())
            }
        }

        (i < len).then(|| {
            let mut bits = bits(i, len);

            std::iter::successors(Some(self), move |&node| {
                node.nodes().and_then(|(left, right)| {
                    let even = bits & 0b1 == 0;
                    bits >>= 1;
                    even.then_some(left).or(Some(right))
                })
            })
        })
    }
}

/// A hash tree.
///
/// According to its underlying nodes' properties with left-handed children always fully balanced, a hash tree looks like:
/// ```text
///             Root: Branch(ABCDE, (ABCD, E))       _
///                     /                   \        |
///                    /                     \       |
///          Branch(ABCD, (AB, CD))        Leaf(E)   v min. depth
///            /                 \                   |
///           /                   \                  |
///  Branch(AB, (A, B))   Branch(CD, (C, D))         |
///       /       \           /       \              |
///    Leaf(A) Leaf(B)     Leaf(C) Leaf(D)           v max. depth
///
///    |---------------- length ----------------->
/// ```
///
/// The only way to alter a hash tree requires a mutable handle on it, allowing to push new leaves with its hash value.
#[derive(Debug, Default)]
pub struct HashTree<H: Hasher> {
    root: HashNode<H>,
}

impl<H: Hasher> HashTree<H> {
    /// Add a new leaf with given hash value in the hash tree.
    pub fn push(&mut self, hash: impl Into<H::Hash>) -> &mut Self {
        self.root.push(hash);
        self
    }

    /// Return the precomputed root hash from this whole hash tree.
    pub fn hash(&self) -> Option<&H::Hash> {
        self.root.hash()
    }

    /// Find a given hash within the leaves of this hash tree.
    ///
    /// Returns `Some(i)` if the hash exists, or `None` otherwise.
    pub fn leaf_index(&self, hash: &H::Hash) -> Option<usize> {
        self.root.leaves().position(|leaf| leaf.match_leaf(hash))
    }

    /// Convenient method to iterate over leaf hashes only (oldest to newest).
    pub fn leaves(&self) -> impl Iterator<Item = &H::Hash> {
        self.root.leaves().filter_map(HashNode::hash)
    }

    /// Compute the proof for the given leaf index.
    ///
    /// Returns an empty proof if `i` is out of range.
    pub fn proof(&self, i: usize) -> HashProof<H> {
        HashProof::new(self.root.leaf_path(i).into_iter().flatten().collect())
    }
}

impl<H: Hasher, T: Into<H::Hash>> Extend<T> for HashTree<H> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, hashes: I) {
        for hash in hashes {
            self.push(hash);
        }
    }
}

impl<H: Hasher, T: Into<H::Hash>> FromIterator<T> for HashTree<H> {
    fn from_iter<I: IntoIterator<Item = T>>(hashes: I) -> Self {
        let mut tree = HashTree::default();
        tree.extend(hashes);
        tree
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use assert_matches::assert_matches;

    #[derive(Debug, Default)]
    pub struct SimpleHasher(Vec<u8>);
    impl Hasher for SimpleHasher {
        type Hash = String;

        fn write(&mut self, bytes: &[u8]) {
            self.0.extend_from_slice(bytes)
        }

        fn finish(self) -> Self::Hash {
            String::from_utf8(self.0).unwrap()
        }
    }

    #[test]
    fn branch_nodes() {
        let empty = HashNode::<SimpleHasher>::default;
        let leaf = || HashNode::<SimpleHasher>::leaf("");
        let branch = || HashNode::branch(leaf(), leaf()).unwrap();
        let balanced = || HashNode::branch(branch(), leaf()).unwrap();
        let unbalanced = || HashNode::branch(leaf(), branch()).unwrap();
        let full = || HashNode::branch(branch(), branch()).unwrap();

        assert_matches!(HashNode::try_from((empty(), empty())), Err(Error::LeftNodeNotFull));
        assert_matches!(HashNode::try_from((leaf(), empty())), Err(Error::NoHash));
        assert_matches!(HashNode::try_from((leaf(), branch())), Err(Error::RightNodeNotCompliant));
        assert_matches!(HashNode::try_from((branch(), unbalanced())), Err(Error::RightNodeNotCompliant));
        assert_matches!(HashNode::try_from((branch(), balanced())), Err(Error::RightNodeNotCompliant));
        assert_matches!(HashNode::try_from((balanced(), leaf())), Err(Error::LeftNodeNotFull));

        assert!(HashNode::try_from((leaf(), leaf())).is_ok());
        assert!(HashNode::try_from((branch(), leaf())).is_ok());
        assert!(HashNode::try_from((branch(), branch())).is_ok());
        assert!(HashNode::try_from((full(), balanced())).is_ok());
        assert!(HashNode::try_from((full(), full())).is_ok());
    }

    #[test]
    fn upgrade_nodes() {
        let mut node = HashNode::<SimpleHasher>::default();
        assert_matches!(&node, HashNode::Leaf(None));
        node.push("");
        assert_matches!(&node, HashNode::Leaf(Some(_)));
        node.push("");
        assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Leaf(Some(_)), HashNode::Leaf(Some(_)))));
        for i in 2..1024usize {
            node.push("");
            if i == i.next_power_of_two() {
                assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Branch(..), HashNode::Leaf(Some(_)))));
            } else {
                assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Branch(..), HashNode::Branch(..))));
            }
        }
    }

    #[test]
    fn insert_single_hashes() {
        let mut tree = HashTree::<SimpleHasher>::default();

        assert_eq!(tree.hash(), None);
        assert_eq!(tree.root.len(), 0);
        assert_eq!(tree.root.depth(), (0, None));

        for (hash, len, depth, root_hash) in [
            ("a", 1, (0, None), "a"),
            ("b", 2, (1, None), "ab"),
            ("a", 3, (2, Some(1)), "aba"),
            ("c", 4, (2, None), "abac"),
            ("def", 5, (3, Some(1)), "abacdef"),
        ] {
            tree.push(hash);

            assert_eq!(tree.hash().unwrap(), root_hash);
            assert_eq!(tree.root.len(), len);
            assert_eq!(tree.root.depth(), depth);

            assert_eq!(tree.leaves().last().unwrap(), hash)
        }
    }

    #[test]
    fn insert_multi_hashes() {
        const ROOT_HASH: &str = "abcdef";
        let tree = HashTree::<SimpleHasher>::from_iter(ROOT_HASH.chars());

        assert_eq!(tree.hash().unwrap(), ROOT_HASH);
        assert_eq!(tree.root.len(), ROOT_HASH.len());
        assert_eq!(tree.root.depth(), (3, Some(2)));

        assert!(tree.leaves().zip(ROOT_HASH.chars()).all(|(hash, c)| hash.chars().eq(Some(c))));
    }

    #[test]
    fn visit_nodes() {
        for (hashes, node_hashes) in [
            (vec![], vec![]),
            (vec!['a'], vec!["a"]),
            (vec!['a', 'b'], vec!["ab", "a", "b"]),
            (vec!['a', 'b', 'c'], vec!["abc", "ab", "a", "b", "c"]),
        ] {
            let tree = HashTree::<SimpleHasher>::from_iter(hashes);

            // println!("{tree:#?}");
            // tree.root.visit_nodes().for_each(|node| println!("{node:?}"));

            assert!(tree.root.visit_nodes().flat_map(HashNode::hash).eq(node_hashes));
        }
    }

    #[test]
    fn expand_nodes() {
        let mut tree = HashTree::<SimpleHasher>::default();

        assert!(!tree.root.is_full()); // empty node is never full

        for hash in 'a'..='z' {
            tree.push(hash);

            assert_eq!(tree.hash().unwrap().chars().last(), Some(hash));
            assert_eq!(tree.root.len(), 1 + hash as usize - 'a' as usize);

            let mut leaf_nodes = 0;
            let mut branch_nodes = 0;

            tree.root.visit_nodes().for_each(|node| match node {
                HashNode::Leaf(None) => {
                    unreachable!("except for root node, `Leaf(None)` variant is only transitory");
                }
                leaf @ HashNode::Leaf(Some(_)) => {
                    leaf_nodes += 1;

                    assert!(leaf.is_full()); // leaf node is always full
                }
                HashNode::Branch(_, nodes) => {
                    branch_nodes += 1;

                    // left node is always full
                    assert!(nodes.0.is_full());
                    // right node is full when it contains 2^n hashes
                    assert_eq!(nodes.1.is_full(), nodes.1.len().is_power_of_two());
                }
            });

            assert_eq!(leaf_nodes, tree.root.len()); // the length of a tree is its number of leaves
            assert_eq!(branch_nodes, tree.root.len() - 1); // there is one branch less than leaves

            assert_eq!(tree.root.max_depth(), tree.root.len().next_power_of_two().ilog2() as usize);
        }
    }

    #[test]
    fn compute_leaf_path() {
        for leaves in (0..100).map(|end| 0..=end) {
            let tree = HashTree::<SimpleHasher>::from_iter(leaves.clone().map(|i| i.to_string()));

            for (i, leaf) in leaves.enumerate() {
                let leaf = leaf.to_string();
                let leaf_index = tree.leaf_index(&leaf).unwrap();

                assert_eq!(leaf_index, i);

                let leaf_path = tree.root.leaf_path(leaf_index).unwrap();

                assert_eq!(leaf_path.last().and_then(HashNode::hash), Some(&leaf));
            }
        }
    }
}
