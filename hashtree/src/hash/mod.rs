use std::fmt::Debug;

/// An enum to deal with errors.
#[derive(Debug)]
enum Error {
    NoHash,
    LeftNodeNotFull,
    RightNodeNotCompliant,
}

/// A hasher trait to produce hash values.
trait Hasher: Default {
    type Hash: AsRef<[u8]> + Debug;

    fn write(&mut self, bytes: &[u8]);
    fn finish(self) -> Self::Hash;

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

        if left.max_depth() < right.max_depth() {
            return Err(Error::RightNodeNotCompliant);
        }

        let mut right_node = &right;
        while let Some((left_subtree, right_subtree)) = right_node.nodes() {
            if !left_subtree.is_full() {
                return Err(Error::RightNodeNotCompliant);
            }
            right_node = right_subtree;
        }

        Self::branch(left, right).ok_or(Error::NoHash)
    }
}

impl<H: Hasher> HashNode<H> {
    fn branch(left: Self, right: Self) -> Option<Self> {
        Some(Self::Branch(H::hash(left.hash()?, right.hash()?), Box::new((left, right))))
    }

    fn leaf(hash: impl Into<H::Hash>) -> Self {
        Self::Leaf(Some(hash.into()))
    }

    fn is_leaf(&self) -> bool {
        matches!(self, Self::Leaf(Some(_)))
    }

    fn is_empty(&self) -> bool {
        matches!(self, Self::Leaf(None))
    }

    fn match_leaf(&self, hash: &H::Hash) -> bool
    where
        H::Hash: PartialEq,
    {
        matches!(self, Self::Leaf(Some(h)) if h == hash)
    }

    #[allow(dead_code)]
    fn match_branch(&self, hash: &H::Hash) -> bool
    where
        H::Hash: PartialEq,
    {
        matches!(self, Self::Branch(h, _) if h == hash)
    }

    fn is_full(&self) -> bool {
        !self.is_empty() && self.min_depth() == self.max_depth()
    }

    fn min_depth(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch(_, nodes) => 1 + nodes.1.min_depth(), // min. depth is always right-handed
        }
    }

    fn max_depth(&self) -> usize {
        match self {
            Self::Leaf(_) => 0,
            Self::Branch(_, nodes) => 1 + nodes.0.max_depth(), // max. depth is always left-handed
        }
    }

    #[allow(dead_code)]
    fn depth(&self) -> (usize, Option<usize>) {
        let min_depth = self.min_depth();
        let max_depth = self.max_depth();

        (max_depth, (min_depth != max_depth).then_some(min_depth))
    }

    fn len(&self) -> usize {
        match self {
            Self::Leaf(None) => 0,
            Self::Leaf(Some(_)) => 1,
            Self::Branch(_, nodes) => nodes.0.len() + nodes.1.len(), // length is the number of non-empty leaves
        }
    }

    fn hash(&self) -> Option<&H::Hash> {
        match self {
            Self::Leaf(opt) => opt.as_ref(),
            Self::Branch(hash, _) => Some(hash),
        }
    }

    fn nodes(&self) -> Option<(&Self, &Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((&nodes.0, &nodes.1)),
        }
    }

    #[allow(dead_code)]
    fn nodes_mut(&mut self) -> Option<(&mut Self, &mut Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((&mut nodes.0, &mut nodes.1)),
        }
    }

    fn into_nodes(self) -> Option<(Self, Self)> {
        match self {
            Self::Leaf(_) => None,
            Self::Branch(_, nodes) => Some((nodes.0, nodes.1)),
        }
    }

    fn upgrade(self, other: H::Hash) -> Self {
        // all `.unwrap()` calls below are safe cause we do have hash and nodes in each case and we handle tree growth cycle
        match self {
            Self::Leaf(None) => Self::leaf(other),
            leaf @ Self::Leaf(Some(_)) => Self::branch(leaf, Self::leaf(other)).unwrap(),
            branch @ Self::Branch(_, _) => {
                if branch.is_full() {
                    Self::branch(branch, Self::leaf(other)).unwrap()
                } else {
                    let (left, right) = branch.into_nodes().unwrap();
                    Self::branch(left, right.upgrade(other)).unwrap()
                }
            }
        }
    }

    fn push(&mut self, hash: impl Into<H::Hash>) {
        *self = std::mem::take(self).upgrade(hash.into());
    }

    #[allow(dead_code)]
    fn visit_left(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |&node| node.nodes().map(|(left, _)| left))
    }

    #[allow(dead_code)]
    fn visit_right(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |&node| node.nodes().map(|(_, right)| right))
    }

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

    fn leaves(&self) -> impl Iterator<Item = &Self> {
        self.visit_nodes().filter(|&node| node.is_leaf())
    }
}

/// A hash tree.
#[derive(Debug, Default)]
struct HashTree<H: Hasher> {
    root: HashNode<H>,
}

impl<H: Hasher> HashTree<H> {
    fn push(&mut self, hash: impl Into<H::Hash>) -> &mut Self {
        self.root.push(hash);
        self
    }

    fn hash(&self) -> Option<&H::Hash> {
        self.root.hash()
    }

    fn leaves(&self) -> impl Iterator<Item = &H::Hash> {
        self.root.leaves().filter_map(HashNode::hash)
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
    struct SimpleHasher(Vec<u8>);
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
        fn empty() -> HashNode<SimpleHasher> {
            HashNode::default()
        }

        fn leaf() -> HashNode<SimpleHasher> {
            HashNode::leaf("")
        }

        fn branch() -> HashNode<SimpleHasher> {
            HashNode::branch(leaf(), leaf()).unwrap()
        }

        assert_matches!(HashNode::try_from((empty(), empty())), Err(Error::LeftNodeNotFull));
        assert_matches!(HashNode::try_from((leaf(), empty())), Err(Error::NoHash));
        assert_matches!(HashNode::try_from((leaf(), branch())), Err(Error::RightNodeNotCompliant));

        let unbalanced = HashNode::branch(leaf(), branch()).unwrap();
        assert_matches!(HashNode::try_from((leaf(), unbalanced)), Err(Error::RightNodeNotCompliant));

        let balanced = HashNode::branch(branch(), leaf()).unwrap();
        assert_matches!(HashNode::try_from((leaf(), balanced)), Err(Error::RightNodeNotCompliant));

        assert!(HashNode::try_from((leaf(), leaf())).is_ok(),);
        assert!(HashNode::try_from((branch(), branch())).is_ok(),);

        let left = HashNode::branch(branch(), branch()).unwrap();
        let right = HashNode::branch(branch(), leaf()).unwrap();
        assert!(HashNode::try_from((left, right)).is_ok(),);
    }

    #[test]
    fn upgrade_nodes() {
        let mut node = HashNode::<SimpleHasher>::default();
        assert_matches!(&node, HashNode::Leaf(None));
        node.push("");
        assert_matches!(&node, HashNode::Leaf(Some(_)));
        node.push("");
        assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Leaf(Some(_)), HashNode::Leaf(Some(_)))));
        node.push("");
        assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Branch(_, _), HashNode::Leaf(Some(_)))));
        node.push("");
        assert_matches!(&node, HashNode::Branch(_, n) if matches!(**n, (HashNode::Branch(_, _), HashNode::Branch(_, _))));
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

        for hash in 'a'..='z' {
            tree.push(hash);

            assert_eq!(tree.hash().unwrap().chars().last(), Some(hash));
            assert_eq!(tree.root.len(), 1 + hash as usize - 'a' as usize);

            let mut empty_nodes = 0;
            let mut leaf_nodes = 0;
            let mut branch_nodes = 0;

            tree.root.visit_nodes().for_each(|node| match node {
                empty @ HashNode::Leaf(None) => {
                    empty_nodes += 1;

                    assert!(!empty.is_full()); // empty node is never full
                }
                leaf @ HashNode::Leaf(_) => {
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

            assert_eq!(empty_nodes, 0); // except for root node, `Empty` variant is only transitory
            assert_eq!(leaf_nodes, tree.root.len()); // the length of a tree is its number of leaves
            assert_eq!(branch_nodes, tree.root.len() - 1); // there is one branch less than leaves

            assert_eq!(tree.root.max_depth(), tree.root.len().next_power_of_two().ilog2() as usize);
        }
    }
}
