use std::fmt::Debug;

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
            Self::Leaf(None) => 0,
            Self::Leaf(Some(_)) => 1,
            Self::Branch(_, nodes) => 1 + nodes.1.min_depth(), // min. depth is always right-handed
        }
    }

    fn max_depth(&self) -> usize {
        match self {
            Self::Leaf(None) => 0,
            Self::Leaf(Some(_)) => 1,
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

    fn traverse<F: FnMut(&Self)>(&self, f: &mut F) {
        f(self);
        if let Some((left, right)) = self.nodes() {
            left.traverse(f);
            right.traverse(f);
        }
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

    fn hash(&self) -> &[u8] {
        self.root.hash().map(AsRef::as_ref).unwrap_or_default()
    }

    fn traverse<F: FnMut(&HashNode<H>)>(&self, mut f: F) {
        self.root.traverse(&mut f);
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

        assert_eq!(tree.hash(), b"");
        assert_eq!(tree.root.len(), 0);
        assert_eq!(tree.root.depth(), (0, None));

        for (hash, len, depth, root_hash) in [
            ("a", 1, (1, None), "a"),
            ("b", 2, (2, None), "ab"),
            ("a", 3, (3, Some(2)), "aba"),
            ("c", 4, (3, None), "abac"),
            ("def", 5, (4, Some(2)), "abacdef"),
        ] {
            tree.push(hash);

            assert_eq!(tree.hash(), root_hash.as_bytes());
            assert_eq!(tree.root.len(), len);
            assert_eq!(tree.root.depth(), depth);
        }
    }

    #[test]
    fn insert_multi_hashes() {
        const ROOT_HASH: &str = "abcdef";
        let tree = HashTree::<SimpleHasher>::from_iter(ROOT_HASH.chars());

        // println!("{tree:#?}");

        // tree.traverse(|node| println!("{node:?}"));

        assert_eq!(tree.hash(), ROOT_HASH.as_bytes());
        assert_eq!(tree.root.len(), ROOT_HASH.len());
        assert_eq!(tree.root.depth(), (4, Some(3)));
    }

    #[test]
    fn expand_nodes() {
        let mut tree = HashTree::<SimpleHasher>::default();

        for hash in 'a'..='z' {
            tree.push(hash);

            assert_eq!(tree.hash().last().copied(), Some(hash as u8));
            assert_eq!(tree.root.len(), 1 + hash as usize - 'a' as usize);

            let mut empty_nodes = 0;
            let mut leaf_nodes = 0;
            let mut branch_nodes = 0;

            tree.traverse(|node| match node {
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
        }
    }
}
