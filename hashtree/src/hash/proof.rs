use std::fmt::Debug;

use super::{HashNode, Hasher};

/// A single hash in a hash tree.
#[derive(Debug)]
enum Hash<'p, H: Hasher> {
    Left(&'p H::Hash),
    Right(&'p H::Hash),
}

impl<H: Hasher> Hash<'_, H> {
    fn hash(&self, other: &H::Hash) -> H::Hash {
        match self {
            Self::Left(hash) => H::hash(hash, other),
            Self::Right(hash) => H::hash(other, hash),
        }
    }
}

impl<H: Hasher> PartialEq for Hash<'_, H> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Left(hash), Self::Left(other)) => hash.eq(other),
            (Self::Right(hash), Self::Right(other)) => hash.eq(other),
            _ => false,
        }
    }
}

/// A hash proof.
#[derive(Debug)]
pub struct HashProof<'p, H: Hasher> {
    root: Option<&'p H::Hash>,
    hashes: Vec<Hash<'p, H>>,
}

impl<'h, H: Hasher> HashProof<'h, H> {
    pub(super) fn new(mut path: Vec<&'h HashNode<H>>) -> Self {
        let mut root = path.pop().and_then(HashNode::hash);
        let mut hashes = Vec::with_capacity(path.len());

        while let Some(node) = path.pop() {
            match node.nodes() {
                Some((left, right)) if left.hash() == root => hashes.push(Hash::Right(right.hash().unwrap())),
                Some((left, right)) if right.hash() == root => hashes.push(Hash::Left(left.hash().unwrap())),
                _ => unreachable!(),
            }

            root = node.hash()
        }

        Self { root, hashes }
    }
}

impl<H: Hasher> HashProof<'_, H> {
    pub fn compute(&self, leaf: H::Hash) -> H::Hash {
        self.hashes.iter().fold(leaf, |hash, h| h.hash(&hash))
    }

    pub fn verify(&self, leaf: H::Hash) -> bool {
        self.root.is_some_and(|root| *root == self.compute(leaf))
    }
}

#[cfg(test)]
mod tests {
    use super::{
        super::{tests::SimpleHasher, HashTree},
        *,
    };

    #[test]
    fn compute_proof() {
        for (leaves, leaf, hashes, root) in [
            ('a'..='a', 'a', vec![], "a"),
            ('a'..='b', 'a', vec![Hash::Right(&String::from("b"))], "ab"),
            (
                'a'..='c',
                'b',
                vec![Hash::Left(&String::from("a")), Hash::Right(&String::from("c"))],
                "abc",
            ),
            (
                'a'..='z',
                'n',
                vec![
                    Hash::Left(&String::from("m")),
                    Hash::Right(&String::from("op")),
                    Hash::Left(&String::from("ijkl")),
                    Hash::Left(&String::from("abcdefgh")),
                    Hash::Right(&String::from("qrstuvwxyz")),
                ],
                "abcdefghijklmnopqrstuvwxyz",
            ),
        ] {
            let tree = HashTree::<SimpleHasher>::from_iter(leaves);

            let leaf = String::from(leaf);
            let index = tree.leaf_index(&leaf).unwrap();

            let proof = tree.proof(index);

            assert_eq!(proof.hashes, hashes);
            assert_eq!(proof.root.unwrap(), root);
        }
    }

    #[test]
    fn verify_proof() {
        for (leaves, index, leaf, verified) in [
            ('a'..='a', 0, 'a', true),
            ('a'..='b', 1, 'c', false),
            ('a'..='c', 1, 'b', true),
            ('a'..='e', 10, 'd', false),
            ('a'..='z', 12, 'n', false),
            ('a'..='z', 13, 'n', true),
        ] {
            let tree = HashTree::<SimpleHasher>::from_iter(leaves);

            let proof = tree.proof(index);

            assert_eq!(proof.verify(leaf.to_string()), verified);
        }
    }
}
