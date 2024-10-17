use super::{HashNode, Hasher};

/// A single hash in a hash tree.
///
/// It can be either `Hash::Left(_)` or `Hash::Right(_)` depending on its position in the hash tree it comes from.
#[derive(Debug)]
enum Hash<'p, H: Hasher> {
    Left(&'p H::Hash),
    Right(&'p H::Hash),
}

impl<H: Hasher> Hash<'_, H> {
    /// Compute the resulting hash associated to this hash value and the given one depending on its position in the hash tree.
    fn hash(&self, other: &H::Hash) -> H::Hash {
        match self {
            Self::Left(hash) => H::hash(hash, other),
            Self::Right(hash) => H::hash(other, hash),
        }
    }
}

// Don't use `#[derive(PartialEq)]` here as it would require `Hasher` to implement `PartialEq` as well.
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
///
/// It is built with all sibling hashes required to compute the root hash for a given leaf hash value.
#[derive(Debug)]
pub struct HashProof<'p, H: Hasher> {
    root: Option<&'p H::Hash>,
    hashes: Vec<Hash<'p, H>>,
}

impl<'h, H: Hasher> HashProof<'h, H> {
    /// Build a hash proof from all sibling hashes required to compute the root hash for a given leaf hash value.
    pub(super) fn new(mut path: Vec<&'h HashNode<H>>) -> Self {
        let mut root = path.pop().map(HashNode::hash);
        let mut hashes = Vec::with_capacity(path.len());

        while let Some(node) = path.pop() {
            match node.nodes() {
                Some((left, right)) if Some(left.hash()) == root => hashes.push(Hash::Right(right.hash())),
                Some((left, right)) if Some(right.hash()) == root => hashes.push(Hash::Left(left.hash())),
                _ => unreachable!(),
            }

            root = Some(node.hash())
        }

        Self { root, hashes }
    }
}

impl<H: Hasher> HashProof<'_, H> {
    /// Compute the hash proof wrt. the given leaf hash value.
    pub fn compute(&self, leaf: H::Hash) -> H::Hash {
        self.hashes.iter().fold(leaf, |hash, h| h.hash(&hash))
    }

    /// Compute the hash proof wrt. the given leaf hash value, comparing it to the expected root hash value.
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
