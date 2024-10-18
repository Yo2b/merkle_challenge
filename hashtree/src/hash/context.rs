use std::cmp::Ordering;

use super::{HashNode, Hasher};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Depth(u8, Option<u8>);

impl Depth {
    #[inline]
    fn new(min: u8, max: u8) -> Self {
        debug_assert!(min <= max);
        Self(max, (min < max).then_some(min))
    }

    #[inline]
    fn merge(left: Self, right: Self) -> Self {
        Self::new(
            u8::min(left.1.unwrap_or(left.0), right.1.unwrap_or(right.0)),
            u8::max(left.0, right.0),
        )
    }

    #[inline]
    fn bump(self) -> Self {
        Self(self.0 + 1, self.1.map(|min| min + 1))
    }

    #[inline]
    pub fn min(&self) -> Option<u8> {
        self.1
    }

    #[inline]
    pub fn max(&self) -> u8 {
        self.0
    }
}

impl PartialEq<(u8, Option<u8>)> for Depth {
    #[inline]
    fn eq(&self, other: &(u8, Option<u8>)) -> bool {
        (self.0, self.1).eq(other)
    }
}

impl PartialOrd for Depth {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.cmp(&other.0).then_with(|| match (self.1, other.1) {
            (Some(ref l), Some(ref r)) => l.cmp(r),
            (None, Some(_)) => Ordering::Greater,
            (Some(_), None) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }))
    }
}

impl From<u8> for Depth {
    #[inline]
    fn from(depth: u8) -> Self {
        Self(depth, None)
    }
}

impl From<Depth> for (u8, Option<u8>) {
    #[inline]
    fn from(depth: Depth) -> Self {
        (depth.0, depth.1)
    }
}

#[derive(Debug)]
pub(super) struct Context(usize, Depth);

impl Context {
    #[inline]
    pub fn depth(&self) -> Depth {
        self.1
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0
    }
}

impl<H: Hasher> From<(&HashNode<H>, &HashNode<H>)> for Context {
    fn from((left, right): (&HashNode<H>, &HashNode<H>)) -> Self {
        let depth = Depth::merge(left.depth(), right.depth());

        Self(left.len() + right.len(), depth.bump())
    }
}
