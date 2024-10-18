use std::cmp::Ordering;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Depth(u8, Option<u8>);

impl Depth {
    #[inline]
    pub(super) fn new(min: u8, max: u8) -> Self {
        debug_assert!(min <= max);
        Self(max, (min < max).then_some(min))
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
