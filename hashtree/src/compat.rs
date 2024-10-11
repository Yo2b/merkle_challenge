pub use digest::{Digest, Output};

impl<D: Digest + Default> crate::Hasher for D {
    type Hash = Output<D>;

    fn write(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }

    fn finish(self) -> Self::Hash {
        self.finalize()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use hex_literal::hex;

    fn assert_root_hash<D: Digest + Default, const N: usize>(data: &[&str], hashes: &[[u8; N]])
    where
        Output<D>: std::fmt::LowerHex,
    {
        assert_eq!(data.len(), hashes.len());

        let mut tree = crate::HashTree::<D>::default();

        for (block, hash) in data.iter().zip(hashes) {
            let root_hash = tree.push(D::digest(block)).hash().unwrap();
            assert_eq!(
                root_hash[..],
                *hash,
                "Hash doesn't match when adding block: '{block}' -> {root_hash:x}"
            );
        }
    }

    const DATA: &[&str] = &[
        "hello world",
        "my name is Yoann",
        "I'm applying for a position at Zama",
        "I hope you enjoy my proposal for solving the challenge 😅",
        "and I really hope I can touch the stars 🤞",
    ];

    #[test]
    fn md5() {
        assert_root_hash::<md5::Md5, 16>(
            DATA,
            &[
                hex!("5eb63bbbe01eeed093cb22bb8f5acdc3"),
                hex!("1429868119701c8c70582d23e454ce71"),
                hex!("90fb9d001fba8350791f98b3a8b735cb"),
                hex!("c0e4812762842021d3f94165492f2000"),
                hex!("2faa8e1707df562a8581ebcb27e5e843"),
            ],
        );
    }

    #[test]
    fn sha1() {
        assert_root_hash::<sha1::Sha1, 20>(
            DATA,
            &[
                hex!("2aae6c35c94fcfb415dbe95f408b9ce91ee846ed"),
                hex!("c15a8812635053b976d6396379ebcef585ba69aa"),
                hex!("6fe21bb02d27baf07c22eb6e7bdf5b8c6f4e1684"),
                hex!("31c05ff040a5cc500f1fccafbf1f1620b291331f"),
                hex!("f91f8bf8aaaf9ad9518fe25df62d47be465e2d09"),
            ],
        );
    }

    #[test]
    fn sha2() {
        assert_root_hash::<sha2::Sha256, 32>(
            DATA,
            &[
                hex!("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"),
                hex!("ca80bb29f3508b82ef163e9babe3f23f7346fddab2c44178efa7ddb5245accdd"),
                hex!("429b4bd6acf20ca61f80050614f12d6d99188be8614c0452abbcde3e0fc387c6"),
                hex!("82581fcc61ef8724be31ff799cf7a179983d428d18a319308b2ec84cd1181d0d"),
                hex!("86b26c3aced43ff3cd47e1359468fb31da9d40442a20372f17ef57e3ea78d191"),
            ],
        );
    }
}
