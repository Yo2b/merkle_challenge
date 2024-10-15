use hashtree::HashTree;

use hex_literal::hex;

#[test]
fn mock() {
    use md5::{Digest, Md5};

    let tree = HashTree::<Md5>::from_iter(crate::DATA.map(Md5::digest));

    assert_eq!(tree.hash().unwrap()[..], hex!("51027a6ae89595786aee4a86b53b9e17"));

    println!("{:x}", tree.hash().unwrap());
}
