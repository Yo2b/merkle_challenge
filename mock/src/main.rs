#![doc(hidden)]

//! A proof-of-concept for the basic use case, mocking the client/server parts.

use hashtree::{HashProof, HashTree};
use md5::{digest::Output, Digest, Md5};

#[cfg(test)]
mod tests;

const DATA: [&str; 3] = [
    "hello Zama team",
    "this is Yoann again",
    "here is some content I'd like to share with you",
];

type File = String;

#[derive(Default)]
struct Server {
    merkle_tree: HashTree<Md5>,
    uploaded_files: Vec<File>,
}

impl Server {
    async fn upload_file(&mut self, content: File, checksum: Output<Md5>) -> Result<(), &'static str> {
        if checksum == Md5::digest(&content) {
            self.uploaded_files.push(content);
            self.merkle_tree.push(checksum);

            println!("File successfully uploaded (checksum: {checksum:x})");

            Ok(())
        } else {
            Err("Upload failed, please retry...")
        }
    }

    async fn download_file(&self, index: usize) -> Result<(File, HashProof<Md5>), &'static str> {
        if index < self.uploaded_files.len() {
            let file = self.uploaded_files[index].clone();
            let proof = self.merkle_tree.proof(index);

            Ok((file, proof))
        } else {
            Err("File not found...")
        }
    }

    fn alter_file(&mut self, index: usize) {
        if index < self.uploaded_files.len() {
            let file = &mut self.uploaded_files[index];
            *file = file
                .chars()
                .map(|c| match c {
                    _ if c.is_ascii_lowercase() => c.to_ascii_uppercase(),
                    _ if c.is_ascii_uppercase() => c.to_ascii_lowercase(),
                    _ => c,
                })
                .collect();

            println!("Oh noes, file #{index} got corrupted on server side!!!");
        }
    }
}

#[derive(Default)]
struct Client {
    root_hash: Output<Md5>,
}

impl Client {
    async fn store_root_hash(&mut self, root_hash: Output<Md5>) {
        self.root_hash = root_hash;
    }

    async fn backup_files(&self, server: &mut Server, files: impl IntoIterator<Item = File>) -> Result<Output<Md5>, &'static str> {
        let mut merkle_tree = HashTree::<Md5>::default();

        for file in files {
            let checksum = Md5::digest(&file);
            server.upload_file(file.clone(), Md5::digest(&file)).await?;
            merkle_tree.push(checksum);
        }

        merkle_tree.hash().copied().ok_or("Something went wrong...")
    }

    async fn restore_file(&self, server: &Server, index: usize) -> Result<File, &'static str> {
        let (file, proof) = server.download_file(index).await?;

        self.check_file(&file, proof)?;

        Ok(file)
    }

    fn check_file(&self, file: &File, proof: HashProof<Md5>) -> Result<(), &'static str> {
        match proof.compute(Md5::digest(file)) == self.root_hash {
            true => Ok(()),
            false => Err("File is corrupted!"),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), &'static str> {
    const CORRUPTED_INDEX: usize = 2;

    let mut server = Server::default();
    let mut client = Client::default();

    println!("Uploading files for backup...");
    let root_hash = client.backup_files(&mut server, DATA.map(Into::into)).await?;

    println!("Storing local information... (root hash: {root_hash:x})");
    client.store_root_hash(root_hash).await;

    server.alter_file(CORRUPTED_INDEX);

    for index in 0..DATA.len() + 1 {
        print!("Restoring file #{index}...");
        let res = client.restore_file(&server, index).await;
        println!(" {res:?}");
    }

    Ok(())
}
