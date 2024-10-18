# merkle\_challenge

## Wording of the challenge
> Imagine a client has a large set of potentially small files ``{F0, F1, …, Fn}`` and wants to upload them to a server and then delete its local copies. The client wants, however, to later download an arbitrary file from the server and be convinced that the file is correct and is not corrupted in any way (in transport, tampered with by the server, etc.).
> 
> You should implement the client, the server and a Merkle tree to support the above (we expect you to implement the Merkle tree rather than use a library, but you are free to use a library for the underlying hash functions).
> 
> The client must compute a single Merkle tree root hash and keep it on its disk after uploading the files to the server and deleting its local copies. The client can request the *i-th* file ``Fi`` and a Merkle proof ``Pi`` for it from the server. The client uses the proof and compares the resulting root hash with the one it persisted before deleting the files - if they match, file is correct.
> 
> You can use any programming language you want (we use Go and Rust internally). We would like to see a solution with networking that can be deployed across multiple machines, and as close to production-ready as you have time for. Please describe the short-coming your solution have in a report, and how you would improve on them given more time.

## Approach
Practicing async & concurrent Rust professionally every day, designing CLI tools and HTTP Restful APIs at work, the trickier and more exciting part for me was the Merkle tree implementation.

I decided on purpose to focus mainly on the design of a generic, robust and efficient crate dedicated to handling Merkle trees and generating Merkle proofs with minimal overhead.
I also wanted to be careful about documenting and testing, as I would with any standard project.
The remaining client/server components would just have been a matter of course after that...

The main assessment I made from the beginning that drives the design and the implementation of the `hashtree` crate is:
- left subtrees are frozen and never require to be updated;
- only right subtrees need to be updated internally, until a node is fully filled and balanced;
- once a node is fully filled and balanced, it is frozen as the left subtree of a new super-node, with a fresh right subtree to be grown.

Here is the representation of a hash tree:

                 Root: Branch(ABCDE, (ABCD, E))       _
                         /                   \        |
                        /                     \       |
              Branch(ABCD, (AB, CD))        Leaf(E)   v min. depth
                /                 \                   |
               /                   \                  |
      Branch(AB, (A, B))   Branch(CD, (C, D))         |
           /       \           /       \              |
        Leaf(A) Leaf(B)     Leaf(C) Leaf(D)           v max. depth
    
        |---------------- length ----------------->

## Workspace & projects
This workspace is made up of the following projects:
* `hashtree`: a `lib` crate dedicated to handling Merkle trees and generating Merkle proofs with minimal overhead.
* `mock`: a `bin` crate dedicated to mock client/server managing a set of back-up files, as a proof-of-concept of the `hashtree` crate.
* [TODO] `client`: a `bin` crate dedicated to the actual client dealing with uploading/deleting/dowloading a set of back-up files.
* [TODO] `server`: a `bin` crate dedicated to the actual server dealing with receiving/storing/sending a set of back-up files.

## Features
The `hashtree` crate aims to provide an efficient shared library with a minimal set of features to handle Merkle trees and generate Merkle proofs.

It is generic over any hash functions through the provided `Hasher` trait and its `Hasher::Hash` associated type.

It includes an optional feature-flagged `compat` module for compatibility with common crates providing cryptographic hash functions. For now, only crates relying on `digest` crate and its `digest::Digest` trait are supported. This can be easily extended by implementing the provided `Hasher` trait.

## Dependencies
The crates in this workspace may rely on other renowned, widely tried and tested crates developed by the ever-growing Rust community, amongst others:

* [``digest``](https://crates.io/crates/digest) crate for compatibility with common crates providing cryptographic hash functions.
* [``tokio``](https://crates.io/crates/tokio) crate for event-driven, async I/O capabilities.
* [``futures``](https://crates.io/crates/futures) crate for futures/streams/sinks adaptations.
* [TODO] [``reqwest``](https://crates.io/crates/reqwest) crate for asynchronous HTTP(S)-based client capabilities.
* [TODO] [``rocket``](https://crates.io/crates/rocket) crate for asynchronous HTTP(S)-based server capabilities.
* [TODO] [``clap``](https://crates.io/crates/clap) crate for CLI management and command-line arguments parsing.
* [TODO] [``serde``](https://crates.io/crates/serde) crate for (de)serialization of data structures.

## Short-comings
- Making the most of the prior knowledge of a Merkle tree is great to keep things simple and performant but it relies on some assumptions that can easily spin out of control, hence the significant test set.
- No networking part.

## Improvements
- Make the most of the prior knowledge of a Merkle tree partitioning:
  - ~~Limit recursive calls when computing the depth and the length of a tree, eg. using const generic parameters to statically store the depth of a node~~.
  - Specialize node iterators, potentially implementing additional `ExactSizeIterator` and `DoubleEndedIterator` traits.
- Make `HashProof` compliant with ownership unconstrained to `HashTree`'s lifetime (turning it into owned values when required), eg. using `Cow`.
- ~~Try to reduce `Option` and `Option::unwrap()` usage in `HashNode` handling~~.
- Implement `serde` (de)serialization traits for `HashTree`, `HashNode` and `HashProof` types.
- Make a whole hash tree fully compliant and optimized for concurrent access, locking only the part of the subtree actually requiring to be updated, eg. using `RwLock`.

## Further ideas:
- The actual `Hasher` implementor used in a concret instantiation of a `HashTree` could be stored at its root level to avoid requiring `Default` constraint trait and allocating a `Hasher` instance each time we need to compute a hash value.
- Sibling leaves could be linked together to traverse leaves more efficiently, avoiding the whole tree to be left-hand traversed.

## Post-mortem
- A first draft of the `hashtree` crate based on a `HashTree` struct and its underlying `HashNode` enum, generic over any hash functions through the `Hasher` trait and its `Hasher::Hash` associated type, came quite naturally.
- Although a first idea would have to handle a binary tree with additional upstream linking between nodes in order to ease browsing within the tree, especially when computing the path from a leaf back to the root, eg. making use of `Rc` / `Weak` smart pointers or its atomic variants, I finally managed to keep lightweight `HashNode` variants with only downstream linking.
- I spent some time on fine-tuning the `HashNode` upgrade process (to finally keep it stupid simple 🤩) as well as its root-to-leaf path computation (touchy but classy ✌️).
- I also took time to write exhaustive tests, perhaps too much time, but I am fully confident in the solution.
- And the last day I focused on refining the `hashtree` documentation and demonstrating the expected behaviour of the client/server in a single `mock` app.
- So, for lack of time due to work/life/challenge balance and being engrossed in polishing the `hashtree` features, I regretfully have to miss the whole networking part... 🙏

Here is the output of the `mock` app:

    Uploading files for backup...
    File successfully uploaded (checksum: 85e384f69b325d96dd6738a0f7fe5f3d)
    File successfully uploaded (checksum: d88ccd0e2c1371f644ad3c5b4cb80179)
    File successfully uploaded (checksum: dfb9867de34ad1703712615aa7161291)
    Storing local information... (root hash: 51027a6ae89595786aee4a86b53b9e17)
    Oh noes, file #2 got corrupted on server side!!!
    Restoring file #0... Ok("hello Zama team")
    Restoring file #1... Ok("this is Yoann again")
    Restoring file #2... Err("File is corrupted!")
    Restoring file #3... Err("File not found...")
