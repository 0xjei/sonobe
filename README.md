# Sonobe

A folding/accumulation schemes library implemented jointly by [0xPARC](https://0xparc.org/) and [PSE](https://pse.dev).

<img align="right" style="width:30%;min-width:250px;margin-bottom:20px;" src="https://raw.githubusercontent.com/privacy-scaling-explorations/sonobe-docs/refs/heads/main/src/imgs/sonobe.png">

_"The [Sonobe module](https://en.wikipedia.org/wiki/Sonobe) is one of the many units used to build modular origami. The popularity of Sonobe modular origami models derives from the simplicity of folding the modules, the sturdy and easy assembly, and the flexibility of the system."_

## About

TL;DR:
- What: Sonobe implements folding/accumulation schemes and higher level primitives such as folding-based IVC, allowing users to prove repetitive computations efficiently.
- Why: There are many folding libraries, but Sonobe's goal is to be _modular_, _secure_, _performant_, and _easy to use_. Choose Sonobe if you think they matter to your use case.

<details>

<summary>What is Sonobe?</summary>

Sonobe focuses on a special type of (zero-knowledge) proof systems that are tailored for repetitive computations, e.g., a for loop.

Let's first consider a naive way to prove such repetitive computations, where we express all of them as a monolithic circuit. This approach has an obvious drawback: the number of iterations determines the circuit size and consequently the consumption of RAM, which is hard to scale (and expensive :D).

Incremental Verifiable Computation (IVC) is proposed to efficiently handle this task. Instead of proving in a single step with a circuit that encodes all iterations, IVC proves in many steps with a _step circuit_ that only encodes a single iteration. In each step, we update a running proof using the evidence that the current invocation of the step circuit is honestly done. Now, the prover's RAM usage no longer depends on the number of iterations.

One extension of IVC is Proof-Carrying Data (PCD). The former only supports a linear execution model, while the latter also allows repetitive computations that form a tree/graph.

Nevertheless, the RAM reduction of IVC and PCD is not free, because the update of a proof requires additional work. For example, a classic realization of IVC is via bruteforce SNARK recursion, where the update requires proving that the previous SNARK proof is correct. This means we need to (1) _prove with a SNARK_ the circuit execution, where the circuit (2) additionally encodes the _SNARK verification algorithm_ for the previous step, both of which are expensive and thus suboptimal.

Folding/accumulation schemes aim to minimize the cost of proof updates. They can "fold" multiple instances of a computation into a single instance, and the validity of the folded instance implies the validity of all input instances. With folding schemes, we (1') _fold_ the circuit execution into the running one, where the circuit instead (2') encodes the _folding verification algorithm_ for the previous step. Now, the overheads are much smaller, as folding's proof generation and verification algorithms are very cheap compared to a fully fledged SNARK.

What Sonobe provides are exactly these folding/accumulation schemes, as well as higher level primitives built on top of folding.

</details>

<details>

<summary>Why Sonobe?</summary>

Our philosophy is to make the library _modular_, _secure_, _performant_, and _easy to use_. Since 2025, efforts have been made to improve these properties.

- **Modularity**: As our main priority, Sonobe features _universal traits_ of folding schemes, commitment schemes, deciders (a.k.a. proof compression SNARKs), and frontends/DSLs. This modularity allows us to (1) provide _multiple instantiations_ of these schemes, and (2) build _compilers_ that can convert folding schemes into higher level primitives (e.g., IVC and PCD).
- **Security**: We believe folding will be a crucial component of many applications, and we want to make Sonobe a secure foundation of them. The code shipped in this branch has gone through three rounds of review, one by human auditors and two by AI auditors, and their findings have been addressed. We intend to keep this bar as the library grows.
- **Performance**: Everyone likes fast and cheap code. The rewrite behind Sonobe brings many optimizations in both running time and memory usage, and we will continue improving Sonobe's performance in the future by porting techniques such as GPU acceleration and lookup arguments.
- **User experience**: We aim for simple and intuitive APIs. Our traits follow the definitions of the cryptographic schemes themselves, so there is no second, code-specific vocabulary to learn on top of the papers. Together with modularity, this lets you pick the schemes that best fit your needs and switch between them with ease.

</details>

## Support Matrix

| Folding Schemes | Folding-to-IVC Compilers | Deciders | Commitment Schemes | Frontends |
|---|---|---|---|---|
| Nova[^nova] (stable) | CycleFold[^cyclefold] (stable) | LegoGroth16[^legosnark] [(to be merged)](https://github.com/privacy-scaling-explorations/sonobe/pull/259) | Pedersen[^pedersen] (stable) | [arkworks](https://github.com/arkworks-rs/snark/tree/master/relations) (stable) |
| HyperNova[^hypernova] [(to be merged)](https://github.com/privacy-scaling-explorations/sonobe/pull/246) | Field-only (planned) |   | KZG[^kzg] (to be revamped) | [Circom](https://github.com/iden3/circom) (to be revamped) |
| ProtoGalaxy[^protogalaxy] [(to be merged)](https://github.com/privacy-scaling-explorations/sonobe/pull/247) |   |   | Ajtai[^ajtai] [(WIP)](https://github.com/privacy-scaling-explorations/sonobe/pull/265) | [Noir](https://github.com/noir-lang/noir) [(WIP)](https://github.com/privacy-scaling-explorations/sonobe/tree/revamp/noir-frontend) |
| Ova[^ova] [(to be merged)](https://github.com/privacy-scaling-explorations/sonobe/pull/244) |   |   |   | [Noname](https://github.com/zksecurity/noname) (to be revamped) |
| Mova[^mova] [(to be merged)](https://github.com/privacy-scaling-explorations/sonobe/pull/245) |   |   |   |   |
| SuperNeo[^superneo] [(WIP)](https://github.com/privacy-scaling-explorations/sonobe/pull/265) |   |   |   |   |


## Quickstart

> **Warning**: Pre-release code, use with caution.
>
> `0.1.0-alpha.1` is an early preview. The public API _will_ change without notice between alpha releases. Docs are still to be polished, and examples cover only the core flows.

Declare the library as a dependency in your `Cargo.toml`:
```toml
[dependencies]
sonobe = "0.1.0-alpha.1"
```

Then you can start building your application with folding schemes or IVC.

Usually you only need to use IVC without caring about the low level details of folding schemes. In this case, you can refer to [`crates/ivc/examples/hash_chain.rs`](crates/ivc/examples/hash_chain.rs) for an end-to-end example, which proves a chain of Poseidon hashes with IVC.

If you really need raw access to folding schemes, you can have a look at [`crates/fs/examples/aggregate_solutions.rs`](crates/fs/examples/aggregate_solutions.rs), which folds independent claims about solutions to an equation into a single accumulator. However, be careful if you are going to construct your own high level cryptographic protocol via folding. We can only ensure the scheme itself works securely, while nothing prevents you from using a secure building block in an insecure way.

`sonobe` re-exports the packages below, which can also be depended on individually:
- `sonobe-primitives`: algebra, arithmetizations, commitment schemes and transcripts, together with their in-circuit gadgets.
- `sonobe-fs`: folding scheme traits implementations.
- `sonobe-ivc`: IVC traits and folding-to-IVC compilers.

Available features:
- `parallel` enables some parallelization optimizations available in the crates. It is not enabled by default.

Supported targets (other targets may work but are not tested):
- x86_64-unknown-linux-gnu
- wasm32-unknown-unknown
- wasm32-wasip2

MSRV: Rust 1.85.1 or newer (edition 2024).

## Documentation

API documentation is published on docs.rs:

- [`sonobe`](https://docs.rs/sonobe)
- [`sonobe-primitives`](https://docs.rs/sonobe-primitives)
- [`sonobe-fs`](https://docs.rs/sonobe-fs)
- [`sonobe-ivc`](https://docs.rs/sonobe-ivc)

A handbook covering the design of the library and how to use it is a work in progress.

## License

Sonobe is [MIT Licensed](https://github.com/privacy-scaling-explorations/sonobe/blob/main/LICENSE).

## Acknowledgments

This project builds on top of multiple [arkworks](https://github.com/arkworks-rs) libraries.

In addition to the direct code contributors who make this repository possible, this project has been improved and refined by many conversations with [Srinath Setty](https://github.com/srinathsetty), [Lev Soukhanov](https://github.com/levs57), [Matej Penciak](https://github.com/mpenciak), [Adrian Hamelink](https://github.com/adr1anh), [François Garillot](https://github.com/huitseeker), [Daniel Marin](https://github.com/danielmarinq), [Han Jian](https://github.com/han0110), [Wyatt Benno](https://github.com/wyattbenno777), [Niсolas Gailly](https://github.com/nikkolasg) and [Nalin Bhardwaj](https://github.com/nalinbhardwaj), to whom we are grateful.

## Citations

[^nova]: "[Nova: Recursive Zero-Knowledge Arguments from Folding Schemes](https://eprint.iacr.org/2021/370)", Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, _CRYPTO_, 2022.
[^hypernova]: "[HyperNova: Recursive arguments for customizable constraint systems](https://eprint.iacr.org/2023/573)", Abhiram Kothapalli, Srinath Setty, _CRYPTO_, 2024.
[^protogalaxy]: "[ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances](https://eprint.iacr.org/2023/1106)", Liam Eagen, Ariel Gabizon, _IACR ePrint_, 2023.
[^ova]: "[Ova: A slightly better Nova](https://hackmd.io/V4838nnlRKal9ZiTHiGYzw)", Benedikt Bünz, _HackMD note_, 2024.
[^mova]: "[Mova: Nova folding without committing to error terms](https://eprint.iacr.org/2024/1220)", Nikolaos Dimitriou, Albert Garreta, Ignacio Manzur, Ilia Vlasov, _IACR ePrint_, 2024.
[^superneo]: "[Neo and SuperNeo: Post-quantum folding with pay-per-bit costs over small fields](https://eprint.iacr.org/2026/242)", Wilson Nguyen, Srinath Setty, _CRYPTO_, 2026.
[^cyclefold]: "[CycleFold: Folding-scheme-based recursive arguments over a cycle of elliptic curves](https://eprint.iacr.org/2023/1192)", Abhiram Kothapalli, Srinath Setty, _IACR ePrint_, 2023.
[^legosnark]: "[LegoSNARK: Modular Design and Composition of Succinct Zero-Knowledge Proofs](https://eprint.iacr.org/2019/142)", Matteo Campanelli, Dario Fiore, Anaïs Querol, _ACM CCS_, 2019.
[^pedersen]: "[Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing](https://doi.org/10.1007/3-540-46766-1_9)", Torben Pryds Pedersen, _CRYPTO_, 1991.
[^kzg]: "[Constant-Size Commitments to Polynomials and Their Applications](https://doi.org/10.1007/978-3-642-17373-8_11)", Aniket Kate, Gregory M. Zaverucha, Ian Goldberg, _ASIACRYPT_, 2010.
[^ajtai]: "[Generating hard instances of lattice problems](https://doi.org/10.1145/237814.237838)", Miklós Ajtai, _STOC_, 1996.
