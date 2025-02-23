# Sunbeam: Wasm front-end for Certora Prover

This is an internal document for how to run _Sunbeam_.
Sunbeam is the name of Certora's verifier for WASM programs.
It currently focuses on WASM generated from [Soroban](https://soroban.stellar.org/docs)'s rust contracts.

We expect the WASM programs to be generated from Rust code but right now the tool does not have the
  capability to compile Rust to generate the wasm, so you must provide the wasm file as input.

This document will show you how to generate the wasm files and what additional arguments you need to
  provide to Sunbeam.

_Note that Sunbeam is still WIP.
Please bear with us as we continue improving it._

## Installing Rust
- We recommend installing Rust like so:

`curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh`

- Next, you should also install the WASM target like so:

`rustup target add wasm32-unknown-unknown`

- We also recommend installing the [wabt](https://github.com/WebAssembly/wabt) toolkit. `wasm2wat` is a useful tool for converting the WASM bytecode to a human-readable format.

- Finally install `rustfilt` like so: `cargo install rustfilt`

## Input to Sunbeam
- The recommended way to run Sunbeam is to provide it a `Cargo.toml` file:
```
certoraRun path/to/Cargo.toml ——rule property_name1 property_name2 ...
```
where the package name at the top of the `Cargo.toml` is the WASM binary you want to verify.

This will invoke the rust compiler to compile and get the right binary file from `target/wasm32-unknonw-unknown/release` which will then
be verified against the provided rules. _Please make sure you are not passing a virtual manifest._

_NOTE_: you will need to add the following line to the `Cargo.toml` file you pass to Sunbeam for it to work:

```
[features]
cvt = []
```

- If you want to compile your project on your own, you can also pass a `.wasm` binary file to Sunbeam.
To run with a `.wasm` file, all you need to do is compile your rust project like so
```commandline
RUSTFLAGS="-C strip=none -C debuginfo=2" cargo build --target=wasm32-unknown-unknown --release --features cvt
```

and generate the `.wasm` file which should be in `target/wasm32-unknown-unknown/release` of your rust project directory.

You can then run Sunbeam like so:
```
certoraRun path/to/foo.wasm --rule property_name
```

- You can also run the tool by passing a `.wat` file. For this, you must first use the `wabt` toolkit to generate the file as described below.
  Note that we need to do a round trip as shown below in order for the input WAT file to have all the necessary mangled names and other debug information.

```commandline
wasm2wat foo.wasm --generate-names -o foo.wat
wat2wasm foo.wat --debug-names -o bar.wasm
wasm2wat bar.wasm -o goo.wat
```

You can then run Sunbeam like so:
```
certoraRun path/to/goo.wat  --rule property_name
```

The support for `.wat` files will eventually be deprecated. It does not provide much call trace information.

## Setting up Soroban

Since currently we focus on WASM generated from Soroban contracts,
  we recommend setting up the Soroban environment as shown [here](https://soroban.stellar.org/docs/getting-started/setup#install-the-soroban-cli).
This will be helpful for generating the WASM bytecode and
also for experimenting with Soroban programs in general.

If you already set up Rust as explained above, you can skip that part of the Soroban setup steps.

## Example for how to run Sunbeam for wasm:
- First, you must write a property that you want to verify. We have many simple examples in
[this repository](https://github.com/Certora/soroban-minimal-examples).
We recommend cloning the repo and trying them out.

- To run Sunbeam easily, we have provided a `justfile` for each example in the repo. Simply run `just build` or `just wat` if you want to run Sunbeam on a compiled binary or pass the path to the `Cargo.toml` and property name to Sunbeam as mentioned in the section "Input to Sunbeam" above.

