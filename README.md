
# A simple Aurora implementation

Protocol reference: appendix B of [[STIR]](https://eprint.iacr.org/2024/390): Reed–Solomon Proximity Testing with Fewer Queries. By Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, and Eylon Yogev.

This is a simplified, non-ZK version of the original SNARK in [Aurora](https://eprint.iacr.org/2018/828): Aurora Transparent Succinct Arguments for R1CS. By Eli Ben-Sasson, Alessandro Chiesa, Michael Riabzev, Nicholas Spooner, Madars Virza, and Nicholas P. Ward

 > *Disclaimer*: This codebase is for demonstration purposes only and not ready for production use - neither from a performance nor a security perspective. 

## Generating R1CS files

In order to generate an `.r1cs` file from a `.circom` one (with name, say, `NAME`), use
```
    circom NAME.circom --r1cs
```

In order to generate a `.wasm` file from a `.circom` one, use
```
    circom NAME.circom --wasm
```
and take the `.wasm` file from within the newly created folder.

## Usage notes

Depending on your Rust installation, the following runtime error may occur:

```
    unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap
```

This comes from a dependency. As a temporary fix, try running with rust 1.77.0: If not installed, run `rustup install 1.77.0` first. Then run `cargo +1.77.0 test`.
