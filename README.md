
In order to generate an `.r1cs` file from a `.circom` one (with name, say, `NAME`), use
```
    circom NAME.circom --r1cs
```

In order to generate a `.wasm` file from a `.circom` one, use
```
    circom NAME.circom --wasm
```
and take the `.wasm` file from within the newly created folder.


# Usage notes

Depending on your Rust installation, the following runtime error can appear:

```
    unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap
```

This comes from a dependency. As a temporary fix, try running with rust 1.77.0. If not installed, run `rustup install 1.77.0` first. Then run `cargo +1.77.0 test`.
