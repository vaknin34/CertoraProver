# Example project

This is a Rust example project that uses the intrinsics functions exposed by the Certora Prover.
When the source code is modified, this needs to be re-compiled with `just build-sbf`.
The build script assumes that the project has been pre-compiled and that the executable is placed in the root directory.
This is to avoid re-compiling the code when running the tests.
