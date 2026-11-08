# wasi-testsuite subset (Preview 1)

Source: https://github.com/WebAssembly/wasi-testsuite, branch `prod/testsuite-base`
at commit `9d84631e427729802085c3d172d0a63cd360a1fa` (prebuilt test binaries).
Licence: Apache-2.0 (`LICENSE`, copied from the same commit).

Copied (unchanged), the tests of the functions that the WasmVM WASI host grants:

- `assemblyscript/`: all 12 tests of `tests/assemblyscript/testsuite/wasm32-wasip1/`
  with their `.json` specifications and `manifest.json` (`args_get`,
  `args_sizes_get`, `environ_get`, `environ_sizes_get`, `fd_write`, `proc_exit`,
  `random_get`).
- `c/`: the 4 clock tests of `tests/c/testsuite/wasm32-wasip1/`
  (`clock_getres-*`, `clock_gettime-*`).

Not copied: the Rust tests (about 2 MB each) and every test that needs files,
directories, sockets or `poll_oneoff`, which the host does not grant.

Run by `lake exe wasmvm-spectest` (after the spec tests) and by
`lake exe wasmvm-bench wasi`, from `formal/lean4`
(`L4Factoidal/WasmVM/Tests/Wasi.lean`), as the suite's `doc/specification.md` says:
the arguments and environment of the `.json` file (the first argument is the file
name), `_start` run, exit code and output compared.
