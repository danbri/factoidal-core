# Signed WGSL scalar controls

The browser WebGPU demo's scalar picker now includes signed decimal floating
literals in the range −10000 to 10000. It recognizes unary minus (also when
whitespace separates the operator and literal), but leaves binary subtraction
outside the edited token. Comments, bracketed index expressions and array type
arguments remain excluded. This is a bounded source editor helper, not a WGSL
parser or semantic scalar analysis.

The three `shader-scalars.test.mjs` tests pass. They cover comments, nested
comments, array/index exclusions, suffix preservation, finite bounds, stale
positions, negative exponents, unary minus and binary subtraction. JavaScript
syntax checks pass for the editor, scalar helper and GPU smoke script.

The GPU smoke script now changes a negative scalar in a manual shader and
requires the resulting frame pixels to change. That new GPU case has not run:
the local server cannot bind `127.0.0.1:8097` in this execution environment
(`listen EPERM`). A fresh Lean WASM build also stopped because the pinned runtime
cache is cold and GitHub DNS failed during the Lean source clone. Existing local
WASM artifacts are from 2026-10-30 and were not rebuilt. The earlier positive
scalar GPU smoke result remains historical evidence only; it does not validate
this negative-control change or the current Lean graphics source.
