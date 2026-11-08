# `Wasm-f3268fa9.lean`: the Lean 4 spec generated from our pinned WebAssembly spec

GENERATED. Do not edit. Issue: https://github.com/danbri/factoidal/issues/1244 (Lean
WebAssembly engine).

| | |
|---|---|
| Generator | SpecTec from https://github.com/Wasm-DSL/spectec branch `lean4-wip`, commit `16b70bde873d7ded498f9b81fd13ddcee95281fa`, with the five patches in `tools/wasmvm/spectec-patches/` |
| Input | `third_party/wasm-spec/specification/wasm-3.0/[012345]*.spectec` (WebAssembly/spec `f3268fa9dcb7d3a60d09546e743e7281e75cddb0`) |
| Output | `Wasm-f3268fa9.lean`, 12,854 lines, SHA-256 `944724783582ce90c2d90a8a7259d727fea7266509089aa7412e7bd69e1ea6c5` |
| Made | 2026-11-08 (patch 0005; first made 2026-11-07), OCaml 5.2.1, dune, menhir 20260209, mdx 2.7.0, zarith 1.14 |
| Consumer | `tools/wasmvm/port-spec.py` ports it to `formal/lean4/L4Factoidal/WasmVM/Spec/Wasm30.lean` |
| Licence | Derived from the SpecTec sources (W3C Software and Document Notice and License, `third_party/wasm-spec/specification/LICENSE-W3C-from-document-core.txt`); generator Apache-2.0 (see `../README.md`) |

The older file `../spectec/test-lean4/Wasm.lean` is the branch's own output for its
February 2026 copy of the spec. It is kept for reference; nothing ports it now.

## Command

```sh
export OPAMROOT=~/working/opam-spectec          # any opam root
opam switch create spectec ocaml-base-compiler.5.2.1
eval $(opam env --switch=spectec --set-switch)
opam install dune menhir mdx zarith
git clone --depth 1 --branch lean4-wip https://github.com/Wasm-DSL/spectec.git spectec-lean4wip
cd spectec-lean4wip                             # HEAD must be 16b70bde
git am <repo>/tools/wasmvm/spectec-patches/*.patch
cd spectec && make exe
cd <repo>                                       # paths in the output's comments are relative to here
<spectec-lean4wip>/spectec/spectec \
  third_party/wasm-spec/specification/wasm-3.0/[012345]*.spectec \
  -v -l --lean4 -o third_party/spectec-lean4/generated/Wasm-f3268fa9.lean
```

Run from the repository root: each declaration's comment holds the source path as given.

## What it holds

534 `inductive` (types and relations, including 119 `wf_` relations), 17 `structure`,
270 `def`, 57 `abbrev`, 118 `opaque`. Every SpecTec `int` is `Int` and every `rat` is
`Rat` (defect D1 fixed). The `wf_` relations of the mutual type groups are present
(gap G1 closed). The binary format (`5.x`) is still type aliases only: the backend
prints no grammar productions.
