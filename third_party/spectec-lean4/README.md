# SpecTec to Lean 4 backend, and the Lean spec it generates

Joachim Breitner's Lean 4 backend for SpecTec, and the Lean file it produces
from the WebAssembly 3.0 SpecTec sources. Vendored as a reference for the Lean
WebAssembly engine `WasmVM` (issue
[#1244](https://github.com/danbri/factoidal/issues/1244)). Nothing here is
built by our Lean build.

| | |
|---|---|
| Upstream | https://github.com/Wasm-DSL/spectec, branch `lean4-wip` |
| Commit | `16b70bde873d7ded498f9b81fd13ddcee95281fa` (Joachim Breitner, 2026-02-19, "Rebase the lean4 wip code onto rocq-backend") |
| Browse | https://github.com/Wasm-DSL/spectec/tree/16b70bde873d7ded498f9b81fd13ddcee95281fa/spectec |
| Fetched | 2026-11-07, `git fetch --depth 1` of that commit |
| Changes | None. Files are copied unmodified. |

## Files

| File | Bytes | What |
|---|---|---|
| `spectec/backend-lean4/print.ml` | 29,588 | The backend: prints SpecTec IL as Lean 4 (OCaml) |
| `spectec/backend-lean4/dune` | 68 | Its dune library stanza (`backend_lean4`, depends on `il`) |
| `spectec/test-lean4/Wasm.lean` | 786,095 | The generated Lean 4 spec. SHA-256 `8d61a9603a3c1f1aa3946dccbb49720fa520865cb35157f4bd646995742042be` |
| `spectec/test-lean4/dune` | 341 | The rule that generates `Wasm.lean` and diffs it in `dune runtest` |
| `spectec/test-lean4/lean-toolchain` | 29 | `leanprover/lean4:v4.25.0-rc1` |
| `LICENSE-Wasm-DSL-toplevel` | | Wasm-DSL/spectec top-level `LICENSE` at this commit |
| `LICENSE-WebAssembly-spec-toplevel` | | WebAssembly/spec top-level `LICENSE` at `f3268fa9dc` |
| `LICENSE-Apache-2.0` | | Apache License 2.0 text, from WebAssembly/spec `interpreter/LICENSE` (identical to Wasm-DSL's `interpreter/LICENSE`) |

## Licence

Apache-2.0, on the following record.

The Wasm-DSL/spectec top-level `LICENSE` does not list `spectec/`, and there
is no `spectec/LICENSE` in that repository. Its text, verbatim:

```
Please see the LICENSE file in each top-level directory for the terms applicable to that directory and its relative sub-directories.

The relevant directories and licenses are:

document/    - W3C Software and Document Notice and License
interpreter/ - Apache License 2.0
test/        - Apache License 2.0
papers/      - Creative Commons Attribution 4.0 International License
```

WebAssembly/spec, which took in the Wasm-DSL SpecTec work, lists `spectec/`
as Apache-2.0 in its top-level `LICENSE` (commit `f3268fa9dc`). It too has no
`spectec/LICENSE` file. Its text, verbatim:

```
Please see the LICENSE file in each top-level directory for the terms applicable to that directory and its relative sub-directories.

The relevant directories and licenses are:

document/       - W3C Software and Document Notice and License
specification/  - W3C Software and Document Notice and License
spectec/        - Apache License 2.0
interpreter/    - Apache License 2.0
test/           - Apache License 2.0
proposals/      - Creative Commons Universal 1.0 International License (CC0)
papers/         - Creative Commons Attribution 4.0 International License (CC BY 4.0)
```

So we treat `print.ml` and `dune` as Apache-2.0, the licence the same code
carries upstream. `Wasm.lean` is generated output: it is a mechanical
translation of the SpecTec sources in `specification/wasm-3.0/`, which are
under the W3C Software and Document Notice and License (full text:
`third_party/wasm-spec/specification/LICENSE-W3C-from-document-core.txt`).
That notice applies to `Wasm.lean` as a derived work, and its condition is
that the notice travels with copies. If the backend is ever merged into
WebAssembly/spec, its upstream licence file settles the question.

## Which spec `Wasm.lean` comes from

`spectec/test-lean4/dune` generates it with:

```
spectec specification/wasm-3.0/[012345]*.spectec -v -l --lean4 -o Wasm.lean.act
```

and `dune runtest` diffs the result against the checked-in `Wasm.lean`. So
`Wasm.lean` is the backend's output for the `0.x` to `5.x` SpecTec files of
the **Wasm-DSL `lean4-wip` branch's own** `specification/wasm-3.0/` at commit
`16b70bde87`. It covers auxiliary definitions, abstract syntax, validation,
numerics, execution and the binary format. It does not cover the text format
(`6.x`), the soundness definitions (`7.x`) or the notation files (`X.x`). We
did not rerun the generator (no OCaml build here); this rests on the dune rule
and the test that diffs against it.

### How those sources differ from our pinned spec

Compared with `third_party/wasm-spec/specification/wasm-3.0/` (WebAssembly/spec
`f3268fa9dc`, 2026-11-06), the branch is about nine months older:

- 37 files on our side, 35 on the branch. In total, 753 changed lines.
- Of the 26 files that feed `Wasm.lean` (`0.x` to `5.x`), 23 differ and only
  `0.2-aux.num`, `0.3-aux.seq`, `1.0-syntax.profiles` and `5.2-binary.types`
  are identical.
- Also differing: `6.1`–`6.3` text files. The branch's `6.3-text.modules` is
  our `6.4-text.modules` (renumbered, 18 lines differ). `7.0` and `7.1`
  (soundness) exist only on our side.
- Largest changes: `4.3-execution.instructions` (166 lines),
  `4.0-execution.configurations` (132), `2.1-validation.types` (65),
  `2.3-validation.instructions` (48), `4.1-execution.values` (41).

The kinds of change:

1. **Reference values.** The separate `addrref` syntax is gone. `ref` now has
   a `REF.NULL_ADDR` case, and execution rules match `REF.NULL_ADDR` where they
   matched `REF.NULL ht`. `REF.EXTERN` wraps a `ref`.
2. **State accessors.** The per-field accessors on the state (`$funcinst(z)`,
   `$moduleinst(z)`, `$globalinst(z)`, ...) are replaced by `$s(z)` and
   `$f(z)`, and rules write `$s(z).FUNCS[a]`, `$f(z).MODULE.FUNCS[x]`.
3. **Host functions.** `hostfunc` is now `_HOSTFUNC text`, and new rules
   such as `Step/call_ref-hostfunc-res` describe calls to host functions.
   `call_ref` moved from `Step_read` to `Step`.
4. **Exception handling.** New `Step/ctxt-handler` context rule; new
   `$free_catch` and `$free_instr` cases for `THROW`, `THROW_REF`,
   `TRY_TABLE`.
5. **Type validation.** New `Heaptype_ok/bot` and `Localtype_ok`. `Expand`
   is now defined via `$unrolldt`, not `$expanddt`. `oktypeidxnat` becomes
   `oktypenat`, and `$before` and `$unrollht` change signature.
6. **Module instantiation.** `$evalglobals` is replaced by `$evalexprs` and
   `$evalexprss` over the `Eval_expr` relation.
7. **Numerics and binary.** `$ishl_` and `$ishr_` take an `iN(N)` shift count
   instead of `u32`. `$iextend_` parameters were renamed. `Bi32`/`Bi64`
   decode via `BiN` instead of `BuN`. The UTF-8 decoding bound was fixed
   (`0x80 <= b`), and `$utf8single` was split out.
8. **Renamings and layout.** `$lsize`/`$vsize` became `$lsizenn`/`$vsizenn`
   in syntax. `STRUCT.GET/SET` take `fieldidx` instead of `u32`. Some `hint`
   annotations and line breaks changed.

Kinds 1 to 6 change definitions that `Wasm.lean` contains, so `Wasm.lean`
does not match the pinned spec. To get a Lean file for `f3268fa9dc`, the
backend has to be rebased onto current WebAssembly/spec and rerun.
