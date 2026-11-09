# Lean upstream: 32-bit and WebAssembly items that affect Factoidal

Our toolchain is Lean 4.33.1 (`formal/lean4/lean-toolchain`). Our Wasm builds compile the C that Lean
generates on a 64-bit machine for 32-bit WebAssembly. Lean does not support WebAssembly as a target:
its last `linux_wasm32` archive was v4.15.0, and the proposal below to bring the CI job back says so.

This page lists the upstream work we depend on or watch. "Release" is the first of v4.34.1, v4.35.0
and v4.36.0-rc2 whose history contains the merge commit, checked on 2026-11-09. Nothing here is
a request to change Lean; we wait for a release.

## Fixes that remove workarounds of ours

| Upstream | State | Release | Our workaround |
|---|---|---|---|
| [PR #16283](https://github.com/leanprover/lean4/pull/16283) `use Nat.isPossibleRef everywhere` | merged 2026-11-05, commit `efd261787` | none yet | `tools/wasm32-nat-literals.py` and its build gate (branch `wip/bpwasm`): a `Nat` literal of 2^31 or more given to two owners is freed twice on wasm32 |
| [Issue #15530](https://github.com/leanprover/lean4/issues/15530), [PR #15533](https://github.com/leanprover/lean4/pull/15533) `String.toList` ends its list with a heap object on 32-bit | merged 2026-10-07 | v4.36.0-rc2 | one-line patch to `string_to_list_core`, `formal/lean4/Wasm/build-wasm.sh` step 1b |

Background to the first: [PR #9789](https://github.com/leanprover/lean4/pull/9789) added the
`isPossibleRef` and `isDefiniteRef` fields to the reference-count pass.

## Other 32-bit fixes we would gain

| Upstream | State | Release |
|---|---|---|
| [Issue #15814](https://github.com/leanprover/lean4/issues/15814), [PR #15816](https://github.com/leanprover/lean4/pull/15816) `LEAN_SCALAR_PTR_LITERAL` truncates static scalar fields on 32-bit | merged 2026-10-25 | none yet |
| [Issue #16089](https://github.com/leanprover/lean4/issues/16089), [PR #16090](https://github.com/leanprover/lean4/pull/16090) eight FFI definitions with the wrong parameter count | merged 2026-11-02 | none yet |
| [Issue #16136](https://github.com/leanprover/lean4/issues/16136), [PR #16137](https://github.com/leanprover/lean4/pull/16137) exit codes of `lean` on 32-bit | merged 2026-11-02 | none yet |
| [PR #16195](https://github.com/leanprover/lean4/pull/16195) 8 MB thread stacks on all 32-bit targets | merged 2026-11-03 | none yet |
| [PR #16279](https://github.com/leanprover/lean4/pull/16279) stop truncating kernel counts and indices to 32 bits | merged 2026-11-05 | none yet |
| [Issue #14973](https://github.com/leanprover/lean4/issues/14973), [issue #15181](https://github.com/leanprover/lean4/issues/15181) Emscripten libuv stubs that did not match their declarations | closed | not checked |
| [PR #13952](https://github.com/leanprover/lean4/pull/13952) wrong parameter type on an exported function, which trapped at initialization | merged 2026-06-09 | v4.34.1 |

## Open upstream, to watch

| Upstream | What |
|---|---|
| [Issue #16134](https://github.com/leanprover/lean4/issues/16134), [PR #16135](https://github.com/leanprover/lean4/pull/16135), [PR #16191](https://github.com/leanprover/lean4/pull/16191) | proposal and PRs to run a non-blocking WebAssembly CI job again |
| [PR #16142](https://github.com/leanprover/lean4/pull/16142) | the CI job's Emscripten moves to 6.0.13 |
| [PR #16149](https://github.com/leanprover/lean4/pull/16149) | native symbols resolved inside `lean.wasm` |
| [Issue #16007](https://github.com/leanprover/lean4/issues/16007), [PR #16015](https://github.com/leanprover/lean4/pull/16015) | `Nat` literals from 2^32 to 2^64 - 1 stop being parsed from a string each time; speeds up such literals, including on 32-bit |
| [Issue #15971](https://github.com/leanprover/lean4/issues/15971) | size truncation in built-in bignum division can overflow a stack buffer |
| [Issue #15977](https://github.com/leanprover/lean4/issues/15977) | closure arity truncation and application-count overflow |
| [Issue #6817](https://github.com/leanprover/lean4/issues/6817) | `linux_wasm32` `libleanrt.a` referring to libuv symbols |

## Reproduction of the literal fault

A `Nat` literal 4000000000 given to two owning callees, then one owner dropped and memory reused,
printed `[0, 8519936]` on wasm32 instead of `[0, 4000000000]`. Native arm64, and the same program
with `x + 4000000000` in place of the literal, were correct (Lean 4.33.1, 2026-11-09). The same
fault needs two owners and a value that is not a closed term: closed terms each get their own copy.
A copy of this test is on `wip/bpwasm` in `tests/wasm32-literals/`.

We have not run the fix in a Lean build. The statement that it fixes this fault comes from reading its diff.
