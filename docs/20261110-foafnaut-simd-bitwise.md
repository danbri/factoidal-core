---
title: "Foafnaut worklog: SIMD bitwise theorems"
date: 2026-11-10T16:33:00Z
draft: false
tags: [foafnaut, theorems, wasm]
---

Work on https://github.com/danbri/factoidal-core/issues/388 (small theorem contributions).
Branch: `wip/388-simd-bitwise`.

## Scope

Prove that `v128.not` applied twice gives the original vector, and that
`v128.and`, `v128.or` and `v128.xor` are commutative and associative.
State these laws on the existing `V128.evalUn` and `V128.evalBin` functions.
Do not change executable definitions.

## Preparation

- Read the Foafnaut skill, repository rules, theorem contribution record,
  and the Lean proof and review skills.
- Searched the WasmVM source for existing proofs of these laws. None found.
  The task has no issue comments and no open SIMD PR was found.
- Made an isolated sparse checkout in the helper workspace. The older source
  checkout has unrelated edits; these were not changed.
- The initial source base is `68e60cad09b649e3ef244a4607ea3306d9d2dd68`.
  Check the current remote base again before publication.
- The checkout uses about 74 MB. Limit: 2 GB new disk, no build below 3 GB
  free, normal shared build queue, remove build output after publication.

## Results

Seven theorems in `L4Factoidal/WasmVM/Proofs/Simd.lean` establish double
complement, commutativity and associativity on the actual evaluator functions.
Each statement applies to all `V128` values, with no hypotheses. The WasmVM
build root imports the new module.

The statements lift Lean core's `UInt64` laws to both halves of a vector.
They are labelled **Bridge**: algebraic identities alone do not specify
the complete operations. In particular, even an identity function is its own
inverse. These results do not prove binary decoding, validation, stack
execution, full WebAssembly conformance or any performance claim.

The statement review found no duplicate theorems and confirmed the four opcode
values against the WebAssembly vector instruction table. No executable
definition or existing test was changed.

## Verification

- `lake build L4Factoidal.WasmVM.Proofs.Simd`: passed, five jobs, including
  fresh builds of Syntax, Numerics and Simd. No copied build cache.
- All seven `#print axioms` reports: only `propext`, `Classical.choice`,
  `Quot.sound`.
- `python3 tools/lean-unbuilt-modules.py --gate`: passed; 1,675 modules
  reached, zero unreached.
- `python3 tools/lean-hygiene-audit.py --build-log <helper>/simd-build.log`: passed.
  The first attempt lacked lab sources in the sparse checkout; restoring the
  106 unchanged lab Lean files let the complete audit run. The permitted lab
  baseline of 29 unsafe declarations and 29 implementation overrides is
  unchanged.
- `lake build WasmVM`: passed, 197 jobs. Existing warnings appeared in
  unchanged dependencies; the new module has no warnings. Both the new proof
  module and its WasmVM importer produced `.olean` files.
- The hygiene audit also passed against the importer build log, checking
  18 axiom reports from rebuilt or replayed proof modules.
- `git diff --cached --check`: passed. The diff contains this worklog, the
  theorem registry entry, the new theorem module and its single root import.

## Local environment

The shared `leanlock.sh` wrapper serialized the builds. The sandbox cannot
read the process list or append to the external coordination log; the wrapper
printed these failures. Build results are recorded separately from those
wrapper diagnostics. All work uses this private checkout and the shared lock.

Shell Git cannot resolve GitHub in this sandbox. The GitHub connector supplied
the current main commit and tree metadata; each object was checked against
its Git SHA before import. The newer main commit
`8d23d6626ec32c4bb7e456846bdb094977923f3b` changes only the Textnaut npm README
and screenshots. It does not change any source used by these proof builds.

The importer build started with 4.9 GiB free. Free space fell to 1.4 GiB
while it ran; it completed before the attempted stop. Removed this checkout's
525 MB `.lake` directory immediately after checking the successful result and
the two `.olean` files. No other session's files were removed. The source
checkout remains below the 2 GB new-disk limit.

Rebased onto the checked main commit. The Lean sources used in both successful
builds are unchanged by that rebase. Review branch:
https://github.com/danbri/factoidal-core/tree/wip/388-simd-bitwise.

No merge or deployment is part of this contribution. Further work can take
another small item from the same theorem task issue.
