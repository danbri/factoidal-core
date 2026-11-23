# Independent Lean 4 London EIP-1559 header arithmetic — 23 November 2026

Parent acceptance: [full EL+CL #725](https://github.com/danbri/factoidal-core/issues/725), [EL #652](https://github.com/danbri/factoidal-core/issues/652). Implementation obligation [#846](https://github.com/danbri/factoidal-core/issues/846); review in draft, unmerged [PR #847](https://github.com/danbri/factoidal-core/pull/847). Base is independently implemented CALL-family PR #827 at `0b60a50eeb06db84366877cd54c8eab9ad424046`. This slice is separate from the active identity CALL integration and SSZ containers.

## Executable work

`EVMCleanroom/HeaderFees.lean` implements the London activation comparison against twice the pre-London parent gas limit, initial base fee of 1,000,000,000 wei, the subsequent London-family parent gas target (parent limit / 2), upward and downward EIP-1559 fee updates with the two ordered integer divisions, a minimum 1-wei upward increment, strict 1/1024 gas-limit bounds, supplied header fee equality, and explicit error/refusal results. It checks parent/child gas usage and local numeric caps before calculating. `EVMCleanroom/HeaderFeeCLI.lean` is the actual native Lean executable, `evm-header-fees`. Its transport accepts seven decimal fields, with `-` for an absent parent fee; JSON numbers are emitted as strings. The host does no fee calculations.

The first-London activation switch, predecessor gas fields and predecessor fee are caller-supplied. They are **not** derived from an authenticated ancestor, fork index or execution header yet. Absence of a needed predecessor fee gives **indeterminate**; local resource refusal is also indeterminate, not a consensus-invalid header. Numeric limits on this standalone API are development limits.

No new external implementation dependency, EthLib package, native crypto or JavaScript fallback is used. The existing `lake-manifest.json` has `"packages":[]`. Lean is pinned to **4.33.1**. The Lean compiler/runtime, operating-system byte transport and completeness/authenticity of supplied parents remain outside the theorems.

## Protocol references

Normative EIP: [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559). For independent review, the Ethereum execution-specs London reference is pinned to commit `391d8a05d5cb182542ac7e7330c858b6ee03f990`, `src/ethereum/forks/london/fork.py`, blob `1444d5c0e452cffb0665b091b60c4c6f0a027439`. Its code is **not** imported, copied, translated or executed by the Lean implementation. The independent test oracle is a small Python standard-library formula and is never used for protocol decisions.

## Exact-source evidence

The implemented Lean files and oracle were unchanged from corrected source head `0e9cb799e091acccc8bc1ecb80718c6cd8a3d531`. Source SHA-1 blobs and the six actual theorem axiom sets are recorded under `formal/lean4/evm-cleanroom/evidence/2026-11-23-london-header/claims.json`. A source-blob and raw-output checker (`scripts/check-london-claims.py`) rejects missing/extra statements and axiom drift, with three negative controls. Run with:

```sh
# Working directory: formal/lean4/evm-cleanroom
lake build EVMCleanroom
lake -f lakefile-london.toml build evm-header-fees
python3 scripts/check-london-header-fees.py --generate /tmp/london-input.tsv /tmp/london-expected.jsonl
lake -f lakefile-london.toml exe evm-header-fees --batch /tmp/london-input.tsv > /tmp/london-observed.jsonl
python3 scripts/check-london-header-fees.py --check /tmp/london-expected.jsonl /tmp/london-observed.jsonl
LEAN_STACK_SIZE_KB=65536 MIMALLOC_ARENA_RESERVE=67108864 lake env lean EVMCleanroom/HeaderFees.lean > /tmp/london-header-axioms.txt
python3 scripts/check-london-claims.py --selftest
python3 scripts/check-london-claims.py --report /tmp/london-header-axioms.txt
```

### Observed Linux run

[Linux EIP-1559 run 45251591536](https://github.com/danbri/factoidal-core/actions/runs/45251591536) passed every specialised step on code head `37af93318c51817655ccc6fa6a067acd111bf65e` on 23 November 2026. Actual Lean 4.33.1 compiled both the library and native executable; 13 `#guard` checks compiled; all **six** `#print axioms` statements used only permitted `propext`, `Classical.choice`, `Quot.sound`. The Lean action audited **3,100** declarations under `EVMCleanroom`.

**1,555 / 1,555 actual Lean results** matched the independent oracle, seeded 1559, with zero mismatches, zero unexecuted, and three comparator mutations detected. The selected inventory is **1,389 accepted**, **162 explicit invalid-header errors**, **four indeterminate outcomes** (missing fee or local numeric bound). It contains 256 first-London activation cases, 1,280 subsequent fee updates, and 19 carefully selected boundary/refusal cases. A deliberately malformed transport record exited with code 2. This is a small selected suite, not full EELS/Hive.

The initial `#guard` attempt failed because Lean 4.33.1 has no implicit `BEq (Except Error Nat)`; a second attempt failed when a fresh standalone proof-transcript Lean process could not create a thread under the process cap. Both were repaired without using any proof bypass, and the above source-head workflow passed.

**Regression discovered during complete EVM CI:** The first integrated root import changed the blob of `EVMCleanroom.lean`. The existing v2 proof/assurance ledger correctly rejected that source drift in both the Lean job and the authenticated real-state job (run [45252161604](https://github.com/danbri/factoidal-core/actions/runs/45252161604)), even though the standalone London slice passed. The root import was therefore reverted in `47b5575ce4bd65e373af5a5c86f0f2bb7e9986ea`, restoring **exact** previously reviewed root blob `26dfa6044a613c42c3351a9b700b5352de0589a4`. London header logic remains compiled, run and audited through the standalone `evm-header-fees` target and fresh source-axiom check. It is **not** imported into the old EVM model or integrated header/block validation yet. The new ledger now pins the original root blob and all independent London source files. This avoids altering the old v2 manifest or accepting stale evidence.

A second source-pin gate detected that the original `lakefile.toml` was also part of the v2 assurance manifest. Its extra native target was moved to a separate, committed, same-directory `lakefile-london.toml` selected explicitly with `lake -f lakefile-london.toml`. The default Lake configuration is now **byte-identical** to its predecessor blob `379997eaeb6e1c9fb147270be0f317f05812683b`; the alternate file has its own source pin and adds no dependency. Thus EVM's original source and build definition remain unchanged while a native Lean London entry point can be compiled separately. The new evidence inventory now has six pinned source blobs.

The corrected post-regression head needs a fresh complete CI run, and no previous passing result substitutes for it. Neither the earlier passing specialised run nor the earlier failing EVM jobs establishes that final verdict. Do not inherit this passing verdict if source, audit or workflow changes fail on that head. The broad repository/premerge and factoidal-builds exact-head Linux gate are separate and not claimed.

## Theorem scope and remaining blockers

- `nextBaseFee_at_target`: equals predecessor fee exactly at target.
- `nextBaseFee_above`, `nextBaseFee_below`: directional arithmetic bounds.
- `expected_firstLondon`: accepted first-London expectation is the initial fee.
- `checkHeader_sound`: successful check equals actual computed fee and supplied fee.
- `missing_parent_refused`: a later header without a predecessor fee has no successful expectation.

These theorems concern executable arithmetic, **not** canonical parent selection, header signatures/hashes, withdrawals, account/receipt/state roots or any block transition. We have not integrated this into authenticated block execution or proven an independent EELS refinement. Other forks' exact header rules, broad historical replay, Engine API, networking, beacon transitions/BLS/finality and independent expert review remain open under #725. No runtime benchmark parity or merge readiness is claimed.
