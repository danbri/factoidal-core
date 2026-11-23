# Checked SSZ single-branch admission — 23 November 2026

Parent: [strict EL+CL acceptance #725](https://github.com/danbri/factoidal-core/issues/725).
Normative correction tracked in [#813](https://github.com/danbri/factoidal-core/issues/813).
Stack: draft [#800](https://github.com/danbri/factoidal-core/pull/800) →
[#808](https://github.com/danbri/factoidal-core/pull/808) →
[#812](https://github.com/danbri/factoidal-core/pull/812) → this draft.

## Specification pins and compatibility distinction

- Current standalone SSZ source: [ethereum/ssz-specs @ 4c2f088, src/ssz/gindex.py](https://github.com/ethereum/ssz-specs/blob/4c2f08805080c6b4b12ede7bf48ad6a80229f4b1/src/ssz/gindex.py), specifically `gindex_depth` (root index 1 depth zero) versus `gindex_length` (root 1 raises `ROOT_HAS_NO_BRANCH`; index 0 is `NOT_A_GINDEX`).
- [src/ssz/proofs.py](https://github.com/ethereum/ssz-specs/blob/4c2f08805080c6b4b12ede7bf48ad6a80229f4b1/src/ssz/proofs.py) separately admits `node_root(value, 1)` as `hash_tree_root(value)`.
- The earlier standalone source [ethereum/consensus-specs @ 802485e, ssz/merkle-proofs.md](https://github.com/ethereum/consensus-specs/blob/802485ec74a6986542bd53bf153189623aab440c/ssz/merkle-proofs.md) exists, but that path was removed by the time of the previous documentation's pinned `498449f` revision. The old URL was not valid provenance.
- The standalone SSZ reference has its own existing Lean conformance suite and EthLib.Consensus.Ssz dependency at `ethereum/EthLib@6b87b0d4951766864af432455c44344fd12b5cdc`. This patch does not import EthLib or replace its proofs, types or conformance harness.

## Actual source semantics and intended proofs

`EthereumConsensus.SSZ.CheckedBranch` adds `branchLength`, `rootNodeIdentity`, `calculateBranch`, `verifyBranch`.
`calculateBranch` is the executable checked entry point: it refuses indices 0 and 1 and incorrect sibling count before invoking the caller-supplied ordered `foldProof` pair function. The generic, historic `calculate pair leaf [] 1 = some leaf` in `GIndex` remains unchanged; it is an algebraic identity, not an admissible proof branch.

The named obligations below were stated in issue #813 before implementation; theorems are attached to the actual functions and each has a `#print axioms` command:

1. `branchLength_rejects_zero`, `branchLength_rejects_root`: invalid/identity-only branches refused.
2. `branchLength_of_valid`: for `index > 1`, admitted branch length equals executable depth.
3. `rootNodeIdentity_at_root`: identity-only node root at index 1 remains expressible, but does not compute a concrete SSZ type's hash tree root.
4. `calculateBranch_rejects_root`, `calculateBranch_rejects_wrong_length`: actual checked path refuses invalid input.
5. `calculateBranch_of_valid`: admitted exact-length input goes through `foldProof`, preserving directionality.
6. `verifyBranch_rejects_root`: verifier does not bypass admission.

There are 16 executable Lean guards. A standalone `ssz-checked-branch` CLI emits 1,025 independent rows (indices 0–1024), including two index refusals and one malformed witness-length refusal for every index. A separate Python model independently computes both gindex length policy and bottom-up ordered fold. **These numbers are an expected fixture inventory, not a successful test result until exact-head CI executes.**

## Reproduce and assurance boundaries

Run Lake commands from `formal/lean4/ethereum-consensus` with pinned `leanprover/lean4:v4.33.1` and the repository single-build lock:

```sh
lake build
lake env lean EthereumConsensus/SSZ/CheckedBranch.lean
set -o pipefail
lake exe ssz-checked-branch | python3 scripts/check-checked-branch.py
```

The CI gate is `.github/workflows/ethereum-consensus.yml`.
This environment has no local Lean, Lake, repository worktree or lower-cost
coding-agent executable; compile and exact-head proof assertions must be read
from hosted results, not inferred from source.

No actual cryptographic binding is established: `α` is unconstrained, `pair` is supplied and untrusted, there is no verified SHA-256, fixed 32-byte Root, typed SSZ serialisation, witness bound or BLS. The operation is not connected to BeaconState, attestation validation, finality, Engine API or a synchronising node. Correct length is necessary but not sufficient for consensus validity. No EVM files or runtime hot paths change; performance parity is not measured.
