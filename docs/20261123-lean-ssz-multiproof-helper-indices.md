# Lean SSZ multiproof positional helper indices (23 November 2026)

Parent: https://github.com/danbri/factoidal-core/issues/725
Pre-code theorem obligations: https://github.com/danbri/factoidal-core/issues/828
Independent precursor: https://github.com/danbri/factoidal-core/pull/825
EVM CALL-family ownership is separate: https://github.com/danbri/factoidal-core/issues/826

## Target and provenance
The normative positional algorithm is `get_path_indices`,
`get_branch_indices`, `_reject_related` and `get_helper_indices` in
`ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1/src/ssz/gindex.py`.
See https://github.com/ethereum/ssz-specs/blob/4c2f08805080c6b4b12ede7bf48ad6a80229f4b1/src/ssz/gindex.py .
The earlier deprecated `consensus-specs/ssz/merkle-proofs.md` source
pin must not be treated as an extant source file.

## Source-connected theorem candidates
`EthereumConsensus.SSZ.MultiProofHelpers` defines the actual
path/branch enumerator, index-set admission, sorted helper construction
and optional caller-supplied claim/depth caps. Its 13 theorem statements
cover branch shape/length, invalid-refusal, successful admission,
cap refusal, bounded delegation, and exact empty/duplicate/nested/single
examples. Every theorem has a `#print axioms` and source comment
explaining what it says and does not say. All require a current-head
Lean 4.33.1 elaboration and axiom audit before claiming proof success.

## Test programme
```sh
# Run in formal/lean4/ethereum-consensus through the shared Lean lock,
# with bounded memory. On CI these commands run on fresh Linux builds:
lake build
lake env lean EthereumConsensus/SSZ/MultiProofHelpers.lean
set -o pipefail
lake exe ssz-multiproof-helpers | python3 scripts/check-multiproof-helpers.py
```
The CLI emits 2048 deterministic requests *and the corresponding Lean
results* (including malformed inputs and deliberately over-budget
requests). The independent Python oracle walks tree indices using
bit shifts, checks input admissibility and reconstructs sorted helper
positions by set subtraction. It includes three corrupt-observation
controls. The fixture is synthetic, with no trusted root or SHA-256
digest. Existing checked-branch and LMD gates are also rerun by
`.github/workflows/ethereum-consensus.yml`.

## Exact-source evidence and limits
At authorship time, there is no local Lean 4.33.1 environment in the
connector-only runtime. CI compilation, exact-head proof axioms,
input totals and latency MUST be recorded after a hosted run. Source
publication alone is not a passing test. There is no before/after
performance result yet; this is a new module, not an existing hot path.

Crucial nonclaims: no concrete 32-byte SSZ Root, no SHA-256 pair
hash, no multiproof **verification** or authenticated beacon
container layout, no beacon state transition, BLS or finality.
The caller-supplied resource caps are not SSZ consensus parameters.
The Python reference is a *test*, not a normative refinement proof.
The full acceptance epic remains open. No main merge is intended.
