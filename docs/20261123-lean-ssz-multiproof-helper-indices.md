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

## Exact-source evidence: 23 November 2026
Implementation and proof head:
`5883087d81014ad306fd036f110032d179c23d99`.
GitHub Actions specialised Linux CI:
https://github.com/danbri/factoidal-core/actions/runs/45141048661
(job 137578847347): **passed** on that exact source head. Fresh
Lean 4.33.1 library compilation, `#guard` elaboration and the
separate complete theorem-file rerun passed. The actual printed sets
for **all 13 new theorem declarations** were independently read from
the CI log: **7 empty**, **4 [propext] only**, and **2
[propext, Quot.sound]**; no `sorryAx`, user axiom or other axiom.
(The four propext-only are `branchIndices_length`,
`helperIndices_refuses_invalid`,
`checkedHelpers_refuses_over_depth_cap` and
`checkedHelpers_within_limits`.) All **15 new `#guard` controls**
elaborated. The other two nonempty declarations are
`helperIndices_of_admissible` and
`checkedHelpers_refuses_over_claim_cap`.

The independent multiproof positional oracle matched **2,048/2,048**
actual Lean input/result rows, comprising **890 admitted, 1,158
refused and 157 valid empty-helper** requests; all three comparator
mutations were detected. The previously published SSZ generalized
index (1,025), checked branch (1,025), latest-message (2,048),
vote-store, attestation, proposer boost, ancestry, child selection
and bounded stored-head (each 1,024) independent gate steps were
rerun and **passed** in the same Linux job. This is synthetic
positional evidence, not SHA-256 or beacon-proof correctness.

The two earlier source heads `31c8f6a81ae80b181905bd3827878cc2ab93f35c`
(CI 45140747273) and `2f3e67721ba0020d8eaaa20162348b2094ae007a`
(CI 45140908823) **failed** to elaborate two example theorems
because `List.mergeSort` was not kernel-reducible in the required
proofs. Commit `5883087` replaces that sort with a transparent
structural insertion sort, so the executable and the example
proofs use the same implementation. The accepted range is limited
by caller-supplied caps (4 claims and depth 64 in the CLI) and not
a complete SSZ parameter policy.

A native local Lean 4.33.1 build, source-tree benchmarking,
memory-profile measurement, full repository premerge, an
independent human review, and broad repository gates are **not**
claimed. On the preceding parent stack, the broad Lean corpus
check https://github.com/danbri/factoidal-core/actions/runs/45129163023
failed at the unrelated existing CSS recursive
`L4Factoidal_Rendering_CssValues_Calc_simpWith` allow-list gate.
Our exact-head broad corpus and npm workflows are separate from the
specialised consensus success and must be inspected independently.
No before/after runtime latency distribution is available for this
new opt-in module. The sorter has quadratic worst-case work over
the returned candidate indices; the caller-supplied caps only
bound it for callers that enforce finite caps.

Crucial nonclaims: no concrete 32-byte SSZ Root, no SHA-256 pair
hash, no multiproof **verification** or authenticated beacon
container layout, no beacon state transition, BLS or finality.
The caller-supplied resource caps are not SSZ consensus parameters.
The Python reference is a *test*, not a normative refinement proof.
The full acceptance epic remains open. No main merge is intended.
