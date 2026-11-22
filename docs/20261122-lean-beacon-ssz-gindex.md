# Lean beacon SSZ generalized-index proof-path foundation (22 November 2026)

Tracking: https://github.com/danbri/factoidal-core/issues/799
Parent acceptance: https://github.com/danbri/factoidal-core/issues/725
Execution subgoal is separate: https://github.com/danbri/factoidal-core/issues/652

## Normative slice and provenance

The upstream Ethereum consensus specification is
https://github.com/ethereum/consensus-specs/blob/master/ssz/merkle-proofs.md
(SSZ generalized-index helpers and single Merkle proof; retrieved 22 November 2026).
A content-addressed upstream commit/hash still needs to be pinned before
a normative refinement claim. Its code states: child = 2*i+right,
parent = i//2, sibling = i xor 1, proof length = floor(log2(i));
odd-index siblings are hashed to the left. These operations are implemented
in the actual Lean module `EthereumConsensus.SSZ.GIndex`.

## Statement-before-code claim ledger

Issue #799 recorded the intended theorem statements before implementation.
These theorem names are now in source (provided the exact-head Lean build
actually elaborates them):

- `parent_child` is the actual parent/child equation.
- `sibling_left_child`, `sibling_right_child` compare actual sibling and child functions.
- `indexForPath_append` is the concrete root-based path composition.
- `calculate_rejects_zero`, `calculate_rejects_wrong_depth` are actual
  calculation-entry refusals prior to invoking the supplied pair hash.
- `calculate_root`, `calculate_one_left`, `calculate_one_right` ensure
  correct order at the first Merkle level.
- `verify_rejects_zero` is connected to the public verifier.

Each selected declaration has an explicit `#print axioms`.
Do not say those are audited until current-head CI checks them.
The intended accepted Lean axioms are the repository's standard set
`propext`, `Classical.choice`, `Quot.sound`; no user axioms.
The 12 `#guard` instances are executable tests, not proofs.
The independent Python checker covers indices 0–1024, including depth,
parent and sibling; it does not independently check cryptography.

## Trust limits / what this does not establish

The generic Merkle fold takes `pair : α → α → α` as **supplied code**.
A malicious or wrong pair can make the verifier accept a forged proof.
There is no SHA-256 implementation or proof here, no fixed 32-byte node
type and no SSZ serialization, multiproof, BeaconState, BLS, fork choice
or finality. Index zero is rejected before hashing. Resource handling is
linear in the supplied sibling list, but there is no byte-level allocation
quota and no cryptographic/hash-cost bound yet.

## Reproduce using the exact revision

```sh
# package working directory: formal/lean4/ethereum-consensus
lake build
lake env lean EthereumConsensus/SSZ/GIndex.lean
set -o pipefail
lake exe ssz-gindex | python3 scripts/check-gindex.py
```

Cloud Linux workflow: `.github/workflows/ethereum-consensus.yml`.
This standalone package never changes the existing EL execution path.
A future change must connect 32-byte SHA-256 pairs to the actual SSZ
branch verifier, use exact fork-indexed BeaconState types and consume
canonical consensus-spec test vectors. The complete goal #725 stays open.
