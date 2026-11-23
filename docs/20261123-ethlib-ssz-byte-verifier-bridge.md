# Isolated upstream EthLib SSZ bridge — 23 November 2026

Full client goal: https://github.com/danbri/factoidal-core/issues/725
Predeclared bridge obligations: https://github.com/danbri/factoidal-core/issues/830
Predecessor SSZ helper prototype: https://github.com/danbri/factoidal-core/pull/829

This **separate** Lean 4.35.0 Lake package pins
ethereum/EthLib@6b87b0d4951766864af432455c44344fd12b5cdc.
It does not modify the production Lean 4.33.1 package.

The byte-level checkedMerkleMultiproof entry point first checks local
claim/depth caps, witness cardinality and the size of each 32-byte chunk,
**including the expected root**, then delegates to EthLib's actual
SHA-256-backed verifyMerkleMultiproof. Neither caller-provided pair
hashing nor a JavaScript proof verifier is substituted. Upstream errors
are distinguished from local policy refusals.

Five named Lean theorems cover budget refusal, upstream-index delegation,
index-refusal propagation and exact delegated verifier results after
actual admission and data checks. They are about the concrete executable
wrapper. Source guards check malformed/duplicate/nested claims, wrong
witness counts, wrong root width and both true/false SHA-256 verification.
The SHA-256 of 64 zero bytes is pinned to the independent published digest
f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b.

The dedicated Linux workflow uses the separate compiler, re-elaborates
theorems and parses the actual #print axioms output. No proof or CI pass
is claimed before a successful exact-head run. There was no local Lean
toolchain, timing run, or memory benchmark in this environment.

Still required: equality/refinement against our older 4.33.1 positional
helper across all admitted cases, official version-pinned ss​​z-specs complete
fixture manifest and malformed corpus, authenticated beacon SSZ types,
BLS, transitions, finality, EL/CL integration, expert review and the full
repository Linux/premerge gates. Security depends on Lean, Mathlib, EthLib,
its SHA-256 implementation and formal/operational bridge correctness.
