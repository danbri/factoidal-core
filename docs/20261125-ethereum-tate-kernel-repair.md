# Independent Tate pairing kernel repair — 25 November 2026

Tracks #1002, #995 and #725. Base draft #996 at dc14d9119a6423251e4886a2f6d26c5d5abb7d1a. Isolated branch wip/ethereum-tate-kernel-repair-20261125-0304.

[Actual failed Linux job](https://github.com/danbri/factoidal-core/actions/runs/45529563170/job/138921204729): source audit passed, but Lean failed at PairingTarget.lean:232 with an unsolved goal in tate_noncanonical. Broad simplification rewrote Array.all's default end index to 6 before using the supplied Boolean hypothesis. The report for that theorem contained an unpermitted sorryAx as a consequence of failed elaboration. Native compile/link and comparisons did not run. The other nine statements printed allowed axiom sets (eight propext and Quot.sound; checkedOutput_ok propext only), but the gate failed and they are not fresh final-head passes.

Repair the proof using an explicit negative width proposition and a Boolean negation equality derived from the existing hypothesis, then restrict simplification to the executable definition and the two if reductions. No theorem statement or executable definition changed: a textual reversal of the proof replacement reproduces the predecessor file exactly. No extra proof assumptions or limits introduced.

Added 14 regression expectations: six p+1 coordinates, wrong width with invalid coordinates, noncanonical before curve rejection, oversized coordinate, malformed decimal before coordinate admission, empty and negative decimal requests. Actual oracle body and comparator executed in an isolated JS engine without Node I/O: 30 expectations, five positive cases, five comparator mutations detected; independent generator, bilinearity, order and denominator checks passed. This is not a native Lean comparison. Retained target oracle and workflow unchanged. Fresh native gate must compare all 318 target and 30 Tate cases and verify all ten exact axiom reports and source/link controls.

## Source pins (source commit 004c31b0ebe4d810e33e9556b6bb7de52d376bc0)

- PairingTarget.lean 37fd42a3796a4aa70fdb472be8a56b8b27eaec0b
- scripts/check-tate-pairing.mjs a4a5f3e82cd5e6b5211270999820320aacef278b
- scripts/check-pairing-target.mjs ad47b702dad594b2173d3f6d5bd17c67eed84a59
- lean-toolchain a8afa7d1b02d96f0671eba854a8dc4b416beb473
- lake-manifest.json 15728fe01a01ed2369565ec5be9afdf6abcf2f91
- lakefile.toml b08203129886735a8fbfc2c31fb7027024665d1f
- .github/workflows/ethereum-bls-pairing-target.yml 5d8956c0a97c4787831065a26cf9dbc9f4e86b9a

Import only Lean; empty external Lake manifest, pinned Lean 4.33.1, no new dependency. Local source audit found no forbidden constructs. No local Lean executable or shared Mac access, no coding subagent available. Use dedicated Linux workflow in isolated consensus package to compile actual executable, print axioms and compare both oracles. Compiler/runtime and line allocation remain trusted. No G2 subgroup integration, hash-to-curve, mathematical pairing refinement, BLS verdict or full consensus claimed. No main merge or release.
