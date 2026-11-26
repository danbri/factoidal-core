# Independent SSZ fixed uint64 vector roots — 23 November 2026

## Source and protocol boundary

Under [strict full-client goal #725](https://github.com/danbri/factoidal-core/issues/725) and [predeclared implementation issue #842](https://github.com/danbri/factoidal-core/issues/842), draft [PR #843](https://github.com/danbri/factoidal-core/pull/843) extends [independent scalar SSZ PR #841](https://github.com/danbri/factoidal-core/pull/841) at base `0c9be2a2ef6bca9a1eb5da253f7e848d5b52471d`. No execution branch was edited. The withdrawn external-implementation path in #830/#832 was not used.

The actual native Lean 4.33.1 `ssz-vector-u64` executable uses `EthereumConsensus.SSZ.checkedVectorU64` and the repository's existing pure Lean `encodeUInt64`, `Chunk.ofBytes` and `hashPair`. It accepts exactly N values for declared 1 <= N <= 64. The local 64-element cap is **not** an Ethereum protocol constant. It concatenates N canonical eight-byte little-endian encodings; packs four uint64s per 32-byte leaf, right-zero-pads the last leaf, pads a complete binary tree with zero leaves to the next power of two, then computes SHA-256(left32 || right32) level by level. A fixed-length Vector has **no length mix-in**. The field-type shape, authenticity of the supplied values and caller's claimed length are not verified against a beacon state.

No new external Lake dependency or JavaScript execution fallback was introduced. JSON Lines is transport; Python's `int.to_bytes` and `hashlib.sha256` are *test oracles only*. The byte-array input limit is checked after stdin has read the line, so this is not yet a robust network-frame allocation bound.

Normative reference used for independent design review: `ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1` (basic values, fixed vectors, 32-byte chunk packing and binary Merkleisation). The existing pure SHA-256 implementation is not proved to satisfy FIPS 180-4 end to end, and the compiler/runtime are trusted.

## Execution and initial correction

The first hosted Lean trial on source head `2775ba27c3c7b65d4bc5390a8f6e1717475a2a91`, [run 45234427240](https://github.com/danbri/factoidal-core/actions/runs/45234427240), **failed**: two claimed public refusal theorems left the `Except.error` bind reduction unresolved. Their `#print axioms` output included `sorryAx`; they do **not** count as proofs or passes. There was no protocol or oracle result on this failed run; inherited later tests were skipped. Repair commit `cd6c5b1fa0016775c589aa28b8cde6062fe78e6f` explicitly simplifies `bind, Except.bind`; evidence blob pins were updated at `67948c3c24197f2ed29a909f1c91539f417815dd`.

**Corrected exact-source Linux run:** [45235021923](https://github.com/danbri/factoidal-core/actions/runs/45235021923), checkout merge `f894ef48f8303564909ee94ae37069884c753a98`, which differs from tested branch head `67948c3c24197f2ed29a909f1c91539f417815dd` by one merge commit and has *zero changed files* in GitHub's comparison. This run passed the dedicated vector step, fresh library and native executable build, actual `#print axioms`, all 12 new `#guard` checks, five code-blob source pins and the independent executable oracle. **1,406/1,406 cases matched; 0 failed, 0 unsupported and 0 not run in the selected vector corpus.** This includes 1,152 seeded random vectors, 224 boundary-pattern valid vectors and 30 separate malformed/capacity/refusal cases. Three forged comparator outputs were detected. The script's two engines are separate: Python calculates full expected roots with standard-library SHA-256, while the Lean binary performs its own hashing. The same workflow also passed the retained 5,580 byte-proof comparisons, 3,126 scalar cases, and ten inherited SSZ/LMD suites.

The nine actual printed theorem axiom sets have **three `[propext]` and six `[propext, Quot.sound]`**; none uses `sorryAx`, other unpermitted axioms, `native_decide` or `unsafe`. The new `vector-u64-claim-ledger.json` stores exact source blobs and, in its subsequent hardening commit, the **nine exact observed axiom sets**. `check-vector-u64-axioms.py` rejects mismatched source hashes, missing/extra printed claims and forbidden axioms; its subsequent hardening also rejects a changed permitted-axiom set. The correction is source-level proof reduction only; no SHA-256 algorithm or previous passing native module was modified.

## Reproduce the selected gates

With working directory explicitly `formal/lean4`, pinned Lean 4.33.1, and a single Lean build under the shared lock:

```bash
ulimit -v 8388608
lake -d ethereum-consensus build ssz-vector-u64
lake -d ethereum-consensus env lean "$PWD/ethereum-consensus/EthereumConsensus/SSZ/VectorU64.lean" > /tmp/vector-u64-axioms.log
python3 ethereum-consensus/scripts/check-vector-u64-axioms.py \
  ethereum-consensus/evidence/2026-11-23-vector-u64-claim-ledger.json /tmp/vector-u64-axioms.log
python3 ethereum-consensus/scripts/check-vector-u64.py \
  ethereum-consensus/.lake/build/bin/ssz-vector-u64 --report /tmp/vector-u64-results.json
```

The hosted consensus workflow also runs its original inherited gates, without excluding older failing data. These commands and outcomes are scoped to the recorded source tree and do not substitute for the separate exact-head factoidal-builds Linux, full premerge, independent protocol review or local performance gates.

## Incomplete requirements

A general theorem for the wire length and chunk padding/root result, full normative SSZ refinement, arbitrary fixed-vector element types and sizes beyond the local cap, SSZ containers/lists/offsets, checked beacon-state field witnesses, BLS, beacon transitions, fork choice/finality, networking and integrated execution/consensus acceptance remain open. No benchmark or performance-parity claim was made. [Full acceptance #725](https://github.com/danbri/factoidal-core/issues/725) remains the target, with the PR draft and unmerged.
