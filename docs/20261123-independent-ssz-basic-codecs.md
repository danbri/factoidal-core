# Independent Ethereum SSZ basic-type codecs — 23 November 2026

## Scope and source

This checkpoint extends [draft SSZ byte-proof PR #836](https://github.com/danbri/factoidal-core/pull/836) at exact base `db570c0e7022612d9956b08d65f56e51f9e823d2`, under [predeclared issue #840](https://github.com/danbri/factoidal-core/issues/840) and the complete [EL+CL acceptance epic #725](https://github.com/danbri/factoidal-core/issues/725). Branch: `wip/ethereum-ssz-basic-codecs-20261123-run4`. The unchanged native implementation modules are committed before the evidence/workflow-only follow-ups.

`formal/lean4/ethereum-consensus/EthereumConsensus/SSZ/BasicTypes.lean` implements actual **pure Lean 4.33.1** canonical `UInt64` encoding (eight little-endian bytes), strict eight-byte decode, canonical Boolean 0/1 wire serialization and strict one-byte decode, and basic-type Merkle roots as right-zero-padded 32-byte chunks. Single basic values are **not SHA-256 hashed** to form their SSZ root. The root constructor reuses this repository's own width-checked `Chunk`; the package manifest still has no external packages. `BasicMain.lean` exposes a native JSON Lines transport. Python implements the **independent test oracle only** and does not supply runtime results.

Normative comparison target: `ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1` for basic-value serialization and roots. Compiler/runtime and the caller's interpretation of roots remain trusted.

## Exact-source Linux results

**Passing implementation and source-audit head:** `ff680e6ccd4512518f90f6335501c4af33c05be0`. [Specialised Linux CI run 45229592864](https://github.com/danbri/factoidal-core/actions/runs/45229592864) passed **every step** (job `ssz`), including a fresh Lean 4.33.1 library and executable build, source-dependency audit, all retained SSZ and LMD reference gates, and the new native scalar codec oracle. All 18 source-level `#guard` instances compiled.

The native `ssz-basic-types` executable agreed with the standard-library independent Python byte oracle on **3,126/3,126 actual requests**, including 1,215 encoding and 1,367 decoding uint64 requests; 256 encoding and 256 decoding Boolean requests; six noncanonical Boolean refusals, 19 wrong-width refusals, three out-of-range uint64 refusals, two length-cap refusals and two invalid-byte refusals. The independent reference used `int.to_bytes(8, 'little')` and `int.from_bytes(..., 'little')`. Three forged comparison outputs were detected; no mismatches or skips were reported in the new corpus.

The retained pure SHA-256 / SSZ byte-verifier [independent corpus](https://github.com/danbri/factoidal-core/pull/836) matched **5,580/5,580** actual executable requests and detected all 12 comparator mutations. The 13 earlier multiproof-index theorem axiom sets and all ten inherited SSZ/LMD oracle suites also passed. Those are separate scoped regressions, not additional new SSZ codec conformance results.

The [seven new theorem source/axiom ledger](../formal/lean4/ethereum-consensus/evidence/2026-11-23-basic-type-claim-ledger.json) and [re-pinned 35-claim retained byte-proof ledger](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proof-claim-ledger.json) were compared to actual Lean `#print axioms` output by the fail-closed source-pinning gate. They check **29 source blobs**. The seven newly compiled proofs are:

| Theorem | Actual printed axioms | Meaning |
| --- | --- | --- |
| `encodeUInt64_size` | none | Actual encoder writes eight bytes |
| `decodeUInt64_wrong_width` | `propext` | Wrong-size decode refuses |
| `encodeBool_size` | none | Actual Boolean encoder writes one byte |
| `decodeBool_encode` | none | Encode/decode Boolean roundtrip |
| `decodeBool_wrong_width` | `propext` | Wrong-size Boolean decode refuses |
| `decodeBool_rejects_two` | none | Noncanonical Boolean byte 2 refuses |
| `checkedBasicRoot_rejects_long` | `propext`, `Quot.sound` | Overlong basic-root payload refuses |

The general uint64 encode/decode roundtrip and exact 32-byte zero-padding equation remain **tested but not yet proved**. A theorem or guard about a basic-value helper is not a proof of normative beacon-state layout, tree-root authenticity, finality or consensus.

## Failed attempts and correction

Two earlier [Linux run 45228440680](https://github.com/danbri/factoidal-core/actions/runs/45228440680) and [run 45228805508](https://github.com/danbri/factoidal-core/actions/runs/45228805508) failed during compilation: Lean 4.33.1 did not provide the assumed `BEq (Except ...)` or `DecidableEq (Except ...)` instances. Explicit result-pattern-matching guards fixed this without changing codec semantics. A later [run 45229088215](https://github.com/danbri/factoidal-core/actions/runs/45229088215) compiled the corrected Lean code but correctly failed the inherited immutable source ledger because `EthereumConsensus.lean` added an import. The ledger was rebuilt with the new exact blob pins; **the successful passing run 45229592864 validates this correction**, not the failed attempts.

## Reproduction (from formal/lean4 only)

```bash
lake -d ethereum-consensus build EthereumConsensus ssz-basic-types
lake -d ethereum-consensus env lean "$PWD/ethereum-consensus/EthereumConsensus/SSZ/BasicTypes.lean"
python3 ethereum-consensus/scripts/check-byte-proof-axioms.py ethereum-consensus/evidence/2026-11-23-basic-type-claim-ledger.json <axiom-output.log>
python3 ethereum-consensus/scripts/check-basic-types.py ethereum-consensus/.lake/build/bin/ssz-basic-types --report <report.json>
```

The hosted workflow uses the same pinned Lean toolchain and retains structured oracle/axiom artefacts. No local Mac build, paired startup/tail-latency benchmark, broad repository premerge, factoidal-builds Linux gate or independent protocol-security review is claimed. The JSONL host checks line size only **after** the line is read into memory. Input-size-before-allocation enforcement and further resource proofs remain necessary for a networked client.

## Remaining full-goal obligations

Composite SSZ vector/list/container serialization, offsets and layout, generalized uintN/bitvector codecs, authenticated beacon state roots, BLS signatures, consensus fork transitions, LMD/FFG finality, networking and integrated EL+CL interoperability remain open. This feature is a small verified/tested protocol-data component, not a full standalone beacon client or operational Ethereum node. Keep this PR **draft and unmerged** until all required Linux/factoidal-builds/premerge gates and explicit merge authority are present.
