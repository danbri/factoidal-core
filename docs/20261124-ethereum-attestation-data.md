# Independent attestation data and signing roots (24 November 2026)

Issue #868; strict parent #725. New isolated branch from #849 at e20294fb1562bf1d4135c7336c7a0fade2b155f9. That predecessor's specialised workflow 45255171564 was cancelled during compilation; it is not a verified checkpoint. The new branch retains all inherited consensus gates. EL transaction-list work #867 remains separate.

The normative pin is ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3, specs/phase0/beacon-chain.md (AttestationData, is_valid_indexed_attestation, DOMAIN_BEACON_ATTESTER). The actual Lean dispatcher computes the 128-byte fixed wire representation, five-field SSZ root with two nested checkpoint roots, and signing root using target epoch to select the fork version. Slot and source epoch do not select the domain. Inputs are decoded, supplied fields, not authenticated state.

Five intended source-connected theorem statements; the CI script requires all five actual printed axiom results, only permitted foundations, and matches 15 exact source blobs. The new test inventory is 1,295 requests (1,281 well-shaped, 14 expected malformed refusals), including a synthetic known-answer vector calculated locally with Python hashlib using an explicit eight-leaf expression. The separate native oracle uses generic bottom-up tree reduction and checks five comparator mutations. Counts describe the planned inventory until native execution finishes.

The toolchain remains Lean 4.33.1 and the external Lake manifest remains empty. The only cryptographic implementation on this path is the existing repository-owned SHA-256. Python is a test oracle, not a runtime provider. The aggregate module pin is refreshed in two retained ledgers, with no change to their existing theorem axioms or other source pins.

Local Git checkout and Lean/Codex executable were unavailable (GitHub DNS lookup in the local container failed; GitHub connector available). No local Lean compile, proof elaboration, native test, timing or independent reviewer result is claimed. The independent known-answer computation ran locally. Hosted build, actual axiom reports, native comparisons and retained suite results are required before promoting the checkpoint. Limits: fixed-size fields and inherited 2048-byte line cap, applied after stdin line allocation. Compiler/runtime and SHA-256 refinement remain trusted. No state validity, BLS, validator membership, vote acceptance, slashing decision, complete consensus transition or node readiness is implied. No merge.

Reproduction, from formal/lean4:
```sh
ulimit -v 8388608
lake -d ethereum-consensus build EthereumConsensus FactoidalSHA2 ssz-container-roots
lake -d ethereum-consensus env lean "$PWD/ethereum-consensus/EthereumConsensus/SSZ/AttestationData.lean" > /tmp/attestation-axioms.log
python3 ethereum-consensus/scripts/check-attestation-data-axioms.py /tmp/attestation-axioms.log
python3 ethereum-consensus/scripts/check-attestation-data.py ethereum-consensus/.lake/build/bin/ssz-container-roots
```
