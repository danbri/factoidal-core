# Independent proposer-slashing preparation — 24 November 2026

Tracking #938, parent #725. Base: draft #916 at `7c7e53f1d343274cf54acc55cf3506af452fc3f3`, with registry workflow run 45431614791 reported successful. Separate branch; #923 attester-signer work is not changed.

## Implementation and boundary

`checkProposerState` takes two typed BeaconBlockHeaders. It requires equal slots and proposer indices but unequal complete root fields. It invokes the existing concrete commitment checks for the supplied state slot, Fork and genesis, registry root, and validator at the first header's proposer index. It derives the eligibility epoch from the state slot and the signing epoch from each header slot. On success the output contains the actual verified-in-commitment public key and both derived signing roots. The native transport explicitly labels this candidate_not_authenticated. Neither a valid BLS signature nor a canonical BeaconState, an authenticated slashing operation, or a mutation is established. Layouts follow the inherited mainnet Phase0–Fulu profile; synthetic maximum uint64 slots exercise arithmetic, not future fork coverage.

Normative pin: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3, specs/phase0/beacon-chain.md, process_proposer_slashing and is_slashable_validator.

New source: ProposerSlashing.lean blob `471d8d3d41dcba4a3b87908b40bdefccb5d1fbb3`; ProposerSlashingMain.lean blob `1090a2f2ec807afb7a6d92941b80a4e8522e8861`; Python oracle blob `a0c36058fac189b8ed3ecf62db1057b204e0aab5`; Lake target config blob `b08203129886735a8fbfc2c31fb7027024665d1f`; new specialised CI blob `884637c29f13d184246491627122505c3572c23d`. Source checkpoint `9ab2041f2556eda06bd0469faaebf091d28280b9`.

The external Lake manifest is unchanged (empty package list, blob `15728fe01a01ed2369565ec5be9afdf6abcf2f91`); Lean remains 4.33.1. Reuse of repository-owned ValidatorRegistry, SigningDomains and pure SHA-256 via their existing import graph is subject to the actual CI source/compiled/native dependency audits. No new cryptographic implementation or host runtime fallback.

## Executed locally

- Exact-blob Python oracle self-test: 1,218 distinct expected rows (46 candidate outputs, 1,172 refusals); all three malformed/forged comparator controls rejected. A second local bit-walk and explicit fixed-tree calculation independently reconstructed all 64 synthetic registry and state commitments, rejected all 256 single state-branch mutations, and recomputed both signing roots for every one of the 46 candidate cases.
- Python is a test oracle only. Zero native Lean cases executed locally: no Lean, Lake or shared Mac connection in this environment. No checked-theorem or compiled/link audit claim. No native timing baseline.

## Required hosted gates

Fresh libraries and native `ssz-proposer-slashing`, all 12 actual printed axiom reports, exact source/tree pins, source/compiled/link audit, native 1,218-row comparison and retained registry and consensus gates. Local IO line admission is after the line read (not a physical heap bound). The full proof and native test results remain pending. No main merge, release, BLS, canonical state or full client claim.

Commands from formal/lean4:
```sh
python3 ethereum-consensus/scripts/check-proposer-slashing.py --self-test
lake -d ethereum-consensus build EthereumConsensus FactoidalSHA2
lake -d ethereum-consensus -v build ssz-proposer-slashing
lake -d ethereum-consensus env lean "$PWD/ethereum-consensus/EthereumConsensus/SSZ/ProposerSlashing.lean"
python3 ethereum-consensus/scripts/check-proposer-slashing.py ethereum-consensus/.lake/build/bin/ssz-proposer-slashing
```
Use the repository build lock on shared hardware and the CI's existing 8 GiB cap.
