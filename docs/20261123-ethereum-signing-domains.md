# Independent Ethereum signing domains (23 November 2026)

Issue #848. Stacked on #845 at 334ec166b642b72404b396b0ed8e19ac8c309fe3. Lean 4.33.1, repository-owned SHA-256, no new dependency. The fork context is supplied, not authenticated. The mainnet profile uses 32 slots per epoch; explicit previous/current versions and activation epoch are checked for widths and selected by a strict epoch comparison. The proposer-header path derives the domain type and slot epoch locally, uses the existing header and signing-data roots, and returns all three roots for inspection.

The source contains seven intended theorem statements and an actual printed-axiom audit. The independent Python oracle constructs 1,280 valid domain/header requests and 52 invalid requests and checks three deliberate comparator mutations. These are planned counts until CI executes. Retained tests remain enabled. Two inherited ledgers pinned the old aggregate root module before #845; only that root pin is refreshed for the appended imports, retaining all earlier theorem sets and other pins. CI reports observed source object IDs, not assumed axiom sets for the new statements.

No local Lean or lower-cost coding-agent runtime is available here. Source review is not independent expert review. No BLS signature, fork schedule, state authentication, canonical header, full SSZ or node operation claim. JSONL line allocation precedes the inherited 2048-byte limit. No benchmark result or main merge claimed.

Reproduction from formal/lean4:
```sh
ulimit -v 8388608
lake -d ethereum-consensus build EthereumConsensus FactoidalSHA2 ssz-container-roots
lake -d ethereum-consensus env lean "$PWD/ethereum-consensus/EthereumConsensus/SSZ/SigningDomains.lean" > /tmp/signing-axioms.log
python3 ethereum-consensus/scripts/check-signing-domain-axioms.py /tmp/signing-axioms.log
python3 ethereum-consensus/scripts/check-signing-domains.py ethereum-consensus/.lake/build/bin/ssz-container-roots
```
