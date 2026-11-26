# Independent Lean SSZ byte-proof implementation

Task: https://github.com/danbri/factoidal-core/issues/834.
Acceptance goal: https://github.com/danbri/factoidal-core/issues/725.
Base: https://github.com/danbri/factoidal-core/pull/829 at
`7c50781db078f03c573ee32c38551c4fba2ac015`.

This work adds executable verification of single and multiple SSZ Merkle
proofs over real 32-byte chunks. It uses the existing repository-owned pure
Lean SHA-256 implementation. It adds no external Lake package and keeps
Lean 4.33.1. The separate EthLib adoption proposal and PR remain withdrawn.

[Architecture, admission rules and trust boundary](designissues/2026-11-23-independent-ethereum-ssz.md).

## Source and proof evidence

The new implementation is in `EthereumConsensus/SSZ/ByteProof.lean`, its
proofs are in `ByteProofTheorems.lean`, and the JSONL interface is
`ByteProofMain.lean`, all under `formal/lean4/ethereum-consensus/`.

The [claim ledger](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proof-claim-ledger.json)
pins **27 Lean source blobs**. Fresh, explicit Lean elaboration matched
**35 actual axiom reports**: 29 new SSZ statements and six existing SHA-2
width/padding statements. One report has no axioms; the other 34 use only
the permitted `propext`, `Classical.choice` and `Quot.sound` foundations.
The new module's ten test guards and the selected SHA-2 test module's 28
active guards compiled. Guards are tests.

The new statements establish:

- Checked chunk widths and exact ordered SHA-256 input construction.
- Actual branch and multiproof refusal for the stated shape, width and
  resource conditions.
- Single-branch calculation through the existing ordered fold.
- A successful frontier step consumes two nodes and inserts their parent,
  reducing its length by one.
- Conditional preservation of agreement with a finite mathematical Merkle
  tree, followed through the actual byte-level multiproof calculation.
- Both public `verifyByte*` results return the corresponding calculated
  root, and their `matchesRoot` result is true exactly when the calculated
  bytes equal the supplied expected bytes.

The finite-tree theorem assumes that the supplied frontier agrees with
the tree and that parent values follow the pair-hash recurrence. It does
not assume the returned root. General completeness of helper admission
and reconstruction remains open, as do full FIPS refinement, collision
resistance and authenticity of the expected beacon root.

## Independent executable comparison

The permanent Python checker drives the compiled Lean executable. It
constructs trees independently and uses `hashlib` only for test answers.
Every expected root exists before proof extraction. Changed-node roots
are recomputed through a separate tree traversal.

The clean native executable matched **5,580 of 5,580 requests in each of
three runs**. Every run detected all 12 forged-output controls.

| Requests | Matching proof | Different root | Digest result | Refused | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| Single branches | 183 | 409 | 0 | 19 | 611 |
| Multiproofs | 1,740 | 3,038 | 0 | 27 | 4,805 |
| SHA-256 | 0 | 0 | 133 | 1 | 134 |
| Wire and recovery | 1 | 0 | 2 | 27 | 30 |
| Total | 1,924 | 3,447 | 135 | 74 | 5,580 |

This includes all **675 nonempty antichains** below the root of a
depth-three tree, both claim orders, and a separate change to each of
their 2,652 claimed-node positions: 4,002 cases in that group. There are
53 accepted empty-helper multiproofs. Further cases cover mixed depths,
32-byte width checks including the ambiguous 31+33 split, incorrect
witness counts/order, tampered roots, published NIST hash values,
padding boundaries, depth 64, 64 claims, and malformed-input recovery.

Duplicate JSON fields, including Unicode-escaped equivalent names, are
refused. The input layer also limits nesting and numeric-token length
before calling the standard JSON parser. The expected-root width check
is deliberately stricter than the pinned Python reference's comparison
of arbitrary byte strings.

Exact identifiers:

- Executable SHA-256:
  `d9f322f8bd18e5a9399bdc7d5d4f9e3c07e1224960e3329701c61f02de340eda`.
- Corpus SHA-256:
  `ebbee2378a01512eb1b520177eb54def35ce9e6a0c70c56ebab5f330ff5c18fb`.
- Checker SHA-256:
  `6864283088187b0056b0b3868b224a51fb23fd34b0434af42f2bb59ec2873af6`.

[Run 1](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/native-run1.json),
[run 2](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/native-run2.json)
and [run 3](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/native-run3.json)
include all raw per-request timings in corpus order and the request and
response stream hashes.

## Timing and resource bounds

In the three sequential, timing-locked runs, JSONL round-trip latency was
0.098–0.101 ms at p50, 0.172–0.200 ms at p95 and 0.286–0.352 ms at p99.
The maximum was 197–217 ms in each run, from the depth-64, 64-claim
multiproof with 3,712 helpers. These measurements include pipe and runtime
costs and are not network or full-client performance figures. The previous
positional CLI did not compute byte-level SHA-256 proofs, so it does not
provide a like-for-like cryptographic baseline.

The CLI permits at most 64 claims and depth 64, with lower caller-selected
limits. Hash-only requests are limited to 65,536 bytes. These are local
resource policies, not Ethereum consensus validity rules. The standard
input reader allocates the line before enforcing the 1 MiB payload limit.
Wire decoding can precede the core caps, and list lengths take linear
work even when the request is subsequently refused. The bound on
reconstruction attempts does not cover those initial costs.

## Build, dependencies and retained checks

A clean Linux build of both library targets and all eleven executable
targets passed under an 8 GiB virtual-memory cap, with two Lean threads
and a 64 MiB Lean thread stack. The initial attempt to build all targets
together hit `INTERNAL PANIC: out of memory`. Building the libraries first
and then executables one at a time passed under the unchanged cap. No
product process failed in the recorded executable comparison. The failed
build's complete log was overwritten during retry preparation; its
[failure record](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/build-attempt1-summary.txt)
contains only the observed failure, not a complete trace.

The [dependency audit](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/dependencies.json)
passed for 27 source and 27 compiled modules. The Lake manifest is empty.
The native link includes the pure SHA-256 object and defined Lean hash
symbol. Its six dynamic dependencies are standard Linux runtime libraries.
The approved Lean toolchain supplies dormant `-lcrypto` and `-lssl` flags;
the executable has no global definitions shared with those toolchain
archives. The audit records this distinction and does not claim that the
compiler/runtime contains no third-party code. Seven source dependency
mutation controls were rejected.

All ten retained consensus oracle suites passed:

- Generalised indices: 1,025 rows.
- Checked branches: 1,025 rows, including the existing malformed-length
  checks.
- Latest messages: 2,048 rows.
- Vote store, attestation score, computed proposer boost, checked ancestry,
  child selection and stored head: 1,024 rows each.
- Multiproof helpers: 2,048 rows and three comparator controls.

The existing 13-statement helper axiom ledger also passed unchanged.
[Retained results](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/retained-regressions.json)
and [actual byte/SHA-2 axiom output](../formal/lean4/ethereum-consensus/evidence/2026-11-23-byte-proofs/axioms.log)
are recorded separately from the new differential suite.

## Repeat the checks

Use the pinned Lean 4.33.1 toolchain. Run Lake commands with
`formal/lean4/` as the explicit working directory. Build under the shared
lock and resource limits required by `AGENTS.md`.

```bash
lake -d ethereum-consensus build EthereumConsensus FactoidalSHA2
lake -d ethereum-consensus -v build ssz-byte-proofs > byte-proof-build.log 2>&1
python3 ethereum-consensus/scripts/check-byte-proofs.py \
  ethereum-consensus/.lake/build/bin/ssz-byte-proofs --report byte-proof-report.json
python3 ethereum-consensus/scripts/check-pure-lean-dependencies.py --self-test \
  --build-dir ethereum-consensus/.lake/build --toolchain-root "$(lean --print-prefix)" \
  --binary ethereum-consensus/.lake/build/bin/ssz-byte-proofs \
  --link-log byte-proof-build.log --report byte-proof-dependencies.json
```

The workflow also elaborates the selected theorem files explicitly,
checks the source-pinned axiom ledger, runs every retained suite and
uploads the compiler, dependency and differential evidence. At this
worknote's first publication, the results above are local Linux evidence;
the PR records the subsequent hosted run. This work is a draft stack, not
a main-branch merge or completion of the full Ethereum client goal.
