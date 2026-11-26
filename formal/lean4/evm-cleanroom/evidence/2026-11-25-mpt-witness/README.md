# Independent Lean state-witness evidence

Tracking: [issue #1043](https://github.com/danbri/factoidal-core/issues/1043).
Predecessor: `40c3f0335501677d782df566ef7fd1e8a5cc4ad5`, draft PR #870.
[Design, schemas and remaining obligations](../../../../../docs/20261125-evm-witness-admission.md).

This checkpoint authenticates initial account and storage observations under
the supplied parent state root before entering the actual ordered transaction
runner. It does not authenticate signed transaction senders, select a canonical
chain, construct the post-state root in Lean or complete the full Ethereum goal.
The explicitly accepted experimental Keccak and compiler/runtime remain trust
boundaries.

## Observed checks

| Check | Result and scope |
| --- | --- |
| Native primitive and state admission | 189 passed, 0 failed; 20 comparator corruptions detected |
| Ordered transaction-list integration | 36 matched outcomes: 30 complete executions, 5 first-index rejections, 1 explicit unsupported execution boundary |
| Integration invocations | 114: three modes for 36 lists, plus six native admission controls |
| Retained signed input inventory | 344 transaction occurrences; 327 transactions in accepted lists |
| Exact historical input reconstruction | All 30 executed requests reproduce their original request SHA-256 before the parent-root substitution |
| Corrupted witness controls | Five refusals before deliberately zero-fuel execution; no accepted partial result |
| Present-empty account control | Authenticated presence preserved; executor profile explicitly refused |
| Evidence join falsification | Altered reference rejection index and category detected |
| Legacy list transport | All 22 existing controls passed, including exact/over input-byte limits |
| New Lean statements | 32 compiled: 8 RLP, 6 MPT, 18 witness/execution linkage |
| RLP executable guards | 22 passed during compilation |
| Source/axiom audit controls | 19 corruptions detected; all 292 predecessor claim records preserved |
| Native runtime controls | 17 corruptions detected; old binaries rejected and final binaries accepted |
| Before/after execution parity | All 189 corpus stdout hashes and all 36 list outcomes identical |

## Native runtime boundary

The final executables initialise the ordinary Lean runtime and their reviewed
JSON/data modules. They do not link the elaborator, compiler, type checker,
JSON elaborator initialiser or full Lean bootstrap. Mathematical proof terms
are erased; Ethereum witness verification still runs the compiled byte checks,
hashing and trie traversal.

| Executable | Before runtime pruning | Final |
| --- | ---: | ---: |
| `evm-transaction-list` | 121,089,912 bytes | 6,970,160 bytes |
| `evm-witness-proof` | 120,632,352 bytes | 6,505,840 bytes |

`runtime-boundary.before-pruning.json`, the intermediate
`runtime-boundary.json-import-only.json`, and
`runtime-boundary.after-pruning.json` preserve the investigation. Narrowing
JSON imports alone did not stop full prover initialisation. The two reviewed
build configurations select the ordinary runtime initialiser; the source
audit pins that startup flag and the exact standard-library source closure.
`runtime-gate.json` verifies actual executable symbols and direct libraries,
with 17 falsification controls in `runtime-gate-controls.json`. Exactly seven
known `Init.MetaTypes` default values are permitted as BSS data, not functions.

These are static native/source checks plus concrete execution tests, not a
proof of startup correctness or of every possible dynamic action. The
attempted syscall trace was denied by the environment's `ptrace` policy.
Compiler, C compilation, native initialisation and ordinary runtime services
remain explicit trust boundaries.

## Final measured process timings

The refreshed benchmark checks complete outputs on every invocation: six
warmups and thirty measured rounds for each of three modes and two fixtures,
using balanced mode order. All 216 invocations matched; no outliers were
removed. Median fresh-process times are:

| Fixture | Predecessor decoded | Current decoded | Current authenticated |
| --- | ---: | ---: | ---: |
| Single blobhash | 33.374 ms | 8.117 ms | 12.165 ms |
| Maximum 256 entries | 41.813 ms | 13.885 ms | 20.035 ms |

The benchmark includes startup, input, JSON, execution and output on a shared
host. It is neither a full-client throughput measurement nor an isolated hash
benchmark. The raw samples, p95, maximum and paired differences remain in
`mpt-benchmark.json`; the paired median authentication additions over current
decoded mode are 4.363 ms and 6.584 ms. Previous acceptance and benchmark
reports are retained separately under `*-before-runtime-pruning.json`, and
`mpt-runtime-output-parity.json` records the complete before/after comparison.

## Detailed records

The complete native records remain in the parent evidence directory:

- [`mpt-native-results.json`](../mpt-native-results.json)
- [`mpt-authenticated-list-results.json`](../mpt-authenticated-list-results.json)
- [`mpt-generated-fixtures.json`](../mpt-generated-fixtures.json)
- [`mpt-sources.json`](../mpt-sources.json)
- [`mpt-benchmark.json`](../mpt-benchmark.json)

The native fixture inventory includes all 54 pinned official RLP vectors, all
three independently reconstructed published secure-trie roots, and the three
retained real Frontier account proofs. Structural, malformed, resource,
proof-bag, code/storage-binding and JSON ambiguity cases are separate groups
with exact counts in the report. The source notes retain the upstream license.

## What was freshly executed

The final native binaries were built with Lean 4.33.1 from the new source;
`native-build.log` records the completed 66-job target set. The old decoded
runner was independently rebuilt from an archive of the predecessor commit;
`baseline-build.log` records that build. No compiled artifacts were copied
between the two trees. `rlp-guards-build.log` records the direct RLP guard
build, and `legacy-list-transport.json` is the unchanged 22-case transport
suite run against the final new binary.

The list harness constructs new state and storage proofs using the existing
locked test-only EthereumJS library. It calls the old decoded binary, the
current decoded mode and the current authenticated mode. Complete outputs
must match modulo schema version. It also checks every receipt and an
independently recomputed final state root against the retained November 24
Geth/EthereumJS evidence. **Those execution clients were not rerun here.**
Signature recovery in this harness is an independent test-oracle operation,
not a Lean signature-authentication claim.

The six refusal/boundary fixtures did not retain their original declared
final execution-gas total. Their reconstruction uses the valid block-gas
limit, leaving signed bytes, prestate and expected first rejection fixed.
They are not included in the 30 byte-exact original-request reconstructions.

## Source and proof binding

`witness-axioms.json` and `axiom-transcripts/` record actual re-elaboration
of all 32 added statements. `witness-axiom-controls.json` challenges missing
and extra theorems, changed or duplicate axioms, `sorryAx`, changed source,
external implementation imports and changes to the retained claim inventory.
The dedicated checker keeps all 292 predecessor claim records unchanged and
pins the transitive sources of both new native entry points. The active
ledger monitors 170 package files; the dedicated runtime import record also
pins 422 standard-library modules, including 14 `Lean.*` data/helper modules.

The expanded active selection has 324 claims. A local audit of the 32 new
claims is distinct from the complete active audit in the existing hosted
workflow. `source-ledger.json` is a source consistency check, not a theorem
proof. The supplemental `witness-source-manifest.json` pins workflow and audit
sources as well as the native source closure. The dependency manifest remains
empty and the compiler remains `leanprover/lean4:v4.33.1`.

`tail-audit.json` and `tail-audit.txt` describe the generated-C files actually
present in this isolated package's build. They check surviving native recursion
in that artifact set, not every source file in the repository and not total
heap use. Source-level budgets and explicit resource refusal remain separate
obligations. The standalone verifier admits 128 nodes of up to 4,096 bytes and
uses at most 65 secure-path visits; the higher-level inventory adds aggregate
limits before hashing.

`provenance.json` and `SHA256SUMS` bind the retained files and binary/compiler
identities. Run `sha256sum --check SHA256SUMS` from this directory. Local
pre-publication reports truthfully retain the predecessor HEAD metadata;
the source pins describe the changed working files. The separate
`witness-axioms-published-head.json` and `axiom-transcripts-published-head/`
freshly check all 32 additions with `--require-head` against published source
[`aeff0b2122bd02eeba2fc44e3b63bbd67fdf6afc`](https://github.com/danbri/factoidal-core/commit/aeff0b2122bd02eeba2fc44e3b63bbd67fdf6afc),
tree `e54488419fd7a2b1a6e8f417cf0d3a759db73b19`.
`runtime-gate-published-head.json` is bound to that exact audit and passes
both final executables. This evidence update does not change production
source, configurations, harnesses or source pins.

## Reproduce

Follow the pinned build and native harness commands in the linked design
note. From the isolated package directory, run the dedicated source/axiom
audit after building both executables:

```sh
python3 scripts/check-active-ledger.py
python3 scripts/check-witness-axioms.py --selftest
python3 scripts/check-witness-runtime.py --selftest
flock /tmp/ethereum-mpt-lean.lock python3 scripts/check-witness-axioms.py \
  --require-head --out /tmp/witness-axioms.json \
  --transcripts-dir /tmp/witness-axiom-transcripts
python3 scripts/check-witness-runtime.py --axiom-report /tmp/witness-axioms.json \
  --out /tmp/witness-runtime.json
```

The checker invokes Lake from `formal/lean4` with `-d evm-cleanroom`. Add the
freshly built predecessor binary with `--baseline-bin PATH` to the list
harness to reproduce the 114-call comparison. Without that optional binary,
CI runs the two current modes and six native controls, for 78 calls. The
benchmark script documents its separate paired measurement invocation and
does not impose a noisy timing threshold on CI.

## Retained raw whitespace

`whitespace-check.json` records the source checkpoint staged check. New source and configuration
files have no whitespace errors. Eight exact raw-artifact paths retain
upstream fixture spacing, compiler transcript blank lines or disassembler
spacing so their recorded bytes are not rewritten.
The three later published-head transcripts retain the same compiler-emitted
final blank lines as their original counterparts.
