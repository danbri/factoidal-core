---
title: "Ethereum Implementation and L2 Readiness"
description: "Ethereum execution and consensus evidence, Prague test coverage, Polygon and L2 readiness, acceptance criteria and next engineering tasks."
layout: hub-tracker.njk
permalink: /web/hub/ethereum-implementation/
---

# Ethereum Implementation and L2 Readiness

[Current evidence](#current-evidence-and-blockers) · [Prague cases](#prague-coverage-and-the-two-omitted-cases) · [Protocol work](#protocol-implementation-workstreams) · [Polygon and L2](#polygon-and-l2-readiness) · [Executable checks](#existing-executable-checks) · [Next tasks](#next-engineering-tasks)

**Evidence snapshot: 23 November 2026.** The goal is a fully working Ethereum implementation with protocol-critical execution and consensus logic in Lean 4, plus usable, tested Ethereum and L2 application integration. The governing acceptance criteria are in [issue 725](https://github.com/danbri/factoidal-core/issues/725).

**Current position:** hosted CI supports several real execution and replay results, including all six selected Prague fixtures and an authenticated historical contract transaction. Full Ethereum conformance, a working execution and consensus node, and live signed Polygon/L2 transactions remain incomplete or unverified. The relevant implementation branches are draft and unmerged. Application integration and native protocol implementation have separate acceptance gates.

The initial priorities come from the recent Ethereum L2 support and assurance requests: finish both omitted Prague cases, continue to full Ethereum execution and consensus, make real network interaction usable, and establish exactly what Polygon/L2 support requires. The next engineering step is to repair the release and evidence gates, reproduce the checked baseline, then extend the authenticated transaction path.

## How to read status

| Status | Meaning |
| --- | --- |
| Recorded pass | Actual hosted test output was inspected for a named revision and scope. It is not a fresh local rerun or a full-protocol claim. |
| Model proof checked | The named Lean proposition compiles at the pinned revision, with inspected actual axiom output containing only declared permitted axioms and no `sorryAx`. Normative specification correspondence and executable linkage need their own evidence. |
| Reported | Source or a prior report describes a result, but the complete supporting execution evidence has not been checked. |
| Unverified | The necessary repository, artifact, execution result or network evidence is unavailable or insufficient. |
| Blocked or incomplete | A known failing gate, missing dependency or unfinished protocol feature prevents the stated acceptance criterion. |

An unimplemented feature must remain distinguishable from a consensus-invalid input. Host or tooling resource exhaustion, absent witnesses and unavailable history are indeterminate outcomes. EVM out-of-gas is a protocol-defined execution result. Neither parsing a fixture nor refusing it establishes execution conformance. Coverage percentages require a pinned, enumerated denominator.

## Current evidence and blockers

Execution evidence is pinned to [PR 798](https://github.com/danbri/factoidal-core/pull/798), head `d1005fb7a009e9c8942f5f74517e068b66fb5f48`. Its tested merge commit has the same Git tree. Recorded passes apply to that tree, not automatically to later commits or the public Hub runtime.

| Capability | Evidence and scope | Current assessment |
| --- | --- | --- |
| Selected Prague state tests | [Hosted real-state log](https://github.com/danbri/factoidal-core/actions/runs/45085809038/job/137404033546): 6 executed, 6 passed, 0 failed, 0 unsupported; all expected state roots checked. | Recorded pass for six EIP-7623 fixtures only. Both formerly omitted cases are included. |
| Selected Cancun state tests | The same log records 6 passed, 0 failed, 0 unsupported in a 24-case multi-fork fixture. | Recorded pass for the six Cancun cases; 18 other-fork cases were not executed. |
| Historical Frontier replay | [Frontier workflow](https://github.com/danbri/factoidal-core/actions/runs/45085808980) passes authenticated transaction and block-root checks for block 46,147, with independent Python evidence. | Recorded pass for that bounded historical replay; broad chain replay remains incomplete. |
| Historical deployed-contract transaction | [Shanghai replay evidence](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/docs/20261122-evm-shanghai-contract-replay.md): index-zero 1CAT transfer in block 19,100,013; Lean, EthereumJS and Geth agree on status, 33,987 gas, 4,800 refund gas, one Transfer log and account effects. The hosted replay step passes. | Recorded pass. The intermediate world root is derived for one transaction; it is not the published final-block world root. |
| Ordinary signed contract calls | The [EVM workflow](https://github.com/danbri/factoidal-core/actions/runs/45085809038) enforces 60 Shanghai/Cancun type-0/1/2 comparisons with exact receipts and state roots, plus admission, boundary and comparator controls. | Recorded pass within the implemented transaction slice. General transaction and block support remains incomplete. |
| RPC and deployed-code reads | The same workflow enforces 46 offline RPC tests and captured mainnet deployed-code authentication. | Recorded pass for captures and offline checks. No fresh endpoint-availability or live-broadcast claim. |
| Lean assurance | [PR 798 evidence](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/docs/20261122-evm-call-transaction-evidence.md) records 172 selected claims across 20 files; the dedicated Lean job passes. | Model proof evidence. Full EELS refinement, cryptographic refinement and whole-client correctness remain open. |
| Execution integration and release | [Broad Lean workflow](https://github.com/danbri/factoidal-core/actions/runs/45085809620) passes. [Package workflow](https://github.com/danbri/factoidal-core/actions/runs/45085808978) fails because no matching ancestor web release is available in factoidal-builds; package tests are skipped. The dataflow job passes. | Blocked. PR 798 remains draft/unmerged; a verified released-main baseline is not established. |
| Consensus scoring slice | [PR 816](https://github.com/danbri/factoidal-core/pull/816), head `174d0173f6e868b5b36d84aad623c7903ab3e1cc`: [dedicated CI](https://github.com/danbri/factoidal-core/actions/runs/45104335434) checks 1,024 Lean scoring cases against a Python reference with zero mismatches. | Recorded pass for synthetic scoring. Full consensus is incomplete; [broad Lean CI](https://github.com/danbri/factoidal-core/actions/runs/45104335427) fails its compiled-recursion/compiler-replacement gate. Draft/unmerged. |

### Trust boundary

At the checked execution revision, the host still supplies signed-envelope decoding, sender recovery, header and Merkle Patricia trie verification, receipt encoding and trie updates. Providers supply canonical chain selection. The native Keccak path requires `--dangerously-enable-unverified-keccak`; independent cryptographic refinement and constant-time assurance remain open. These dependencies are explicit in [SOUNDNESS](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/formal/lean4/evm-cleanroom/SOUNDNESS.md).

The consensus branch's checked-branch examples use arithmetic pairing rather than cryptographic SSZ hashing. Eligibility, ancestry, balances and authentication are externally supplied in the scoring slice. It does not establish BLS verification, signed-attestation admission, beacon transitions, finality or a complete fork-choice head algorithm.

## Prague coverage and the two omitted cases

The old 4-passed/2-unsupported result is a historical checkpoint. The checked current six-case run closes those two fixture omissions. It does not close all EIP-4844, EIP-7702 or Prague implementation work.

The [pinned upstream fixture](https://github.com/ethereumjs/execution-spec-tests-fixtures/blob/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json) has SHA-256 `9afff783c1365a2743662353b88f8938d6171fa764184902053ad20ec3539cd4`. Every ID below uses this exact common prefix:

```text
tests/prague/eip7623_increase_calldata_cost/test_eip_mainnet.py::test_eip_7623[fork_Prague-state_test----
```

| ID suffix | Recorded result | Scope and remaining work |
| --- | --- | --- |
| `type_0_protected]` | Passed, expected root matched | Protected legacy envelope within this empty-code fixture. |
| `type_0_unprotected]` | Passed, expected root matched | Unprotected legacy envelope within this fixture; no blanket acceptance policy for live submission. |
| `type_1]` | Passed, expected root matched | Access-list envelope in the selected fixture. |
| `type_2]` | Passed, expected root matched | Dynamic-fee envelope in the selected fixture. |
| `type_3]` | Previously omitted; now passed, expected root matched | EIP-4844 accounting at zero excess blob gas. General blob-price contexts, KZG, BLOBHASH, point evaluation and fork-appropriate sidecar/data-availability validation remain unverified/incomplete. |
| `type_4]` | Previously omitted; now passed, expected root matched | One new authority with delegation-code and nonce updates, without executing delegate bytecode. General authorization combinations and delegated execution remain unverified/incomplete. |

The [six-case checker](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/formal/lean4/evm-cleanroom/scripts/check-prague-six-ledger.py) requires all six IDs, six actual executions, zero unsupported cases, and agreement among calculated roots, fixture roots and separately pinned expected roots. The two formerly omitted expected roots are:

```text
type_3  0xb1b71e9e7b952746963d29d13179fcb171b3fb26afa8aa09b46788d3e6fb1fea
type_4  0xc54c35114b8064c991bc8ed66d3065e9f3ba4f07e6c196b7d396b29b382b5d32
```

**Regression gate:** retain the nine [fixture controls](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/formal/lean4/evm-cleanroom/scripts/eels/prague-all-selftest.mjs): altered versioned hash, blob fee cap, type-3 root, nonzero excess-blob context, authority signer, authorization signature, delegation code, type-4 root and missing type-4 case. Retain the six ledger mutations covering roots, pass count, missing case, blob burn, authority nonce and unsupported count. Refusal of the nonzero-excess case records the current limitation; implementing that case requires a positive conformance test.

**Expansion acceptance:** pin the official corpus and fork; enumerate applicable cases; add nonzero blob-price contexts, malformed/invalid authorizations, existing authorities, nonce/chain-ID boundaries, duplicate authorizations and actual delegated execution. Compare the specification-required outcomes, including ignored authorization tuples where appropriate, rather than treating every malformed tuple as rejection of the whole transaction. Use [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844), [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702) and [EIP-7623](https://eips.ethereum.org/EIPS/eip-7623) as normative anchors and version-pin their execution-spec implementation.

For type 4, test whole-transaction invalidity for an empty authorization list, null destination and invalid tuple field shapes/bounds. Separately test tuple-processing failures such as wrong chain ID, failed signature recovery, disallowed authority code and nonce mismatch, which skip that tuple. Successfully processed delegations persist when subsequent EVM execution reverts. Pin later-fork changes separately.

## Protocol implementation workstreams

These exit criteria implement the [full-client acceptance epic](https://github.com/danbri/factoidal-core/issues/725), [external conformance work](https://github.com/danbri/factoidal-core/issues/649) and [assurance programme](https://github.com/danbri/factoidal-core/issues/654). Unlisted capabilities are unverified, not implicitly supported.

### Fork coverage baseline

| Fork scope | Established evidence | Full-fork status |
| --- | --- | --- |
| Frontier | One authenticated historical transaction/block replay. | Incomplete. |
| Historical forks between Frontier and Shanghai | Coarse profiles and selected operations are described in SOUNDNESS; no complete per-fork corpus result is established here. | Unverified. Enumerate each fork and its activation separately. |
| Shanghai | Selected type-0/1/2 contract-call comparisons and the authenticated historical contract transaction. | Incomplete. |
| Cancun | Six selected state cases and the ordinary contract-call slice. | Incomplete; 18 other-fork cases in the selected fixture remain unexecuted. |
| Prague | Six EIP-7623 state cases spanning envelope types 0–4. | Incomplete; six fixtures are not the complete Prague corpus. |
| Osaka/Fusaka and subsequent activated changes | The acceptance epic requires these; no complete corpus, activation or node-compatibility evidence is established here. | Unverified. Resolve the mainnet-active configuration from pinned canonical sources. |

### Workstream exit criteria

| Workstream | Remaining engineering work | Acceptance evidence |
| --- | --- | --- |
| Fork selection | Replace coarse profiles with explicit fork-indexed execution, transaction and block rules; pin historical activations through the mainnet-active fork and relevant later activated parameter changes. | Machine-readable fork/EIP matrix; boundary tests immediately before and after activation; no future rules leaking into earlier forks. Prague must not stand in for current mainnet. |
| Whole EVM | Complete CALL variants, CREATE/CREATE2, precompiles, environment, gas, warmth/refunds, transient/persistent storage, rollback and fork-specific destruction rules. | All applicable official opcode/frame fixtures; independent gas, exception and state comparisons; code-linked refinement theorems for the claimed operations. |
| Signed transactions | Complete all fork-valid envelopes, signature and admission checks, fee/value/nonce accounting, blobs and authorization/delegation semantics. | Exact receipts, logs, state roots and rejection/indeterminate classifications; malformed encodings and boundary cases; no host execution fallback counted as Lean execution. |
| Blocks and authenticated state | Validate headers and ordered transactions; implement trie/state persistence, withdrawals and fork-specific system operations; carry authenticated pretransaction state across a whole block. | Published full-block state/receipt roots reproduced across forks; missing/forged witness controls; crash/restart and reorg tests. |
| Proof connection | Independently specify reference transitions and connect parsing, normalized input and actual dispatcher to the theorems. | Per-claim statement, source/spec SHA, actual axiom output, executable link, assumptions and adversarial counterexamples; external review of correspondence. |
| Execution node | Engine API, JSON-RPC service, txpool, sync, networking, durable state and authenticated forkchoice handling. | Interoperability with mature execution/consensus clients; valid/invalid/syncing payload scenarios, restart and reorg recovery; no incomplete state labelled invalid. |
| Consensus node | Cryptographic SSZ and BLS, signed input admission, beacon transitions, fork choice, justification/finalization, networking and EL/CL integration. | Pinned official consensus fixtures, differential client results and replay across consensus forks; explicit cryptographic and synchrony assumptions. |
| Robustness and release | Repair required gates, package a reproducible build, measure resource limits/performance and retain evidence. | Clean-host reproduction, hostile-input/fault tests, deterministic replay, reviewed trust ledger and durable artifacts. A subset pass cannot close the whole-client goal. |

## Polygon and L2 readiness

Ethereum-style RPC access, locally executing a contract, submitting a transaction and independently validating an L2 are different capabilities. Each network needs a pinned chain ID, active release/fork configuration, RPC capabilities, gas currency, contract addresses and finality policy.

| Target | Evidence in Factoidal | Next gate |
| --- | --- | --- |
| Polygon PoS and Amoy | The inspected [manifest](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json) contains Polygon mainnet synthetic state-override captures. The Amoy call probe returned error code 1; comparison is unverified. | Start with Amoy `80002`, POL; mainnet is `137`, POL. Test real deployed-code reads, signing, receipts and state changes. Treat Bor/Heimdall-v2 implementation as a separate native-client project. |
| Polygon zkEVM Mainnet Beta | Retired network, not an active transaction target. | Archival/recovery work only if needed. Polygon states that block production ended on 3 July 2026. Do not plan ordinary deployments or bridge transfers there. |
| OP Stack | The manifest records synthetic OP Sepolia overrides and one deployed `decimals()` comparison, returning 6; the latter remains provider-asserted, not authenticated chain/state evidence. | Pin one named testnet/deployment. Verify real contract reads/writes, execution plus L1-data and applicable operator fees, and unsafe/safe/finalized transitions. Add deposits, withdrawals and derivation separately. |
| Arbitrum | No inspected Factoidal execution or live transaction result establishes integration readiness. | Start with Arbitrum Sepolia `421614`; One is `42161`. Pin Nitro/ArbOS rules; test fees, precompiles and messages, with sequencer confirmation, L1 data finality and assertion settlement recorded separately. |

Network sources: [Polygon architecture](https://docs.polygon.technology/pos/architecture/overview), [Polygon network configuration](https://docs.polygon.technology/pos/reference/rpc-endpoints), [zkEVM retirement](https://polygon.technology/polygon-zkevm), [OP fees](https://docs.optimism.io/op-stack/transactions/fees), [OP transaction statuses](https://docs.optimism.io/app-developers/guides/transactions/statuses), [Arbitrum chain configuration](https://docs.arbitrum.io/chain-info), [Arbitrum finality](https://developer.arbitrum.io/how-arbitrum-works/deep-dives/finality).

Polygon PoS uses Bor execution and Heimdall-v2 consensus with Ethereum checkpointing; ordinary Polygon application support does not establish Ethereum rollup implementation. For every rollup, verify its deployed fork and opcode/precompile set rather than inferring complete Prague compatibility from an EVM-compatible label.

**Bridge gate:** a successful contract call does not establish a completed cross-chain transfer. Retain L1 and L2 transaction hashes, message identity, token mapping, deployed bridge-code identity, proof/claim data, finalization status and reconciled balances. Exercise invalid proofs, duplicate claims, retries and reorgs. Full native L2 support additionally requires the relevant derivation, execution and settlement rules; generic Ethereum fixtures cannot establish those rules.

## Gates for real Ethereum interaction

| Gate | Required executable demonstration | Status |
| --- | --- | --- |
| G0 Reproducible baseline | Clean checkout of the recorded revision; build, exact axiom audit, selected state tests and replay; all required packaging gates green; published binary linked to source. | Execution evidence exists; release/package gate blocked. |
| G1 Reliable real reads | At a fixed block hash, obtain chain identity, code, balance, nonce, storage, calls, logs and receipts; retain transcripts and verify available proofs. Name the header/canonicality trust anchor. | Captured Ethereum examples exist. Fresh connectivity and a production read path remain unverified. |
| G2 Signed testnet transaction | On a selected Ethereum testnet, sign and broadcast a controlled transfer and state-changing contract call; verify raw bytes/hash, nonce, receipt, gas, logs and resulting state independently. | Unverified. Local replay of a historical signed transaction does not establish this path. |
| G3 Contract lifecycle | Deploy a minimal contract and test token; execute read/write/transfer, revert and out-of-gas cases; exercise CALL variants and creation against independent clients. | Partial call replay exists; deployment and full lifecycle remain incomplete/unverified. |
| G4 Polygon and active rollup | Run the application harness on Amoy and one named active rollup testnet, with network-specific fees, finality and failure handling. | Unverified; repair the failed Amoy probe first. |
| G5 Broad authenticated replay | Replay complete blocks and multi-block ranges across fork boundaries and current chain, using authenticated prestate; compare published roots and at least two mature client implementations. | One Frontier block and one Shanghai contract transaction are bounded evidence; broad replay incomplete. |
| G6 Full client operation | Meet every execution and consensus criterion in issue 725, including interoperability, persistence, sync, cryptography and independent review. | Incomplete. RPC integration does not close this gate. |

For G2–G4, include wrong chain ID, invalid signature, stale nonce, insufficient balance, fee-cap failure, revert, out-of-gas, duplicate submission, timeout, provider disagreement and reorg controls. Status must distinguish submitted, included and finalized. A retry must not cause an unintended second state change. Future testnet runs need an explicitly configured signer and test funds; this tracker makes no live-send or mainnet-spending claim.

## Existing executable checks

These commands are present in the [pinned EVM workflow](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/.github/workflows/evm-cleanroom.yml). They were inspected, not rerun while preparing this tracker. Use the exact PR 798 revision, Lean 4.33.1 and Node 22. Follow the workflow's pinned dependencies and explicit working directories.

From `formal/lean4`:

```sh
lake -d evm-cleanroom build evm-subset evm-call-transaction
```

From `formal/lean4/evm-cleanroom`, install the workflow's EELS dependencies, obtain the pinned fixture and execute it:

```sh
npm install --prefix scripts/eels --ignore-scripts --no-audit --no-fund
printf '2f5caf7dd31ee1d2b36290788e509110955005c28302ed0f038dadbc2bf6c6c7  scripts/eels/package-lock.json\n' | sha256sum --check
mkdir -p .lake/eels
curl --fail --location --silent --show-error \
  'https://raw.githubusercontent.com/ethereumjs/execution-spec-tests-fixtures/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json' \
  -o .lake/eels/eip7623.json
printf '9afff783c1365a2743662353b88f8938d6171fa764184902053ad20ec3539cd4  .lake/eels/eip7623.json\n' | sha256sum --check
node scripts/eels/run-lean-prague-all-types.mjs \
  --fixture .lake/eels/eip7623.json \
  --out .lake/eels/lean-prague-all-results.json
python3 scripts/check-prague-six-ledger.py .lake/eels/lean-prague-all-results.json
node scripts/eels/prague-all-selftest.mjs .lake/eels/eip7623.json .lake/eels/negative-controls
```

Continue in `formal/lean4/evm-cleanroom`:

```sh
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py --selftest
python3 scripts/check-axiom-output.py
node scripts/eels/call-transaction-differential.mjs "$PWD/.lake/build/bin/evm-subset"
```

For the three-engine historical contract replay, supply the pinned Geth `evm` executable through `EVM_GETH_EXE` and run from the same directory:

```sh
node scripts/eels/replay-authenticated-contract.mjs \
  evidence/historical-1cat-shanghai-19100013.json \
  "$PWD/.lake/build/bin/evm-call-transaction"
```

The workflow pins `geth-alltools-linux-amd64-1.17.10-1df30b18`, archive SHA-256 `f991c32e5b7bb68db97a1b06d50c7c06f6aa9ae84d8f6f9b2301dc02cad2a7cf`. The replay explicitly opts in to the unverified Keccak implementation; record that assumption with the result.

For the offline RPC suite, return to `formal/lean4`:

```sh
EVM_RPC_TEST_LEAN_EXE="$PWD/evm-cleanroom/.lake/build/bin/evm-subset" \
  node --test --test-reporter=tap evm-cleanroom/scripts/rpc/capture.test.mjs
```

G1–G6 expansion tests above are acceptance specifications, not claims that commands or working implementations already exist.

## Next engineering tasks

Task ownership is unassigned until claimed. Completing a task requires a source revision and linked evidence; editing a checkbox alone cannot establish readiness.

- [ ] **P0 Evidence reconciliation.** Update the current presentation in the EELS README, active manifest, root README and SOUNDNESS. Preserve the historical 4/2 record, clearly select the current 6/0 result, replace stale pending-CI annotations with revision-scoped outcomes, and record the package failure. **Exit:** one current count per declared scope; a consistency check fails on mismatched displayed counts. See [the stale EELS README](https://github.com/danbri/factoidal-core/blob/d1005fb7a009e9c8942f5f74517e068b66fb5f48/formal/lean4/evm-cleanroom/scripts/eels/README.md).
- [ ] **P0 Release and integration blockers.** Produce or identify the permitted matching factoidal-builds ancestor release, rerun package tests, and fix PR 816's compiled-recursion/compiler-replacement failure. **Exit:** the actual required jobs execute and pass on the exact proposed head; no skipped package tests described as success. Keep the two PR stacks and their dependencies explicit.
- [ ] **P0 Durable evidence and independent reproduction.** Preserve the real-state CI artifact before its 22 December 2026 expiry, verify its digest and contents, and reproduce G0 on a clean host. **Exit:** stable content-addressed archive plus commands, toolchain, binary digest, fixture inventory and complete results. The ZIP contents have not yet been inspected for this tracker.
- [ ] **P1 Extend the authenticated transaction path.** Add the next missing CALL variant and contract-creation path with fork-correct admission, rollback, gas, logs and receipts. **Exit:** official positive/negative fixtures and independent client agreement, with linked Lean refinement obligations; broaden G3 incrementally.
- [ ] **P1 Complete blob and authorization semantics.** Expand the two previously omitted transaction families beyond their six-case fixture scope. **Exit:** nonzero blob contexts and delegated execution pass applicable official fixtures; record remaining KZG/crypto assumptions without counting unimplemented cases as protocol-invalid.
- [ ] **P1 Make live application interaction reproducible.** Add chain-configured read, signer, submission, receipt/finality and retry handling; first prove G2 on an Ethereum testnet. **Exit:** an evidence bundle with exact bytes, hashes, state changes and failure controls. Keep live application integration separate from Lean-native protocol coverage.
- [ ] **P1 Polygon and rollup integration.** Diagnose the Amoy call error; prove G4 on Amoy, then one pinned OP Stack or Arbitrum testnet. **Exit:** real deployed-contract reads/writes with correct network fees/finality. Track bridge tests separately.
- [ ] **P1 Full fork and corpus inventory.** Pin upstream execution and consensus revisions and enumerate applicable tests, features and fork activations. **Exit:** every applicable case has an outcome; newly added upstream cases cannot silently disappear; final claimed scope has zero unexpected skips or unsupported features.
- [ ] **P2 Whole-block replay and node interoperability.** Complete G5, add Engine API/client integration and persistence/reorg recovery, then advance the remaining G6 consensus work. **Exit:** published full-block roots and interoperable node behaviour, not only selected transaction agreement.
- [ ] **P2 Independent assurance review.** Review normative model fidelity, serialization-to-executable linkage, cryptographic/runtime trust and hostile-input behaviour with Ethereum and Lean specialists. **Exit:** reproducible claim-by-claim evidence and tracked counterexamples under [issue 654](https://github.com/danbri/factoidal-core/issues/654).

## Evidence record and update rules

For every future result, record: claim and scope; repository/head and tested tree; build and binary digests; Lean/runtime/oracle versions; specification and fixture revisions/digests; exact command and working directory; complete selected/applicable inventory; passed, failed, unsupported and not-executed counts; expected/observed roots, receipts and logs; run/artifact links; negative controls; trust assumptions; merge/release state; owner and next action. Keep applicability exclusions separate from implementation gaps.

The execution tree checked here is `d513a1b22ac1983e3f606304d475fd87cf896a5d`: both PR head `d1005fb7a009e9c8942f5f74517e068b66fb5f48` and tested merge `e078baa0c445e277222491b5fcb477d1863db6a7` reference it. The [real-state artifact](https://github.com/danbri/factoidal-core/actions/runs/45085809038/artifacts/14779765098) is named `evm-eels-state-45085809038`, with recorded ZIP SHA-256 `e5985612afa494d79769cf9558b56897f56b6c7499f52319a7732633489d673b`. Metadata and logs were inspected; archive contents and a clean-host rerun remain outstanding.

On each update, check branch and CI state again. Retain old results as dated evidence; do not copy their pass status onto changed source. Mark inaccessible or missing evidence unverified. Do not infer merge, release, deployment, live connectivity or finality from another stage's success. This is an editable implementation tracker and does not itself schedule engineering runs.
