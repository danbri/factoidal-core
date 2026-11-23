# Independent Lean identity execution integration — 23 November 2026

Address `0x04` now uses the repository's independent Lean identity executor
through the actual CALL-family continuation, the public `CallOpcode.callStep`
entry, and direct `CallTransaction.run` transactions. This advances
[integration issue #838](https://github.com/danbri/factoidal-core/issues/838)
under the independent Ethereum [epic #725](https://github.com/danbri/factoidal-core/issues/725).
[PR #839](https://github.com/danbri/factoidal-core/pull/839) remains draft; this
worknote records local evidence, not a merge into `main` or a hosted-CI result.
Consult its [current checks](https://github.com/danbri/factoidal-core/pull/839/checks)
for the exact submitted revision.

The source revision, source hashes, compiler and executable SHA256 values belong
to the accompanying [provenance record](../formal/lean4/evm-cleanroom/evidence/2026-11-23-identity-integration/provenance.json).
Performance evidence is recorded separately in
[timing.json](../formal/lean4/evm-cleanroom/evidence/2026-11-23-identity-integration/timing.json);
passing semantic tests alone establishes no latency claim. The earlier
[standalone worknote](20261123-evm-identity-precompile.md) retains its original
revision and evidence attribution.

## Defects resolved and execution boundary

The incoming branch already dispatched identity from nested CALL opcodes. Three
remaining problems prevented treating that as complete integration of the
supported entry points:

1. **Raw oracle warmth:** EthereumJS `runCall` fixtures did not initialise the
   precompile warm-address set. [EIP-2929](https://eips.ethereum.org/EIPS/eip-2929)
   requires precompiles to start warm. The reference setup now seeds that set;
   an explicit cold-versus-warm control measures the expected **2,500 gas**
   difference.
2. **Public `callStep` bypass:** this helper entered child bytecode without the
   precompile branch used by the opcode loop. Both now share `precompileStep`,
   including successful output, out-of-gas rollback and resource refusal.
   Nine new CALL guards failed against the prior implementation and pass with
   the repair.
3. **Direct transaction refusal:** the transaction admission path refused every
   precompile, including identity. It now distinguishes unimplemented targets
   and routes address 4 through `CallTransaction.runFrame`. The existing fee
   escrow and settlement path commits value on success and restores it on
   exceptional failure. Existing account code at address 4 is ignored.

Identity costs `15 + 3 * ceil(inputBytes / 32)` gas. Nested execution retains
the existing memory-expansion charge, EIP-150 cap, value stipend, continuation,
output-window copy and world journal. Direct identity execution consumes no EVM
bytecode instructions, so it also works with zero instruction fuel. Ordinary
bytecode frames retain their instruction-fuel bound.

The integration accepts at most **1,048,576 input bytes (1 MiB)**. Exceeding this
local cap produces **indeterminate `resourceLimit`**, before gas classification;
it is not an Ethereum invalidity rule or a completed failed receipt. Missing
account/slot witnesses also remain explicit refusals. Other precompiles remain
unimplemented. The older `WorldCall.callZeroValue` and `WorldCall.callWithValue`
helpers retain their historical precompile refusal. Generic
`CallOpcode.execute`/`executeAtDepth` execute a supplied bytecode frame and its
nested opcodes; their root address is execution context, not a transaction
destination router. Direct identity transactions use `CallTransaction.run`.

All runtime changes are repository-owned **pure Lean 4.33.1**. The Lake external
package graph remains empty. No Ethereum implementation, EthLib, crypto package
or host executor was imported into the Lean implementation. Existing
EthereumJS and Geth installations are test oracles; no dependency was added.
Synthetic transactions use a public fixture key and execute offline. No live
transaction was submitted.

## Observed local results

The final native/library build passed **71 jobs**, including both new guard
modules. The following results are separate gates, not additive measures of
Ethereum coverage.

| Gate | Observed result |
| --- | --- |
| New CALL integration matrix | **660/660** match EthereumJS; **648/648** match Geth and agree across both clients. Geth explicitly excludes **4 static-entry** and **8 nonzero-entry-depth** cases; all 660 still execute against EthereumJS. Zero mismatches/errors. |
| Signed identity transactions | **84/84** match EthereumJS `runTx` and Geth `t8n`: **57 nested + 27 direct**, covering transaction types 0/1/2. Zero failed, unsupported, local-refusal or unexecuted cases. |
| New Lean guards | **26 pass: 16 CALL + 10 transaction**. These are executable tests, distinct from theorems. |
| Retained standalone identity corpus | **1,056/1,056**, unchanged: 528 successes, 176 out-of-gas results, 352 resource refusals; three comparator mutations and malformed-input rejection pass. |
| Retained CALL regressions | CALL opcode **330/330**; byte/context corpus **122/122** EthereumJS and **112/112** eligible Geth; CALL-family corpus **213/213** EthereumJS and **194/194** eligible Geth, plus its separate **27/27** identity probes; six repair cases pass. Existing exclusions remain explicit. |
| Retained signed call transactions | **60/60** receipt/state-root matches; eight independent admission rejections, one preserialization rejection, eleven boundary refusals and three comparator mutations pass. The former identity-refusal control now uses unimplemented ECRECOVER at address 1. |
| Published EELS Prague fixtures | **6/6** state-root matches, zero failed/unsupported; six ledger mutations and nine forged-envelope/delegation/root controls rejected. |
| Published EELS Cancun contracts | **6/6** state-root matches, zero failed/unsupported; fixture inventory **24**, with **18 other-fork cases** explicitly outside this run; four forgery controls rejected. |
| Authenticated Shanghai mainnet transaction, block **19,100,013**, index 0 | Lean/EthereumJS/Geth match: **33,987 gas**, **4,800 refund**, successful receipt, one log and expected return word; three authenticated accounts, four authenticated storage slots and six negative controls. |
| Authenticated Frontier block **46,147** | Three-account transaction intermediate root and final block root match, including the 5 ETH subsidy. Separate signed/header commitment gate passes six controls; independent repository Python reproduces both roots and passes 24 Keccak vectors plus six forgery controls. |

The raw matrix exercises all four CALL opcodes, word/gas boundaries, output
truncation and overlap, zero-length maximal-offset windows, address masking,
repeated calls, returndata, static context, depth, stipends and parent rollback.
Its four mutations change gas, success bit, returndata and copied memory.

The signed corpus adds direct observation of account 4, including value credit,
creation, rollback, hostile stored code ignored and storage preservation. Both
reference clients execute the same signed bytes. Lean receives a host-decoded
envelope and explicit synthetic witnesses through `--call-transaction`.
Complete outputs and host-constructed post-state roots are compared. Geth RPC
receipt fields are **host-reconstructed**; the independently returned Geth
`receiptsRoot` is also compared with the single-transaction trie built from
Lean's receipt. Four mutations and a missing-account-4 witness control pass.
Signature recovery, receipt encoding and trie construction remain trusted host
operations, not newly implemented Lean functionality.

## Proof inventory and assurance status

This change authors **19 theorem declarations**. The selected audit grows by
**32 declarations**, because previously existing identity/integration results
are also brought under that gate. The updated manifest selects **216 theorems
across 22 source files**, up from 184, and contains **112 source pins**, up from
103. The source-consistency gate and the complete actual-output audit both
passed. All 216 selected reports match the recorded axiom sets after fresh
Lean elaboration; the [audit result](../formal/lean4/evm-cleanroom/evidence/2026-11-23-identity-integration/active-axioms.json)
and five passing source-ledger tests are included with the provenance record.

The new declarations have compiled with actual `#print axioms` output. Their
dependencies are confined to `propext`, `Classical.choice` and `Quot.sound`;
some byte-view lemmas need none. The six new direct-transaction declarations
prove exact output/gas, out-of-gas classification and settlement, resource
refusal, fuel independence and ordinary-frame delegation. The twelve existing
transaction proof outputs were rechecked after the admission predicate change.
The identity-specific auditor now requires all **11** selected identity-module
outputs and rejects six corrupted-output controls.

The full-audit parser also required a repair: Lean wraps the long
`executeAtDepth_identity_variant_oversize` axiom list across lines. The former
per-line parser falsely reported that declaration missing. The parser now reads
whole transcript records, accepts a valid wrapped list, and rejects wrapped
`sorryAx` and duplicate reports. All **five** active-auditor corruption controls
pass; the dedicated identity auditor's **six** controls remain separate.

These are **local properties of the actual execution paths**, not a normative
Lean-to-EELS refinement proof. The published fixtures are narrowly admitted
cases: Prague includes restricted empty destinations and zero-excess blob-gas
envelopes, not KZG sidecar validation or arbitrary type-3/4 execution. Cancun
coverage is the six selected contracts. Shanghai's derived world root is after
transaction index zero, not a replay of every transaction in that block.
Frontier reconstruction still trusts the historical headers and host trie
machinery; it does not prove PoW chain canonicality or Lean MPT refinement.
Full fork rules, remaining precompiles and the rest of the independent client
remain obligations under epic #725.

## Paired runtime observations

The existing timing runner compared native binaries from
`85579939b390b52bd0fed6e258655288ae00704a` and the published implementation
checkpoint `53f258e1718fe68f5cfe90066b165e5a77206ca1`. Each path used 12 warm-up
pairs and 160 measured pairs, alternating which binary ran first. Every run
checked the pre-existing CLI result fields against the baseline result.
Measurements include process launch, interpretation, JSON output and exit;
they do not isolate interpreter throughput.

| Path and revision | p50 ms | p95 ms | p99 ms | Max ms | Min ms | Spread ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Existing frame/ABI path, before | 5.621 | 7.029 | 12.550 | 15.396 | 4.808 | 10.587 |
| Existing frame/ABI path, after | 5.423 | 6.593 | 10.411 | 29.948 | 4.720 | 25.228 |
| Existing zero-window CALL/storage path, before | 5.451 | 6.894 | 12.373 | 13.013 | 4.619 | 8.394 |
| Existing zero-window CALL/storage path, after | 5.414 | 7.200 | 9.765 | 11.295 | 4.603 | 6.692 |

Medians stayed close on these two retained paths. The frame/ABI maximum rose
to 29.948 ms despite lower p50/p95/p99, so this run does not support a general
speedup or a latency guarantee. Raw paired samples, machine details, executable
hashes and the complete distribution summaries are in `timing.json`.

## Reproduction

Run every command below from `formal/lean4/evm-cleanroom` with the pinned Lean
4.33.1 toolchain. Shared hosts must obey the repository's single-build lock.
The [EVM workflow](../.github/workflows/evm-cleanroom.yml) supplies the exact
official fixture URLs/SHA256 checks and pinned Geth archive/version; use those
steps to populate `.lake/eels/eip7623.json`, `.lake/eels/push0-contracts.json`
and the decoded Frontier witness. Set `EVM_GETH_EXE` to that verified Geth
`evm` binary. The existing npm packages are test infrastructure only.

```sh
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
npm install --prefix scripts/eels --ignore-scripts --no-audit --no-fund
lake build EVMCleanroom evm-subset evm-call-transaction evm-identity-precompile
python3 scripts/check-active-ledger.py
python3 scripts/test-active-ledger.py
python3 scripts/check-axiom-output.py --selftest
python3 scripts/check-axiom-output.py
python3 scripts/check-identity-axioms.py --selftest
python3 scripts/check-identity-axioms.py
python3 scripts/differential/identity-precompile.py .lake/build/bin/evm-identity-precompile

export EVM_GETH_EXE=/absolute/path/to/verified/geth-alltools-linux-amd64-1.17.10-1df30b18/evm
node scripts/differential/identity-call.mjs .lake/build/bin/evm-subset
node scripts/differential/identity-transaction.mjs .lake/build/bin/evm-call-transaction
node scripts/differential/call-opcode.mjs
node scripts/differential/call-data.mjs
node scripts/differential/call-family.mjs
node scripts/differential/call-repairs.mjs
node scripts/eels/call-transaction-differential.mjs .lake/build/bin/evm-call-transaction

node scripts/eels/run-lean-prague-all-types.mjs --fixture .lake/eels/eip7623.json --out .lake/eels/lean-prague-all-results.json
python3 scripts/check-prague-six-ledger.py .lake/eels/lean-prague-all-results.json
node scripts/eels/prague-all-selftest.mjs .lake/eels/eip7623.json .lake/eels/negative-controls
node scripts/eels/run-lean-contract-state-tests.mjs --fixture .lake/eels/push0-contracts.json --out .lake/eels/lean-contract-results.json
node scripts/eels/contract-selftest.mjs .lake/eels/push0-contracts.json
node scripts/eels/replay-authenticated-contract.mjs evidence/historical-1cat-shanghai-19100013.json .lake/build/bin/evm-call-transaction
node scripts/eels/replay-first-mainnet.mjs --fixture evidence/frontier-mainnet-46147.json --out .lake/eels/first-real-mainnet.json
node scripts/eels/verify-frontier-account-witness.mjs --historical evidence/frontier-mainnet-46147.json --witness .lake/eels/frontier-46146-archive-witness.json --out .lake/eels/frontier-real-mainnet-state-root-replay.json
python3 scripts/eels/independent-frontier-trie.py .lake/eels/frontier-46146-archive-witness.json
python3 scripts/eels/frontier-independent-negative.py .lake/eels/frontier-46146-archive-witness.json
```
