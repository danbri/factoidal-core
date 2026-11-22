# Witness-limited Ethereum call transactions

The Shanghai and Cancun call-transaction entry accepts ordinary type-0,
type-1 and type-2 calls. It validates supplied envelope and block fields,
charges intrinsic gas, checks the sender nonce and upfront funds, and
creates the account and storage view from explicit witnesses. It escrows
the effective fee and advances the sender nonce before the frame. On
success it settles the caller and beneficiary against the resulting world.
On REVERT or an exceptional halt it settles fees against the execution
checkpoint and preserves the already advanced nonce. Reached accounts or
slots absent from the witness set yield an indeterminate result.
[Tracking issue, #796](https://github.com/danbri/factoidal-core/issues/796) ·
[Full Lean Ethereum goal, #725](https://github.com/danbri/factoidal-core/issues/725)

Lean receives normalised envelope, header and state facts. The replay
host handles signature recovery, witness and code authentication, and
receipt and state commitments. An incomplete witness or unsupported
execution produces no completed receipt. The transition model covers the
supported bytecode, call variants and fork contexts.
[Call-transaction implementation](../formal/lean4/evm-cleanroom/EVMCleanroom/CallTransaction.lean) ·
[Trust boundary](../formal/lean4/evm-cleanroom/SOUNDNESS.md)

The `evm-subset` executable forwards only transaction mode to the sibling
`evm-call-transaction`. Its bytecode paths use the lightweight Lean
runtime, while the transaction companion uses Lean’s standard JSON
parser and full initialisation. Three routing controls compare exit
status and byte output with direct invocation. Two missing-companion
controls require a structured error, even with a companion on `PATH`.
A separate control checks legacy log JSON without the companion.
[Native entry points](../formal/lean4/evm-cleanroom/README.md#witness-limited-call-transactions)

## Proof checks

Lean 4.33.1 built the library and both native executables in 63 jobs. Fresh
per-file elaboration checked the exact axiom sets for 172 selected
theorems in 20 files. That includes 133 retained statements, 23 for hash,
log and standalone frame changes, and 16 for world-aware execution and
call transactions. The current axiom output for 52 retained statements
also lists `Quot.sound`. The versioned audit delta records each changed
set. Three deliberate axiom-report mutations were rejected.
[Active proof ledger](../formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json) ·
[Printed axiom changes](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/axiom-deltas.json)

## Bytecode comparisons

The native instruction matrix matched 80 of 80 programs against Cancun
EthereumJS, including 24 XKCP-pinned inputs whose hash bytes also matched
noble. Seven gas-boundary triplets, six native-only controls and four
output mutations checked the exact gas, default hash refusal, opt-in
propagation, oversized inputs and complete log observations. The opt-in
is scoped to public and synthetic replay evidence. Formal cryptographic
refinement and constant-time execution remain open.
[Versioned hash and log report](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/hash-log.json) ·
[Experimental scope](20261122-evm-hash-log-boundary.md)

## Transaction comparisons

The synthetic Shanghai and Cancun matrix matches EthereumJS receipt
bytes and state roots for all 60 calls. Eight independent admission
rejections, one host-side pre-serialization rejection and 11 boundary
refusals are separate controls. The comparator rejects three mutations
of gas, receipt log data and state balance.
[Synthetic transaction report](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/call-transaction-differential.json)

The mainnet fixture replays one Shanghai call at index zero of block
19,100,013. The host verifies the signed transaction and receipt against
the published header commitments, then checks the contract code and four
storage slots against the authenticated parent state. The replay matches
the receipt's status, 33,987 gas and ordered Transfer log. Lean's
execution returns the ABI word 1 and reports a 4,800-gas refund. The
host applies account effects from Lean, EthereumJS and Geth to the same
sparse parent trie and obtains the same derived intermediate world root.
The target storage root matches the proven final-block value. The
canonical block selection comes from the recorded providers. Six
controls check witness, code, receipt, trie key and opt-in failures.
[Historical replay record](20261122-evm-shanghai-contract-replay.md) ·
[Historical replay report](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/historical-replay.json)

## Retained checks

The raw bytecode corpus matched 10,000 of 10,000 restricted cases. Six
Prague and six Cancun official state roots matched, and all five active
ledger test groups ran against a fresh Cancun report.
[Retained check counts](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/retained-checks.json)

The initial JSON-enabled native binary grew from 6.56 MB to 121.08 MB.
The paired ABI CLI median rose from 4.716 to 33.901 ms, the zero-window
CALL median from 4.513 to 33.176 ms and the 10,000-case raw batch median
from 154.781 to 187.701 ms. All measured legacy field values and raw
outputs agreed. Timing investigation remains tracked in issue #739.
[Native timing samples and link diagnosis](../formal/lean4/evm-cleanroom/evidence/2026-11-22-call-transaction/TIMING.md)
