# Ordered Cancun transactions with state and counters derived in Lean

Tracking: [#867](https://github.com/danbri/factoidal-core/issues/867), under the
[independent execution and consensus goal #725](https://github.com/danbri/factoidal-core/issues/725).
This continuation starts from the submitted
[BLOBHASH integration #866](https://github.com/danbri/factoidal-core/pull/866),
`2e8a64e86b1578017cc96bcc4045d801ed6319c9`.

## Change

`TransactionList.run` takes one initial account/storage witness inventory, one
parent/child header pair and an ordered list of decoded transactions. The Lean
runner derives every intermediate state, receipt and gas counter. The host
cannot supply a replacement state or counter between transactions.

The admitted slice is mainnet Cancun, with ordinary call transactions of types
0, 1 and 2, and type-3 blob call transactions. The timestamp check also applies
to empty lists and lists containing only ordinary transactions. Execution
outside the Cancun interval gives an explicit local refusal.

The normative reference is the Cancun execution specification at
[`391d8a05d5cb182542ac7e7330c858b6ee03f990`](https://github.com/ethereum/execution-specs/blob/391d8a05d5cb182542ac7e7330c858b6ee03f990/src/ethereum/forks/cancun/fork.py),
Git blob `50a6524a09c33a1576ec7cd6f6acae59abcdd432`, especially
`check_transaction`, `process_transaction`, `apply_body` and `state_transition`.
The implementation is independently authored Lean; the reference is used to
check requirements, not imported or translated into production code.

## State and transaction boundaries

The initial inventory fixes which account addresses and storage keys are
covered. After each executed transaction, `refreshWitnesses` reads the settled
world's balances, nonces, code and covered storage values. It retains the
inventory's address/key order and does not make an unlisted slot witnessed.
The next request builds a fresh transaction world from those values.

This new world snapshots current storage as the next transaction's original
storage. Its refund counter, log journal, blob-hash context and effective gas
price start afresh. Address and slot warmth come from the new transaction's
sender, recipient, beneficiary, precompile range and access list. A prior
transaction's warm accesses cannot leak into the next transaction.

Ordinary entries use `CallTransaction.run`, whose hash list is empty. Blob
entries use the existing admitted blob execution path and install their own
ordered versioned hashes. Both paths retain their existing escrow, value,
identity-precompile, nested CALL and rollback rules. Publishing the existing
`runAdmitted` helper allows proofs to follow this actual path; its code is
unchanged and it does not independently admit arbitrary supplied values.

A reverted or exceptional frame is still an executed transaction. Its settled
fee/nonce effects enter the next state, its gas charge enters cumulative gas,
and a type-3 entry still consumes and burns its blob gas. Rejected or
indeterminate execution stops the list with the zero-based entry index. That
outcome contains no accepted partial account state or receipt list.

## Gas accounting

Each entry receives the execution gas used by preceding receipts, after their
refunds. Admission therefore checks the next transaction's gas limit against
the remaining block gas pool. The sum of transaction gas limits need not fit
the block limit when completed transactions return enough gas.

The runner separately accumulates blob gas, including failed receipts. At the
end, execution gas must equal header field 10 and blob gas must equal header
field 17. Equality applies to the complete supplied list, including the empty
list. It does not authenticate that list against the header's transaction root.

The standalone blob adapter treats an inconsistent caller-supplied prefix as
unavailable evidence. The list runner owns the prefix, so it classifies a
prefix exceeding either declared total as `rejected/declared-gas-total-exceeded`.
Later nonnegative charges cannot repair that mismatch. This includes an
aggregate seventh blob against a Cancun header declaring six.

Receipts retain the original transaction type, actual frame/receipt status,
complete returned-byte view, charge, cumulative gas, effective price, logs,
blob gas and blob burn. They are returned in execution order. Intermediate
worlds are not returned as additional host-supplied inputs.

## Transport and resource bounds

`TransactionCodec` contains the shared JSON parsing and ordinary response
functions previously duplicated between the two transaction CLIs.
`TransactionListCLI` adds one bounded list transport. Its top-level fields are
`schemaVersion`, `parentHeader`, `childHeader`, `accounts` and `transactions`.
Each entry has `fuel`, `transaction`, and, for a blob entry, the paired
`blobVersionedHashes` and `maxFeePerBlobGas` fields. Unknown top-level and entry
fields are refused, including attempts to inject intermediate state or gas.

The local runner permits at most 256 entries and reserves at most 1,000,000
instruction-fuel units across them. It bounds initial witnesses to 1,024
accounts, 4,096 keys per account and 16,384 total keys. Individual code is at
most 1 MiB, and aggregate code/calldata/hash payload is at most 16 MiB.
Inventory bounds are inspected before the aggregate folds. Individual
transaction admission retains its own resource and numeric checks.

The accumulated logical returned bytes and log payload are at most 16 MiB;
the check precedes retaining another receipt. The CLI reads at most 16 MiB
plus a sentinel byte, and emits a resource refusal if its compressed JSON
would exceed 64 MiB. These are local implementation limits, not Ethereum
consensus maxima. They establish explicit refusal points; they do not prove
a wall-clock, physical memory or compiler/runtime safety bound.

### Parsing before schema validation

Resource review reproduced a stack overflow in standard JSON parsing before
the schema checks. A 6,000,034-byte document with 3,000,000 nested arrays was
below the file limit but aborted the unguarded executable. Under the same
8 GiB virtual-memory cap, one Lean worker, 64 MiB stack and 64 MiB Mimalloc
arena reservation, a minimal object and a 100,000-level document produced
ordinary input errors. An initial 1 GiB probe could not initialise the runtime
even for the minimal object and is not parser-failure evidence.

`TransactionTransport` now scans the finite UTF-8 byte array before the
standard parser. It bounds nesting to 64, numeric tokens to 96 bytes and the
magnitude of a numeric exponent to 78. Quoted content and escaped quotes or
backslashes do not contribute to these structural/numeric counters. Keeping
the exponent small also prevents a compact numeric token from asking the
standard parser to construct a very large power of ten.

`TransactionCodec.parseJSON` applies this check to all three transaction
CLIs. Ordinary JSON grammar and schema validation still use the existing
parser. Excess returns `inputError` with `json-nesting-limit`,
`json-number-token-limit` or `json-exponent-limit`. These are local transport
restrictions, including on unusual numeric spellings, not Ethereum validity
rules. The regression suite retains the previously crashing document, exact
limit boundaries, escaped strings and safe old/new spelling comparisons.

## Validation record

The core and all three native transaction entries compile locally under Lean
4.33.1, with an 8 GiB virtual-memory cap and a 64 MiB Mimalloc arena reservation.
Before/after codec checks preserve stdout bytes, stderr and exit status on
12 ordinary/blob success, failure and malformed requests. The new transport
checks include the exact 16,777,216/16,777,217-byte input boundary.

The signed list comparison uses one invocation of the native list runner,
EthereumJS block execution and Geth's full `t8n` transaction batch. During
harness development, a 21,000-gas first transaction followed by an 80,000-gas
reservation in a 100,000-gas block exposed the boundary of bare EthereumJS `runTx`: cumulative
gas-pool admission belongs to its block caller. The list oracle therefore
uses `runBlock` and records the actual transaction results. It does not
reimplement the missing admission rule in the host harness.

Independent review also found that reference agreement alone did not bind
admission failures to the fixture's expected index. The recorded cases already
agreed, but a common wrong reference index could have passed the comparator.
The final comparison explicitly joins each reference's category and first
rejection index to the same fixture/native expectation, and mutation controls
change both references together or make both accept. Local unsupported-frame
cases separately require both reference clients to complete execution.

The reference block has an empty withdrawals list and no beacon-root contract.
The harness asserts that this contract remains absent after the client's Cancun
system operation, then compares the complete state roots. It retains real body
validation in EthereumJS while skipping parent-chain header authentication.
The native runner's narrower transaction-list boundary is therefore explicit.

The retained suites also pass after the codec extraction: 179 signed BLOBHASH
cases and 84 signed identity cases against both clients, the 200-case blob-call
matrix, and 60 ordinary signed cases with receipt/state-root checks. The new
list has a separate native entry; existing transaction protocols retain their
wire behaviour.

### Measured execution and controls

The final guarded native executable passes all **36 primary list cases**:
30 complete execution comparisons, five same-index admission rejections, and
one explicit native unsupported-operation refusal. Both reference clients
execute the unsupported case; it is not counted as a native execution match.
The 30 accepted lists contain 327 transactions: 321 successful receipts and
six intentional failed receipts. All primary lists contain 344 entries and
308 distinct signed byte strings. These counts describe synthetic cases,
not mainnet blocks or a percentage of Ethereum conformance.

The native runner is invoked once per primary list. It receives no host
intermediate state. Comparisons include complete returned bytes from actual
Geth terminal traces, ordered receipt/frame status, gas and refund accounting,
logs and bloom, account existence/balances/nonces/code/covered storage, typed
receipt bytes, and state/receipt/transaction roots. Twenty-five comparator and
signed-binding mutations are rejected, including common-mode reference
category/index mutations. KZG operations remain zero.

Sixteen separate native controls cover final gas/blob declarations, missing
state, unsupported type, missing/extra blob fields, fuel exhaustion, aggregate
fuel excess, reordered nonces, fork endpoints and output bounds. Thus the
signed harness makes 52 native calls: 36 primary plus 16 controls. Its two
output-boundary lists contain another 512 reference-executed transactions.
At exactly 16,777,216 returned bytes, all 256 native receipts and the complete
state/receipt roots match both clients. At 16,777,217 bytes, native execution
returns a local resource refusal at index 255, without accepted partial output.
Reference execution agreement on that over-limit list is recorded separately
from the native refusal.

Gas-pool examples distinguish declared transaction limits from settled gas:

| Ordered-list example | Observed result |
| --- | --- |
| First transaction uses 26,004 gas before a 4,800 refund; next reserves 76,000 in a 100,000-gas block | First charge is 21,204, leaving 78,796; the second transaction succeeds |
| Three transactions each declare 50,000 gas in a 100,000-gas block | Each charges 21,000; all three execute, total 63,000 |
| First transaction charges 21,000; next reserves 80,000 in a 100,000-gas block | Both clients and Lean reject at index 1 |

All 22 persistent list-transport controls pass, including exactly 16 MiB of
input and refusal at one extra byte. All 90 adversarial JSON controls pass
across the three CLIs, including 42 exact lexical refusals. Nine small
old/new spelling comparisons match byte for byte: six accepted cases and
three preserved decimal-type schema refusals. `schemaVersion: 1e0` is
accepted; transaction types `2.0` and `3.0` still produce
`Natural number expected`. The original 12 codec extraction checks also
remain byte-identical after the parsing guard.

### Proof scope

Twenty-nine list statements connect the actual transaction paths to the
public list result. `run_accepted` derives an ordered `receiptTrace`, including
the exact final witnesses, from the real `runEntry` and `advance` transitions.
It establishes one receipt per input, exact receipt gas/blob sums and
cumulative gas, exact header totals, preserved address inventory and the
checked logical resource bounds. Separate lemmas establish covered storage
values, unchanged slot coverage and fresh transaction state. Thirty-six
executable list guards are tests, distinct from those theorem claims.

Seventeen additional transport statements connect the actual byte-array fold
from its empty initial state to bounded scanner counters, error persistence,
exact limit refusals, quoted/escaped byte behaviour and the shared codec's
parser-continuation boundary. The parser-refusal theorem is an equality
independent of the supplied parser continuation; it is not a machine-code
call-count or general memory-safety theorem. Actual compiler axiom sets and
the complete active source inventory are retained with the final evidence.
Forty-four executable transport guards supplement these proofs. Together,
this continuation adds 46 checked statements and 80 Lean guards.

## London audit repair

The hosted London-fee audit on the predecessor branch correctly refused an
outdated pin for `EVMCleanroom.lean`. Its actual six theorem compilations had
passed. The pin still described the original import root, before the identity
and BLOBHASH integration imports were added.

The repair preserves the dated London evidence byte for byte and adds a
separate active London manifest. The checker still requires the exact six
reviewed source paths and actual axiom sets, and now also checks the historical
manifest hash, toolchain and absence of external Lake packages. A new corruption
control changes a source pin and must fail. The workflow uses the required
explicit Lake working directory, memory limits and pipeline failure handling.

The standalone London executable, all six actual axiom reports, all four audit
controls, 1,555 formula cases, all three comparator mutations and malformed
transport guard pass locally. This repairs a stale assurance input; it does
not change London fee arithmetic.

## Published implementation and measured cost

The implementation is published at
[`91cae62479cbd3a13775b3dd15f502646c11db41`](https://github.com/danbri/factoidal-core/commit/91cae62479cbd3a13775b3dd15f502646c11db41),
tree `7d8ef4d75ef64e634574ee4a313294e9072e4f4f`. The subsequent evidence
commit adds this record and the
[dated evidence bundle](../formal/lean4/evm-cleanroom/evidence/2026-11-24-transaction-list/).
It changes no executable or proof source.

The post-publication audit actually re-elaborated all 46 new statements and
required all 47 dedicated implementation, proof and support pins to match
Git HEAD. A separate comparison matched every one of the 146 active source
pins to that same commit. The complete local compiler audit checks 292
selected statements across 27 files. The new statements use these actual
axiom sets: seven empty, eight `propext`, 22 `propext` with `Quot.sound`,
and nine using all three permitted foundations. These are selected local
theorems, not a count of independently established Ethereum requirements.

The paired timing run on 24 November 2026 uses the unchanged ordinary and
blob CLI requests against separately built predecessor source
`85da2a6b307c0a0269257344d889051ce6902e82` and the published implementation
above. The predecessor binary hashes match the BLOBHASH milestone's
published hashes. Each path has 12 warm-up pairs and 160 measured pairs,
alternating order under the shared timing and compiler locks. Every
invocation must return byte-identical output with the expected successful
status and no stderr.

| Path and statistic | Before (ms) | After (ms) |
| --- | ---: | ---: |
| Ordinary call, median | 31.84 | 33.37 |
| Ordinary call, p95 | 41.42 | 47.19 |
| Ordinary call, p99 | 53.58 | 82.80 |
| Ordinary call, maximum | 60.40 | 114.71 |
| Blob call, median | 31.22 | 32.29 |
| Blob call, p95 | 39.10 | 41.66 |
| Blob call, p99 | 74.50 | 61.78 |
| Blob call, maximum | 94.10 | 89.04 |

These measurements include process launch, file and JSON input, transaction
execution, JSON output and exit. Medians increased by approximately 4.8%
and 3.4%, respectively; the ordinary path also has a larger observed tail.
No individual component cost, speed improvement, stable latency guarantee
or whole-list throughput result is inferred. Raw nanosecond samples,
nearest-rank quantiles, paired differences, binary identities, request/output
hashes and machine details are retained in `cli-timings.json`.

The raw development crash report is also retained unchanged. It records the
payload size, nesting, process exit and stack-overflow stderr, but does not
itself embed the executable hash or process-limit settings. Its association
with the retained pre-guard development binary and documented limits comes
from the execution session. It is not attributed to a published list-source
commit. The guarded regression, published source audit and timing reports
carry their own native or source identities.

The evidence bundle gives reproduction commands and SHA-256 checksums.
Hosted checks are pending at evidence publication; their outcome is recorded
in the linked tracking issue and draft PR. The predecessor's broader Lean
corpus passed. The repository npm job remains blocked before tests by its
missing ancestor web-release prerequisite. No main merge or release-gate
bypass is part of this continuation.

## Remaining complete-system work

This is a decoded transaction-list transition. It does not yet authenticate
signed transaction bytes, initial state witnesses or transaction inventory;
compute or check trie commitments in Lean; process the beacon-root system
call or withdrawals; or validate all parts of a block. Host signature recovery
and receipt/trie construction remain test-oracle operations. The Lean
compiler/runtime and explicit experimental Keccak acceptance remain trusted.

Complete opcode, precompile and fork coverage, contract creation, independent
signature and KZG checking, storage, networking, synchronisation, consensus
state transition and fork choice remain obligations of the full client goal.
The independent consensus/SSZ work is a separate branch; this list change
does not assert that the execution and consensus components form a running
node.
