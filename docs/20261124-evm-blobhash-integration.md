# Cancun BLOBHASH connected to transaction and CALL execution

Tracking: [#864](https://github.com/danbri/factoidal-core/issues/864), under the
[independent execution and consensus goal #725](https://github.com/danbri/factoidal-core/issues/725).

## Change and ancestry

This work starts from the released blob-call transport checkpoint
`afa1e511412193d04a45fc28cc3cbf81a1829adf` in
[#863](https://github.com/danbri/factoidal-core/pull/863). The isolated branch
also merges the full identity checkpoint
`60995cd75a425fcde5eea20281f074f57605ae6a` from
[#839](https://github.com/danbri/factoidal-core/pull/839), preserving both
predecessor histories. The resulting implementation is independently authored
pure Lean 4.33.1 with no external Lake packages. Existing EthereumJS and Geth
dependencies remain test oracles and host codecs.

The normative source is
[EIP-4844, versioned-hash opcode](https://eips.ethereum.org/EIPS/eip-4844#opcode-to-get-versioned-hashes).
Opcode `0x49` consumes one unsigned 256-bit index, returns the corresponding
ordered versioned hash or zero, and costs three gas. It is permitted in static
frames. Replacing one stack word needs no additional stack capacity.

The previous Cancun transaction adapter validated the hash list and charged
blob fees, then discarded the hashes while creating the internal type-2-shaped
accounting request. The new `Prepared.txBlobHashes` retains that list as
big-endian EVM words after the one-to-six and 32-byte/version checks.
`CallTransaction.runWithBlobHashes` installs the context in the shared
admission, escrow, execution and settlement path. The ordinary public `run`
always supplies an empty list. No transport field was added to ordinary
transactions, and the existing blob JSON transport is unchanged.

`World.frameInput` copies the transaction context into each frame. Account
updates, frame commits, value transfer and return/rollback keep that context.
The same path serves CALL, CALLCODE, DELEGATECALL and STATICCALL, including
identity calls. Blob fee burning remains before the execution checkpoint.

## Regression and implementation evidence

The baseline native executable, SHA256
`ca332992a4f95c5ea7b18779a13a361f14b8171ca3d746189893f7fb20e153c3`,
returned `indeterminate/invalidOpcode` for a signed Cancun transaction running
`5f495f5260205ff3`. EthereumJS `runTx` and Geth `t8n` independently executed
the identical signed bytes and returned
`01001326394c5f728598abbed1e4f70a1d304356697c8fa2b5c8dbee0114273a`
using 21,018 total transaction gas. The rebuilt Lean executable returns the
same complete result. Both the failing baseline and passing smoke reports are
retained with the evidence.

The previous 200-row blob-fee matrix passed on the unmodified baseline:
180 executed, eight rejected and twelve indeterminate, seven rejected
comparator mutations and nine malformed transport controls. Its old bare
`49` unsupported-opcode fixture is now `5f40` (PUSH0; BLOCKHASH), retaining a
real unsupported instruction. BLOBHASH underflow is an executed failure case
in the new signed suite.

## Measured validation

The final signed matrix has **179 compared cases**: 173 standalone cases and
six transactions in a real prefix sequence. There are 161 type-3 cases
and six each of ordinary types 0, 1 and 2. Lean, EthereumJS and Geth match on
every case, and the two reference clients agree independently on all 179.
There are zero mismatches, local refusals or unexecuted declared cases. Sixteen
cases intentionally produce failed receipts; these are completed, correctly
charged execution failures, not skipped comparisons.
The corpus contains 22 distinct signed byte strings; the 179 cases vary code,
pre-state, block context and sequence position as well as the envelope.

| Signed case group | Cases |
| --- | ---: |
| Full-width lookup and list sizes | 68 |
| List order and duplicate hashes | 4 |
| Ordinary transactions with empty context | 15 |
| Nested calls | 12 |
| All pairs of two nested call variants | 16 |
| Child gas boundaries | 12 |
| Parent gas boundaries | 8 |
| Direct gas boundaries | 7 |
| Stack boundaries | 3 |
| Storage, logs, revert, exceptions and refunds | 13 |
| Static-context boundaries | 2 |
| Value transfer | 4 |
| Blob prices and burns | 9 |
| Real transaction sequence and context reset | 6 |
| **Total** | **179** |

The six-transaction sequence uses the preceding native post-state and real
EthereumJS/Geth prefixes, including their cumulative gas and blob consumption.
It runs distinct type-3 contexts, then ordinary types 0/1/2, then another
type-3 context. The ordinary transactions return zero. The type-0 transaction
clears a previously stored hash and gets the independently matched 4,800-gas
refund. Prefixes are rerun by Geth to check intermediate commitments; the
table counts distinct compared cases, not every repeated oracle execution.

Comparisons cover complete returned bytes from actual Geth terminal traces,
frame/receipt status, gas, account existence/nonces/balances/code/witnessed
storage, logs and bloom, typed receipt bytes, state roots, receipt roots and
signed transaction roots. Thirteen negative controls change execution gas, a
returned byte, blob burn, blob gas, a signed hash byte, signed hash order,
receipt status, an account balance, log data, stored data, chain ID, access
list or the case inventory.
Every mutation is detected. A missing child witness is explicitly refused.
The KZG sentinel records zero operations; no sidecar check is implied.

| Retained lane | Observed result |
| --- | --- |
| Header RLP / parent hash / derived fees | 7,849/7,849; eight mutations detected |
| BLOBBASEFEE | 42/42; two mutations detected |
| Existing blob-call matrix | 200/200; 180 executed, eight rejected, twelve indeterminate |
| Standalone identity | 1,056/1,056 |
| Identity through CALL | 660/660 EthereumJS; 648/648 Geth |
| Signed identity transactions | 84/84 against both clients |
| Ordinary signed transactions | 60/60 with receipt and state-root matches |
| CALL opcode / byte-context / CALL family / repairs | 330 / 122 / 213 / 6 cases, all passing |
| Official Prague / Cancun selections | Six / six exact published state roots |
| Authenticated historical Shanghai | Block 19,100,013 transaction index zero passes |
| Authenticated historical Frontier | Block 46,147 intermediate and final state roots pass |

The 12 Geth exclusions in the retained identity CALL matrix are four raw
static-entry and eight nonzero-entry-depth cases, all checked by EthereumJS.
Other retained raw suites retain their own explicit harness exclusions.
The new 179-case signed matrix has no such exclusions. The Cancun published
fixture selection executes six Cancun cases from a 24-case cross-fork file;
the other 18 fork cases are not counted as executed.

## What the proofs establish

The source-connected Core statements derive actual successful execution,
stack replacement, exact three-gas charge, full-width in-range/out-of-range
lookup and unchanged memory/storage/context. Separate statements cover
underflow, out-of-gas and the older coarse-profile refusal. The success proof
uses the existing stack bound, including a full 1,024-word input stack.

`prepareWithFees_checked` and `prepare_blobHashes_checked` follow the actual
admission branches and establish the exact prepared list and the six-word
bound. `validated_entry_blobHashes` composes actual preparation and successful
value transfer with the real `entryFrame`. The budget is a parameter; this
theorem does not by itself prove successful ordinary admission, receipt
production or arbitrary execution termination. The retained transaction
admission theorem and signed execution tests check their respective boundaries.

The CALL-family entry statements start from a real entered-child result and
derive the child's world and frame context. They do not assume that an
arbitrary externally constructed parent state agrees with its world, or that
the child's initially empty stack contains an index. The Core preservation
statement covers intervening instructions. There is no new whole-execution
refinement theorem.

This change authors **23 theorem statements** and brings **30 additional
statements** under the selected audit, including seven inherited BlobCall
statements. The full active audit passes **246 statements across 25 source
files**. The dedicated BLOBHASH/blob-call audit selects 30 statements across
seven files. Exact actual axiom sets contain only `propext`, `Classical.choice`
and `Quot.sound`; several new statements need no axioms. The old
`prepared_exact` statement now reports `propext` after the prepared record
gained its normalised array; the declaration was rebuilt and its recorded set
was updated to the observed result.

The active ledger pins 126 reviewed source files. The dedicated audit checks
the complete imported implementation and supporting test/configuration closure
of 39 files, and hosted CI requires those bytes to match the checked-out Git
commit. Eight dedicated axiom-output corruptions, five active-auditor controls,
six retained identity-auditor controls and all five active-ledger test groups
pass. The parser accepts wrapped Lean output while rejecting missing,
duplicated or altered theorem reports and forbidden axioms.

The 38 Lean guards are tests, covering word and stack boundaries, static
execution, exact return bytes, all call variants, value transfer, nesting and
rollback. Actual theorem axiom reports, source pins, negative controls and
the final signed/replay counts are recorded in the accompanying evidence.

## Trust, resource and unfinished boundaries

Lean receives a decoded envelope, a recovered sender and explicit account and
storage witnesses. The signed suite binds those fields to the exact bytes
executed by both clients, but signature recovery, receipt encoding and trie
construction remain host operations. Geth trace output checks return bytes;
receipt roots alone cannot establish them. These are synthetic transactions,
not new authenticated mainnet captures.

The context is at most six words on the checked Cancun path; normalisation
touches at most 192 hash bytes. The full-width opcode index is compared before
array indexing and never narrowed first. Existing fuel, depth, witness and
transport resource bounds remain in force. General host allocation/runtime
safety is not proved by these local bounds.

The compiler/runtime and experimental Keccak acceptance remain trusted. No
KZG sidecar verification or blob body access was added. The low-level explicit
context runner does not itself authenticate or validate a blob envelope;
`BlobCall.run` supplies its admitted context. The coarse older opcode profiles
return a local fork refusal, not a fork-exact consensus invalidity proof.
Prague blob transaction execution, full block-inventory equality, signatures,
remaining precompiles, complete fork coverage, networking and consensus remain
obligations of the full independent client goal.

## Published implementation and timing

The source checkpoint is
[`85da2a6b307c0a0269257344d889051ce6902e82`](https://github.com/danbri/factoidal-core/commit/85da2a6b307c0a0269257344d889051ce6902e82),
tree `e1f3e475c367681410573c004a6b9273e00af273`, with the two predecessor
commits as parents. A post-publication dedicated audit passed with
`--require-head`, matching all 39 imported/support source files to that commit.
The later evidence checkpoint changes this worknote and archived reports only.

Native SHA256 values:

| Executable | SHA256 |
| --- | --- |
| `evm-subset` | `0fcf78570a399f9941063ec1419fd62b14dfeb956a3f1af9bcce1d36e670758e` |
| `evm-call-transaction` | `7a7c99e7e9957596f1cb8298cf2eaa0425aa1cb896eab3c0ebc5b4f46f98f9cd` |
| `evm-blob-call` | `fc33d369b084791173ec178c100fce347acf24af52efb7f0b1d64c554587f510` |
| `evm-identity-precompile` | `f54f0f8a2756d6b3ab5ba12698f7624de242e35577c5da4fce052ddf170d6089` |

The paired timing runner compares the original blob checkpoint to this
combined identity/BLOBHASH checkpoint. It therefore measures the complete
branch change, not an isolated BLOBHASH-only change. Each retained path uses
12 warm-up pairs and 160 measured pairs, alternating launch order and checking
the complete pre-existing CLI result on every run. Timing includes process
launch, native interpretation, JSON serialisation and exit.

| Path and revision | p50 ms | p95 ms | p99 ms | Max ms | Min ms | Spread ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Existing frame/ABI, before | 3.525 | 4.934 | 12.008 | 16.094 | 3.128 | 12.966 |
| Existing frame/ABI, after | 3.542 | 4.677 | 10.640 | 27.721 | 3.172 | 24.549 |
| Existing CALL/storage, before | 3.645 | 4.458 | 5.222 | 8.968 | 3.049 | 5.919 |
| Existing CALL/storage, after | 3.658 | 4.633 | 5.067 | 27.540 | 3.185 | 24.355 |

Medians remain close in this sample, while both after-build maximums are
higher. These process-inclusive measurements do not establish a speedup or a
latency bound. Raw pairs, machine information and source/binary identities are
retained in the timing report.

[Full evidence and provenance](../formal/lean4/evm-cleanroom/evidence/2026-11-24-blobhash-integration/provenance.json) ·
[Signed comparisons](../formal/lean4/evm-cleanroom/evidence/2026-11-24-blobhash-integration/signed-transactions.json) ·
[Published-source axiom audit](../formal/lean4/evm-cleanroom/evidence/2026-11-24-blobhash-integration/blobhash-axioms.json) ·
[Paired timings](../formal/lean4/evm-cleanroom/evidence/2026-11-24-blobhash-integration/timing.json)

Hosted results are recorded on the draft PR at its submitted head. A passing
local checkpoint does not substitute for the repository's full build-release
and premerge gates; this work does not merge the stack into main.

## Reproduction

All Lake commands use `formal/lean4` as their explicit working directory and
the pinned Lean 4.33.1 toolchain. The dedicated blob workflow records the
pinned existing test dependencies and Geth archive/executable hashes.

```sh
lake -d evm-cleanroom build EVMCleanroom evm-subset evm-call-transaction evm-identity-precompile
lake -d evm-cleanroom -f lakefile-blob-call.toml build evm-blob-call
python3 evm-cleanroom/scripts/check-active-ledger.py
python3 evm-cleanroom/scripts/check-axiom-output.py --selftest
python3 evm-cleanroom/scripts/check-axiom-output.py
python3 evm-cleanroom/scripts/check-blobhash-axioms.py --selftest
python3 evm-cleanroom/scripts/check-blobhash-axioms.py
node evm-cleanroom/scripts/differential/blobhash-transactions.mjs \
  evm-cleanroom/.lake/build/bin/evm-blob-call \
  evm-cleanroom/.lake/build/bin/evm-call-transaction
```

Shared-host compilation uses one lock, one Lean worker and an 8 GiB virtual
memory cap with a 64 MiB Mimalloc arena reservation. The runtime cap is a local
build constraint, not an Ethereum consensus parameter. Source and native
hashes, exact invocation records and before/after timing samples accompany
the final evidence checkpoint.
