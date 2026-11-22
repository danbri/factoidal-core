# From Lean EVM seed to independently reviewed Ethereum execution and consensus

**Project state as of 22 November 2026.** The Lean interpreter and replay
tools cover specific parts of the execution layer. Independent comparisons
and formal results are scoped to the tested implementation.

## Full Lean Ethereum goal

The full goal covers both the execution layer (EL) and the consensus layer
(CL). It requires protocol-critical consensus logic in Lean, including
beacon-state transitions, fork choice and finality, fork-indexed SSZ and BLS
rules, and consensus networking for peer messages, gossip and sync.
Acceptance requires the integrated EL and CL to pass published fork-specific
fixtures and independent-client interoperability checks, with independent
review of protocol semantics, Lean proofs and systems security against the
exact source and evidence.
[Full Lean Ethereum execution and consensus goal, #725](https://github.com/danbri/factoidal-core/issues/725) ·
[Ethereum consensus specifications](https://github.com/ethereum/consensus-specs)

## Execution-layer subgoal

Milestones A–C and gates G0–G6 track the execution-layer subgoal.
[Execution client and assurance tracker, #652](https://github.com/danbri/factoidal-core/issues/652)

**A. Replay a real mainnet transaction.** Given the canonical typed or RLP
transaction, its correct *pre-transaction* state, historical fork and block
context, deterministically reproduce the receipts/logs/state changes and gas.

**B. Prove a deployed contract property.** Given immutable deployment identity,
exact reproduced deployed runtime bytecode and an explicit formal contract
specification, prove a selected property for that deployed bytecode under
the declared EVM, compiler, environmental and external-call assumptions.

**C. Conform to Ethereum execution-layer consensus.** For every claimed
historical/mainnet fork, implement the state transition accurately, including
exceptional execution, precompiles, fee and account rules, state roots and
receipts. Engine API interoperability with an independently validated
consensus client is an intermediate milestone on the way to integrated
Lean execution and consensus.

Do not promote any success in A to B or C without separate evidence.

## Current partial milestones

- **Official fixtures.** Six of six selected Prague EIP-7623 cases and
  six of six selected Cancun nonempty-contract cases reproduced the
  published state roots. Eighteen other-fork cases in the Cancun input
  remain unexecuted. The runners use Lean execution and EthereumJS
  signature recovery and trie serialisation. [Active evidence ledger](evidence/active-claim-manifest-v2.json)
- **Authenticated Frontier replay.** One ETH transfer in Ethereum mainnet
  block 46,147 uses account proofs anchored at the parent state root.
  The Lean-driven replay and independent Python checker reproduced both
  the intermediate transaction and final block roots. Canonical chain
  selection and the headers are supplied externally. [Replay scope](README.md#authenticated-historical-frontier-replay)
- **Executable frames and CALL.** The CLI covers fuel-bound STOP, memory,
  RETURN/REVERT and scoped storage rollback. Standalone frames accept
  calldata, and the restricted CALL path carries context, value and byte
  windows through nested frames. The shared fuel budget and depth check
  bound frame dispatch. CALLCODE, DELEGATECALL, STATICCALL, CREATE and
  precompile execution remain open.
  [CALL and calldata scope](README.md#calldata-and-bounded-call-execution)
- **Read-only RPC capture.** The capture and comparison tool supports
  Polygon PoS and OP Sepolia profiles. The saved Polygon mainnet and OP
  Sepolia samples matched local output with synthetic code overrides.
  Amoy returned an RPC error for the override call. Provider assertions
  are recorded and independent block, root, receipt and consensus
  validation remain open for these captures. [RPC evidence](scripts/rpc/README.md)

## Historical milestone on 19 November 2026

On 19 November 2026 the restricted EELS runner passed **4/6** published
EIP-7623 Prague state tests, with the remaining two explicitly unsupported.
Lean computed the empty-code EVM result and scoped transaction fee/nonce/
balance transitions. The host validated signed transaction metadata and used
EthereumJS MPT serialization; the resulting official EELS post-state root
and account-set expectations matched for the supported inputs.

The run rejected two negative controls (altered expected root and sender
balance). It established the first slice of G1. At that checkpoint,
nonempty contract execution, persistent storage, exceptional outcomes,
authenticated historical witnesses, official receipts and EELS semantic
refinement were still open. [EELS runner and original evidence](scripts/eels/README.md)

## Execution-layer acceptance gates G0–G6

| Gate | Work | Demonstrable exit criterion |
|---|---|---|
| G0 — executable interface | Run our Lean bytecode semantics from a CLI with parseable results | A CI runner executes the actual Lean model and checks structured success and errors; currently implemented in CLI.lean |
| G1 — reference conformance | Pinned current EELS and official fixtures; count pass, fail and **unsupported** separately | Named fixture IDs, reference release, fork, exact outputs including exceptional halts, all differences reproducible; see issue #649 |
| G2 — full machine semantics | Memory bytes, expansion, stack, storage, warm/cold, CALL/CREATE/REVERT, environment, precompiles, logs and fork-selected gas | All supported EVM instruction families compared to EELS and independent clients; formal semantics refinement theorems per supported profile |
| G3 — transaction replay | Transaction envelope/signatures; nonce, balances, intrinsic gas, state changes and authenticated prestate; receipts and poststate roots | Fixed canonical mainnet transactions (ordinary ETH transfer; successful, reverted and storage-mutating calls) replay with independent evidence; see issue #650 |
| G4 — deployed source-to-bytecode contract | Reproducible Solidity compiler metadata and actual deployed runtime code | At least one invariant theorem about a *specific deployment*, with fully declared trust boundary; see issue #651 |
| G5 — execution client | Block transition, historical fork handling, world-state trie, persistent state, Engine API, sync/JSON-RPC | Official state/block/engine fixtures, Hive, historical blocks and multi-client comparisons with no silent coverage gaps; issue #652 |
| G6 — independent assurance | Ethereum semantics specialist, separate Lean proof specialist, and systems-security review | Versioned signed review(s) identifying exact claims, assumptions, code/spec commits, conformance coverage and counterexamples; issue #652 |

G3, G4 and G5 need not be completed in that order after G2: a small
deployed-contract claim can precede a production execution client.

## Two kinds of evidence: neither can substitute for the other

1. **Theorems:** Lean checks that the formal implementation refines a *formally
   stated* semantic relation. The relation's accuracy is a separate review
   obligation. A theorem about a self-defined interpreter is not equivalent
   to correctness relative to Ethereum.
2. **External execution evidence:** EELS, official generated fixtures and
   independent clients check behavior on concrete inputs. They are not
   universal proofs. No successful run may be counted as conformance without
   comparing all relevant expected outputs, not merely a final stack value.

Each check must identify fork, code/state/transaction IDs, source commit,
expected output fields, observed outcome, and whether the check was truly run.

## Mainnet replay: minimum evidence bundle

- Canonical chain ID, block hash/number, transaction hash/index, fork schedule.
- Exact transaction bytes and signature, sender, receiver/created address,
  transaction type and access list.
- Parent and current block context: timestamp, number, base fee, coinbase,
  gas limit, prevRandao and relevant blob/excess-blob/base-fee fields.
- Correct state *immediately preceding the transaction*, **not merely** the
  end of the previous block. For transaction index > 0, replay earlier block
  transactions or supply an authenticated intermediate-state witness.
- Account code hash and code, account balances/nonces, storage and all
  account-trie data required to recompute roots; changes to accessed trie
  paths must be propagated correctly.
- Receipt fields (status, cumulative gas, logs bloom, log entries, effective
  gas semantics) and expected canonical block/receipts roots where applicable.
- Source provider, retrieval date, state proof/witness provenance and
  independent comparison with another source/client.

An RPC debug_traceTransaction is a useful *observation* but not a complete
or normative proof of consensus validity. Some archive endpoints supply
historical state and traces but not the entire authenticated data needed for
independent poststate-root calculation.

## Contract proof: minimum evidence bundle

- Chain ID, deployment address, deployment block hash, runtime bytecode hash.
- Verified/reproducible Solidity source and exact solc version, metadata
  settings, optimizer settings, EVM version, immutables, linked libraries,
  constructor effects and proxy/delegatecall context if any.
- A separate proposition expressing the relevant security or business rule.
- Theorem names and proof assumptions, with an explicit source-to-EVM
  compilation trust boundary (trusted solc / translation validation / verified
  compiler are *different* assurance claims).
- Real bytecode semantics, including exceptional outcomes, gas and
  adversarial external calls, to the extent the theorem's scope requires.
- Reproducible verification commands and independent reviewer notes.

A Sourcify match is evidence of compilation provenance, **not** evidence
that a contract meets a financial or security invariant.

## Immediate implementation priorities

1. Prove a property for an identified Solidity deployment. Build on the
   guarded zero-value ABI dispatcher and its reproducible compiler fixture.
   [Active work, #736](https://github.com/danbri/factoidal-core/issues/736)
2. Extend independent coverage and formal reference correspondence for CALL
   gas, state and nested checkpoints. Implement the other call variants,
   CREATE and precompile execution.
   [Bounded CALL, #744](https://github.com/danbri/factoidal-core/issues/744) ·
   [Machine semantics, #649](https://github.com/danbri/factoidal-core/issues/649)
3. Advance fork-exact transaction and block transitions. Expand authenticated
   mainnet replay to successful, reverted and storage-mutating contract
   calls. Use an independent reference transition relation, and preserve
   unsupported cases in fixture totals. [Transaction replay, #650](https://github.com/danbri/factoidal-core/issues/650)
4. Complete the execution client and check Engine API interoperability with
   an independent consensus client. Obtain external review against the
   exact execution-layer revisions and claims.
   [Execution client and assurance, #652](https://github.com/danbri/factoidal-core/issues/652)
5. Implement and validate the Lean consensus layer, then exercise the
   integrated EL and CL against the full goal's acceptance and review criteria.
   [Full Lean Ethereum execution and consensus goal, #725](https://github.com/danbri/factoidal-core/issues/725)

## Independent external specifications

- https://steel.ethereum.foundation/docs/execution-specs/
- https://steel.ethereum.foundation/docs/execution-specs/running_tests/test_formats/state_test/
- https://steel.ethereum.foundation/docs/execution-specs/running_tests/running/
- https://github.com/ethereum/execution-specs
- https://github.com/ethereum/go-ethereum/tree/master/cmd/evm

Issue tracker: [#649](https://github.com/danbri/factoidal-core/issues/649),
[#650](https://github.com/danbri/factoidal-core/issues/650),
[#651](https://github.com/danbri/factoidal-core/issues/651),
[#652](https://github.com/danbri/factoidal-core/issues/652).

See SOUNDNESS.md for the *current* theorem inventory and trust boundaries.
