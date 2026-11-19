# From Lean EVM seed to independently reviewed Ethereum execution

**Project state: 2026-11-19.** This is a *dependency graph with exit gates*, not a claim
that any downstream milestone is complete. This repository contains a limited
opcode interpreter with internally checked Lean theorems. Upstream current
reference: https://github.com/ethereum/execution-specs .
The older ethereum/execution-spec-tests repository was archived in July 2026.

## Scope: three promises that must remain distinct

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
receipts. This does **not** automatically verify beacon-chain PoS consensus:
a production node pairs with an independently validated consensus client.

Do not promote any success in A to B or C without separate evidence.

## Acceptance gates (ordered by dependencies, not by excitement)

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

1. Keep the standalone CLI executable under GitHub Actions, with a
   machine-readable schema, strict parse errors, and deterministic outputs.
2. Fix fuel termination semantics so STOP with the last available step
   succeeds; add tests and adjust the actual-run trace proof accordingly.
3. Implement the official fixture adapter using the maintained EELS
   state-test schema; always preserve unsupported tests in the denominator.
4. Add a genuinely separate reference transition relation (do not reuse
   our current opcode dispatch to define the reference's result).
5. Start with a fork-scoped arithmetic/flow subset and **then** add
   memory bytes, MLOAD/MSTORE/RETURN/REVERT, storage, CALL and accounts.
6. Select fixed public mainnet transactions with small reproducible
   state witnesses, advance first to genuine state-test replay, then
   mainnet block/transaction replay.

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
