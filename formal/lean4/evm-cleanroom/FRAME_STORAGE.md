# New executable slices: SLOAD/SSTORE and RETURN/REVERT

**Snapshot: 20 November 2026. These slices are not an Ethereum client or
full EELS state-test executor.** This note covers stacked PRs
[#655](https://github.com/danbri/factoidal-core/pull/655) (storage)
and [#656](https://github.com/danbri/factoidal-core/pull/656) (frame
checkpoints). The original SOUNDNESS.md documents the earlier restricted
base; do not conflate its 2026-11-19 scope with these new changes.

## What actually executes

- **SLOAD (0x54):** reads single-account persistent storage, 2100 gas cold
  or 100 gas warm, and adds the key to the warm-access set only after a
  gas-checked commit.
- **SSTORE (0x55):** original/current/new value distinction, clean/dirty
  costs, EIP-2200 net metering, EIP-2929 cold surcharge and 2300 stipend
  check, EIP-3529 signed refund changes, static-write protection.
  Transaction-original slot values cannot be mutated by committed steps.
- **RETURN (0xf3) and REVERT (0xfd):** a separate scoped Frame runner applies
  memory-expansion charges, records output offset/length and distinguishes
  successful return from reverted execution. The CLI materializes return
  bytes only if length <=4096, otherwise reports unsupported observation.
- **Reverted or exceptional top-level frames:** restore the pre-frame
  persistent-storage snapshot (including slot warmth and signed refund).
  REVERT preserves unused frame gas; exceptional halts consume it. Fuel
  exhaustion and unsupported instructions are classified **unsupported**,
  not Ethereum-invalid.

The Core.run CLI remains a *restricted raw-bytecode* interface; for new
RETURN/REVERT behaviour use the explicit Frame.run / --frame-storage
entrypoint. Both operate on one storage account. Addresses, calls and
transaction-wide side effects are not yet implemented.

## Proof inventory, including executable-driver connection

Proofs checked by Lean 4.33.1, with #print axioms and CI axiom audit:

- Storage.store_read_same, store_read_other, store_original,
  store_warm_read, touch_warm_read, noop_refund, store_refund_exact:
  one-account storage data and pricing helpers.
- commit_original_unchanged, step_original_unchanged,
  Trace.original_unchanged, run_original_unchanged: starting original
  storage values stay immutable for *arbitrary successful Core.run
  executions*, not merely hand-constructed abstract traces.
- commit_static_current_unchanged: a successful commit in static mode
  cannot modify its current storage.
- Frame.restore_current/original/warmth/refund: the checkpoint restoration
  operation restores every key's storage state and refund.
- **Frame.run_revert_atomic:** every Frame.run result classified REVERT has
  exactly the entry values for all storage keys, the original map,
  the warm-access set and refund counter.
- **Frame.run_exception_atomic:** every Frame.run exceptional result
  preserves the entry current storage and refund and has zero gas left.

These last two results are properties of the *actual new execution driver*
for any bytecode, gas, fuel and key. Their proofs reduce the execution
outcome to the checkpointing branch and then prove the equality of storage
snapshots. This is useful, but the checkpoint model is our own;
**these are not yet machine-checked refinements of independent EELS rules**.

The #print axioms output on the current PR lists standard Lean axioms such
as propext, not sorryAx, for these new driver theorems. This is not a proof
of the Lean compiler, runtime or external JavaScript fixture host.

## Reproduction

From formal/lean4/evm-cleanroom:

    lake build
    lake exe evm-subset --storage 600160005500 30000 6 0 0
    lake exe evm-subset --frame-storage 600160005560006000fd 30000 12 0 0
    lake exe evm-subset --frame-storage 600160005560006000f3 30000 12 0 0

The REVERT example updates slot zero, then rolls it back. The RETURN
example retains the update. Both deduct execution gas.

Independent comparison:

    npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
    node scripts/differential/storage.mjs
    node scripts/differential/frame.mjs

The pinned @ethereumjs/evm 10.1.3 Prague oracle compares 136 single-slot
storage histories against the actual Lean CLI (slot, original, remaining
gas, refund), plus 13 top-level frame outcomes against EthereumJS runCall
(checkpoint/revert, output data, gas, state and refund). CI gates both
against **zero disagreements**, in addition to the original 10,000-case
synthetic bytecode differential and restricted 4/6 official EELS
empty-code state-root replays.

The newly tested storage/frame examples are **not** official EELS state
fixtures. The existing EELS runner still does not accept nonempty
state-changing contract code or reproduce a storage post-state root.

## Consensus-critical gaps before stronger claims

1. Address-keyed world state and authenticated Merkle Patricia account and
   storage tries; transaction prestate and state-root reconstruction.
2. Nested CALL/CALLCODE/DELEGATECALL/STATICCALL, CREATE/CREATE2, state
   journaling, return-data propagation, LOGs and precompiles.
3. Full transaction execution and gas settlement including refund caps,
   intrinsic gas, signed envelopes, access lists, typed transactions,
   receipts and block validation.
4. Complete historical fork schedule. The coarse preShanghai profile rejects
   storage operations as unsupported rather than misusing Prague prices.
   The storage module's constants apply to post-London/Prague, not earlier
   SSTORE schedules or future repricings.
5. Independent declarative Ethereum semantics and fork-indexed Lean
   refinement theorems; official EELS contract state tests, adversarial
   differential fuzzing against multiple clients and historical mainnet
   state-changing transaction/block replays.
6. Consensus-layer state transition/fork choice and the complete networked
   Ethereum client; runtime, disk, crash and security assurance.

For questions about whether a theorem proves *Ethereum* rather than just
the local model, inspect the independently specified semantic relation,
upstream fork/spec pin, assumptions, exact test scope and source-to-output
trust boundaries.

References:
[EIP-140](https://eips.ethereum.org/EIPS/eip-140),
[EIP-2200](https://eips.ethereum.org/EIPS/eip-2200),
[EIP-2929](https://eips.ethereum.org/EIPS/eip-2929),
[EIP-3529](https://eips.ethereum.org/EIPS/eip-3529),
[EELS](https://github.com/ethereum/execution-specs).
