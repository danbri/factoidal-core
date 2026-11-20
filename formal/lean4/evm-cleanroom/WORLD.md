# Multi-account transaction-state scaffold

**Scope:** stacked draft PR #659, based on frame rollback PR #656. Not a verified Ethereum execution client.

## Executable components

- `EVMCleanroom/World.lean`: independent per-address code, balance, nonce and storage maps; transaction-original storage snapshot; shared transaction refund; account-and-slot warm access map; `runAt` executes existing `Frame.run` for a selected account, committing successful storage effects only for that account.
- `EVMCleanroom/WorldTests.lean`: execute a successful storage-modifying frame on account 1, followed by a reverting storage modification on account 2; verify account 1 remains modified, account 2 is restored, and transaction-original snapshots, balances, nonces and warmth remain consistent.
- `EVMCleanroom/Value.lean`: validated 160-bit account identifiers, 256-bit initial account balances, funded transfers, recipient-overflow checks and exact self-transfer identity.
- `EVMCleanroom/ValueTests.lean`: conservation cases, insufficient-funds, address bounds, initial balance bounds and recipient overflow.

## Machine-checked claims

- `World.commitFrame_other_account`: any successful frame commit leaves every distinct account unchanged, including its code, balance, nonce and storage.
- `World.commitFrame_original` and `World.commitFrame_other_warmth`: successful frame updates cannot rewrite transaction-original storage or warm unrelated accounts.
- `World.runAt_revert_world_unchanged` and `World.runAt_exception_world_unchanged`: the actual framed execution driver discards all world changes on an unsuccessful frame.
- `World.payUnchecked_conserves_pair`: two distinct account balances conserve value when the sender is funded.
- `World.pay_conserves_pair`: the checked transfer operation conserves the pair's combined balance whenever it returns `.ok`.
- `World.pay_preserves_original`: successful transfers leave transaction-original storage snapshots unchanged.

These theorems are checked in Lean; `#print axioms` and the CI axiom audit expose the trusted logical axioms. They prove local-model facts. They are **not** machine-checked refinements to independent EELS semantics.

## Reproduce

From `formal/lean4/evm-cleanroom`, run `lake build`; check the new proof sources with `lake env lean EVMCleanroom/World.lean` and `lake env lean EVMCleanroom/Value.lean`. The dedicated `.github/workflows/evm-cleanroom.yml` also reruns inherited synthetic EVM, storage, frame and restricted EELS checks.

## Critical incomplete functionality

Running account A and then account B through `runAt` is not executing EVM `CALL`: there is no stack-driven call dispatcher, environment/returndata propagation, calldata, EIP-150 gas forwarding, nested value transfer, precompiles, logs or call-depth enforcement. The world uses functional account mappings rather than authenticated Merkle Patricia tries; addresses passed to `runAt` are not yet subtype-checked. No nonempty official EELS state-root replay is claimed. Balance transfers exist as a checked pure operation but are not wired to CALL, CREATE or settlement.

Before any broader Ethereum assurance claim, implement nested calls and their journal, EELS-derived fork-specific semantics, receipts, post-storage and post-state roots, transaction accounting and a fixed canonical mainnet replay bundle. See issues #649–#654.