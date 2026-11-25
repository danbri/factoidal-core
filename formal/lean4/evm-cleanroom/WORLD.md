# Multi-account transaction-state scaffold

The transaction world supplies account state to single-frame and nested CALL execution. The scope is a functional account journal.

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

## Single-frame and nested execution

`World.runAt` runs a single selected account through `Frame.run`. `CallOpcode.run`
uses the same account projections with an explicit continuation list for
stack-driven `CALL` (`0xf1`). It prices caller memory windows, passes child
calldata and returndata, checks depth, applies value transfer when funded,
and journals account state, warmth, refunds and logs around each child.
Parent REVERT and exceptional execution restore the entry world.
[CALL dispatcher](EVMCleanroom/CallOpcode.lean) ·
[Executable and test scope](README.md#calldata-and-bounded-call-execution)

The world uses functional account mappings and natural-number addresses.
The call-transaction entry checks reached accounts and storage slots against
the supplied witness set. An explicit account witness can record absence.
The replay host authenticates those facts and handles trie serialisation.
Open work includes authenticated general world state, fork-exact semantics,
other CALL variants, CREATE, precompiles and complete block settlement.
[Call-transaction boundary](README.md#witness-limited-call-transactions) ·
[Published replay scope](README.md#published-eels-state-test-replay) ·
[Machine semantics, #649](https://github.com/danbri/factoidal-core/issues/649)
