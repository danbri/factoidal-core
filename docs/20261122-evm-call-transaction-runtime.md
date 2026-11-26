# Ordinary Ethereum call transactions from explicit state witnesses

Issue [#796](https://github.com/danbri/factoidal-core/issues/796) extends the
execution layer work in [#652](https://github.com/danbri/factoidal-core/issues/652)
towards the full execution and consensus goal in
[#725](https://github.com/danbri/factoidal-core/issues/725).

## Execution boundary

The Lean CLI takes `--call-transaction REQUEST.json`. The host verifies and
decodes the signed envelope, anchors block context, authenticates the account
and storage witnesses, and checks code against the witnessed code hash.
Lean receives the recovered sender and decoded fields for Shanghai or Cancun
transaction types 0, 1 and 2, with a 160-bit destination for an ordinary call.
The host also serialises the receipt and rebuilds the post-state trie.

The transaction runner computes calldata and access-list intrinsic gas and
validates nonce, block and transaction gas, fee caps and sender funds. It
increments the nonce and escrows the effective gas fee before transferring
value. It seeds the warm address and slot sets and enters the existing nested
CALL dispatcher with actual calldata and block and transaction context.
REVERT and exceptional halts restore the world after fee escrow and before
value transfer. Both settle a status-zero receipt. A successful execution
settles with the updated world and reads the accumulated logs in execution
order. Fee settlement limits refunds to one fifth of gross gas and credits
the sender refund and beneficiary tip in order, including aliases.

The host lists every account the execution can read, including proved
absences, and every storage key that may be read or written, including zero
values. The dispatcher checks that coverage before reading a value. A missing
witness, exhausted simulation fuel, unsupported opcode or exceeded resource
cap yields `indeterminate` without accounts or a receipt. Whole transaction
requests allow at most 100 million gas, one million simulator dispatches,
1,024 account records, 4,096 access-list entries, 4,096 slots per witness or
access-list entry, and 16,384 total slots or access-list keys. Code is limited to
1 MiB per account and 16 MiB in total. The JSON input has a 16 MiB limit, as does the combined return-byte and log
observation. Present-empty account records
yield an explicit witness refusal in this profile. The coarse Shanghai
dispatcher conservatively refuses some ordinary addresses in the range later
reserved for Cancun and Prague precompiles.

Native Keccak requires the explicit leading CLI flag
`--dangerously-enable-unverified-keccak`, and output records `keccakOptIn`.
The default rejects an attempted hash without producing a receipt. This flag
is for the separately scoped experimental hash path, including public test
fixtures. Contract creation, precompiles and all-fork transaction or block
transition coverage remain separate obligations in #652 and #725.

## Checked Lean properties

The pinned Lean 4.33.1 build completed all 58 jobs for the runtime and CLI.
The proof inventory covers the actual admission, dispatcher, settlement and
balance update functions. In the table, theorem names without a qualifier
are in namespace `EVMCleanroom.CallTransaction`.

| Actual printed axioms | Theorems |
|---|---|
| `[propext, Classical.choice, Quot.sound]` | `admit_checked`, `run_executed_admitted`, `EVMCleanroom.CallOpcode.execute_missing_sload`, `EVMCleanroom.CallOpcode.execute_missing_sstore` |
| `[propext]` | `debitSender_projection`, `charge_bounded`, `charge_escrow_exact`, `finish_projection`, `finish_balance`, `settleFrame_reverted_checkpoint`, `settleFrame_exception_checkpoint`, `settleFrame_reverted_balance`, `settleFrame_exception_balance`, `EVMCleanroom.CallOpcode.beginCall_missing_account` |
| No axioms | `settleFrame_indeterminate`, `EVMCleanroom.CallOpcode.finishCall_logs_projection` |

These claims establish local properties of the executable model. The proof
boundary assumes the decoded envelope and verified witness supplied to it.
Normative fork refinement, authentication implementation proofs and independent
whole-client review remain tracked separately.

## Synthetic signed transaction matrix

The runner `scripts/eels/call-transaction-differential.mjs` creates independent
synthetic accounts and signs transactions with a public fixture key. It
decodes the same bytes for both engines. Its trace checks that the synthetic
prestate explicitly covers the storage reads and writes and CALL targets used
by the reference. No network access or real funds are required.

- All **60 signed executions** matched `@ethereumjs/vm@10.1.3` `runTx`. They
  compare outcome and return bytes, gross/charged gas, gas refund, effective
  price, base-fee burn, beneficiary tip, ordered logs and account/storage
  projection. The shared host receipt codec and trie implementation produce
  exactly matching typed receipt bytes and post-state roots in all 60 cases.
- A separate **eight signed admission rejections** match independent
  rejection, including a transaction signed for a different chain, incorrect
  nonce and insufficient maximum upfront funds. An additional max-nonce
  case was independently refused before serialisation and challenged at
  Lean's decoded boundary.
- **Eleven separate indeterminate controls** cover omitted account and
  storage witnesses, fuel and simulator gas limit, missing hash opt-in,
  unsupported features and malformed witness shape. EthereumJS completes each
  of the corresponding complete, supported synthetic reference executions.
- The same comparators detect three deliberately changed observations
  covering gas, receipt log topics and post-state balance.

Reproduce with the executable built from `formal/lean4` using
`lake -d evm-cleanroom build EVMCleanroom evm-subset evm-call-transaction`.
The `evm-subset` invocation forwards to its sibling transaction executable. From
`formal/lean4/evm-cleanroom`, install the pinned dependencies for
`scripts/eels`, then run

```bash
node scripts/eels/call-transaction-differential.mjs "$PWD/.lake/build/bin/evm-subset"
```

The initial single-binary build recorded SHA-256
`a5ab16c6f3049f7897305065536902445ee4ed0449673bb08f2f164b41c36436`.
