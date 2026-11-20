# Executed EELS nonempty-contract evidence: Cancun PUSH0

**Claim (20 November 2026):** on [CI run 44738540988](https://github.com/danbri/factoidal-core/actions/runs/44738540988), six of six official EELS-generated Cancun `test_push0_contracts` vectors executed with the Lean EVM and reproduced the published account post-state roots. No cases failed or were unsupported within the Cancun subset; the same fixture contains 18 other-fork cases not in this gate.

## Exactly what ran

- Fixture mirror: `ethereumjs/execution-spec-tests-fixtures` at commit `3c4287ae3aea1f45af9288629834f0584fcde69a`, file `stable/state_tests/shanghai/eip3855_push0/test_push0_contracts.json`; SHA-256 `1eb74ceb4d3a4fefaa93f907e85f4d3632cc3f376448488fe04e84fc5c50cfba`.
- Fork under test: **Cancun**, not Prague. Restricted signed legacy transactions with empty calldata, zero transferred value, zero refunds, two initial accounts, and contract storage observation restricted to slot zero.
- **Lean frame execution:** nonempty contract EVM bytecode, implicit STOP, PUSH0, PUSH1/PUSHn, OR, DUP/SWAP, jumps, GAS and SSTORE. Charge actual instruction gas, record full exceptional frame failure and rollback.
- **Lean transaction settlement:** restricted sender balance/nonce, base-fee burn and coinbase reward arithmetic via `--tx-fee`; the Prague EIP-7623 empty-calldata floor coincides with the Cancun intrinsic cost of 21,000 in these specifically zero-calldata examples. No assertion of general Cancun/Prague fee equivalence.
- **Trusted host:** EthereumJS signed transaction decoding, sender recovery, account code hashing, storage-trie and world-state MPT serialization; JavaScript fixture mapping and post-state comparison. There is **no EthereumJS EVM execution** inside this runner.
- Account-level validation includes code, balances, nonce and sparse post-storage value, and published post-state root. Published logs hash is compared to a fixed empty-log hash: no general log generation or receipt root is verified.

## Results

| Cancun vector | Outcome in Lean | Main semantic test |
| --- | --- | --- |
| `before_jumpdest` | success | JUMP skips PUSH0 immediate and stores 1 |
| `fill_stack` | success | 1,024 PUSH0 operations reduced with 1,023 ORs, stores 1 |
| `gas_cost` | success | GAS-sensitive computation and SSTORE of 2 |
| `key_sstore` | success | Cold SSTORE of 1 at slot zero |
| `stack_overflow` | exceptional | Store occurs before stack overflow; entire frame rolls back and burns remaining gas |
| `storage_overwrite` | success | Storage writes and net metering; slot zero ends at 2 |

All six published post-state roots matched exactly. The stored slot values also matched all published post-account states. This is **not** an independently computed expected storage-root oracle: the final global state root depends on EthereumJS storage trie hashing.

## Reproduction

From `formal/lean4/evm-cleanroom`:

```sh
lake build
npm ci --prefix scripts/eels --ignore-scripts --no-audit --no-fund
mkdir -p .lake/eels
curl -fL https://raw.githubusercontent.com/ethereumjs/execution-spec-tests-fixtures/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/shanghai/eip3855_push0/test_push0_contracts.json -o .lake/eels/push0-contracts.json
printf '1eb74ceb4d3a4fefaa93f907e85f4d3632cc3f376448488fe04e84fc5c50cfba  .lake/eels/push0-contracts.json\n' | sha256sum --check
node scripts/eels/run-lean-contract-state-tests.mjs --fixture .lake/eels/push0-contracts.json --out .lake/eels/lean-contract-results.json
node scripts/eels/contract-selftest.mjs .lake/eels/push0-contracts.json
```

The self-test requires rejection of a forged published state root, forged post-storage value, changed sender and removed fixture case. Full raw fixture and JSON reports are uploaded as GitHub Actions artifacts.

## Remaining high-priority obligations

Independent EELS semantic-refinement theorems for SSTORE, OR and exceptional frame rollback; transaction-level receipts, logs and refund caps; EVM CALL/CREATE and nested frame journaling; complete address-keyed world state; independently implemented trie/RLP/Keccak and authenticated prestate; mainnet transaction replay; all historical forks and consensus layer. These six successes are an independently published **test subset**, not generalized Ethereum conformance.

Related: PRs #642, #655, #656, #658, #659, #661; issues #649, #650, #654, #660.