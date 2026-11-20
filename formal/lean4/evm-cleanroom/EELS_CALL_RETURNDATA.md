# EELS CALL → RETURN → RETURNDATACOPY → storage: reproducible proof/evidence ledger

**Status: first real official EELS-generated Cancun CALL-context state-root replay, scoped.** This is not a full EVM, blockchain client, independently verified trie implementation or normative EELS refinement theorem.

## Official fixture and exact result

- Fixture source: `ethereumjs/execution-spec-tests-fixtures`, mirror commit `3c4287ae3aea1f45af9288629834f0584fcde69a`, `stable/state_tests/shanghai/eip3855_push0/test_push0_contract_during_call_contexts.json`.
- SHA-256 of exact JSON fixture bytes: `a20350b0b4bc0f0d6e6bbcaa5b4cc24f5b2bfc3537ea37ab343767feeecb5e05`.
- EELS test ID: `tests/shanghai/eip3855_push0/test_push0.py::TestPush0CallContext::test_push0_contract_during_call_contexts[fork_Cancun-state_test-call]`.
- Published **and reproduced** post-state root: `0x87c138760a85e3e5ee9236ff3bf895b5bf32c210153a800dc18bd0fae7be425c`.
- Fixture: 16 total cases across forks; 4 Cancun cases; **1 passed, 0 failed, 3 explicitly unsupported** (CALLCODE, DELEGATECALL and STATICCALL). Twelve other-fork cases are not executed. No general CALL-family or multi-fork claim.
- Verified independent CI run: [44783929795](https://github.com/danbri/factoidal-core/actions/runs/44783929795), with the existing 6/6 earlier Cancun nonempty contract roots and 4/6 restricted Prague empty-code state-root replays still green.

## End-to-end observable path actually executed in Lean

1. The parent executes real `CALL` (`0xF1`) bytecode with a 160-bit target, zero transferred value and zero CALL input/output ranges. EIP-2929 address pricing precedes EIP-150 forwarded gas capping.
2. The child runs its own bytecode and uses `MSTORE8` to place `0xff` in memory, then `RETURN` (`0xF3`) sends exactly one byte. For REVERT (`0xFD`) test paths the returned bytes remain observable while storage effects roll back.
3. The parent retains the byte in an EIP-211 return-data buffer, uses `RETURNDATACOPY` (`0x3E`) to place it at memory byte 31, and `MLOAD` reads a 256-bit word whose low byte is `0xff`.
4. The parent executes `SSTORE` into slot one (255), in addition to slot zero (1). The signed transaction's restricted balance/nonce/fee settlement is computed by Lean `TxAccounting`.
5. A separate JavaScript host checks the signed envelope and reconstructs the sender, parent, child and coinbase account set and the complete world-state root. It uses **trusted EthereumJS account encoding, code hashing, storage trie and MPT hashing**, not EthereumJS VM execution of the transaction.

## Formal facts now checked in Lean

- `ReturnData.copy_has_exact_bill`: every successful EIP-211 return-data copy through the actual `commit` path has a reconstructible opcode, word-copy and memory-expansion gas charge. Axiom audit: `[propext, Quot.sound]`.
- `ReturnData.copy_original_unchanged`: every successful copy preserves transaction-original storage; axiom audit: `[propext]`.
- Existing `OpcodeCall.run_exception_world_atomic`: exceptional parent execution restores accounts, transaction-original storage, refunds and slot warmth, even when a prior child completed successfully. These are statements about the **defined Lean interpreter**, not yet machine-checked equivalence with EELS.

## Other external checks and falsification

- [The CI differential gate](https://github.com/danbri/factoidal-core/pull/676) executes five additional complete parent/child bytecode scenarios in Lean and independent EthereumJS Cancun: RETURN data copied into storage, REVERT data copied, empty return buffer, exceptionally failing child, and RETURNDATASIZE.
- `scripts/eels/call-context-selftest.mjs` changes the official expected root, slot one post-value, sender metadata, child RETURN bytecode or fixture inventory; all five mutations must be rejected.
- Active assurance manifest v2 integrity-pins the source blobs for the new interpreter, return-data logic, EELS host, tests, independent comparison and the two newly audited theorems. It checks the *fresh* EELS CALL report with exact fixture ID, root, storage effects and unsupported case classifications.

## Reproduction

From `formal/lean4/evm-cleanroom`:

```sh
lake build
npm ci --prefix scripts/eels --ignore-scripts --no-audit --no-fund
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
mkdir -p .lake/eels
curl -fL https://raw.githubusercontent.com/ethereumjs/execution-spec-tests-fixtures/3c4287ae3aea1f45af9288629834f0584fcde69a/stable/state_tests/shanghai/eip3855_push0/test_push0_contract_during_call_contexts.json -o .lake/eels/push0-call-contexts.json
printf 'a20350b0b4bc0f0d6e6bbcaa5b4cc24f5b2bfc3537ea37ab343767feeecb5e05  .lake/eels/push0-call-contexts.json\n' | sha256sum --check
node scripts/eels/run-lean-call-context.mjs --fixture .lake/eels/push0-call-contexts.json --out .lake/eels/lean-call-context-results.json
node scripts/eels/call-context-selftest.mjs .lake/eels/push0-call-contexts.json
node scripts/differential/returndata.mjs
python3 scripts/check-active-ledger.py --call-result .lake/eels/lean-call-context-results.json
```

## Trust and remaining work

The return-data implementation presently observes at most 4096 child bytes; oversized return values are explicitly unsupported. There is no general value-stipend logic, nonzero calldata or CALL output-memory copying, nested/reentrant CALL, CALLCODE/DELEGATECALL/STATICCALL, precompiles, receipts/log-bloom computation, arbitrary account/storage-trie representation in Lean, complete historical fork schedule, mainnet block replay, Engine API, consensus client, or independent full EELS refinement theorem.

**The highest-value next step is one real canonical mainnet transaction replay with authenticated pre-state, coupled with a separately stated and reviewed EELS-equivalent semantics for the supported CALL/RETURN/RETURNDATACOPY path.**

Related PRs: #642, #655, #656, #658, #659, #661, #662, #668, #669, #676; issue #660.