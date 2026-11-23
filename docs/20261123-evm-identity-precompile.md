# Independently implemented Lean EVM identity precompile — 23 November 2026

## Tested implementation and deliberate scope

[Issue #835](https://github.com/danbri/factoidal-core/issues/835) records the model and theorem obligations before coding. [Draft PR #837](https://github.com/danbri/factoidal-core/pull/837) stacks on independent execution [draft PR #827](https://github.com/danbri/factoidal-core/pull/827), head `0b60a50eeb06db84366877cd54c8eab9ad424046`. Work is disjoint from independent consensus SSZ [#834](https://github.com/danbri/factoidal-core/issues/834).

The Lean module `EVMCleanroom.IdentityPrecompile` implements **the address-0x04 identity precompile's bytes and gas**:

- Input length `n` costs `15 + 3 * ((n + 31) / 32)` gas, with natural integer division; the caller supplies the **child gas**, not the parent's complete budget.
- If `input.size > maxBytes`, the function returns `.error .resourceLimit` **before allocating an output**. This is a local implementation refusal and must be reported as indeterminate rather than as an Ethereum exceptional halt.
- Otherwise insufficient supplied gas gives `.error .outOfGas`; sufficient gas returns exactly the same array with remaining gas `gas - charge`.
- No external EVM implementation, EthLib, third-party crypto library, FFI or imported host executor is used. The only added Lean imports are existing repository-owned `EVMCleanroom.Core`, `EVMCleanroom.IdentityPrecompile` and `EVMCleanroom.CLIEncoding`. The original empty Lake external dependency graph remains empty, and Lean is pinned to **4.33.1**.
- `evm-identity-precompile` is a direct native executable. It handles `HEX GAS MAX_BYTES` or `--batch RECORDS.tsv`, with exact output bytes and decimal-string gas. Its JSON output distinguishes success, EVM out-of-gas, local resource refusal and malformed input.

**Important boundary:** This is **not yet connected** to the actual EVM `CALL`, `CALLCODE`, `DELEGATECALL` or `STATICCALL` dispatch. Those code paths still reject precompiles. It is a testable execution component, not completed Ethereum contract composition or fork-complete precompile support.

## Actual Linux compilation and independent evidence

The source state at **`49b45fdaf3a5c9e073116c9b454dce0c4e43ec95`** passed the [dedicated fresh Linux run 45213565261](https://github.com/danbri/factoidal-core/actions/runs/45213565261) on 23 November 2026. All eight job phases passed, including clean library compilation, native target build, source-pin and dependency checks, actual printed axiom checks, independent full-output comparisons and direct invocation checks.

Five named theorems compiled and produced the following **actual** kernel axiom sets:

| Theorem, qualified under `EVMCleanroom.IdentityPrecompile` | Printed axioms |
| --- | --- |
| `execute_oversize` | `propext` |
| `execute_underfunded` | `propext`, `Quot.sound` |
| `execute_exact` | `propext`, `Quot.sound` |
| `execute_preserves_input` | `propext`, `Quot.sound` |
| `execute_gas_accounting` | `propext`, `Quot.sound` |

No `sorryAx`, user axiom or unpermitted dependence was reported for these declarations. The three explicit axiom-checker corruption cases were rejected. These are local execution-path properties, **not** a Lean-to-EELS refinement proof.

Seventeen `#guard` evaluations compiled. The independent Python standard-library oracle checked **1,056 actual Lean results**, with **1,056 matching, zero mismatches**: 528 successful outputs, 176 EVM out-of-gas exceptions and 352 implementation resource refusals. It compared **122,207 input bytes** and entire output JSON objects, including gas and byte identity. Three independent comparator mutations (data, gas and verdict) were rejected. A malformed batch record was also rejected with exit code 2.

The machine-readable source-blob/axiom/evidence pin is [`claims.json`](../formal/lean4/evm-cleanroom/evidence/2026-11-23-identity-precompile/claims.json). The retained active EVM assurance ledger still contains its original 184 theorem selections and 103 source pins; the changed Lake file and library entry root were re-pinned rather than silently inheriting old hashes. The five new declarations are recorded **separately** in this phase ledger, not added to earlier counts.

## Reproduction

Working directory for each Lean command: `formal/lean4/evm-cleanroom`. On the shared Mac, wrap builds in the prescribed single-build lock. On Linux CI:

```sh
lake build EVMCleanroom
lake build evm-identity-precompile
python3 scripts/check-active-ledger.py
python3 scripts/check-identity-axioms.py --selftest
python3 scripts/check-identity-axioms.py
python3 scripts/differential/identity-precompile.py .lake/build/bin/evm-identity-precompile
.lake/build/bin/evm-identity-precompile 0x0001 18 2
```

The final command prints a successful result with `dataHex=0001`, `gasUsed=18` and `gasRemaining=0`. Exact-gas minus one gives out-of-gas; input longer than the caller cap gives a local resource refusal.

## Regression and remaining obligations

At the evidence capture time, [exact-source Frontier replay 45213565021](https://github.com/danbri/factoidal-core/actions/runs/45213565021) and AES had passed. The EVM cleanroom, broader Lean corpus and npm jobs were still in progress. They are separate gates and must be checked before any merge. No local Lean compilation, paired latency samples, independent expert review or broad premerge gate is claimed. The specialised Linux result does not prove runtime-tail performance parity.

The next required implementation step is **integration into the existing CALL-family continuation** with exact address-0x04 dispatch precedence, account-witness handling, warm-address rules, parent memory/input/output windows, child gas return, rollback and static/delegate behavior. That code must then be checked against at least two mature clients, retained EVM regressions and source-connected proofs before claiming integrated precompile support. Other precompiles, complete fork rules, transaction/block/state fidelity, EL networking, all Lean beacon consensus and independent full-client review remain open under [#725](https://github.com/danbri/factoidal-core/issues/725).

No changes were made to Ethereum accounts, signatures, private keys, wallets or network transactions. The PR remains draft and unmerged.
