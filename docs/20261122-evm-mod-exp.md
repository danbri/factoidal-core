# EVM MOD and EIP-160 EXP — bounded executable increment (22 November 2026)

Tracking: [MOD/EXP scope and intended theorems](https://github.com/danbri/factoidal-core/issues/757).
Execution-layer goal: [#652](https://github.com/danbri/factoidal-core/issues/652).
Full Lean EL+CL goal: [#725](https://github.com/danbri/factoidal-core/issues/725).

## Executable changes

- `Core.step` dispatches `0x06 MOD` with unsigned remainder and a zero result for a zero divisor, charging five gas.
- `Core.step` dispatches `0x0a EXP` on `shanghaiPlus` and `osaka` through `Word.powMod`. The helper uses a structurally bounded square-and-multiply algorithm with at most 256 exponent-bit iterations and early exit after a zero exponent. Every multiplication is reduced modulo 2^256 before another iteration. It never constructs the mathematical unbounded power.
- The post-EIP-160 price is `10 + 50 * (floor(log2(exponent)/8) + 1)` for nonzero exponent and 10 for zero exponent. Each opcode pays through `commit`, after computing the operation plan.
- The coarse `preShanghai` profile cannot distinguish pre-EIP-160 and post-EIP-160 historical pricing. It explicitly refuses EXP; that refusal **does not** count as a supported historical-fork execution. MOD remains available.
- The zero-value, read-only frame policy now admits both opcodes, allowing a real raw-bytecode and ABI-path comparison.

## Theorems / verification obligation

The five intended statements are declared in the actual `EVMCleanroom/Core.lean` source:

- `EVMCleanroom.Word.modulo_zero`: zero divisor yields zero.
- `EVMCleanroom.Word.powMod_zero`: zero exponent yields one, including 0^0.
- `EVMCleanroom.expGas_zero`: ten gas when exponent is zero.
- `EVMCleanroom.step_mod`: real dispatcher, pop order and five-gas commit path.
- `EVMCleanroom.step_exp`: real dispatcher, the bounded helper and the EIP-160 gas formula enter the shared gas-checked commit path.

The manifest records *expected* axiom sets, not a compiler pass. The source-pinned Lean 4.33.1 CI must independently compile every theorem and compare actual `#print axioms` with those expected lists. No `sorry`, new axioms, `native_decide`, `unsafe` or unbounded recursion were added. A separate universal theorem showing `Word.powMod` equals the mathematical `base^exponent mod 2^256` is still missing. The independent EVM oracle checks finite cases and does not substitute for that proof.

## Differential and regression gates

The updated pinned `@ethereumjs/evm@10.1.3` Shanghai oracle harness adds 169 execution cases: a 64-case MOD matrix, two MOD errors, a 96-case EXP matrix, six precise gas-threshold cases (0-, 1- and 2-byte exponents) and one EXP underflow. The matrix covers zero, sign-bit and maximal 256-bit values, exponents 255 and 256, high-bit exponents, and short/long exponent-byte charges. Oracle expectations come from EthereumJS execution rather than duplicated JavaScript implementation.

Run within `formal/lean4/evm-cleanroom` (with Lean 4.33.1 and the environment's single-build lock):

```sh
lake build
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/solidity-pure.mjs
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
```

The unchanged 10,000-program corpus, official maintained EELS fixture selections, Frontier witness replay and broader repository Linux/premerge gates must also pass against the exact new commit. Before any hosted run completes, **no new passing totals are claimed**. Existing recorded passes belong to their old commits. Historical unsupported/unexecuted forks, missing opcode families, CREATE/precompiles, transactions, blocks, Engine API and Lean consensus remain in scope and unfinished.

## Performance

There is no local Lean compiler or native performance runner in this execution environment. Thus no before/after latency sample is claimed here. The existing observed raw-10,000 batch median and tail increase in [#739](https://github.com/danbri/factoidal-core/issues/739) remains open. Once executable CI/native timing is available, compare raw and ABI results with p50/p95/p99/max, not only arithmetic averages.

This is a restricted EVM implementation increment, not complete execution-client or consensus conformance.
