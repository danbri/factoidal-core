# CALL resumption and child execution boundaries

The regressions cover [issue #734](https://github.com/danbri/factoidal-core/issues/734)
and continuation work in [#652](https://github.com/danbri/factoidal-core/issues/652),
[#650](https://github.com/danbri/factoidal-core/issues/650) and
[#654](https://github.com/danbri/factoidal-core/issues/654).

On return from CALL, the caller now reads its current storage, warm slots,
balance and refund from the resulting child world. It retains its original
transaction storage snapshot. This matters for a successful self-CALL,
which changes the same account whose resumed frame may commit at STOP or
RETURN. An unsuccessful parent still restores the entire entry world.

Zero-value CALL inherits the caller's static flag. Both value paths inherit
its opcode profile. A static child that attempts SSTORE consequently fails
with write protection, and the caller can observe a zero success bit.

Both schedulers return an indeterminate outcome for precompile addresses
before ordinary account dispatch. The coarse pre-Shanghai profile excludes
the precompile set through Shanghai. The pre-Osaka Shanghai-and-later profile
also excludes the Cancun and Prague additions. Osaka also excludes
`P256VERIFY` at `0x100`. The added address ranges follow
[EIP-4844](https://eips.ethereum.org/EIPS/eip-4844),
[EIP-2537](https://eips.ethereum.org/EIPS/eip-2537) and
[EIP-7951](https://eips.ethereum.org/EIPS/eip-7951). These opcode profiles
cover a subset of their respective execution rules. Precompile execution and
its gas costs remain to be implemented.

## Checked theorems

Names below are in the `EVMCleanroom` namespace. The final column records
the Lean build's `#print axioms` results.

| Theorem | Scope | Axioms |
| --- | --- | --- |
| `World.frameInput_context` | The executing frame receives the supplied static flag and profile. | None |
| `WorldCall.callZeroValue_precompile` | An in-range precompile target is unsupported before ordinary dispatch. | `propext` |
| `WorldCall.callWithValue_precompile` | A precompile target is indeterminate before transfer or ordinary dispatch. | `propext` |
| `WorldCall.callZeroValue_child_exception` | A child run with the supplied static flag and profile that halts exceptionally keeps only the caller's address warm-up. | `propext` |
| `WorldCall.callWithValue_child_exception` | A funded child run with the supplied profile and value that halts exceptionally discards the transfer. | `propext` |
| `CallOpcode.finishCall_state_projection` | The caller reads balance, current storage, warm slots and refund from the returned world and preserves original storage. | None |
| `CallOpcode.finishCall_commit_preserves_world` | Committing that caller without intervening journal changes preserves the returned world. | `propext`, `Quot.sound` |

The existing `CallOpcode.run_parent_revert_atomic` and
`CallOpcode.run_parent_exception_atomic` still build, both with `propext`.
These theorems describe the Lean executable model. The compiler and runtime
are trusted. Oracle agreement is tested on the fixtures below.

## Reproduction and comparison

Run from `formal/lean4`, with the locked EthereumJS dependencies installed
in `evm-cleanroom/scripts/differential`.

```sh
lake -d evm-cleanroom build EVMCleanroom EVMCleanroom.CallBoundaryTests
node evm-cleanroom/scripts/differential/call-repairs.mjs
```

The library and test module built in 28 jobs. Sixteen new guards ran.
The probe compared actual bytecode executions with EthereumJS 10.1.3.
All five executions in the supported subset matched on status, full parent
stack, remaining gas, slot 0 and parent balance. The precompile fixture
checked the unsupported boundary separately.

| Case | Before on `b1fcf16a` | After | EthereumJS |
| --- | --- | --- | --- |
| Cancun self-CALL | Success bit 1, slot 0 = 0, gas 68547 | Success bit 1, slot 0 = 42, gas 68547 | Same as after |
| Cancun static caller | Success bit 1, slot 0 = 1, gas 75278 | Success bit 0, slot 0 = 0, gas 67384 | Same as after |
| Cancun writable control | Success bit 1, slot 0 = 1, gas 75278 | Success bit 1, slot 0 = 1, gas 75278 | Same as after |
| Osaka zero-value child with CLZ | Indeterminate | Success bit 1, slot 0 = 256, gas 75275 | Same as after |
| Osaka value child with CLZ | Indeterminate | Success bit 1, slot 0 = 256, gas 68574 | Same as after |
| Cancun identity precompile, zero forwarded gas | Success bit 1, gas 97385 | Indeterminate | Success bit 0, gas 97385 |

The Linux Lean 4.33.1 interpreter microbenchmark measured 30 batches of
2,000 executions, after three warm-up batches. Each run varied initial gas
and used a cold world. Both versions agreed on the gas sum for each
benchmark. Reported percentiles are across batch-average microseconds per
execution. These are local interpreter timings.

| Fixture | Version | p50 | p95 | p99 | Max | Max minus min |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| Parent ending with ADD and STOP | Before | 33.676 | 35.865 | 36.960 | 36.960 | 3.861 |
| Parent ending with ADD and STOP | After | 32.653 | 36.517 | 38.457 | 38.457 | 6.594 |
| Parent CALL to SSTORE child | Before | 55.036 | 56.690 | 57.919 | 57.919 | 4.155 |
| Parent CALL to SSTORE child | After | 57.031 | 66.549 | 68.239 | 68.239 | 13.953 |
