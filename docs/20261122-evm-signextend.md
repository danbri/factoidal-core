# EVM SIGNEXTEND (0x0b), 22 November 2026

Issue: https://github.com/danbri/factoidal-core/issues/752

Base: draft PR #751, commit `22a2b6ab09bbe78b10506974d1094ca3666e783b`, stacked over CALL-byte PR #748. Source-only wip branch; not main.

## Intended theorems (stated in issue before code)

- `EVMCleanroom.Word.signExtend_large`: for a 256-bit index whose natural value is >= 32, the real `Word.signExtend` implementation returns its original value.
- `EVMCleanroom.step_signExtend`: when `Core.step` fetches 0x0b in a running frame with `index :: value :: rest`, the executable dispatcher invokes `commit` with precisely `index.signExtend value :: rest` and cost 5.

These statements are proof obligations on the concrete helper and dispatcher, not a theorem that all EELS instructions, fork profiles or transaction transitions match the specification. On exact source commit `90bd86bd2fe6363e26b10eb5e90c73d2a7b42ab9`, Lean 4.33.1 printed `[propext]` for each theorem in EVM CI run 45036718007; the 105-selected-claim follow-up audit is pending its next run.

## Semantics and code

The byte index counts from the low end. For index < 32, keep `8*(index+1)` bits of the value and sign-fill the remaining high bits, inspecting bit `8*index+7`. For index >= 32 preserve the 256-bit word unchanged. This predicate is tested before any exponentiation; no full-width index is used as a host shift count. `Core.planStep` executes 0x0b via the common five-gas `binary` and `commit` path. `Frame.zeroValueContextFree` admits this context-free operation in a read-only zero-value frame.

## Executable tests

`EVMCleanroom/Tests.lean` adds helper and real-bytecode guards for 0x7f/0x80, two-byte sign, indexes 0, 1, 30, 31, 32 and max, pop order, one/two-operand underflows and exact/out-of-gas boundaries.

`scripts/differential/solidity-pure.mjs` adds 144 combinations (12 byte indexes by 12 values) plus gas and underflow controls. It compares actual Lean executable status, gas, stack and memory against pinned `@ethereumjs/evm@10.1.3` Shanghai independently, with 527 total comparisons required (381 prior + 146 additional). No host-side JS implementation of SIGNEXTEND is introduced. Five separate policy refusals remain checked.

## Validation status

GitHub CI run [45036718007](https://github.com/danbri/factoidal-core/actions/runs/45036718007) passed all three jobs on `90bd86bd2fe6363e26b10eb5e90c73d2a7b42ab9`, including 527/527 EthereumJS comparisons (146 new SIGNEXTEND), 103 previously selected axiom audits, six Prague and six Cancun state roots and retained 10,000-program corpus. Both new proof outputs were actually printed with only `propext`. [Authenticated Frontier replay 45036717984](https://github.com/danbri/factoidal-core/actions/runs/45036717984) passed independently on that head. The two new theorems are now selected for a 105-claim audit in the next commit. Broader repository corpus/npm workflows are still separate. The current authoring host has no Lean toolchain and cannot give local compilation or native performance figures. Existing tail regression in https://github.com/danbri/factoidal-core/issues/739 is not resolved by this change.

Reproduction from `formal/lean4/evm-cleanroom` with Lean 4.33.1 and bounded memory / single-build lock:

```sh
lake build
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
node scripts/differential/solidity-pure.mjs
```

Outstanding full-client work remains under https://github.com/danbri/factoidal-core/issues/725 and execution subset https://github.com/danbri/factoidal-core/issues/652: fork-exact complete opcode/gas set, CALL/CREATE variants, precompiles, transactions, persistence, authenticated replay breadth, Engine API, network and Lean beacon consensus.
