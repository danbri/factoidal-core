# EVM SDIV, SMOD and SAR implementation, 22 November 2026

Issue: https://github.com/danbri/factoidal-core/issues/749

Base: [PR #748](https://github.com/danbri/factoidal-core/pull/748), commit `d752d109ddb3c6707650053930f95ed6ef0bfdc4`.
Scope: three additional context-free opcodes in the actual Lean EVM dispatcher.

## Intended semantics before implementation

- `SDIV 0x05`: two's-complement signed division truncating towards zero. Zero divisor returns zero, and `-2^255 / -1` wraps to `-2^255`.
- `SMOD 0x07`: magnitude remainder, with the original dividend's sign. Zero divisor and exact multiples yield zero.
- `SAR 0x1d`: EIP-145 arithmetic right shift with high sign extension; shifts >= 256 fill with either zero or one bits. Full-width offsets must never become host shift counts.
- Costs are 5, 5 and 3 gas respectively. `Core.step` delegates through `planStep` and the existing checked `commit` path.
- `Frame.zeroValueContextFree` admits these instructions when a zero-value, read-only context is explicitly supplied.

## Executable code and proof boundaries

`EVMCleanroom/Core.lean` now contains `Word.signedMagnitude`, `Word.signedDivide`, `Word.signedMod`, `Word.shiftArithmetic` and dispatch cases. Their seven new statements are:

- `Word.signedDivide_zero`, `Word.signedMod_zero`: zero-divisor behavior.
- `Word.shiftArithmetic_large_nonnegative`, `Word.shiftArithmetic_large_negative`: full-width shift saturation at >=256.
- `step_sdiv`, `step_smod`, `step_sar`: actual `step` dispatch equals a particular `commit` call with the stack in EVM pop order and exact static charge.

These are helper/boundary/dispatcher properties, **not an independently proved correspondence to the Ethereum Yellow Paper or EELS**. The 256-bit arithmetic domain is inherited from the existing `Word` definition; underlying Lean compiler/runtime and host execution remain trusted.

## Tests and reproducibility

`EVMCleanroom/Tests.lean` adds direct helper boundaries and actual interpreter tests for sign, zero, shift saturation, gas refusal, stack underflow and the coarse pre-Shanghai SAR refusal.

`scripts/differential/solidity-pure.mjs` additionally generates 198 cases for the three new instructions: two 8x8 signed operand matrices with two error controls each (132), plus an 8x8 SAR matrix with two error controls (66). Every case is independently executed through `@ethereumjs/evm@10.1.3` Shanghai and compared against the real Lean frame executable. The combined expected result is 381/381 (265 signed cases, 100 modular cases and 16 retained compiled/guarded cases). Exact bytecode and gas are retained in the runner; the oracle comparison examines halt category, gas, stack and memory for successful cases. It is **not** a full state transition or mainnet fixture check.

Reproduce from `formal/lean4/evm-cleanroom` with pinned Lean 4.33.1 and controlled memory/build lock:

```sh
lake build
node scripts/differential/solidity-pure.mjs
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
```

The workflow `.github/workflows/evm-cleanroom.yml` requires 381 comparisons and validates the 75-source active evidence inventory. The historical 10,000-program corpus, EELS state and authenticated Frontier replay gates are retained without reducing their thresholds.

**Validation status at initial publication:** authoring environment has no Lean binary or repository checkout and cannot run the local build/oracle. New Lean `#guard`s, theorem axioms, independent comparisons, retained corpus and hosted CI are **pending** until checks on the exact published head complete. No measurements of performance on this head have been made; the existing observed CALL tail regression remains tracked in https://github.com/danbri/factoidal-core/issues/739.

## Remaining scope

The `preShanghai` profile is coarse: its refusal of EIP-145 instructions does not distinguish Istanbul from older forks, while SDIV/SMOD precede that fork. Missing opcodes, CREATE, precompiles, exact fork gas, signed transactions, receipt/block transitions, persistence, networking, fork choice and Lean beacon consensus remain under https://github.com/danbri/factoidal-core/issues/725. No unsupported case is counted as passing.
