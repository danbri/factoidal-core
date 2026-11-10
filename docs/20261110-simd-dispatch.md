---
title: "Bitwise SIMD dispatch refinement"
date: 2026-11-10T22:06:00Z
draft: false
---

# Bitwise SIMD dispatch refinement

`Run.simdStepFast` directly handles `v128.not`, `and`, `andnot`, `or` and `xor`.
Other opcodes call the unchanged generic dispatcher. `simdStep_eq_fast` proves
function equality for every memory backend, store, stack, pointer and immediate,
including invalid opcodes and traps. The compiler uses it through `csimp`.
This is refinement of the executable interpreter, not external Wasm conformance;
it does not depend on the seven earlier bitwise algebraic laws.

Measurements compare the unmodified dispatcher at `eb1821829` with this branch's
literal-match variant (generic fallback plus reference wrapper). The WasmVM sources
at that base and `6899566ca` are identical. Both binaries use the same benchmark,
Lean 4.33.1, native `-O3`, macOS arm64; six alternating pairs, first pair discarded.
Printed results matched for every pair. Tables use medians; lower time is better.

Bitwise interpreter loops took 4.0–6.1% less time across the two sizes. Fallback
controls took 0.5–1.3% more time. At the larger size:

| Instruction | Iterations | Before ms | After ms | Change |
|---|---:|---:|---:|---:|
| v128.not | 4,000,000 | 524.56 | 492.57 | -6.1% |
| v128.and | 4,000,000 | 706.08 | 664.50 | -5.9% |
| v128.andnot | 4,000,000 | 705.74 | 665.43 | -5.7% |
| v128.or | 4,000,000 | 706.83 | 667.20 | -5.6% |
| v128.xor | 4,000,000 | 714.59 | 674.91 | -5.6% |
| i8x16.swizzle (control) | 200,000 | 108.02 | 108.77 | +0.7% |
| i8x16.eq (control) | 200,000 | 819.13 | 823.56 | +0.5% |
| i8x16.add (control) | 4,000,000 | 2612.46 | 2637.31 | +1.0% |

Direct bitwise dispatch took 7.5–14.9% less time; this larger gain is not the
whole-interpreter result.

`Bench/SimdDispatch.lean` supplies both `direct` and `engine` modes:
`lake exe wasmvm-simd-dispatch engine 78 4000000` runs the AND loop.
Bitwise/add counts were one and four million; swizzle/equality controls used
50,000 and 200,000. The direct mode isolates dispatch; the engine mode includes
local accesses, a scalar loop counter and fuel. These repeat one instruction:
no real-page, mixed-opcode or wasm32 speed claim is established. The fallback
cost needs workload evidence before a merge recommendation.

Checks: targeted Run/benchmark/SIMD-test builds; existing 15 SIMD movement cases,
no-copy and refusal tests; standard three axioms only; AND-to-OR mutation rejected;
hygiene and import gates; generated-C replacement and recursion gates on the
compiled closure. Full browser and wasm32 builds were not run.

Tracking: https://github.com/danbri/factoidal-core/issues/388 (theorem contributions)
and https://github.com/danbri/factoidal/issues/1244 (WebAssembly engine).
