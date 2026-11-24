# 2026-11-24 — BubblePopJS expm1 and log1p near zero

Computing exp(x) minus one or log(1+x) directly can lose most or all of a small
input once the intermediate rounds near one. Near zero, expm1 now evaluates the
Taylor correction to x through degree 15. Log1p accounts for the rounding of
1+x, returning x when that sum rounds to one. Both keep the input's signed zero.

The two zero-path theorems compiled with Lean 4.33.1. All 42 expm1 and 12 log1p
numerical vectors extracted from the pinned Test262 accuracy tests passed on the
local Lean runtime. These differential checks do not establish a global ULP
bound. The hosted Test262 run exercises the actual JavaScript entry points.

[ECMA-262 Math.expm1](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-math.expm1)
[ECMA-262 Math.log1p](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-math.log1p)
