# BubblePopJS Math constants and rounding

The pinned Test262 run reported missing Math constants, lost negative
zero in expm1 and log1p, and an upward round on the float immediately
below one half. Add LOG2E, LOG10E and SQRT1_2 with the standard property
attributes. Return the input for both signed zeros in expm1 and log1p.

Round by comparing the fractional part with one half. The old sum
could round before floor saw it, including at large already integral
values. The Lean theorems cover preservation of zero and nonfinite
inputs. Boundary guards and the pinned full Test262 run check concrete
input behaviour. This change leaves the accuracy of expm1 and log1p
for nonzero inputs as before.

References: [ECMA-262 Math](https://tc39.es/ecma262/multipage/numbers-and-dates.html#sec-math-object)
and [baseline Test262 run](https://github.com/danbri/factoidal-builds/actions/runs/45405583208).
