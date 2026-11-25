# Number::toString and the Number.prototype formats on 64-bit words (BubblePopJS)

Issue: https://github.com/danbri/factoidal-core/issues/1076 (Number::toString of a fraction cost
about 20 µs). Date: 2026-11-25. Measured on a Linux cloud VM, 4 vCPU, one run of each command
below on the same tree.

## 1. What the code does

- `JS/Number.lean` `numToString` (ECMA-262 §6.1.6.1.20). NaN, zero and infinities as before. An
  integer below 2^53 prints its digits (`toString` of an `Int`). Every other finite value goes to
  `JS/Ryu.lean` `finiteToString`.
- `JS/Ryu.lean`: Ryū (Ulf Adams, PLDI 2018), the algorithm of `d2s.c` of the reference
  implementation with its full tables. All arithmetic is `UInt64`; the 128-bit product is four
  32 × 32-bit products (`mulHi`). Output: the shortest digits, nearest the value, ties to even
  (§6.1.6.1.20 Note 2). Then the layout of §6.1.6.1.20 steps 6 to 12, written digit by digit
  into the string.
- `JS/RyuTables.lean`: the two tables (342 and 326 entries of 128 bits), written by
  `tools/gen-ryu-tables.py`. `#guard`s in `Ryu.lean` compare every entry with its formula.
- `JS/NumFmt.lean` `fixedOf`, `precisionOf`, `expoOf`, `expoShortest` (§21.1.3.3, .5, .2). A
  double is `m × 2^e2` with `m < 2^53`. For a scale `10^k`, `|k| ≤ 19`, the integer nearest
  `|x| × 10^k` (the larger on a tie, as the specification says) is exact on 64-bit words:
  for `k ≥ 0` a 128-bit product and a shift (`scaledUp`); for `k < 0`, with `I` the integer part
  of `|x|`, `⌊(I + 5 × 10^(j-1)) / 10^j⌋` (`scaledDown`; the fraction of `|x|` cannot change the
  result because `10^j / 2` is an integer). When a result does not fit, the function takes the
  exact `Nat` path (`fixed`, `precision`, `expo`), as before.
- `numToStringRef` and `shortestFracRef` keep the exact algorithm (`XPath4.shortestDigits`,
  rational arithmetic) as the reference of the differential test.

## 2. What is shown, and how

Not proved. Checked by differential test:

- `leanjs numfmt-diff 3000000 987654321`: 6,057,106 doubles, both signs (random bit patterns,
  every power of two and its neighbours, `1e-325` to `1e309` and `5e-325` to `5e309` with
  neighbours, subnormals, integers from 2^53, `i / 7`, `i / 10`, `i / 1000`). 0 differences,
  except 92 powers of two where the reference gives one digit more than the shortest (section 4).
  564,284 doubles through toFixed (8 digit counts), toPrecision (8), toExponential (7, and no
  argument): 0 differences.
- `tools/ryu-differential.sh LEANJS 1000000 777`: the text of 2,059,016 doubles against Node 22
  `String(x)`: 0 differences.
- `#guard`s in `JS/RegressionTests.lean` (five scripts; the expected lines are what Node 22 and
  QuickJS-NG 0.18.0 both print) and in `JS/Ryu.lean`, `JS/NumFmt.lean`.

There is no `@[csimp]` equality with the reference, because the two functions differ on the 92
powers of two, where the reference is wrong.

## 3. Measurements

`labs/demos/foafnaut/bubblepop_perf/opcost.py` (new operations `div7`, `num_to_str_frac`,
`tpl_frac`, `concat_frac`, `to_fixed2`, `to_precision4`, `to_exponential`), ns for one operation
less the empty loop, one interleaved run, `before` = main at `9fa1d855`:

| operation | before | after | QuickJS-NG | Node --jitless |
|---|---|---|---|---|
| `String(i / 7)` | 16,236 | 553 | 176 | 130 |
| `` `${i / 7}` `` | 16,249 | 668 | 195 | 123 |
| `'x' + i / 7` | 16,186 | 296 | 197 | 137 |
| `(i / 7).toFixed(2)` | 1,083 | 543 | 119 | 84 |
| `(i / 7).toPrecision(4)` | 1,298 | 745 | 121 | 80 |
| `(i / 7).toExponential()` | 18,010 | 787 | 270 | 108 |

Callgrind (instructions for one operation less the empty loop, on the build before the last
two changes): no call into the big-number runtime in any of these operations.
`leanjs numfmt-bench` (the conversion alone, `i / 7`, one million values): `numToString` 185 ns
(170 to 290 ns over four runs), `numToStringRef` 19,320 ns; `toFixed(2)` and `toPrecision(4)`
together 267 ns.

`String(i)` of an integer costs 367 ns in the same run, so most of the 553 ns of `String(i / 7)`
is the call, not the conversion.

Test262 `test/built-ins/Number` (pinned commit `5ef1e572`, fetched, not vendored): before 337
pass, 3 fail; after 338 pass, 2 fail (of 340). The new pass is `toFixed/exactness.js` (section 4).
The two failures are `toLocaleString`. The vendored language subset: 5,962 pass, 338 fail, the
same files, before and after. `leanjs bench`: fib(24) 29 ms, loop 67 ms, before and after.

## 4. Defects found

- Integers from 2^53 to 10^21 printed their exact digits (`2 ** 60` as `1152921504606846976`);
  §6.1.6.1.20 asks for the fewest digits (`1152921504606847000`, as Node and QuickJS-NG print).
  Repaired: such integers take Ryū. This made test262 `toFixed/exactness.js` pass.
- `XPath4.shortestDigits` gives one digit too many at some powers of two (it reads back only
  the nearest decimal of each length, and the rounding interval of a power of two is narrower
  below than above): https://github.com/danbri/factoidal-core/issues/1131. The XPath
  `xs:double` cast has the same defect. Expected-failure guard in `JS/NumFmt.lean`.
- Third-party, for the owner (not reported upstream): QuickJS-NG 0.18.0 `String(x)` gives the
  same 17-digit text as our old reference at 108 of the 2,059,016 doubles, all powers of two
  (for example bits `0x0060000000000000`: QuickJS-NG `7.1202363472230444e-307`, Node and Ryū
  `7.120236347223045e-307`, which reads back as the same double). So QuickJS-NG is not an
  oracle for powers of two; `tools/ryu-differential.sh` reports its differences but Node decides.
- `PageCanvas/Wire.lean` `jsNumber` compared with the `Nat` literal 2^53, which the generated C
  read from text at each call. It is now a `@[noinline]` constant (`twoPow53Nat`).

- Our own error, found before landing: `fixedOf` took the fast path for zero with 20 or more
  fraction digits and read `pow10[20]`. In compiled Lean an out-of-bounds `[i]!` prints a panic
  and returns a default value, and the run goes on; here the default happened to give the right
  text, so the differential test reported 0 differences while the code was wrong. The message
  was on standard error, which the first runs did not keep. Repaired (`fixedOf` checks `f > 19`
  first, `#guard` in `NumFmt.lean`), and `tools/ryu-differential.sh` now runs `leanjs` with
  `LEAN_ABORT_ON_PANIC=1`, so a panic fails the test. Rule for any differential test of
  compiled Lean: abort on panic, or count the panic messages.

## 5. Commands

```sh
cd formal/lean4 && lake build leanjs
.lake/build/bin/leanjs numfmt-bench
.lake/build/bin/leanjs numfmt-diff 3000000 987654321
../../tools/ryu-differential.sh .lake/build/bin/leanjs 1000000 777 [QJS]
python3 ../../labs/demos/foafnaut/bubblepop_perf/opcost.py --only base_empty,num_to_str_frac,to_fixed2,to_precision4,to_exponential before='OLD run' after='.lake/build/bin/leanjs run'
```
