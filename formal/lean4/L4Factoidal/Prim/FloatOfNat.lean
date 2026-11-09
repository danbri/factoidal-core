/-!
# L4Factoidal.Prim.FloatOfNat — `Float.ofNat` and `Float.ofInt` with no decimal parse per call

Record and measurements: `docs/designissues/2026-11-09-foafnaut-perf-exploration.md`.

## The cost this module removes

In Lean 4.33.1, `Float.ofNat n` is `Float.ofScientific n false 0` (`Init/Data/OfScientific.lean`),
and `Float.ofScientific` starts with the test `m < 2 ^ 53`. The C that Lean generates for a `Nat`
literal of 2^32 or more is `lean_cstr_to_nat("9007199254740992")`: the literal is read from decimal
text, through a GMP number, at every evaluation. So every `Float.ofNat`, `Float.ofInt` and
`Nat.toFloat` call paid one such parse (and its `malloc` and `free`). Measured 2026-11-09, Linux
x86_64, `leanc -O3`: 52 to 55 ns for `Float.ofNat n` against 10 to 15 ns for
`n.toUInt64.toFloat` in the same loop.

Upstream: https://github.com/leanprover/lean4/issues/16007 (literals from 2^32 to 2^64 - 1 parsed
from a string each time). When the toolchain has that repair, these twins cost nothing and can go.

## What is here

- `natToFloat n`: for `n < 2 ^ 32`, the fast case of `Float.ofScientific` written with a bound
  that is a small literal; else `Float.ofNat n`. `natToFloat_eq` proves it equal to `Float.ofNat`
  for every `n`. The proof unfolds the two definitions; it uses no property of `Float`
  multiplication, because the fast case is the same term on both sides.
- `intToFloat i`, equal to `Float.ofInt i` (`intToFloat_eq`).
- Three `@[csimp]` theorems (`Float.ofNat`, `Nat.toFloat`, `Float.ofInt`), so that compiled code
  calls the twins. A `csimp` theorem changes only the code of modules that import the module
  that states it: a module whose hot path makes these conversions imports this module.
  `python3 tools/lean-literal-parse-audit.py --conversions` lists the compiled functions that
  still call the core conversions.

## What the `csimp` theorems do not reach

The compiler replaces a name where the source of an importing module says it. A body that comes
from Lean core already compiled keeps the core conversion:

- `Float.ofInt` and `Nat.toFloat` in core call `Float.ofNat`; each has its own theorem here for
  that reason. Before `Nat.toFloat` had one, `len.toFloat` in `JS.relIndex` still compiled to
  `lean_float_of_nat` (generated C, 2026-11-09).
- A numeric literal of type `Float` with no decimal point (`(1114111 : Float)`) is
  `OfNat.ofNat` through the core instance, whose body calls `Float.ofNat`. Such a literal is
  normally made once, at module start. Where the compiler leaves it in a function body, the
  call stays the core one.
-/

namespace L4Factoidal.Prim

/-- `Float.ofNat` (`natToFloat_eq`). For `n < 2 ^ 32`: one machine conversion and one
multiplication by the first entry of `Float.exactlyRepresentablePowersOfTen` (1.0), as the fast
case of `Float.ofScientific` does. The bound is a literal below 2^32, so it is not read from
text. -/
def natToFloat (n : Nat) : Float :=
  if _h : n ≤ 4294967295 then
    n.toUInt64.toFloat *
      Float.exactlyRepresentablePowersOfTen[0]'(by simp [Float.exactlyRepresentablePowersOfTen])
  else Float.ofNat n

theorem natToFloat_eq (n : Nat) : natToFloat n = Float.ofNat n := by
  unfold natToFloat
  split
  · next h =>
    have hb : n < 2 ^ 53 ∧ (0 : Nat) ≤ 22 := ⟨by omega, by omega⟩
    simp [Float.ofNat, OfScientific.ofScientific, Float.ofScientific, hb]
  · rfl

@[csimp] theorem float_ofNat_eq_natToFloat : @Float.ofNat = @natToFloat :=
  funext fun n => (natToFloat_eq n).symm

/-- `n.toFloat` on a `Nat` is `Nat.toFloat n`, a core `abbrev` of `Float.ofNat n`. The compiler
inlines its body as core compiled it, with the core conversion. This theorem replaces the name
before that. -/
@[csimp] theorem nat_toFloat_eq_natToFloat : @Nat.toFloat = @natToFloat :=
  funext fun n => (natToFloat_eq n).symm

/-- `Float.ofInt` (`intToFloat_eq`), over `natToFloat`. -/
def intToFloat : Int → Float
  | .ofNat n => natToFloat n
  | .negSucc n => Float.neg (natToFloat (n + 1))

theorem intToFloat_eq (i : Int) : intToFloat i = Float.ofInt i := by
  cases i <;> simp [intToFloat, Float.ofInt, natToFloat_eq]

@[csimp] theorem float_ofInt_eq_intToFloat : @Float.ofInt = @intToFloat :=
  funext fun i => (intToFloat_eq i).symm

/-! The compiled twins against the core functions, at the edges of each case. `Float.ofNat` in
these guards is the twin too (the `csimp` theorem above), so the right side is restated through
`Float.ofScientific`, which no `csimp` theorem replaces. -/
#guard [0, 1, 2, 255, 65536, 2147483647, 2147483648, 4294967295, 4294967296, 9007199254740991,
    9007199254740992, 9007199254740993, 18446744073709551615, 18446744073709551616,
    123456789012345678901234567890].all fun n =>
  (natToFloat n).toBits == (Float.ofScientific n false 0).toBits
#guard [(0 : Int), 1, -1, 2147483647, -2147483648, 4294967295, -4294967295, -4294967296,
    4294967296, -9007199254740993, 9007199254740993].all fun i =>
  (intToFloat i).toBits ==
    (if i < 0 then Float.neg (Float.ofScientific i.natAbs false 0)
     else Float.ofScientific i.natAbs false 0).toBits

end L4Factoidal.Prim
