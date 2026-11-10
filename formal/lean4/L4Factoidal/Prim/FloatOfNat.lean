/-!
# L4Factoidal.Prim.FloatOfNat — conversions to `Float` with no decimal parse per call

Record and measurements: `docs/designissues/2026-11-09-foafnaut-perf-exploration.md`.

## The cost this module removes

In Lean 4.33.1, `Float.ofScientific m s e` (`Init/Data/OfScientific.lean`) starts with the test
`m < 2 ^ 53`, and `Float.ofNat n` is `Float.ofScientific n false 0`. The C that Lean generates for
a `Nat` literal of 2^32 or more is `lean_cstr_to_nat("9007199254740992")`: the literal is read from
decimal text, through a GMP number, at every evaluation. So each of these paid one such parse (and
its `malloc` and `free`):

- every `Float.ofNat`, `Float.ofInt` and `Nat.toFloat` call;
- every `Float` literal that the compiler left in the body of a function, with a decimal point
  (`0.5`, through `OfScientific`) or without one (`0`, `-1`, through `OfNat`).

Measured 2026-11-09, Linux x86_64, `leanc -O3`: 52 to 55 ns for `Float.ofNat n` against 10 to 15 ns
for `n.toUInt64.toFloat` in the same loop.

Upstream: https://github.com/leanprover/lean4/issues/16007 (literals from 2^32 to 2^64 - 1 parsed
from a string each time; see `docs/designissues/2026-11-09-lean-upstream-wasm32.md`). When the
toolchain has that repair, these twins cost nothing and can go
(`python3 tools/test_lean_literal_parse_audit.py` fails then, on purpose).

## What is here

- `natToFloat n`: for `n < 2 ^ 32`, the fast case of `Float.ofScientific` written with a bound
  that is a small literal; else `Float.ofNat n`. `natToFloat_eq` proves it equal to `Float.ofNat`
  for every `n`. The proof unfolds the two definitions; it uses no property of `Float`
  multiplication, because the fast case is the same term on both sides.
- `intToFloat i`, equal to `Float.ofInt i` (`intToFloat_eq`).
- `ofScientificFast m s e`: for `m < 2 ^ 32` and `e ≤ 22`, the fast case of `Float.ofScientific`
  with small-literal bounds; else `Float.ofScientific m s e` (`ofScientificFast_eq`).
- Six `@[csimp]` theorems, so that compiled code calls the twins: for the functions
  `Float.ofNat`, `Nat.toFloat`, `Float.ofInt` and `Float.ofScientific`, and for the instances
  `instOfNatFloat` and `instOfScientificFloat`, through which every `Float` literal goes.

The core functions are the specification. Each twin is proved equal to its core function for
every argument. The `csimp` theorems put the twins in the compiled code, and the compiler is
trusted. The `#guard`s below are tests: they stand before the `csimp` theorems, so the core names
in them are the core functions.

## Reach

A `csimp` theorem changes only the code of modules that import the module that states it: a
module whose hot path makes these conversions imports this module, with a comment that says why.

The compiler replaces a name where the source of an importing module says it. A body that comes
from Lean core already compiled keeps the core conversion. That is why `Nat.toFloat` and the two
instances have theorems of their own: before `Nat.toFloat` had one, `len.toFloat` in
`JS.relIndex` still compiled to `lean_float_of_nat`; before the instances had theirs, `k < 0` and
`.num (-1)` in the native functions of `JS/Interp.lean` did (generated C, 2026-11-09).

A literal with an exponent above 22, or with a mantissa of 2^53 or more, still takes the slow
case of `Float.ofScientific` (big number arithmetic): `1e300`, `9007199254740991.0`. Put such a
literal in a definition of its own with no argument. `python3 tools/lean-literal-parse-audit.py`
lists, from the generated C, the literals and conversions that a build still evaluates at each
call (`--float-literals`, `--conversions`).

## Order of the declarations

Each twin is defined before the `csimp` theorem for its core function. A twin's own slow branch
names the core function; a definition placed after the theorem would call itself there.
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

/-- `Float.ofInt` (`intToFloat_eq`), over `natToFloat`. -/
def intToFloat : Int → Float
  | .ofNat n => natToFloat n
  | .negSucc n => Float.neg (natToFloat (n + 1))

theorem intToFloat_eq (i : Int) : intToFloat i = Float.ofInt i := by
  cases i <;> simp [intToFloat, Float.ofInt, natToFloat_eq]

/-- `Float.ofScientific` (`ofScientificFast_eq`). For a mantissa below 2^32 and an exponent of at
most 22: the fast case of the core function, with bounds that are small literals. -/
def ofScientificFast (m : Nat) (s : Bool) (e : Nat) : Float :=
  if h : m ≤ 4294967295 ∧ e ≤ 22 then
    let powerOfTen : Float :=
      Float.exactlyRepresentablePowersOfTen[e]'(by simp [Float.exactlyRepresentablePowersOfTen]; omega)
    if s then m.toUInt64.toFloat / powerOfTen else m.toUInt64.toFloat * powerOfTen
  else Float.ofScientific m s e

theorem ofScientificFast_eq (m : Nat) (s : Bool) (e : Nat) :
    ofScientificFast m s e = Float.ofScientific m s e := by
  unfold ofScientificFast
  split
  · next h =>
    have hb : m < 2 ^ 53 ∧ e ≤ 22 := ⟨by omega, h.2⟩
    simp [Float.ofScientific, hb]
  · rfl

/-! Tests of the twins against the core functions, at the edges of each case. No `csimp` theorem
is stated yet at this point of the file, so `Float.ofNat`, `Float.ofInt` and `Float.ofScientific`
here are the core functions. -/
#guard [0, 1, 2, 255, 65536, 2147483647, 2147483648, 4294967295, 4294967296, 9007199254740991,
    9007199254740992, 9007199254740993, 18446744073709551615, 18446744073709551616,
    123456789012345678901234567890].all fun n =>
  (natToFloat n).toBits == (Float.ofNat n).toBits
#guard [(0 : Int), 1, -1, 2147483647, -2147483648, 4294967295, -4294967295, -4294967296,
    4294967296, -9007199254740993, 9007199254740993].all fun i =>
  (intToFloat i).toBits == (Float.ofInt i).toBits
#guard [0, 1, 5, 192, 1114111, 4294967295, 4294967296, 9007199254740991, 9007199254740992,
    90071992547409910].all fun m =>
  [0, 1, 2, 21, 22, 23, 300].all fun e =>
    [false, true].all fun s =>
      (ofScientificFast m s e).toBits == (Float.ofScientific m s e).toBits

/-! The `csimp` theorems. From here on, compiled code that names a left side calls the right
side. -/

@[csimp] theorem float_ofNat_eq_natToFloat : @Float.ofNat = @natToFloat :=
  funext fun n => (natToFloat_eq n).symm

/-- `n.toFloat` on a `Nat` is `Nat.toFloat n`, a core `abbrev` of `Float.ofNat n`. The compiler
inlines its body as core compiled it, with the core conversion. This theorem replaces the name
before that. -/
@[csimp] theorem nat_toFloat_eq_natToFloat : @Nat.toFloat = @natToFloat :=
  funext fun n => (natToFloat_eq n).symm

@[csimp] theorem float_ofInt_eq_intToFloat : @Float.ofInt = @intToFloat :=
  funext fun i => (intToFloat_eq i).symm

@[csimp] theorem float_ofScientific_eq_ofScientificFast : @Float.ofScientific = @ofScientificFast :=
  funext fun m => funext fun s => funext fun e => (ofScientificFast_eq m s e).symm

/-- The `OfNat Float` instance over `natToFloat`: a `Float` literal with no decimal point. -/
@[instance_reducible, inline] def ofNatFloatFast (n : Nat) : OfNat Float n := ⟨natToFloat n⟩

/-- A `Float` literal with no decimal point (`0`, `-1`, `1114111`) is `OfNat.ofNat` through the
core instance, whose compiled body calls the core `Float.ofNat`. This theorem replaces the
instance. -/
@[csimp] theorem instOfNatFloat_eq_ofNatFloatFast : @instOfNatFloat = @ofNatFloatFast :=
  funext fun n => congrArg OfNat.mk (natToFloat_eq n).symm

/-- The `OfScientific Float` instance over `ofScientificFast`: a `Float` literal with a decimal
point. -/
@[instance_reducible, inline] def ofScientificFloatFast : OfScientific Float := ⟨ofScientificFast⟩

/-- A `Float` literal with a decimal point is `OfScientific.ofScientific` through the core
instance, whose compiled body calls the core `Float.ofScientific`. This theorem replaces the
instance. -/
@[csimp] theorem instOfScientificFloat_eq_ofScientificFloatFast :
    @instOfScientificFloat = @ofScientificFloatFast :=
  congrArg OfScientific.mk
    (funext fun m => funext fun s => funext fun e => (ofScientificFast_eq m s e).symm)

end L4Factoidal.Prim
