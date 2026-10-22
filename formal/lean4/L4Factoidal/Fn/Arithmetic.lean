/- F&O 2007 §§6.2.1–6.2.4: IEEE binary arithmetic over XSD values.
   Inputs come from the canonical XSD parser/promotion layer. Finite operations
   use exact integer ratios, then one ties-to-even rounding at the result type.
   No host floating-point arithmetic or new foreign implementation is used.
   Decimal division precision and result lexical formatting are caller policies. -/
import L4Factoidal.Fn.Numeric

namespace L4Factoidal.Fn.Arithmetic
open XSD

inductive Op where
  | add | sub | mul | div
  deriving DecidableEq, Repr

def nan : Fval := ⟨false, .nan⟩
def negate (v : Fval) : Fval := { v with neg := !v.neg }

/-- Magnitude of a finite canonical value (zero included). Special classes
    are handled before this helper is called. -/
def magnitude (v : Fval) : Nat × Nat := match v.cls with
  | .finite m e => if e ≥ 0 then (m * 2 ^ e.toNat, 1) else (m, 2 ^ (-e).toNat)
  | _ => (0, 1)

/-- Preserve zero's sign; round nonzero ratios directly to binary32/64. -/
def rounded (double neg : Bool) (num den : Nat) : Fval :=
  ⟨neg, if num == 0 then .zero else
    if double then roundRational 53 (-1022) 1023 num den
    else roundRational 24 (-126) 127 num den⟩

def add (double : Bool) (a b : Fval) : Fval :=
  match a.cls, b.cls with
  | .nan, _ | _, .nan => nan
  | .inf, .inf => if a.neg == b.neg then a else nan
  | .inf, _ => a
  | _, .inf => b
  | _, _ =>
      let (an, ad) := magnitude a
      let (bn, bd) := magnitude b
      let ai : Int := if a.neg then -(an : Int) else an
      let bi : Int := if b.neg then -(bn : Int) else bn
      let n := ai * bd + bi * ad
      -- Cancellation gives +0; only -0 + -0 gives -0, in nearest mode.
      rounded double (if n == 0 then a.neg && b.neg else n < 0) n.natAbs (ad * bd)

def multiply (double : Bool) (a b : Fval) : Fval :=
  let neg := a.neg != b.neg
  match a.cls, b.cls with
  | .nan, _ | _, .nan => nan
  | .zero, .inf | .inf, .zero => nan
  | .inf, _ | _, .inf => ⟨neg, .inf⟩
  | _, _ =>
      let (an, ad) := magnitude a
      let (bn, bd) := magnitude b
      rounded double neg (an * bn) (ad * bd)

def divide (double : Bool) (a b : Fval) : Fval :=
  let neg := a.neg != b.neg
  match a.cls, b.cls with
  | .nan, _ | _, .nan => nan
  | .zero, .zero | .inf, .inf => nan
  | .inf, _ | _, .zero => ⟨neg, .inf⟩
  | .zero, _ | _, .inf => ⟨neg, .zero⟩
  | _, _ =>
      let (an, ad) := magnitude a
      let (bn, bd) := magnitude b
      rounded double neg (an * bd) (ad * bn)

def calculate (double : Bool) (op : Op) (a b : Fval) : Fval := match op with
  | .add => add double a b
  | .sub => add double a (negate b)
  | .mul => multiply double a b
  | .div => divide double a b

/-- Promote operands once, operate at the common floating type, retain it.
    Decimal-only arithmetic is intentionally outside this entry point. -/
def floating (op : Op) (a b : Val) : Option Val := do
  match a, b with
  | .dec _, .dec _ => none
  | _, _ =>
      let double := match a, b with | .dbl _, _ | _, .dbl _ => true | _, _ => false
      let x ← Numeric.floatingValue double a
      let y ← Numeric.floatingValue double b
      let result := calculate double op x y
      some (if double then .dbl result else .flt result)

/-- F&O §6.2.1–4: exact decimal arithmetic except division, which truncates
    toward zero at the requested number of fractional places. -/
def decimal (places : Nat) (op : Op) (a b : Dec) : Option Dec :=
  match op with
  | .add => some (a.add b)
  | .sub => some (a.sub b)
  | .mul => some (Dec.norm ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩)
  | .div => if b.mantissa == 0 then none else
      some (Dec.norm ⟨Int.tdiv (a.mantissa * 10 ^ (b.scale + places))
        (b.mantissa * 10 ^ a.scale), places⟩)

/-- F&O §6.2.5: decimal idiv uses an exact ratio, with no intermediate
    decimal rounding. The result truncates toward zero for either sign. -/
def decimalIntegerDivide (a b : Dec) : Option Int :=
  if b.mantissa == 0 then none else
    some (Int.tdiv (a.mantissa * 10 ^ b.scale) (b.mantissa * 10 ^ a.scale))

/-- F&O §6.2.6: exact decimal remainder, with the dividend's sign. -/
def decimalMod (a b : Dec) : Option Dec := do
  let q ← decimalIntegerDivide a b
  some (a.sub (b.mulInt q))

/-- F&O §6.2.5: integer division of promoted IEEE values. Division rounds
    at the common operand type before integer conversion. -/
def floatingIntegerDivide (double : Bool) (a b : Fval) : Option Int :=
  match a.cls, b.cls with
  | .nan, _ | _, .nan | .inf, _ | _, .zero => none
  | _, _ =>
      let q := divide double a b
      match q.cls with
      | .nan | .inf => none
      | _ =>
        let (num, den) := magnitude q
        some (Int.tdiv (if q.neg then -(num : Int) else num) den)

/-- F&O §6.2.6: floating remainder uses an exact truncating quotient,
    unlike rounded floating division. Signed zero follows the dividend. -/
def floatingMod (double : Bool) (a b : Fval) : Fval :=
  match a.cls, b.cls with
  | .nan, _ | _, .nan | .inf, _ | _, .zero => nan
  | _, .inf | .zero, _ => a
  | _, _ =>
      let (an, ad) := magnitude a
      let (bn, bd) := magnitude b
      let q := (an * bd) / (ad * bn)
      rounded double a.neg (an * bd - q * bn * ad) (ad * bd)

/-- F&O §6.2.5: validate/promote numeric values and return an integer. -/
def integerDivide (a b : Val) : Option Int := do
  match a, b with
  | .dec x, .dec y => decimalIntegerDivide x y
  | _, _ =>
      let double := match a, b with | .dbl _, _ | _, .dbl _ => true | _, _ => false
      floatingIntegerDivide double (← Numeric.floatingValue double a) (← Numeric.floatingValue double b)

/-- F&O §6.2.6: validate/promote operands, retaining the numeric result type. -/
def modulo (a b : Val) : Option Val := do
  match a, b with
  | .dec x, .dec y => (decimalMod x y).map Val.dec
  | _, _ =>
      let double := match a, b with | .dbl _, _ | _, .dbl _ => true | _, _ => false
      let r := floatingMod double (← Numeric.floatingValue double a) (← Numeric.floatingValue double b)
      some (if double then .dbl r else .flt r)

end L4Factoidal.Fn.Arithmetic
