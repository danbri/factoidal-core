/- Shared numeric inputs for F&O comparisons and Boolean conversion.
   SPARQL §§17.1–17.3 and §17.4.2.4; F&O 2007 §17.1.6.
   Lexical parsing uses XSD 1.0, including integer-derived bounds and the
   existing IEEE conversion profile. This module also owns exact decimal
   arithmetic and the lexical decimal adapters used by existing consumers. -/
import L4Factoidal.RDF.Core
import L4Factoidal.XSD.Lexical
import L4Factoidal.Fn.Rounding

namespace L4Factoidal.Fn.Numeric
open RDF XSD

def isType (b : Builtin) : Bool :=
  (intBounds b).isSome || b == .decimal || b == .float || b == .double

/-- Datatype classification alone does not establish lexical validity. -/
def isDatatype (dt : WfIri) : Bool := (builtinOfIri? dt.val).any isType

def lexicalValue? (dt : WfIri) (s : String) : Option Val := do
  let b ← builtinOfIri? dt.val
  if isType b then lexicalFor .xsd10 b s else none

def literalValue? (l : Literal) : Option Val := lexicalValue? l.datatype l.lexicalForm

/-- Exact decimal input to the shared IEEE conversion profile. -/
def decimalParsed (d : Dec) : Parsed :=
  .num (d.mantissa < 0) d.mantissa.natAbs (-(d.scale : Int))

/-- F&O numeric promotion, shared by comparison and arithmetic. -/
def floatingValue (double : Bool) : Val → Option Fval
  | .dec d => some (if double then canonDouble (decimalParsed d) else canonFloat (decimalParsed d))
  | .flt f => some f
  | .dbl f => if double then some f else none
  | _ => none

/-- F&O numeric-to-Boolean conversion: zero and NaN are false. Parsing
    must happen first so underflow and derived-type bounds have taken effect.
    Nonnumeric values remain errors; string conversion is a caller policy. -/
def booleanValue? : Val → Option Bool
  | .dec d => some (d.mantissa != 0)
  | .flt f | .dbl f => some (match f.cls with
      | .zero | .nan => false
      | .inf => true
      | .finite m _ => m != 0)
  | _ => none



open L4Factoidal.XSD (Dec)

/-- Fractional digits kept by `decDiv?`. -/
def divScale : Nat := 18

/-- Lean 4's `Int` `/` and `%` are EUCLIDEAN, not truncating:
    `(-7) / 2` is `-4` and `(-7) % 2` is `1`. F&O's numeric operators
    truncate toward zero (§6.2.4 `op:numeric-divide`, §6.2.5
    `op:numeric-integer-divide`), so every division in this module
    names `Int.tdiv` or `Int.fdiv` explicitly and none is written `/`.

    This was pinned after `RIF/Builtins.lean` carried the comment
    "`Int./` truncates toward zero, which is the direction this states,
    and both signs go the same way" on `divDec` — the comment was
    wrong, and `func:numeric-divide` floored on a negative operand
    where F&O truncates. `divDec` below is corrected. -/
example : ((-7 : Int) / 2) = -4 := by decide
example : ((-7 : Int) % 2) = 1 := by decide
example : Int.tdiv (-7 : Int) 2 = -3 := by decide
example : Int.fdiv (-7 : Int) 2 = -4 := by decide

/-- §6.2.3 `op:numeric-multiply` on `xs:decimal`: exact. -/
def decMul (a b : Dec) : Dec :=
  Dec.norm ⟨a.mantissa * b.mantissa, a.scale + b.scale⟩

/-- §6.2.4 `op:numeric-divide`. `none` on a zero divisor, which F&O
    makes the dynamic error `FOAR0001`; each front end maps `none` to
    its own error discipline. -/
def decDiv? (scale : Nat) (a b : Dec) : Option Dec :=
  if b.mantissa == 0 then none
  else
    let num := a.mantissa * (10 : Int) ^ (b.scale + scale)
    let den := b.mantissa * (10 : Int) ^ a.scale
    some (Dec.norm ⟨Int.tdiv num den, scale⟩)

/-- The FLOOR of a decimal, which is not `Dec.floorDiv` — that name is
    on a truncating division. Needed wherever a negative offset must
    carry into the next lower day (`Fn.DateTime.plusDuration`). -/
def decFloorInt (a : Dec) : Int := Rounding.integral .floor a.mantissa ((10 : Int) ^ a.scale)

/-- The fractional part, in `[0, 1)`, for any sign. -/
def decFrac (a : Dec) : Dec := Dec.sub a (Dec.ofInt (decFloorInt a))

/-- §6.4.4 `fn:round`: the nearest integer, and a value exactly halfway
    goes toward POSITIVE infinity. `fn:round(-2.5)` is `-2`, not `-3`.
    RIF-DTB 4.8 needs this and not a half-away-from-zero rounding:
    F&O 10.6.5 rounds `func:multiply-yearMonthDuration` "to the nearest
    month", and the Approved `Builtins_Time` fixture asserts
    `multiply-yearMonthDuration("P2Y11M", 2.3) = "P6Y9M"` — 35 months
    times 2.3 is 80.5 months, and the answer is 81. -/
def decRound (a : Dec) : Int := Rounding.integral .nearest a.mantissa ((10 : Int) ^ a.scale)

/-- §6.2.5 `op:numeric-integer-divide`: truncated toward zero. -/
def decIntDiv? (a b : Dec) : Option Int :=
  if b.mantissa == 0 then none
  else
    let s := max a.scale b.scale
    let ma := a.mantissa * (10 : Int) ^ (s - a.scale)
    let mb := b.mantissa * (10 : Int) ^ (s - b.scale)
    some (Int.tdiv ma mb)

/-- §6.2.6 `op:numeric-mod`: `a - (a idiv b) * b`, so the result takes
    the sign of `a`. -/
def decMod? (a b : Dec) : Option Dec :=
  (decIntDiv? a b).map (fun q => Dec.sub a (decMul b (Dec.ofInt q)))

/-! ## The decimal-NUMERAL layer

RIF-DTB's lexical decimal adapters now delegate parsing and rendering to
`XSD.parseDecimalLex` and `Dec.canonical`, and arithmetic to the operations
above. Existing public function names remain adapters to this one decimal
kernel. Lexical admission changes require the RIF and SPARQL regression gates. -/

/-- A decimal numeral as an exact MANTISSA and SCALE: the value is
    `mant / 10 ^ scale`. -/
def decParts (s : String) : Option (Int × Nat) :=
  (XSD.parseDecimalLex s).map (fun d => (d.mantissa, d.scale))

def decRender (m : Int) (scale : Nat) : String := (Dec.norm ⟨m, scale⟩).canonical

def decOfNumeral (s : String) : Option Dec := XSD.parseDecimalLex s

def addDec (a b : String) : Option String := do
  pure ((← decOfNumeral a).add (← decOfNumeral b)).canonical

def subDec (a b : String) : Option String := do
  pure ((← decOfNumeral a).sub (← decOfNumeral b)).canonical

def mulDec (a b : String) : Option String := do
  pure (decMul (← decOfNumeral a) (← decOfNumeral b)).canonical

def divDec (a b : String) : Option String := do
  (decDiv? divScale (← decOfNumeral a) (← decOfNumeral b)).map Dec.canonical

/-! ## Pins

Each `#guard` is an equation the specification or a vendored fixture
writes out. -/

-- RIF-DTB 4.5, the `Builtins_Numeric` lines.
#guard divDec "6" "3" = some "2"
#guard divDec "1" "8" = some "0.125"
#guard divDec "1" "0" = none
#guard addDec "1.5" "2.25" = some "3.75"
#guard subDec "1" "1" = some "0"
#guard mulDec "-1.5" "2" = some "-3"
-- The truncation direction §6.2.4 states, on both signs. Written `/`
-- this line gave `-0.333…334`, because Lean's `Int` `/` floors.
#guard divDec "-1" "3" = some "-0.333333333333333333"
#guard divDec "1" "3" = some "0.333333333333333333"

-- F&O 6.2.3-6.2.6 over `XSD.Dec`.
#guard decMul ⟨7800, 0⟩ ⟨21, 1⟩ = ⟨16380, 0⟩
#guard decDiv? 18 ⟨40, 0⟩ ⟨-16, 0⟩ = some ⟨-25, 1⟩
#guard decDiv? 18 ⟨1, 0⟩ ⟨0, 0⟩ = none
#guard decIntDiv? ⟨10, 0⟩ ⟨3, 0⟩ = some 3
#guard decIntDiv? ⟨-10, 0⟩ ⟨3, 0⟩ = some (-3)
#guard decMod? ⟨10, 0⟩ ⟨3, 0⟩ = some ⟨1, 0⟩

-- F&O 6.4.4 `fn:round`, including the tie the `Builtins_Time` fixture
-- depends on (80.5 months goes to 81).
#guard decRound ⟨805, 1⟩ = 81
#guard decRound ⟨-25, 1⟩ = -2
#guard decRound ⟨25, 1⟩ = 3
#guard decRound ⟨2333333333333333333, 17⟩ = 23

-- The floor, which is what a negative time-of-day offset needs.
#guard decFloorInt ⟨-15, 1⟩ = -2
#guard decFloorInt ⟨15, 1⟩ = 1
#guard decFrac ⟨-15, 1⟩ = ⟨5, 1⟩


end L4Factoidal.Fn.Numeric
