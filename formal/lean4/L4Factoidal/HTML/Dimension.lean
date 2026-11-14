/-
L4Factoidal.HTML.Dimension — the numeric attribute values of HTML's presentational hints:
the "rules for parsing integers" and "non-negative integers" (HTML §2.3.4.1, §2.3.4.2), the
"rules for parsing dimension values" and "nonzero dimension values" (§2.3.4.4).

A dimension is a decimal number, read exactly: `mantissa / 10 ^ scale`, a length (CSS
pixels) or a percentage. `200.25%` is `⟨20025, 2, .percentage⟩`; text after the number is
ignored (`200in` is 200, `20.25e2` is 20.25), a sign or a leading `.` is a failure.

The rendering section maps these to CSS properties (HTML §15.2 "maps to the dimension
property", "maps to the dimension property (ignoring zero)", "maps to the pixel length
property"): `Rendering.Style` does that, below author CSS.
-/

namespace L4Factoidal.HTML.Dimension

inductive Kind where
  | length | percentage
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A dimension value: `mantissa / 10 ^ scale` of `kind`. -/
structure Dim where
  mantissa : Nat
  scale : Nat := 0
  kind : Kind := .length
  deriving Repr, BEq, DecidableEq, Inhabited

/-- ASCII whitespace (Infra): tab, line feed, form feed, carriage return, space. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitsValue (ds : List Char) : Nat := ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- "The current dimension value" (§2.3.4.4): a percentage when the next character is `%`. -/
def kindAt : List Char → Kind
  | '%' :: _ => .percentage
  | _ => .length

/-- The rules for parsing dimension values, on the characters after the leading whitespace. -/
def parseChars (cs : List Char) : Option Dim :=
  let int := cs.takeWhile isDigit
  if int.isEmpty then none else
  match cs.drop int.length with
  | '.' :: after =>
    let frac := after.takeWhile isDigit
    if frac.isEmpty then some { mantissa := digitsValue int, kind := kindAt after }
    else some { mantissa := digitsValue (int ++ frac), scale := frac.length, kind := kindAt (after.drop frac.length) }
  | rest => some { mantissa := digitsValue int, kind := kindAt rest }

/-- HTML §2.3.4.4 "rules for parsing dimension values". -/
def parse (input : String) : Option Dim := parseChars (input.toList.dropWhile isWs)

/-- HTML §2.3.4.4 "rules for parsing nonzero dimension values": zero is a failure. -/
def parseNonzero (input : String) : Option Dim :=
  match parse input with
  | some d => if d.mantissa == 0 then none else some d
  | none => none

/-- HTML §2.3.4.1 "rules for parsing integers". -/
def parseInteger (input : String) : Option Int :=
  let cs := input.toList.dropWhile isWs
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ds := cs.takeWhile isDigit
  if ds.isEmpty then none else
  let v := digitsValue ds
  some (if neg then -(v : Int) else v)

/-- HTML §2.3.4.2 "rules for parsing non-negative integers". -/
def parseNonNegative (input : String) : Option Nat :=
  match parseInteger input with
  | some v => if 0 ≤ v then some v.toNat else none
  | none => none

/-- The value as a float (exact for the short decimals of attributes). -/
def Dim.toFloat (d : Dim) : Float := Float.ofScientific d.mantissa true d.scale

/-! ## What is proved -/

/-- Says: a value whose first character after the whitespace is not a digit (a sign, a
`.`, a letter, nothing) is a failure. -/
theorem parse_needs_digit (s : String) (h : ∀ c rest, s.toList.dropWhile isWs = c :: rest → isDigit c = false) :
    parse s = none := by
  unfold parse parseChars
  cases hc : s.toList.dropWhile isWs with
  | nil => simp
  | cons c rest =>
    have := h c rest hc
    simp [List.takeWhile, this]

/-- Says: leading whitespace does not change the value. -/
theorem parse_space (s : String) : parse (" " ++ s) = parse s := by
  unfold parse
  simp [String.toList_append, isWs]

/-- Says: a nonzero dimension is positive. -/
theorem parseNonzero_pos (s : String) (d : Dim) (h : parseNonzero s = some d) : d.mantissa ≠ 0 := by
  unfold parseNonzero at h
  split at h
  · split at h
    · cases h
    · cases h; simp_all
  · cases h

/-- Says: a nonzero dimension is a dimension. -/
theorem parseNonzero_parse (s : String) (d : Dim) (h : parseNonzero s = some d) : parse s = some d := by
  unfold parseNonzero at h
  split at h
  · rename_i d' hd
    split at h
    · cases h
    · cases h; exact hd
  · cases h

/-- Says: a non-negative integer is an integer of the same value: no failure turns into a
value, and a negative value is never answered. -/
theorem parseNonNegative_sound (s : String) (n : Nat) (h : parseNonNegative s = some n) :
    parseInteger s = some (n : Int) := by
  unfold parseNonNegative at h
  split at h
  · rename_i v hv
    split at h
    · cases h; rw [hv]; congr 1; omega
    · cases h
  · cases h

/-- Says: the empty value and whitespace alone are failures. -/
theorem parse_blank : parse "" = none ∧ parse "   " = none := by decide

/-! ## Tests (html/rendering/dimension-attributes.html, pixel-length-attributes.html) -/

#guard parse "200" == some ⟨200, 0, .length⟩
#guard parse "   00523   " == some ⟨523, 0, .length⟩
#guard parse "200.25" == some ⟨20025, 2, .length⟩
#guard parse "200." == some ⟨200, 0, .length⟩
#guard parse "200in" == some ⟨200, 0, .length⟩
#guard parse "200 %" == some ⟨200, 0, .length⟩
#guard parse "200%abc" == some ⟨200, 0, .percentage⟩
#guard parse "200.25%" == some ⟨20025, 2, .percentage⟩
#guard parse "200.%" == some ⟨200, 0, .percentage⟩
#guard parse "20.25e2" == some ⟨2025, 2, .length⟩
#guard parse "0%" == some ⟨0, 0, .percentage⟩
#guard ["-0", "-200", "+200", "   +200in    ", "+0%", ".", ".%", ".x", ".5", ".5%", "", "abc"].all (parse · == none)
#guard parseNonzero "0" == none && parseNonzero "0%" == none && parseNonzero "0px" == none && parseNonzero "0.0" == none
#guard parseNonzero "0.5" == some ⟨5, 1, .length⟩
#guard (parse "200.25").map Dim.toFloat == some 200.25 && (parse "200.7").map Dim.toFloat == some 200.7
#guard parseNonNegative "200.25" == some 200 && parseNonNegative "   +200in    " == some 200
#guard parseNonNegative "-0" == some 0 && parseNonNegative "+0" == some 0 && parseNonNegative "200%" == some 200
#guard ["-200", "-200px", "   -200", "+-200", "-+200", "", "x"].all (parseNonNegative · == none)

end L4Factoidal.HTML.Dimension
