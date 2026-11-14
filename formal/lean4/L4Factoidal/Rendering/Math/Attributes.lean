/-
L4Factoidal.Rendering.Math.Attributes — the declarations a MathML element has with no
author style sheet: the user agent style sheet of MathML Core appendix A, and the
attributes that MathML Core maps to CSS (§2.1.3 `dir`, `displaystyle`, `scriptlevel`,
`mathcolor`, `mathbackground`, `mathsize`; §3.2.2 `mathvariant="normal"` on `mi`; §3.1.1
`display` on `math`).

Specification: https://w3c.github.io/mathml-core/ (appendix A "User Agent Stylesheet",
§2.1.3 "Global Attributes", §2.1.4 "Attributes common to HTML and MathML elements").

The style sheet of appendix A is written here as a function of the element, its parent
and its place among its element siblings, because the cascade of the layout profile
does not read child and `:nth-child` selectors. Each declaration has a level: the user
agent's, the user agent's `!important`, or a presentational hint (CSS Cascade 4 §6.1: the
author origin with specificity zero, before every author rule). `key` gives the cascade
key of a level in the form the cascades use (`CSS.computedFrom`,
`ComputedGeneric.cascaded`): a list compared by `keyLE`, later wins on a tie.

Only elements in the MathML namespace get declarations (`hints` answers `#[]` for any
other node), so a page with no MathML pays one namespace test per element.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.Rendering.Math
open L4Factoidal.DOM

/-- The cascade level of a declaration made here. -/
inductive Level where
  /-- The user agent style sheet (appendix A). -/
  | ua
  /-- An `!important` declaration of the user agent style sheet. -/
  | uaImportant
  /-- A presentational hint from an attribute. -/
  | hint
  deriving Repr, BEq, DecidableEq

/-- A declaration of an element: property, value and level. -/
structure Hint where
  property : String
  value : String
  level : Level := .ua
  deriving Repr, BEq

/-- Cascade keys in the cascades' order: importance, origin and context, style
attribute, specificity (three numbers), source order. -/
def Level.key : Level → List Nat
  | .ua => [0, 0, 0, 0, 0, 0, 0]
  | .uaImportant => [1, 5, 0, 0, 0, 0, 0]
  | .hint => [0, 2, 0, 0, 0, 0, 0]

/-- The order of cascade keys (the text of `ComputedGeneric.keyLE` and of the layout
profile's `lexLE`): lexicographic, a shorter key first. -/
def keyLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then keyLE as bs else a < b

/-- A cascade slot takes a declaration when the slot is empty or holds a key that is not
greater: the step both cascades make for each declaration. -/
def place {α : Type} (slot : Option (List Nat × α)) (key : List Nat) (value : α) : Option (List Nat × α) :=
  match slot with
  | none => some (key, value)
  | some old => if keyLE old.1 key then some (key, value) else some old

theorem keyLE_refl (k : List Nat) : keyLE k k = true := by
  induction k with
  | nil => rfl
  | cons a as ih => simp [keyLE, ih]

private theorem keyLE_zero (b : Nat) (as bs : List Nat) :
    keyLE (0 :: as) (b :: bs) = if b = 0 then keyLE as bs else true := by
  by_cases h : b = 0
  · subst h; simp [keyLE]
  · have h' : (0 == b) = false := by simp; omega
    simp [keyLE, h, h']; omega

private theorem keyLE_zeros (l : List Nat) : keyLE (List.replicate l.length 0) l = true := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, List.replicate_succ, keyLE_zero]
    split <;> simp [ih]

/-- Kind: algebraic law (idempotence).
Says: giving a cascade slot the same declaration twice leaves it as after once. So
mapping an element's attributes again (after a script sets the same attribute, or on a
second style pass) does not change the result.
Does not say: that two different hints for one property commute (the later one wins). -/
theorem place_idem {α : Type} (slot : Option (List Nat × α)) (key : List Nat) (value : α) :
    place (place slot key value) key value = place slot key value := by
  cases slot with
  | none => simp [place, keyLE_refl]
  | some old =>
    by_cases h : keyLE old.1 key = true
    · simp [place, h, keyLE_refl]
    · simp [place, h]

/-- The cascade key of a presentational hint is not above the key of any author
declaration `[i, 2 + c, s, a, b, n, o]`. -/
theorem hint_le_author (i c s a b n o : Nat) : keyLE Level.hint.key [i, 2 + c, s, a, b, n, o] = true := by
  simp only [Level.key, keyLE_zero]
  split
  · by_cases hc : c = 0
    · subst hc
      have := keyLE_zeros [s, a, b, n, o]
      simpa [keyLE] using this
    · have h' : (2 == 2 + c) = false := by simp; omega
      simp [keyLE, h']; omega
  · rfl

/-- Kind: specification conformance (CSS Cascade 4 §6.1; MathML Core §2.1.4).
Says: a declaration of an author rule, or of a `style` attribute, with any importance,
context, specificity and source order, takes a slot that holds a presentational hint: a
mapped attribute never overrides an author style. (An author key is `[i, 2 + c, s, a, b,
n, o]`, as the cascades make it.)
Does not say: anything about a rule of the user agent sheet (`hint_over_ua`). -/
theorem author_over_hint {α : Type} (h v : α) (i c s a b n o : Nat) :
    place (some (Level.hint.key, h)) [i, 2 + c, s, a, b, n, o] v = some ([i, 2 + c, s, a, b, n, o], v) := by
  simp [place, hint_le_author]

/-- Kind: specification conformance (CSS Cascade 4 §6.1).
Says: a presentational hint takes a slot that holds a normal user agent declaration, and
a normal user agent declaration does not take a slot that holds a hint, whatever its
specificity and order: a mapped attribute overrides the user agent style sheet. (A normal
user agent key is `[0, c, 0, a, b, n, o]` with `c` 0 or 1.)
Does not say: anything about `!important` user agent declarations (they win over all). -/
theorem hint_over_ua {α : Type} (h v : α) (c a b n o : Nat) (hc : c ≤ 1) :
    place (some ([0, c, 0, a, b, n, o], v)) Level.hint.key h = some (Level.hint.key, h) ∧
    place (some (Level.hint.key, h)) [0, c, 0, a, b, n, o] v = some (Level.hint.key, h) := by
  have e1 : (c == 2) = false := by simp; omega
  have e2 : (2 == c) = false := by simp; omega
  have h1 : keyLE [0, c, 0, a, b, n, o] Level.hint.key = true := by
    simp [Level.key, keyLE, e1]; omega
  have h2 : keyLE Level.hint.key [0, c, 0, a, b, n, o] = false := by
    simp [Level.key, keyLE, e2]; omega
  simp [place, h1, h2]

/-- The value of an attribute with no namespace. -/
def attr? (n : Node) (key : String) : Option String :=
  (n.attrs.find? fun a => a.ns.isNone && a.lname == key).map (·.value)

/-- An attribute value compared ASCII case-insensitively, with its white space trimmed. -/
def attrIs (n : Node) (key value : String) : Bool :=
  match attr? n key with
  | some v => v.trimAscii.toString.toLower == value
  | none => false

/-- The elements whose children's style depends on their place (appendix A). -/
def placedParents : List String :=
  ["mfrac", "mroot", "msub", "msup", "msubsup", "mmultiscripts", "munder", "mover", "munderover",
   "semantics", "maction"]

/-- The parent element when it is a MathML element of `placedParents`, with the 1-based
index of `id` among its element children and whether an `mprescripts` comes before it.
One pass over the siblings, made only for children of those parents. -/
def placeOf (dom : Dom) (id : Nat) : Option (Node × Nat × Bool) :=
  match (dom.get id).parent with
  | none => none
  | some p =>
    let pn := dom.get p
    if pn.type != .element || pn.ns != some mathmlNS || !placedParents.contains pn.lname then none else Id.run do
      let mut idx := 0
      let mut pre := false
      for k in pn.kids do
        let kn := dom.get k
        if kn.type == .element then
          idx := idx + 1
          if k == id then return some (pn, idx, pre)
          if kn.ns == some mathmlNS && kn.lname == "mprescripts" then pre := true
      return none

/-- `scriptlevel` (§2.1.3): `+N` and `-N` add to the depth, `N` sets it. `none`: not an
integer with an optional sign. -/
def scriptlevelValue (value : String) : Option String :=
  let v := value.trimAscii.toString
  let digits := fun (s : String) => !s.isEmpty && s.toList.all Char.isDigit
  if v.startsWith "+" then
    let d := (v.drop 1).toString
    if digits d then some s!"add({d})" else none
  else if v.startsWith "-" then
    let d := (v.drop 1).toString
    if digits d then some s!"add(-{d})" else none
  else if digits v then some v else none

/-- The declarations of the MathML element `id`: appendix A in the order of the sheet
(a later declaration of one level wins), then the mapped attributes. `#[]` for a node
that is not an element in the MathML namespace. -/
def hints (dom : Dom) (id : Nat) : Array Hint := Id.run do
  let n := dom.get id
  if n.type != .element || n.ns != some mathmlNS then return #[]
  let name := n.lname
  let mut out : Array Hint := #[]
  let ua := fun (out : Array Hint) (p v : String) => out.push ⟨p, v, .ua⟩
  -- * { font-size: math; display: block math; writing-mode: horizontal-tb !important; }
  out := ua out "display" "block math"
  out := out.push ⟨"writing-mode", "horizontal-tb", .uaImportant⟩
  if name == "math" then
    out := ua out "direction" "ltr"
    out := ua out "text-indent" "0"
    out := ua out "letter-spacing" "normal"
    out := ua out "line-height" "normal"
    out := ua out "word-spacing" "normal"
    out := ua out "font-style" "normal"
    out := ua out "font-weight" "normal"
    out := ua out "math-shift" "normal"
    out := ua out "math-depth" "0"
    -- math[display="block" i] and math[display="inline" i]
    if attrIs n "display" "block" then
      out := ua out "display" "block math"
      out := ua out "math-style" "normal"
    else
      out := ua out "display" "inline math"
      out := ua out "math-style" "compact"
  else
    out := ua out "font-size" "math"
  match name with
  | "merror" =>
    out := ua out "border" "1px solid red"
    out := ua out "background-color" "lightyellow"
  | "mphantom" => out := ua out "visibility" "hidden"
  | "mi" => out := ua out "text-transform" "math-auto"
  | "mtable" =>
    out := ua out "display" "inline-table"
    out := ua out "math-style" "compact"
  | "mtr" => out := ua out "display" "table-row"
  | "mtd" =>
    out := ua out "display" "table-cell"
    out := ua out "text-align" "center"
    out := ua out "padding" "0.5ex 0.4em"
  | "mfrac" => out := ua out "padding-inline" "1px"
  | "mroot" | "msqrt" => out := ua out "math-shift" "compact"
  | _ => pure ()
  if let some (pn, idx, pre) := placeOf dom id then
    let parent := pn.lname
    let accent := attrIs pn "accent" "true"
    let accentUnder := attrIs pn "accentunder" "true"
    match parent with
    | "semantics" | "maction" => if idx > 1 then out := ua out "display" "none"
    | "mfrac" =>
      out := ua out "math-depth" "auto-add"
      out := ua out "math-style" "compact"
      if idx == 2 then out := ua out "math-shift" "compact"
    | "mroot" =>
      if idx > 1 then
        out := ua out "math-depth" "add(2)"
        out := ua out "math-style" "compact"
    | _ =>
      if idx > 1 then
        out := ua out "math-depth" "add(1)"
        out := ua out "math-style" "compact"
      -- accents keep the font size
      if (parent == "munder" && accentUnder && idx == 2) || (parent == "mover" && accent && idx == 2) ||
         (parent == "munderover" && accentUnder && idx == 2) || (parent == "munderover" && accent && idx == 3) then
        out := ua out "font-size" "inherit"
      -- cramped positions
      if ((parent == "msub" || parent == "msubsup") && idx == 2) ||
         (parent == "mmultiscripts" && ((!pre && idx % 2 == 0) || (pre && idx % 2 == 1))) ||
         ((parent == "mover" || parent == "munderover") && accent && idx == 1) then
        out := ua out "math-shift" "compact"
      if parent == "mmultiscripts" && pre && idx % 2 == 0 then out := ua out "math-shift" "inherit"
  -- the mapped attributes
  let hint := fun (out : Array Hint) (p v : String) => out.push ⟨p, v, .hint⟩
  if attrIs n "dir" "ltr" then out := hint out "direction" "ltr"
  if attrIs n "dir" "rtl" then out := hint out "direction" "rtl"
  if let some v := attr? n "mathcolor" then out := hint out "color" v.trimAscii.toString
  if let some v := attr? n "mathbackground" then out := hint out "background-color" v.trimAscii.toString
  if let some v := attr? n "mathsize" then out := hint out "font-size" v.trimAscii.toString.toLower
  if attrIs n "displaystyle" "true" then out := hint out "math-style" "normal"
  if attrIs n "displaystyle" "false" then out := hint out "math-style" "compact"
  if let some v := (attr? n "scriptlevel").bind scriptlevelValue then out := hint out "math-depth" v
  if name == "mi" && attrIs n "mathvariant" "normal" then out := hint out "text-transform" "none"
  return out

/-- A decimal number with an optional sign and fraction, no exponent (the numbers of
MathML length attributes). At most 24 characters. -/
def parseNumber (source : String) : Option Float :=
  let s := source.trimAscii.toString
  let negative := s.startsWith "-"
  let s := if negative || s.startsWith "+" then (s.drop 1).toString else s
  if s.length > 24 || s.isEmpty then none else
  let parts := s.splitOn "."
  if parts.length > 2 || parts.any (fun p => !p.toList.all Char.isDigit) || parts.all String.isEmpty then none else
  let whole := (parts.headD "").toNat?.getD 0
  let fraction := parts[1]?.getD ""
  let scale := fraction.toList.foldl (fun (n : Float) _ => n * 10) 1
  let value := Float.ofNat whole + Float.ofNat (fraction.toNat?.getD 0) / scale
  some (if negative then -value else value)

/-- A MathML length attribute (`<length-percentage>`, §2.1.2) in CSS pixels: `em` and `ex`
against `fontSize` (with no font metrics an `ex` is half an em), a percentage against
`basis` when one is given. Units are ASCII case-insensitive; a number with no unit is a
length only when it is zero. `none`: not a length, so the attribute is ignored. -/
def lengthPx (fontSize : Float) (value : String) (basis : Option Float := none) : Option Float :=
  let s := value.trimAscii.toString.toLower
  let num := fun (drop : Nat) => parseNumber (s.dropEnd drop).toString
  if s.endsWith "px" then num 2
  else if s.endsWith "rem" then (num 3).map (· * 16)
  else if s.endsWith "em" then (num 2).map (· * fontSize)
  else if s.endsWith "ex" then (num 2).map (· * fontSize / 2)
  else if s.endsWith "pt" then (num 2).map (· * 96 / 72)
  else if s.endsWith "pc" then (num 2).map (· * 16)
  else if s.endsWith "in" then (num 2).map (· * 96)
  else if s.endsWith "cm" then (num 2).map (· * 96 / 2.54)
  else if s.endsWith "mm" then (num 2).map (· * 96 / 25.4)
  else if s.endsWith "q" then (num 1).map (· * 96 / 101.6)
  else if s.endsWith "%" then basis.bind fun b => (num 1).map (· * b / 100)
  else match parseNumber s with
    | some v => if v == 0 then some 0 else none
    | none => none

/-- The value the layout profile reads for a declaration made here (the profile reads
pixel lengths and the display types it lays out): `none` when the profile keeps its own
default. `display` keeps `none`, and the outer type of a `math` element; a `font-size`
from `mathsize` becomes pixels against the parent's font size. -/
def profileValue (name property value : String) (parentFontSize : Float) : Option String :=
  if property == "display" then
    if value == "none" then some "none"
    else if name == "math" then some (if value == "block math" then "block" else "inline")
    else none
  else if property == "font-size" then
    if value == "math" || value == "inherit" then some value
    else match lengthPx parentFontSize value (some parentFontSize) with
      | some v => if v > 0 then some s!"{v}px" else none
      | none => none
  else if property == "padding" || property == "padding-inline" then none
  else some value

/-- 0.71 to the power `n` (the script scale of a font with no MATH table), `n` at most 64. -/
def scalePower (n : Nat) : Float := (List.range (min n 64)).foldl (fun f _ => f * 0.71) 1

/-- `math-depth` (MathML Core §4.5... CSS `math-depth`): the computed depth from the
cascaded value and the parent's depth and `math-style`. -/
def depthOf (value : String) (parentDepth : Int) (parentCompact : Bool) : Int :=
  let v := value.trimAscii.toString.toLower
  if v == "auto-add" then (if parentCompact then parentDepth + 1 else parentDepth)
  else if v.startsWith "add(" && v.endsWith ")" then
    match ((v.drop 4).toString.dropEnd 1).toString.trimAscii.toString.toInt? with
    | some k => parentDepth + k
    | none => parentDepth
  else match v.toInt? with
    | some k => k
    | none => parentDepth

/-- The exponent pair of the font size scale between two depths (MathML Core §4.5 "the
math-depth property", the `font-size: math` algorithm) for a font with no MATH table,
where each script level scales by 0.71: `(up, n)` means 0.71 to the power `n`, inverted
when `up` (the depth falls). -/
def depthScale (parentDepth depth : Int) : Bool × Nat :=
  if depth ≥ parentDepth then (false, (depth - parentDepth).toNat) else (true, (parentDepth - depth).toNat)

/-- Kind: algebraic law.
Says: an unchanged depth gives the scale exponent zero: `font-size: math` leaves the
inherited size as it is.
Does not say: what the scale of a font with a MATH table is. -/
theorem depthScale_same (d : Int) : depthScale d d = (false, 0) := by
  simp [depthScale]

#guard scriptlevelValue "+2" == some "add(2)" && scriptlevelValue "-1" == some "add(-1)" &&
       scriptlevelValue " 3 " == some "3" && scriptlevelValue "1.5" == none && scriptlevelValue "+" == none
#guard depthOf "auto-add" 1 true == 2 && depthOf "auto-add" 1 false == 1 && depthOf "add(2)" 1 false == 3 &&
       depthOf "add(-1)" 1 false == 0 && depthOf "7" 1 false == 7 && depthOf "x" 4 false == 4
#guard lengthPx 16 "20px" == some 20 && lengthPx 16 "2EM" == some 32 && lengthPx 16 "0" == some 0 &&
       lengthPx 16 "5" == none && lengthPx 16 "50%" == none && lengthPx 16 "50%" (some 10) == some 5 &&
       lengthPx 16 " 1in " == some 96 && lengthPx 16 "-3px" == some (-3) && lengthPx 16 "1e2px" == none
#guard profileValue "math" "display" "block math" 16 == some "block" && profileValue "mrow" "display" "block math" 16 == none &&
       (profileValue "mtext" "font-size" "30px" 50).isSome && profileValue "mi" "display" "none" 16 == some "none" &&
       profileValue "mtext" "font-size" "math" 50 == some "math" && profileValue "mtd" "padding" "0.5ex 0.4em" 16 == none
#guard depthScale 0 2 == (false, 2) && depthScale 3 1 == (true, 2)
#guard keyLE Level.ua.key Level.hint.key && !keyLE Level.hint.key Level.ua.key && keyLE Level.hint.key Level.uaImportant.key

end L4Factoidal.Rendering.Math
