/-
L4Factoidal.DOM.SvgValues — the attribute values that the SVG DOM reflects (SVG 2 §4,
https://svgwg.org/svg2-draft/types.html): a length (`SVGLength`), a number, a list of
numbers or points, a transform list (`SVGTransformList`, CSS Transforms 1 §8.1 for the
attribute syntax). `web_api` ops 92 to 95 (`WasmVM.Hosts.WebApi`).

The page's SVG interfaces (prelude.js) are the WebIDL surface; whether an attribute value is
a length, a number or a transform, and its parts, is read here. A number is answered as its
own text (a decimal the page's `Number` reads exactly as ECMAScript reads it), so no
floating-point value is made or rounded in Lean.

Every loop is a core list combinator or a tail call on a shorter list.
-/

namespace L4Factoidal.DOM.SvgValues

/-- ASCII whitespace of an SVG attribute (SVG 2 §4.2: space, tab, line feed, form feed,
carriage return). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

/-- Without leading and trailing whitespace. -/
def trim (cs : List Char) : List Char := ((cs.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- The longest prefix of `cs` that is a number (CSS Syntax 3 §4.3.12 "consume a number":
an optional sign, digits with an optional fraction or a fraction alone, an optional
exponent), and the rest; `none` when `cs` does not start with a number. -/
def takeNumber (cs : List Char) : Option (List Char × List Char) :=
  let (sign, cs) := match cs with
    | '+' :: r => (['+'], r)
    | '-' :: r => (['-'], r)
    | _ => ([], cs)
  let int := cs.takeWhile Char.isDigit
  let cs := cs.dropWhile Char.isDigit
  let (frac, cs) := match cs with
    | '.' :: r =>
      let d := r.takeWhile Char.isDigit
      if d.isEmpty then ([], cs) else ('.' :: d, r.dropWhile Char.isDigit)
    | _ => ([], cs)
  if int.isEmpty && frac.isEmpty then none else
  let (exp, cs) := match cs with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (s, r') := match r with
          | '+' :: x => (['+'], x)
          | '-' :: x => (['-'], x)
          | _ => ([], r)
        let d := r'.takeWhile Char.isDigit
        if d.isEmpty then ([], cs) else (e :: s ++ d, r'.dropWhile Char.isDigit)
      else ([], cs)
    | [] => ([], cs)
  some (sign ++ int ++ frac ++ exp, cs)

/-- A number alone (surrounding whitespace allowed): its text. -/
def parseNumber (s : String) : Option String :=
  match takeNumber (trim s.toList) with
  | some (n, []) => some (String.ofList n)
  | _ => none

/-- The `SVGLength` unit type of a unit (SVG 2 §4.6.1): 1 number, 2 percentage, 3 ems,
4 exs, 5 px, 6 cm, 7 mm, 8 in, 9 pt, 10 pc; `none` for a unit the interface has no type for. -/
def unitType (unit : String) : Option Nat :=
  match unit.toLower with
  | "" => some 1
  | "%" => some 2
  | "em" => some 3
  | "ex" => some 4
  | "px" => some 5
  | "cm" => some 6
  | "mm" => some 7
  | "in" => some 8
  | "pt" => some 9
  | "pc" => some 10
  | _ => none

/-- The unit of an `SVGLength` unit type, as it is written. -/
def unitText (t : Nat) : String :=
  match t with
  | 2 => "%" | 3 => "em" | 4 => "ex" | 5 => "px" | 6 => "cm" | 7 => "mm" | 8 => "in" | 9 => "pt" | 10 => "pc"
  | _ => ""

/-- The other CSS length units an attribute may use (their `SVGLength` type is 0, unknown, and
the page resolves them from its styles): font-relative and viewport-relative. -/
def otherUnits : List String := ["rem", "ch", "ic", "lh", "rlh", "cap", "rex", "vw", "vh", "vmin", "vmax", "vi", "vb", "q"]

/-- A length: the number's text, the unit in lower case, and the unit type (0: a unit of
`otherUnits`). `none` when the value is not a length. -/
def parseLength (s : String) : Option (String × String × Nat) :=
  match takeNumber (trim s.toList) with
  | some (n, rest) =>
    match unitType (String.ofList rest).toLower with
    | some t => some (String.ofList n, (String.ofList rest).toLower, t)
    | none =>
      if otherUnits.contains (String.ofList rest).toLower then some (String.ofList n, (String.ofList rest).toLower, 0)
      else none
  | none => none

/-- A separator between list items: whitespace with at most one comma. The rest after it, and
whether a comma was passed; `none` for two commas. -/
def skipSeparator (cs : List Char) : List Char × Bool :=
  match cs.dropWhile isWs with
  | ',' :: r => (r.dropWhile isWs, true)
  | r => (r, false)

/-- The numbers of a list (SVG 2 §4.2: separated by whitespace, a comma, or both). `fuel`:
each turn takes a number, so the length of the text and one suffices. -/
def numbersGo : List Char → List String → Nat → Option (List String)
  | _, acc, 0 => some acc.reverse
  | [], acc, _ => some acc.reverse
  | cs, acc, fuel + 1 =>
    match takeNumber cs with
    | none => none
    | some (n, rest) =>
      let (rest', comma) := skipSeparator rest
      -- a comma must be followed by a number
      if comma && rest'.isEmpty then none else numbersGo rest' (String.ofList n :: acc) fuel

/-- A list of numbers; the empty text is the empty list. -/
def parseNumberList (s : String) : Option (List String) :=
  let cs := trim s.toList
  numbersGo cs [] (cs.length + 1)

/-- The transform functions of the `transform` attribute and how many numbers each takes. -/
def arityOk (name : String) (n : Nat) : Bool :=
  match name with
  | "matrix" => n == 6
  | "translate" | "scale" => n == 1 || n == 2
  | "rotate" => n == 1 || n == 3
  | "skewX" | "skewY" => n == 1
  | _ => false

/-- The transforms of a transform list: each a function name and its numbers. `fuel`: each
turn takes a function. -/
def transformsGo : List Char → List (String × List String) → Nat → Option (List (String × List String))
  | _, acc, 0 => some acc.reverse
  | [], acc, _ => some acc.reverse
  | cs, acc, fuel + 1 =>
    let name := String.ofList (cs.takeWhile Char.isAlpha)
    match (cs.dropWhile Char.isAlpha).dropWhile isWs with
    | '(' :: rest =>
      let inner := rest.takeWhile (· != ')')
      match rest.dropWhile (· != ')') with
      | ')' :: after =>
        match parseNumberList (String.ofList inner) with
        | some nums =>
          if arityOk name nums.length then transformsGo (skipSeparator after).1 ((name, nums) :: acc) fuel else none
        | none => none
      | _ => none
    | _ => none

/-- A transform list; the empty text is the empty list. -/
def parseTransformList (s : String) : Option (List (String × List String)) :=
  let cs := trim s.toList
  transformsGo cs [] (cs.length + 1)

/-! ## The ops -/

/-- One field of a `web_api` call as a string. -/
def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

/-- `web_api` ops 92 to 95 (no state; -1 when the value is not of the kind): 92 a length:
the number, the unit and the unit type, each on a line; 93 a number; 94 a list of numbers,
one on a line; 95 a transform list: each transform on a line, its name and its numbers
separated by spaces. -/
def op (code : Nat) (fs : Array ByteArray) : Except Int ByteArray :=
  match code with
  | 92 =>
    match parseLength (strAt fs 0) with
    | some (n, u, t) => .ok (n ++ "\n" ++ u ++ "\n" ++ toString t).toUTF8
    | none => .error (-1)
  | 93 =>
    match parseNumber (strAt fs 0) with
    | some n => .ok n.toUTF8
    | none => .error (-1)
  | 94 =>
    match parseNumberList (strAt fs 0) with
    | some ns => .ok ("\n".intercalate ns).toUTF8
    | none => .error (-1)
  | 95 =>
    match parseTransformList (strAt fs 0) with
    | some ts => .ok ("\n".intercalate (ts.map fun (n, xs) => " ".intercalate (n :: xs))).toUTF8
    | none => .error (-1)
  | _ => .error (-2)

/-! ## Theorems -/

/-- Kind: lemma. Says: a unit type that `unitType` gives is 1 to 10. -/
theorem unitType_le (u : String) (t : Nat) (h : unitType u = some t) : t ≤ 10 := by
  unfold unitType at h
  split at h <;> first | (simp only [Option.some.injEq] at h; omega) | simp at h

/-- Kind: validity of the answer. Says: the unit type of a parsed length is one of the eleven
of `SVGLength` (0 to 10). -/
theorem parseLength_type (s n u : String) (t : Nat) (h : parseLength s = some (n, u, t)) : t ≤ 10 := by
  unfold parseLength at h
  split at h
  · split at h
    · rename_i ht
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
      exact unitType_le _ _ ht
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      · simp at h
  · simp at h

/-- Kind: validity of the answer. Says: `arityOk` accepts only the six transform functions of
the attribute, each with a number count the function takes. -/
theorem arityOk_names (name : String) (n : Nat) (h : arityOk name n = true) :
    name ∈ ["matrix", "translate", "scale", "rotate", "skewX", "skewY"] ∧ 1 ≤ n ∧ n ≤ 6 := by
  unfold arityOk at h
  split at h <;> simp_all <;> omega

/-! ## Checks (SVG 2 §4.2, and WPT svg/types/scripted cases) -/

#guard parseNumber "10" == some "10" && parseNumber " -1.5e3 " == some "-1.5e3" && parseNumber ".5" == some ".5"
#guard parseNumber "1." == none && parseNumber "" == none && parseNumber "1 2" == none && parseNumber "e3" == none
#guard parseNumber "1e" == none && parseNumber "+.5E-2" == some "+.5E-2" && parseNumber "abc" == none
#guard parseLength "10px" == some ("10", "px", 5) && parseLength " 2.5EM " == some ("2.5", "em", 3)
#guard parseLength "50%" == some ("50", "%", 2) && parseLength "7" == some ("7", "", 1)
#guard parseLength "1e2cm" == some ("1e2", "cm", 6) && parseLength "3rem" == some ("3", "rem", 0)
#guard parseLength "10 px" == none && parseLength "px" == none && parseLength "10foo" == none && parseLength "" == none
-- `1em` is a number and the unit em, not an exponent with no digits
#guard parseLength "1em" == some ("1", "em", 3) && parseLength "1ex" == some ("1", "ex", 4)
#guard parseNumberList "1 2,3 , 4" == some ["1", "2", "3", "4"] && parseNumberList "" == some []
#guard parseNumberList "1,,2" == none && parseNumberList "1," == none && parseNumberList "1 a" == none
#guard parseNumberList "1-2" == some ["1", "-2"] && parseNumberList "1.5.5" == some ["1.5", ".5"]
#guard parseTransformList "translate(10 20) rotate(45)" == some [("translate", ["10", "20"]), ("rotate", ["45"])]
#guard parseTransformList "matrix(1,0,0,1,5,6),scale(2)" == some [("matrix", ["1", "0", "0", "1", "5", "6"]), ("scale", ["2"])]
#guard parseTransformList "" == some [] && parseTransformList "rotate(1 2)" == none && parseTransformList "foo(1)" == none
#guard parseTransformList "translate(1" == none && parseTransformList "skewX ( 30 )" == some [("skewX", ["30"])]

end L4Factoidal.DOM.SvgValues
