/-
L4Factoidal.Rendering.CssSupports — the `CSS` namespace of page scripts: `CSS.supports`
(CSS Conditional Rules 3 §8.1, the `<supports-condition>` grammar of §2) and `CSS.escape`
(CSSOM §2.1 "serialize an identifier").

`supports` answers for what this engine's style profile reads (`CSS.supportsDeclaration`)
and what `DOM.Selectors` parses (`selector(...)`): a page that asks gets the truth about
this engine, not about other browsers.
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.DOM.Selectors

namespace L4Factoidal.Rendering.CssSupports

/-- The text inside the parenthesis that opens at the start of `cs` (which starts after
the `(`), and the rest after its `)`; none when it does not close. Strings and nested
parentheses are skipped. -/
def inParens (cs : List Char) : Option (List Char × List Char) := Id.run do
  let mut depth := 0
  let mut inside : List Char := []
  let mut rest := cs
  let mut quote : Option Char := none
  for _ in [0:cs.length + 1] do
    match rest with
    | [] => return none
    | c :: r =>
      rest := r
      match quote with
      | some q => if c == q then quote := none
      | none =>
        if c == '"' || c == '\'' then quote := some c
        else if c == '(' then depth := depth + 1
        else if c == ')' then
          if depth == 0 then return some (inside.reverse, r) else depth := depth - 1
      inside := c :: inside
  return none

def trimL (cs : List Char) : List Char := cs.dropWhile (·.isWhitespace)

/-- A keyword at the start of `cs` (ASCII case-insensitive), followed by white space or
`(`; the rest. -/
def keyword (kw : String) (cs : List Char) : Option (List Char) :=
  let n := kw.length
  let head := String.ofList (cs.take n)
  if head.toLower == kw then
    match cs.drop n with
    | c :: r => if c.isWhitespace || c == '(' then some (c :: r) else none
    | [] => none
  else none

/-- `<supports-in-parens>` contents: a condition, a declaration, or anything else (general
enclosed: false). -/
def declaration (cs : List Char) : Option Bool :=
  let s := String.ofList cs
  match s.splitOn ":" with
  | p :: v :: more =>
    let p := p.trimAscii.toString
    if p.isEmpty || p.toList.any Char.isWhitespace then none
    else some (CSS.supportsDeclaration p (":".intercalate (v :: more)))
  | _ => none

/-- Evaluate a `<supports-condition>` (CSS Conditional 3 §2): `not`, `and`, `or` over
parenthesized conditions, declarations and `selector()`. `none` is a syntax error. `fuel`
bounds the nesting. -/
def condition : Nat → List Char → Option Bool
  | 0, _ => none
  | fuel + 1, cs =>
    let cs := trimL cs
    match keyword "not" cs with
    | some r =>
      match inParensValue fuel (trimL r) with
      | some (v, rest) => if (trimL rest).isEmpty then some !v else none
      | none => none
    | none => Id.run do
      let some (v0, rest0) := inParensValue fuel cs | return none
      let mut acc := v0
      let mut rest := trimL rest0
      let mut op : Option String := none
      for _ in [0:cs.length + 1] do
        if rest.isEmpty then return some acc
        let (o, r) := match keyword "and" rest, keyword "or" rest with
          | some r, _ => ("and", r)
          | _, some r => ("or", r)
          | _, _ => ("", rest)
        if o.isEmpty || (op.isSome && op != some o) then return none
        op := some o
        let some (v, r') := inParensValue fuel (trimL r) | return none
        acc := if o == "and" then acc && v else acc || v
        rest := trimL r'
      return some acc
where
  /-- One `<supports-in-parens>` or `<supports-feature>` at the start: its value and the rest. -/
  inParensValue (fuel : Nat) (cs : List Char) : Option (Bool × List Char) :=
    match cs with
    | '(' :: r =>
      match inParens r with
      | some (inner, rest) =>
        match condition fuel inner with
        | some v => some (v, rest)
        | none => some ((declaration inner).getD false, rest)
      | none => none
    | _ =>
      match keyword "selector" cs with
      | some ('(' :: r) =>
        match inParens r with
        | some (inner, rest) => some ((L4Factoidal.DOM.Selectors.parse (String.ofList inner)).isSome, rest)
        | none => none
      | _ =>
        -- a function we do not know (general enclosed) is false
        let name := cs.takeWhile fun c => c.isAlphanum || c == '-'
        match cs.drop name.length with
        | '(' :: r => if name.isEmpty then none else (inParens r).map fun (_, rest) => (false, rest)
        | _ => none

/-- `CSS.supports(conditionText)`: the condition, or the text in parentheses as a
declaration (CSS Conditional 3 §8.1). -/
def supportsText (text : String) : Bool :=
  let cs := text.toList
  match condition (cs.length + 2) cs with
  | some v => v
  | none => (declaration cs).getD false

/-- `CSS.escape(ident)`: "serialize an identifier" (CSSOM §2.1). -/
def escape (s : String) : String := Id.run do
  let cs := s.toList
  let mut out := ""
  let hex := fun (c : Char) => "\\" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ " "
  for i in [0:cs.length] do
    let c := cs[i]!
    let n := c.toNat
    if n == 0 then out := out.push (Char.ofNat 0xFFFD)
    else if (1 ≤ n && n ≤ 0x1F) || n == 0x7F then out := out ++ hex c
    else if i == 0 && c.isDigit then out := out ++ hex c
    else if i == 1 && c.isDigit && cs[0]! == '-' then out := out ++ hex c
    else if i == 0 && c == '-' && cs.length == 1 then out := out ++ "\\-"
    else if n ≥ 0x80 || c == '-' || c == '_' || c.isAlphanum then out := out.push c
    else out := out ++ "\\" ++ String.singleton c
  return out

#guard escape "0a" == "\\30 a"
#guard escape "-1x" == "-\\31 x"
#guard escape "-" == "\\-"
#guard escape "a b#c" == "a\\ b\\#c"
#guard escape "\x01" == "\\1 "
#guard supportsText "(display: block)"
#guard supportsText "display: block"
#guard supportsText "(display: grid)"
#guard !supportsText "(display: gridd)"
#guard supportsText "not (display: gridd)"
#guard supportsText "(display: gridd) or (color: red)"
#guard !supportsText "(display: gridd) and (color: red)"
#guard supportsText "selector(div > p)"
#guard !supportsText "(display: block) and (color: red) or (x: y)"
#guard supportsText "(--foo: bar)"
#guard !supportsText "foo(bar)"
#guard CSS.supportsDeclaration "margin" "1px 2px"
#guard CSS.supportsDeclaration "COLOR" "red"
#guard !CSS.supportsDeclaration "color" "red !important"

end L4Factoidal.Rendering.CssSupports
