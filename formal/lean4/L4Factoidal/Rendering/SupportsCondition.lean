/-
L4Factoidal.Rendering.SupportsCondition — the `<supports-condition>` grammar of CSS
Conditional Rules 3 §2, evaluated: `not`, `and`, `or` over declarations and `selector()`.

One evaluator for `CSS.supports(conditionText)` (`CssSupports`) and for the `@supports`
rules of a style sheet (`SheetReader`, `CSS.parseRaw`): a declaration is supported when
the property table parses it (`CssValues.supports`, the function behind `element.style`,
`getComputedStyle` and `CSS.supports(property, value)`), a selector when `DOM.Selectors`
reads it. It sits below `Style`, which reads sheets through it.
-/
import L4Factoidal.Rendering.CssValues.Properties
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
    else some (CssValues.supports p (":".intercalate (v :: more)))
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

/-- The condition of an `@supports` rule (CSS Conditional 3 §6): the rule's contents apply
when the condition is true; a condition that does not parse is false. -/
def ruleHolds (text : String) : Bool :=
  let cs := text.toList
  (condition (cs.length + 2) cs).getD false

/-- An `@supports` rule holds exactly when its condition parses and is true: a condition
that is a syntax error holds nothing, as a false one. -/
theorem ruleHolds_iff (text : String) :
    ruleHolds text = true ↔ condition (text.toList.length + 2) text.toList = some true := by
  unfold ruleHolds
  cases h : condition (text.toList.length + 2) text.toList <;> simp [h]

#guard ruleHolds "(display: grid)"
#guard ruleHolds "(display: grid) and (not (display: gridd))"
#guard !ruleHolds "(display: gridd)"
#guard !ruleHolds "display: grid"
#guard ruleHolds "not (foo: bar)"
#guard ruleHolds "selector(a > b)"
#guard !ruleHolds "selector(a >> b)"
#guard ruleHolds "(--x: 1)"
#guard !ruleHolds ""

end L4Factoidal.Rendering.CssSupports
