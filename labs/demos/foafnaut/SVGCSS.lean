/- Bounded SVG author-CSS slice. CSS Syntax 3 and Cascade 5.
   This is an explicit-refusal profile, not CSS error recovery or full CSS. -/
namespace NativeSVGCSS
structure Declaration where
  property : String
  value : String
  deriving Repr, BEq, Inhabited
structure Rule where
  selectors : List String
  declarations : List Declaration
  deriving Repr, BEq, Inhabited
private def trim (s : String) := s.trimAscii.toString
private def ident (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isAlpha && c.toNat < 128 || c == '-' || c.isDigit) &&
  (s.toList.head!).isAlpha

/-- Comments separate tokens; quoted/escaped syntax is outside this slice. -/
def clean (source : String) : Except String String := do
  if source.length > 65536 then throw "CSS exceeds 65536 characters"
  let chars := source.toList.toArray
  let mut i := 0
  let mut comment := false
  let mut out : Array Char := #[]
  for _ in [:chars.size] do
    if i < chars.size then
      let c := chars[i]!
      let next := chars[i+1]?.getD '\x00'
      if comment then
        if c == '*' && next == '/' then comment := false; i := i+2
        else i := i+1
      else if c == '/' && next == '*' then
        comment := true; out := out.push ' '; i := i+2
      else
        if c == '\\' || c == '\'' || c == '"' then throw "CSS strings/escapes unsupported"
        if c == '!' then throw "CSS !important/annotation unsupported"
        if c == '@' then throw "CSS at-rules unsupported"
        out := out.push c; i := i+1
  if comment then throw "unterminated CSS comment"
  pure (String.ofList out.toList)

private def declarationsClean (properties : List String) (source : String) : Except String (List Declaration) := do
  let parts := source.splitOn ";"
  if parts.length > 1025 then throw "CSS declaration count exceeds 1024"
  let mut result : Array Declaration := #[]
  for part in parts do
    if !(trim part).isEmpty then
      let [key,value] := part.splitOn ":" | throw "CSS declaration requires one colon"
      let key := (trim key).toLower
      let value := trim value
      if !ident key || !properties.contains key then throw ("unsupported CSS property: "++key)
      if value.isEmpty || value.contains '{' || value.contains '}' then throw "invalid CSS value"
      result := result.push {property:=key,value}
  pure result.toList

def parseDeclarations (properties : List String) (source : String) : Except String (List Declaration) := do
  declarationsClean properties (← clean source)

/-- One compound selector of this slice (Selectors 4 §3.1): an optional type selector or
    `*`, then any number of `#id` and `.class` selectors, with no combinator, attribute,
    pseudo-class or namespace. -/
structure Compound where
  tag : Option String := none
  ids : List String := []
  classes : List String := []
  deriving Repr, BEq, Inhabited

/-- The pieces of a compound: the head before the first `#` or `.`, then each `#` or `.`
    with the name after it. -/
private def compoundPieces (cs : List Char) : List Char × List (Char × List Char) :=
  let isMark := fun c => c == '#' || c == '.'
  let head := cs.takeWhile (!isMark ·)
  let rec go : Nat → List Char → List (Char × List Char)
    | 0, _ => []
    | _, [] => []
    | fuel + 1, m :: rest =>
      let name := rest.takeWhile (!isMark ·)
      (m, name) :: go fuel (rest.drop name.length)
  (head, go (cs.length + 1) (cs.drop head.length))

/-- A selector text as a compound, or `none` when it is outside this slice. -/
def compound? (selector : String) : Option Compound :=
  let (head, parts) := compoundPieces selector.toList
  let head := String.ofList head
  let tag := if head.isEmpty || head == "*" then some none else if ident head then some (some head) else none
  match tag with
  | none => none
  | some tag =>
    if selector.isEmpty || !parts.all (fun (_, n) => ident (String.ofList n)) then none
    else some { tag, ids := parts.filterMap (fun (m, n) => if m == '#' then some (String.ofList n) else none),
                classes := parts.filterMap (fun (m, n) => if m == '.' then some (String.ofList n) else none) }

/-- Selectors 4 §17: (ids, classes, types) of a compound. -/
def Compound.specificity (c : Compound) : Nat × Nat × Nat := (c.ids.length, c.classes.length, if c.tag.isSome then 1 else 0)

/-- Specificities compared in order: ids, then classes, then types (Selectors 4 §17). -/
def specLT (a b : Nat × Nat × Nat) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 < b.2.2)))

/-- What a selector of this slice can see of an element: its local name (case-sensitive for
    SVG), its `id` and the words of its `class`. -/
structure Subject where
  tag : String
  id : Option String := none
  classes : List String := []

/-- Whether the compound matches the element. -/
def Compound.matches (c : Compound) (e : Subject) : Bool :=
  c.tag.all (· == e.tag) && c.ids.all (some · == e.id) && c.classes.all e.classes.contains

/-- `*` (or an empty compound) matches every element. -/
theorem universal_matches (e : Subject) : ({} : Compound).matches e = true := by
  simp [Compound.matches]

/-- An `#id` selector matches only the element with that `id`. -/
theorem id_matches_only (n : String) (e : Subject) (h : ({ ids := [n] } : Compound).matches e = true) :
    e.id = some n := by
  simp [Compound.matches] at h
  exact h.symm

/-- A `.class` selector matches only an element that has the class. -/
theorem class_matches_only (n : String) (e : Subject) (h : ({ classes := [n] } : Compound).matches e = true) :
    n ∈ e.classes := by
  simpa [Compound.matches] using h

/-- The specificity of the most specific selector of the list that matches, or `none`. -/
def matchSpecificity (selectors : List String) (e : Subject) : Option (Nat × Nat × Nat) :=
  selectors.foldl (fun best s =>
    match compound? s with
    | some c => if c.matches e then
        let sp := c.specificity
        match best with
        | some b => if specLT b sp then some sp else some b
        | none => some sp
      else best
    | none => best) none

/-- Compound selector lists (type, `*`, `#id`, `.class`); source order is retained. SVG
    type matching is case-sensitive. No namespace prefix, combinator, attribute selector or
    pseudo-class: a sheet with one is refused. -/
def parseSheet (properties : List String) (source : String) : Except String (List Rule) := do
  let source ← clean source
  let parts := source.splitOn "}"
  if parts.length > 257 then throw "CSS rule count exceeds 256"
  if !(trim (parts.getLast!)).isEmpty then throw "CSS rule missing closing brace"
  let mut rules : Array Rule := #[]
  for part in parts.dropLast do
    let [selector,body] := part.splitOn "{" | throw "CSS rule requires one opening brace"
    let selectors := (selector.splitOn ",").map trim
    if selectors.isEmpty || !selectors.all (fun s => (compound? s).isSome) then throw "unsupported CSS selector"
    rules := rules.push {selectors,declarations:= ← declarationsClean properties body}
  pure rules.toList

/-- Caller validates the full property value grammar on rules that match this element, before
    choosing a winner. This strict profile refuses malformed/unsupported declarations, including
    overridden declarations of matching rules; unmatched selectors do not affect this element.
    Returned declarations are unique by property. Higher priority replaces lower:
    presentation attributes, matched author rules by specificity (CSS Cascade 5 §6.4) and
    then source order, inline style. `classes` and `id` are the element's, for `.class`
    and `#id` selectors. -/
def cascade (validate : Declaration → Except String Unit) (tag : String)
    (presentation : List Declaration) (rules : List Rule) (inlineStyle : List Declaration)
    (classes : List String := []) (id : Option String := none) : Except String (List Declaration) := do
  let subject : Subject := {tag, id, classes}
  let matched := rules.filterMap fun r => (matchSpecificity r.selectors subject).map (·, r)
  for d in presentation ++ matched.flatMap (·.2.declarations) ++ inlineStyle do validate d
  -- each matched rule with the specificity of its most specific matching selector; a
  -- stable sort keeps source order among equals
  let applicable := (matched.mergeSort (fun a b => !specLT b.1 a.1)).map (·.2)
  let all := presentation ++ applicable.flatMap (·.declarations) ++ inlineStyle
  let mut result : List Declaration := []
  for d in all do result := d :: result.filter (fun old => old.property != d.property)
  pure result.reverse
end NativeSVGCSS
