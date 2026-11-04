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

/-- Type selector lists only; source order is retained. SVG type matching is
    case-sensitive. No namespace prefix, universal selector or combinator. -/
def parseSheet (properties : List String) (source : String) : Except String (List Rule) := do
  let source ← clean source
  let parts := source.splitOn "}"
  if parts.length > 257 then throw "CSS rule count exceeds 256"
  if !(trim (parts.getLast!)).isEmpty then throw "CSS rule missing closing brace"
  let mut rules : Array Rule := #[]
  for part in parts.dropLast do
    let [selector,body] := part.splitOn "{" | throw "CSS rule requires one opening brace"
    let selectors := (selector.splitOn ",").map trim
    if selectors.isEmpty || !selectors.all ident then throw "unsupported CSS selector"
    rules := rules.push {selectors,declarations:= ← declarationsClean properties body}
  pure rules.toList

/-- Caller validates the full property value grammar BEFORE cascade selection.
    This strict profile refuses malformed/unsupported declarations, including
    overridden declarations; it does not emulate CSS's ignore-invalid behavior.
    Returned declarations are unique by property. Higher priority replaces lower:
    presentation attributes, matched author rules in source order, inline style.
    All admitted selectors have the same type-selector specificity. -/
def cascade (validate : Declaration → Except String Unit) (tag : String)
    (presentation : List Declaration) (rules : List Rule) (inlineStyle : List Declaration) : Except String (List Declaration) := do
  for d in presentation ++ rules.flatMap (·.declarations) ++ inlineStyle do validate d
  let applicable := rules.filter (fun r => r.selectors.contains tag)
  let all := presentation ++ applicable.flatMap (·.declarations) ++ inlineStyle
  let mut result : List Declaration := []
  for d in all do result := d :: result.filter (fun old => old.property != d.property)
  pure result.reverse
end NativeSVGCSS
