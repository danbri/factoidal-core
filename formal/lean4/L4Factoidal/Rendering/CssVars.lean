/-
L4Factoidal.Rendering.CssVars — custom properties and `var()` for the cascade (CSS Custom
Properties for Cascading Variables 1).

The custom properties of an element are a map from name to value, inherited from the
parent, with the element's own declarations over it (`resolve`). The value kept is the
computed value: the declared text with its own `var()` references replaced (§2.2), so a
reference never needs a second look. A declaration of another property that mentions
`var()` has the references replaced when the element's style is computed (`substitute`,
§3): a variable with no value takes the fallback; with none, the declaration is invalid at
computed-value time and the property is as if not declared. Custom properties that refer
to each other in a cycle are invalid (§2.3).

Text in, text out: the value is not tokenised into numbers, so what a sheet wrote reaches
the property's own parser as written. A declaration that does not mention `var(` is never
looked at (`value_plain`): a page that uses no variables pays one test per declaration
that has a `(`.
-/
import L4Factoidal.Rendering.SupportsCondition
import Std.Data.TreeMap

namespace L4Factoidal.Rendering.CssVars

private def trim (s : String) : String := s.trimAscii.toString

/-- The value mentions `var(` (in any case). -/
def mentions (value : String) : Bool :=
  value.contains '(' && ((value.splitOn "var(").length > 1 || (value.toLower.splitOn "var(").length > 1)

/-- What a variable name stands for when a value is read: a value; nothing (not declared,
or invalid); or `pending`, a custom property of the same element that is not resolved yet. -/
inductive Found where
  | value (v : String)
  | missing
  | pending
  deriving Repr, BEq, DecidableEq, Inhabited

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '\\' || c.toNat ≥ 0x80

/-- The arguments of a `var()` split at the first comma outside strings and brackets: the
name, and the fallback when there is one. -/
def splitArgs (args : List Char) : List Char × Option (List Char) := Id.run do
  let mut name : List Char := []
  let mut rest := args
  let mut depth := 0
  let mut quote : Option Char := none
  for _ in [0:args.length] do
    match rest with
    | [] => break
    | c :: r =>
      rest := r
      match quote with
      | some q => if c == q then quote := none
      | none =>
        if c == '"' || c == '\'' then quote := some c
        else if c == '(' || c == '[' || c == '{' then depth := depth + 1
        else if c == ')' || c == ']' || c == '}' then depth := depth - 1
        else if c == ',' && depth == 0 then return (name.reverse, some r)
      name := c :: name
  return (name.reverse, none)

/-- `value` with each `var(--name, fallback)` replaced (CSS Variables 1 §3): by what `get`
finds for the name, else by the fallback, itself substituted. `missing`: a reference has
neither, or its name is not a custom property name; the declaration is then invalid at
computed-value time. `pending`: a reference is to a property not resolved yet. `fuel`
bounds the nesting of fallbacks. A `var(` that never closes ends with the value, as CSS
Syntax closes an open function. -/
def substitute (get : String → Found) : Nat → String → Found
  | 0, _ => .missing
  | fuel + 1, value => Id.run do
    let mut out := ""
    let mut rest := value.toList
    let mut quote : Option Char := none
    let mut afterName := false
    for _ in [0:value.length + 1] do
      match rest with
      | [] => break
      | c :: r =>
        match quote with
        | some q =>
          out := out.push c
          rest := r
          if c == q then quote := none
        | none =>
          if c == '"' || c == '\'' then
            quote := some c
            out := out.push c
            rest := r
            afterName := false
          else if !afterName && (c == 'v' || c == 'V') && (String.ofList (r.take 3)).toLower == "ar(" then
            let after := r.drop 3
            let (args, rest') := (CssSupports.inParens after).getD (after, [])
            let (name, fallback) := splitArgs args
            let name := trim (String.ofList name)
            let found := if name.startsWith "--" && name.length > 2 then get name else .missing
            match found with
            | .value v => out := out ++ v
            | .pending => return .pending
            | .missing =>
              match fallback with
              | none => return .missing
              | some fb =>
                match substitute get fuel (String.ofList fb) with
                | .value v => out := out ++ trim v
                | other => return other
            rest := rest'
            afterName := false
          else
            out := out.push c
            rest := r
            afterName := isNameChar c
    return .value out

/-- The most nested fallbacks that are followed. -/
def maxFallbacks : Nat := 32

/-- The value of a declaration with its `var()` references replaced. A value that does not
mention `var(` is itself. -/
def value (get : String → Found) (text : String) : Found :=
  if mentions text then substitute get maxFallbacks text else .value text

/-- A declaration that does not mention `var(` is not changed, whatever the variables. -/
theorem value_plain (get : String → Found) (text : String) (h : mentions text = false) :
    value get text = .value text := by
  simp [value, h]

/-- The custom properties of an element: name to computed value. -/
abbrev Vars := Std.TreeMap String String

def Vars.find (vars : Vars) (name : String) : Found :=
  match vars.get? name with
  | some v => .value v
  | none => .missing

/-- The value of a declaration against the custom properties of its element; `none` when
it is invalid at computed-value time. -/
def Vars.apply (vars : Vars) (text : String) : Option String :=
  match value vars.find text with
  | .value v => some v
  | _ => none

theorem Vars.apply_plain (vars : Vars) (text : String) (h : mentions text = false) :
    vars.apply text = some text := by
  simp [Vars.apply, value_plain _ _ h]

/-- The custom properties of an element (CSS Variables 1 §2): the inherited ones, with the
element's winning declarations `own` (name and declared value) over them. `inherit` and
`unset` keep the inherited value; `initial` and a declaration that is invalid at
computed-value time leave the property with no value. A declaration that refers to other
custom properties of the element is resolved after them; those in a cycle have no value
(§2.3). At most `own.length` passes over the declarations not yet resolved. -/
def resolve (inherited : Vars) (own : List (String × String)) : Vars := Id.run do
  let mut vars := inherited
  let mut pending : List (String × String) := []
  -- declarations with no reference are their own value
  for (name, text) in own do
    let low := text.toLower
    if low == "inherit" || low == "unset" then pure ()
    else if low == "initial" then vars := vars.erase name
    else if mentions text then pending := (name, text) :: pending
    else vars := vars.insert name text
  pending := pending.reverse
  for _ in [0:own.length] do
    if pending.isEmpty then break
    let names := pending.map (·.1)
    let mut still : List (String × String) := []
    let mut progress := false
    for (name, text) in pending do
      match value (fun n => if names.contains n then .pending else vars.find n) text with
      | .value v =>
        vars := vars.insert name v
        progress := true
      | .missing =>
        vars := vars.erase name
        progress := true
      | .pending => still := (name, text) :: still
    pending := still.reverse
    if !progress then break
  -- what is left refers to itself through a cycle
  for (name, _) in pending do vars := vars.erase name
  return vars

/-- An element that declares no custom property has its parent's. -/
theorem resolve_nil (inherited : Vars) : resolve inherited [] = inherited := by
  simp [resolve, Id.run]
  rfl

private def vars (l : List (String × String)) : Vars := l.foldl (fun m (k, v) => m.insert k v) {}
private def sub (l : List (String × String)) (text : String) : Option String := (vars l).apply text
private def res (inherited own : List (String × String)) : List (String × String) :=
  (resolve (vars inherited) own).toList

#guard mentions "var(--x)" && mentions "calc(VAR(--x) + 1px)" && !mentions "red" && !mentions "rgb(1, 2, 3)"
#guard sub [("--x", "red")] "var(--x)" == some "red"
#guard sub [("--x", "red")] "1px solid var(--x)" == some "1px solid red"
#guard sub [] "var(--x)" == none
#guard sub [] "var(--x, blue)" == some "blue"
#guard sub [] "var(--x,)" == some ""
#guard sub [("--y", "2px")] "var(--x, var(--y, 3px))" == some "2px"
#guard sub [] "var(--x, var(--y, 3px))" == some "3px"
#guard sub [] "var(--x, var(--y))" == none
#guard sub [("--x", "1px")] "calc(var(--x) * 2)" == some "calc(1px * 2)"
#guard sub [("--x", "a, b")] "f(var(--x), var(--z, c, d))" == some "f(a, b, c, d)"
#guard sub [("--x", "red")] "var( --x )" == some "red"
#guard sub [("--x", "red")] "var(x)" == none
#guard sub [("--x", "red")] "\"var(--x)\" var(--x)" == some "\"var(--x)\" red"
-- `--myvar(` is not a reference; an open reference closes with the value
#guard sub [("--x", "red")] "url(--myvar(--x))" == some "url(--myvar(--x))"
#guard sub [("--x", "red")] "var(--x" == some "red"
#guard sub [("--X", "red")] "var(--x, green)" == some "green"
-- resolution: own over inherited, references in any order, cycles, keywords
#guard res [("--a", "1")] [("--b", "2")] == [("--a", "1"), ("--b", "2")]
#guard res [("--a", "1")] [("--a", "3")] == [("--a", "3")]
#guard res [] [("--a", "var(--b)"), ("--b", "var(--c)"), ("--c", "5px")] == [("--a", "5px"), ("--b", "5px"), ("--c", "5px")]
#guard res [("--a", "1")] [("--a", "var(--a) 2")] == []
#guard res [] [("--a", "var(--b)"), ("--b", "var(--a)"), ("--c", "1")] == [("--c", "1")]
#guard res [] [("--a", "var(--b, 7px)"), ("--b", "var(--a)")] == []
#guard res [("--a", "1"), ("--b", "2")] [("--a", "initial"), ("--b", "inherit")] == [("--b", "2")]
#guard res [("--a", "1")] [("--b", "var(--a) var(--zz, x)")] == [("--a", "1"), ("--b", "1 x")]
#guard res [("--a", "1")] [("--b", "var(--zz)")] == [("--a", "1")]

end L4Factoidal.Rendering.CssVars
