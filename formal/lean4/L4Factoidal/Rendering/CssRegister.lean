/-
L4Factoidal.Rendering.CssRegister — CSS Properties and Values API 1: the checks of
`CSS.registerProperty` (§5.1): the property name, the syntax string (§5.4 "consume a
syntax definition") and the initial value, which must be a value of the syntax and
computationally independent (§2.1).

A syntax string is read into a grammar of `CssValues.Grammar`, so a registered property's
values are matched by the matcher that matches every other property.

Not here: the registration's effect on the cascade and on computed values (a registered
property's initial value, its typed computed value, `inherits`). The page keeps the names
it registered so that a second registration is refused.
-/
import L4Factoidal.Rendering.CssValues.Properties

namespace L4Factoidal.Rendering.CssRegister
open L4Factoidal.Rendering.CssValues

/-- The data types a syntax component may name (§5.4.1), and whether a multiplier may
follow. -/
def dataTypes : List (String × Bool) :=
  [("length", true), ("number", true), ("percentage", true), ("length-percentage", true), ("color", true),
   ("image", true), ("url", true), ("integer", true), ("angle", true), ("time", true), ("resolution", true),
   ("transform-function", true), ("custom-ident", true), ("string", true), ("transform-list", false)]

/-- One component of a syntax string from its tokens (no white space inside): a data type
name or a custom identifier, with an optional `+` or `#`. -/
def componentGrammar (ts : List Tok) : Option G :=
  let withMultiplier := fun (g : G) (allowed : Bool) (rest : List Tok) =>
    match rest with
    | [] => some g
    | [.delim '+'] => if allowed then some (G.rep g 1 none false) else none
    | [.delim '#'] => if allowed then some (G.rep g 1 none true) else none
    | _ => none
  match ts with
  | .delim '<' :: .ident name :: .delim '>' :: rest =>
    match dataTypes.lookup name with
    | some allowed => withMultiplier (.ref name none none) allowed rest
    | none => none
  | .ident name :: rest =>
    -- a custom identifier stands for itself, case-sensitively; a CSS-wide keyword is not one
    if cssWide.contains (lower name) || lower name == "default" then none
    else withMultiplier (.ref ("ident=" ++ name) none none) true rest
  | _ => none

/-- Split a token list at the `|` delimiters. -/
def splitBars (ts : List Tok) : List (List Tok) :=
  let (groups, last) := ts.foldl (fun (acc : List (List Tok) × List Tok) t =>
    if t == .delim '|' then (acc.2.reverse :: acc.1, []) else (acc.1, t :: acc.2)) ([], [])
  (last.reverse :: groups).reverse

def trimToks (ts : List Tok) : List Tok :=
  ((ts.dropWhile (· == .ws)).reverse.dropWhile (· == .ws)).reverse

/-- The grammar of a syntax string: `none` when the string is not a syntax definition,
`some none` for the universal syntax `*`, else the grammar. -/
def syntaxGrammar (syn : String) : Option (Option G) :=
  let ts := trimToks (tokenize syn)
  if ts == [.delim '*'] then some none
  else
    match (splitBars ts).mapM fun part => componentGrammar (trimToks part) with
    | some [] => none
    | some gs => some (some (.oneOf gs))
    | none => none

def fontRelativeUnits : List String :=
  ["em", "rem", "ex", "rex", "cap", "rcap", "ch", "rch", "ic", "ric", "lh", "rlh"]

/-- Whether the values hold a length in a unit that depends on the element's font: such a
value is not computationally independent. -/
def hasFontRelative : Nat → List CV → Bool
  | 0, _ => true
  | fuel + 1, cvs => cvs.any fun cv => match cv with
    | .tok (.dim _ _ u) => fontRelativeUnits.contains (lower u)
    | .fn _ args => hasFontRelative fuel args
    | .block _ body => hasFontRelative fuel body
    | _ => false

/-- Whether `initial` can be the initial value of a property registered with `syntax`. -/
def initialValid (syn : Option G) (initial : String) : Bool :=
  let cvs := CV.parse initial
  let top := stripWs cvs
  let bad := if syn.isNone then badCustomValue top else hasBadToken 32 true top
  if bad || hasFn "var" 32 cvs || hasFn "env" 32 cvs then false
  else if (wideKeyword top).isSome then false
  else
    match syn with
    | none => true
    | some g =>
      !top.isEmpty && !hasFontRelative (maxNesting + 2) top && (matchAll (env none) g top).isSome

/-- The check of `CSS.registerProperty` (§5.1, the steps that can fail): "" when the
registration is accepted, else the name of the DOMException. `initial` is `none` when the
definition has no `initialValue`. -/
def registerCheck (name syn : String) (initial : Option String) : String :=
  if !isCustom name || (tokenize name) != [.ident name] then "SyntaxError"
  else
    match syntaxGrammar syn with
    | none => "SyntaxError"
    | some none =>
      -- the universal syntax: the initial value is optional
      match initial with
      | some v => if initialValid none v then "" else "SyntaxError"
      | none => ""
    | some (some g) =>
      match initial with
      | some v => if initialValid (some g) v then "" else "SyntaxError"
      | none => "SyntaxError"

/-- The page's protocol: `name` U+0000 `syntax` U+0000 "1" and the initial value, or "0". -/
def registerOp (q : String) : String :=
  match q.splitOn "\x00" with
  | [name, syn, initial] =>
    registerCheck name syn (if initial.startsWith "1" then some (initial.drop 1).toString else none)
  | _ => "SyntaxError"

/-! ### Tests (from css-properties-values-api/register-property-syntax-parsing.html) -/

private def ok (syn initial : String) : Bool := registerCheck "--p" syn (some initial) == ""

#guard ok "*" "a"
#guard ok " * " "b"
#guard ok "<length>" "2px"
#guard ok " <number>" "5"
#guard ok "<color>+" "red"
#guard ok " <length>+ | <percentage>" "2px 8px"
#guard ok " <length>+ | <color>#" "red, blue"
#guard ok "<length>|<percentage>|<length-percentage>" "2px"
#guard ok "\t<color>\n|   foo" "foo"
#guard ok "*" "([ brackets ]) { yay (??)}"
#guard ok "*" "unmatched opening bracket is valid :("
#guard ok "<length>" "0"
#guard ok "<length>" "10px /*:)*/"
#guard ok "<length>" "calc(2px*4 + 10px)"
#guard ok "<length>#" "2px, 7px, calc(8px)"
#guard ok "<length>" "10vmin"
#guard ok "<integer>" "calc(3.1415)"
#guard ok "<angle>" "calc(50grad + 3.14159rad)"
#guard ok "<resolution>" "3dPpX"
#guard ok "<transform-function>+" "translateX(2px) rotate(42deg)"
#guard ok "<transform-list>" "translateX(2px) rotate(20deg)"
#guard ok "<string>" "'foo bar"
#guard ok "<image>" "linear-gradient(yellow, blue)"
#guard ok "<url>" "url(a)"
#guard ok "yellow" "yellow"
#guard ok "bAnAnA" "bAnAnA"
#guard ok "banana" "banan\\61"
#guard ok "--foo | <color>" "--foo"
#guard ok "foo+|bar" "foo foo foo"
#guard !ok "banana,nya" "banana"
#guard !ok "<banana>" "banana"
#guard !ok "<length" "10px"
#guard !ok "< length>" "10px"
#guard !ok "<length> +" "10px"
#guard !ok "<transform-list>#" "scale(2)"
#guard !ok "<length>##" "10px"
#guard !ok "<length>+" "2px,7px,calc(8px)"
#guard !ok "*|banana" "banana"
#guard !ok " |" "banana"
#guard !ok "foo bar" "foo bar"
#guard !ok "<length> <number>" "0px 0"
#guard !ok "initial" "initial"
#guard !ok "<integer>|deFAUlt" "1"
#guard !ok "*" "inherit"
#guard !ok "<custom-ident>" "default"
#guard !ok "*" "([)]"
#guard !ok "*" "semi;colon"
#guard !ok "*" "var(--foo)"
#guard !ok "<length>" "10%"
#guard !ok "<length>" "10em"
#guard !ok "<length>" "calc(4px + calc(8 * 2em))"
#guard !ok "<length>#" ""
#guard !ok "<integer>" "1.0"
#guard !ok "bAnAnA" "banana"
#guard registerCheck "p" "*" none == "SyntaxError"
#guard registerCheck "--p" "*" none == ""
#guard registerCheck "--p" "<length>" none == "SyntaxError"

/-- Kind: policy. Says: a name that is not a custom property name is refused, whatever the
syntax and the initial value. Does not say: that a custom property name is accepted (the
syntax and the initial value are checked next). -/
theorem registerCheck_name (name syn : String) (initial : Option String) (h : isCustom name = false) :
    registerCheck name syn initial = "SyntaxError" := by
  unfold registerCheck
  simp [h]

end L4Factoidal.Rendering.CssRegister
