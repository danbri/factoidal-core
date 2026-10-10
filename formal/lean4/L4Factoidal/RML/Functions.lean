/-
L4Factoidal.RML.Functions — the functions a mapping can call, keyed by the
IRI of their Function Ontology (FnO) description.

Spec: RML-FNML (https://w3id.org/rml/fnml/spec), "Link to FnO: Overview"
and "Definitions"; the Function Ontology (https://w3id.org/function/spec/)
for `fno:Function`, `fno:expects`, `fno:returns`, `fno:required`.

## Description and implementation are two things

FnO describes a function without implementing it: its IRI, an ordered
list of parameters (each with a `fno:required` flag) and an ordered list
of returns. An RML-FNML processor owns the implementation. This module
holds both, side by side, in one record (`FnImpl`): the description is
data, and `run` is the implementation. The data is what `RML.Validate`
checks a mapping against (a function, a parameter or a return that the
description does not have is a mapping error), and what the test runner
compares with the FnO file of the test suite (`FnImpl.agreesWith`).

## What `run` sees

`run` takes the values bound to the parameters, by parameter IRI, and
returns one value per return, in the order of `returns`; `none` is the
NULL value, from which a term map generates no term. It runs only when
every REQUIRED parameter has a value: with a required value missing, the
execution is not performed and every return is NULL. An error (a value of
the wrong type for its parameter, an escape mode the function does not
have) rejects the run.

## The functions

* GREL (`http://users.ugent.be/~bjdmeest/function/grel.ttl#`), the
  functions of the test suite's `functions.ttl`: `toUpperCase`,
  `string_length`, `string_substring`, `string_replace`, `escape`; and
  `toLowerCase`.
* `http://example.com/functions/` (`functions.ttl`): `helloworld`, `schema`,
  `parseURL`.
* IDLab (`https://w3id.org/imec/idlab/function#`): `alwaysReturnsABC`,
  `toUpperCaseURL`, and the condition functions `equal`, `notEqual` and
  `trueCondition`.
-/
import L4Factoidal.RML.FromGraph
import L4Factoidal.RML.Value
import L4Factoidal.Fn.String

namespace L4Factoidal.RML

open L4Factoidal.RDF

def grelNs : String := "http://users.ugent.be/~bjdmeest/function/grel.ttl#"
def idlabNs : String := "https://w3id.org/imec/idlab/function#"
def fnsNs : String := "http://example.com/functions/"
def fnoNs : String := "https://w3id.org/function/ontology#"

/-- A parameter of a function and its `fno:required` flag. -/
structure FnParam where
  iri      : String
  required : Bool
deriving Repr, DecidableEq

/-- A function: its FnO description (`iri`, `params`, `returns`) and its
    implementation (`run`). -/
structure FnImpl where
  iri     : String
  params  : List FnParam
  /-- The IRIs of the returns, in the order of `fno:returns`. -/
  returns : List String
  run     : (String → Option RVal) → Except String (List (Option RVal))

/-! ## Values -/

private def str (s : String) : RVal := { lexical := s }
private def int (n : Nat) : RVal := { lexical := toString n, natural := some (xsdNs ++ "integer") }
private def bool (b : Bool) : RVal :=
  { lexical := if b then "true" else "false", natural := some (xsdNs ++ "boolean") }

/-- The lexical form of a parameter value. -/
private def lexOf (arg : String → Option RVal) (p : String) : Option String := (arg p).map (·.lexical)

/-! ## String operations

Case mapping is `String.toUpper` / `String.toLower` of Lean core through
the shared function library (`Fn.String`); they map the ASCII letters. -/

/-- Replace every occurrence of a non-empty `find` by `repl`; an empty
    `find` leaves the string as it is. -/
def replaceAll (s find repl : String) : String :=
  if find.isEmpty then s else s.replace find repl

/-- GREL `substring(s, from)`: the characters from index `from` on. A
    negative index counts from the end; an index beyond the length gives
    NULL, and an index equal to the length gives the empty string. -/
def grelSubstring (s : String) (from' : Int) : Option String :=
  let cs := s.toList
  let n : Int := cs.length
  let start : Int := if from' < 0 then max 0 (from' + n) else from'
  if start > n then none else some (String.ofList (cs.drop start.toNat))

/-- The five characters XML and HTML always escape. -/
private def escapeMarkup (apos : Bool) (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '&' then "&amp;"
    else if c == '<' then "&lt;"
    else if c == '>' then "&gt;"
    else if c == '"' then "&quot;"
    else if apos && c == '\'' then "&apos;"
    else String.singleton c))

/-- `java.net.URLEncoder.encode(s, "UTF-8")`: ASCII letters and digits and
    `.`, `-`, `*`, `_` stay, a space is `+`, anything else is the
    percent-escaped UTF-8 bytes. -/
private def escapeUrl (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == ' ' then "+"
    else Fn.String.pctEncodeWith (fun d =>
      (d.toNat < 128 && d.isAlphanum) || d == '.' || d == '-' || d == '*' || d == '_')
      (String.singleton c)))

/-- A comma, a double quote, a carriage return or a line feed makes the
    field quoted, with its quotes doubled. -/
private def escapeCsv (s : String) : String :=
  if s.toList.any (fun c => c == ',' || c == '"' || c == '\r' || c == '\n')
  then "\"" ++ replaceAll s "\"" "\"\"" ++ "\""
  else s

private def hex4 (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  "\\u" ++ String.ofList (List.replicate (4 - d.length) '0') ++ d.toUpper

/-- ECMAScript string escaping: the quotes, the backslash and the slash,
    the control characters with their short forms, and every other
    character outside printable ASCII as `\uXXXX` (a surrogate pair above
    U+FFFF). -/
private def escapeJs (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '\'' then "\\'"
    else if c == '"' then "\\\""
    else if c == '\\' then "\\\\"
    else if c == '/' then "\\/"
    else if c == '\n' then "\\n"
    else if c == '\r' then "\\r"
    else if c == '\t' then "\\t"
    else if c.toNat == 8 then "\\b"
    else if c.toNat == 12 then "\\f"
    else if c.toNat < 32 || c.toNat > 126 then
      let n := c.toNat
      if n < 0x10000 then hex4 n
      else
        let m := n - 0x10000
        hex4 (0xD800 + m / 1024) ++ hex4 (0xDC00 + m % 1024)
    else String.singleton c))

/-- GREL `escape(s, mode)`. -/
def grelEscape (s mode : String) : Option String :=
  if mode == "html" then some (escapeMarkup false s)
  else if mode == "xml" then some (escapeMarkup true s)
  else if mode == "csv" then some (escapeCsv s)
  else if mode == "url" then some (escapeUrl s)
  else if mode == "javascript" then some (escapeJs s)
  else none

/-- IDLab `toUpperCaseURL`: the string in upper case, with `HTTP://` in
    front when it does not start with it. -/
def toUpperCaseUrl (s : String) : String :=
  let up := Fn.String.upperCase s
  if up.startsWith "HTTP://" then up else "HTTP://" ++ up

/-- `parseURL`: protocol, domain and path of `protocol://domain/path`. A
    string of another shape has none of them. -/
def parseUrl (s : String) : Option (String × String × String) :=
  match Fn.String.indexOfSub s "://" with
  | none => none
  | some i =>
      let cs := s.toList
      let protocol := String.ofList (cs.take i)
      let rest := cs.drop (i + 3)
      let domain := String.ofList (rest.takeWhile (· != '/'))
      let path := String.ofList ((rest.dropWhile (· != '/')).drop 1)
      some (protocol, domain, path)

/-! ## The registry -/

private def p (ns local' : String) (required : Bool) : FnParam := ⟨ns ++ local', required⟩

private def valueParam : FnParam := p grelNs "valueParam" true

/-- One string in, one string out. -/
private def stringFn (iri : String) (f : String → Option String) : FnImpl :=
  { iri := iri
    params := [valueParam]
    returns := [grelNs ++ "stringOut"]
    run := fun arg => .ok [(lexOf arg valueParam.iri >>= f).map str] }

def registry : List FnImpl :=
  [ stringFn (grelNs ++ "toUpperCase") (fun s => some (Fn.String.upperCase s))
  , stringFn (grelNs ++ "toLowerCase") (fun s => some (Fn.String.lowerCase s))
  , { iri := grelNs ++ "string_length"
      params := [valueParam]
      returns := [grelNs ++ "output_number"]
      run := fun arg => .ok [(lexOf arg valueParam.iri).map (fun s => int s.toList.length)] }
  , { iri := grelNs ++ "string_substring"
      params := [valueParam, p grelNs "p_int_i_from" true]
      returns := [grelNs ++ "stringOut"]
      run := fun arg =>
        match lexOf arg valueParam.iri, lexOf arg (grelNs ++ "p_int_i_from") with
        | some s, some i =>
            match i.trim.toInt? with
            | some n => .ok [(grelSubstring s n).map str]
            | none => .error s!"'{i}' is not an integer, so it cannot be the start of a substring"
        | _, _ => .ok [none] }
  , { iri := grelNs ++ "string_replace"
      params := [valueParam, p grelNs "param_find" true, p grelNs "param_replace" true]
      returns := [grelNs ++ "stringOut"]
      run := fun arg =>
        match lexOf arg valueParam.iri, lexOf arg (grelNs ++ "param_find"),
              lexOf arg (grelNs ++ "param_replace") with
        | some s, some f, some r => .ok [some (str (replaceAll s f r))]
        | _, _, _ => .ok [none] }
  , { iri := grelNs ++ "escape"
      params := [valueParam, p grelNs "modeParam" true]
      returns := [grelNs ++ "stringOut"]
      run := fun arg =>
        match lexOf arg valueParam.iri, lexOf arg (grelNs ++ "modeParam") with
        | some s, some m =>
            match grelEscape s m with
            | some r => .ok [some (str r)]
            | none => .error s!"'{m}' is not an escape mode (html, xml, csv, url, javascript)"
        | _, _ => .ok [none] }
  , { iri := fnsNs ++ "helloworld"
      params := []
      returns := [fnsNs ++ "stringOutput"]
      run := fun _ => .ok [some (str "Hello World!")] }
  , { iri := fnsNs ++ "schema"
      params := [p fnsNs "stringParameter" false]
      returns := [fnsNs ++ "stringOutput"]
      run := fun arg =>
        .ok [(lexOf arg (fnsNs ++ "stringParameter")).map (fun s => str ("https://schema.org/" ++ s))] }
  , { iri := fnsNs ++ "parseURL"
      params := [p fnsNs "stringParameter" false]
      returns := [fnsNs ++ "protocolOutput", fnsNs ++ "domainOutput", fnsNs ++ "stringOutput"]
      run := fun arg =>
        match (lexOf arg (fnsNs ++ "stringParameter")).bind parseUrl with
        | some (a, b, c) => .ok [some (str a), some (str b), some (str c)]
        | none => .ok [none, none, none] }
  , { iri := idlabNs ++ "alwaysReturnsABC"
      params := []
      returns := [idlabNs ++ "_stringOut"]
      run := fun _ => .ok [some (str "ABC")] }
  , { iri := idlabNs ++ "toUpperCaseURL"
      params := [p idlabNs "str" true]
      returns := [idlabNs ++ "_stringOut"]
      run := fun arg => .ok [(lexOf arg (idlabNs ++ "str")).map (fun s => str (toUpperCaseUrl s))] }
  , { iri := idlabNs ++ "equal"
      params := [valueParam, p grelNs "valueParam2" true]
      returns := [idlabNs ++ "_boolOut"]
      run := fun arg =>
        match lexOf arg valueParam.iri, lexOf arg (grelNs ++ "valueParam2") with
        | some a, some b => .ok [some (bool (a == b))]
        | _, _ => .ok [none] }
  , { iri := idlabNs ++ "notEqual"
      params := [valueParam, p grelNs "valueParam2" true]
      returns := [idlabNs ++ "_boolOut"]
      run := fun arg =>
        match lexOf arg valueParam.iri, lexOf arg (grelNs ++ "valueParam2") with
        | some a, some b => .ok [some (bool (a != b))]
        | _, _ => .ok [none] }
  , { iri := idlabNs ++ "trueCondition"
      params := [p idlabNs "strBoolean" true, p idlabNs "str" true]
      returns := [idlabNs ++ "_stringOut"]
      run := fun arg =>
        match lexOf arg (idlabNs ++ "strBoolean"), lexOf arg (idlabNs ++ "str") with
        | some b, some s => .ok [if b == "true" then some (str s) else none]
        | _, _ => .ok [none] } ]

def lookupFn (iri : String) : Option FnImpl := registry.find? (fun f => f.iri == iri)

/-- Perform an execution: bind the arguments, run, and take the return
    named `ret` (the first return when it is `none`). The value is NULL
    when a required parameter has no argument. -/
def FnImpl.call (f : FnImpl) (args : List (String × RVal)) (ret : Option String)
    : Except String (Option RVal) :=
  let idx : Option Nat :=
    match ret with
    | none => some 0
    | some r => f.returns.findIdx? (· == r) |>.filter (· < f.returns.length)
  match idx with
  | none => .error s!"<{ret.getD ""}> is not a return of <{f.iri}>"
  | some k =>
      let arg := fun (q : String) => (args.find? (fun a => a.1 == q)).map (·.2)
      if f.params.any (fun q => q.required && (arg q.iri).isNone) then .ok none
      else
        match f.run arg with
        | .error m => .error m
        | .ok outs => .ok ((outs.getD k none))

/-! ## Comparing with an FnO description -/

/-- The FnO description of the function `iri` in a graph: its parameters
    with their `fno:required` flags, and its returns, in list order.
    `none` when the graph does not say the node is an `fno:Function`. -/
def fnoDescription (g : Graph) (iri : String) : Option (List FnParam × List String) :=
  if !(objectsOf g iri rdfTypeStr).any (fun t => match t with
        | .iri i => i.val == fnoNs ++ "Function" | _ => false)
  then none
  else
    let items := fun (prop : String) =>
      match (objectsOf g iri (fnoNs ++ prop)).head? with
      | some h => (listItems g h).filterMap nodeKey
      | none => []
    some ((items "expects").map (fun q =>
            ⟨q, (strOf g q (fnoNs ++ "required")) == some "true"⟩),
          items "returns")

/-- The functions an FnO graph describes, as `fno:Function` nodes. -/
def describedFunctions (g : Graph) : List String :=
  ((g.filter (fun t =>
      t.p.val == rdfTypeStr &&
      (match t.o with | .iri i => i.val == fnoNs ++ "Function" | _ => false))).map
    (fun t => subjKey t.s)).eraseDups

/-- Does the registry implement the function with the description the
    graph gives it? -/
def FnImpl.agreesWith (f : FnImpl) (g : Graph) : Bool :=
  fnoDescription g f.iri == some (f.params, f.returns)

/-! ## Build-time checks -/

/-- Run a function by IRI on string arguments: `none` is an error (or an
    unknown function), `some none` is the NULL value. -/
private def run1 (iri : String) (args : List (String × String)) (ret : Option String := none)
    : Option (Option String) :=
  match lookupFn iri with
  | none => none
  | some f =>
      match f.call (args.map (fun a => (a.1, str a.2))) ret with
      | .ok v => some (v.map (·.lexical))
      | .error _ => none

private def ok (v : Option String) : Option (Option String) := some v

private def gv : String := grelNs ++ "valueParam"
private def gstr : String := grelNs ++ "stringOut"

-- toUpperCase: an ASCII string, the empty string
#guard run1 (grelNs ++ "toUpperCase") [(gv, "Venus")] == ok (some "VENUS")
#guard run1 (grelNs ++ "toUpperCase") [(gv, "")] == ok (some "")
-- ...and with the required parameter missing: NULL, not an error
#guard run1 (grelNs ++ "toUpperCase") [] == ok none
-- a parameter the function does not have is not its value
#guard run1 (grelNs ++ "toUpperCase") [(grelNs ++ "other", "Venus")] == ok none
-- a return the function does not have is an error; the named one is fine
#guard run1 (grelNs ++ "toUpperCase") [(gv, "a")] (some (grelNs ++ "unknownOut")) == none
#guard run1 (grelNs ++ "toUpperCase") [(gv, "a")] (some gstr) == ok (some "A")
-- a function that is not in the registry
#guard (lookupFn (grelNs ++ "unknown_func")).isNone
-- the number of code points, with a datatype
#guard run1 (grelNs ++ "string_length") [(gv, "Venus")] == ok (some "5")
#guard run1 (grelNs ++ "string_length") [(gv, "Zoë")] == ok (some "3")
#guard ((lookupFn (grelNs ++ "string_length")).bind (fun f =>
         (f.call [(gv, str "ab")] none).toOption.bind id)).map (·.natural) ==
       some (some (xsdNs ++ "integer"))

-- substring: the middle, the whole, the end (empty), beyond the end (NULL), from the back
#guard grelSubstring "Venus" 2 == some "nus"
#guard grelSubstring "Venus" 0 == some "Venus"
#guard grelSubstring "Venus" 5 == some ""
#guard grelSubstring "Venus" 1000 == none
#guard grelSubstring "Venus" (-2) == some "us"
#guard grelSubstring "Venus" (-100) == some "Venus"
#guard run1 (grelNs ++ "string_substring") [(gv, "Venus"), (grelNs ++ "p_int_i_from", "5")] == ok (some "")
#guard run1 (grelNs ++ "string_substring") [(gv, "Venus"), (grelNs ++ "p_int_i_from", "1000")] == ok none
#guard run1 (grelNs ++ "string_substring") [(gv, "Venus"), (grelNs ++ "p_int_i_from", "x")] == none

-- replace: every occurrence; an empty needle changes nothing
#guard replaceAll "M Venus is M" " " "-" == "M-Venus-is-M"
#guard replaceAll "abc" "" "-" == "abc"
#guard replaceAll "abc" "x" "-" == "abc"

-- escape, one case per mode, and an unknown mode
#guard grelEscape "A&B" "html" == some "A&amp;B"
#guard grelEscape "<a href=\"x\">" "html" == some "&lt;a href=&quot;x&quot;&gt;"
#guard grelEscape "it's" "html" == some "it's"
#guard grelEscape "it's" "xml" == some "it&apos;s"
#guard grelEscape "plain" "csv" == some "plain"
#guard grelEscape "a,b" "csv" == some "\"a,b\""
#guard grelEscape "say \"hi\"" "csv" == some "\"say \"\"hi\"\"\""
#guard grelEscape "a b&c" "url" == some "a+b%26c"
#guard grelEscape "Zoë" "url" == some "Zo%C3%AB"
#guard grelEscape "a.b-c*d_e" "url" == some "a.b-c*d_e"
#guard grelEscape "it's \"x\"/\n" "javascript" == some "it\\'s \\\"x\\\"\\/\\n"
#guard grelEscape "é" "javascript" == some "\\u00E9"
#guard grelEscape "x" "unknown" == none
#guard run1 (grelNs ++ "escape") [(gv, "A&B"), (grelNs ++ "modeParam", "html")] == ok (some "A&amp;B")
#guard run1 (grelNs ++ "escape") [(gv, "A&B"), (grelNs ++ "modeParam", "nope")] == none

-- IDLab and the example functions
#guard run1 (idlabNs ++ "alwaysReturnsABC") [] == ok (some "ABC")
#guard toUpperCaseUrl "http://example.com/venus" == "HTTP://EXAMPLE.COM/VENUS"
#guard toUpperCaseUrl "example.com" == "HTTP://EXAMPLE.COM"
#guard run1 (idlabNs ++ "equal") [(gv, "A"), (grelNs ++ "valueParam2", "A")] == ok (some "true")
#guard run1 (idlabNs ++ "equal") [(gv, "B"), (grelNs ++ "valueParam2", "A")] == ok (some "false")
#guard run1 (idlabNs ++ "notEqual") [(gv, "B"), (grelNs ++ "valueParam2", "A")] == ok (some "true")
#guard run1 (idlabNs ++ "trueCondition") [(idlabNs ++ "strBoolean", "true"), (idlabNs ++ "str", "x")] == ok (some "x")
#guard run1 (idlabNs ++ "trueCondition") [(idlabNs ++ "strBoolean", "false"), (idlabNs ++ "str", "x")] == ok none
#guard run1 (fnsNs ++ "helloworld") [] == ok (some "Hello World!")
#guard run1 (fnsNs ++ "schema") [(fnsNs ++ "stringParameter", "Person")] == ok (some "https://schema.org/Person")
#guard run1 (fnsNs ++ "schema") [] == ok none
#guard parseUrl "https://example.com/a/b" == some ("https", "example.com", "a/b")
#guard parseUrl "not a url" == none
#guard run1 (fnsNs ++ "parseURL") [(fnsNs ++ "stringParameter", "https://example.com/a/b")]
         (some (fnsNs ++ "domainOutput")) == ok (some "example.com")
#guard run1 (fnsNs ++ "parseURL") [(fnsNs ++ "stringParameter", "https://example.com/a/b")]
         (some (fnsNs ++ "stringOutput")) == ok (some "a/b")

-- the registry has no function twice, every return list is non-empty
#guard (registry.map (·.iri)).eraseDups.length == registry.length
#guard registry.all (fun f => !f.returns.isEmpty)

-- KNOWN SHORTFALL: case mapping is ASCII only, so an accented letter is
-- not upper-cased (Java's String.toUpperCase maps it). This guard asserts
-- the present behaviour; it fails when case mapping becomes Unicode, and
-- must then be replaced by the correct expectation "É" and its issue closed.
-- Issue: NOT YET FILED (the coordinator files it).
#guard run1 (grelNs ++ "toUpperCase") [(gv, "é")] == ok (some "é")

-- KNOWN SHORTFALL: html mode escapes the five markup characters only;
-- GREL's escapeHtml4 also writes a named entity for a non-ASCII character
-- ("&eacute;" for "é"). This guard asserts the present behaviour and must
-- be replaced when the entity table is added.
-- Issue: NOT YET FILED (the coordinator files it).
#guard grelEscape "é" "html" == some "é"

end L4Factoidal.RML
