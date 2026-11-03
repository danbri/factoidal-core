/-
L4Factoidal.YAML.Loader — a total YAML 1.2.2 loader that composes a YAML
stream into JSON values (`L4Factoidal.JSON.Json`).

Specification: YAML Ain't Markup Language version 1.2.2 (2021-10-01),
https://yaml.org/spec/1.2.2/ . The loader runs the three load steps of
§3.1 (parse, compose, construct) in one pass and constructs JSON values
directly, so it supports the part of YAML that has a JSON representation:

  - §3.2.1.1 nodes: block and flow sequences and mappings, and scalars
    (plain, single-quoted, double-quoted, literal `|` and folded `>`, with
    the chomping and indentation indicators of §8.1.1);
  - §6.8 directives: `%TAG` (handles `!`, `!!`, `!name!`) and `%YAML`;
  - §6.9 node properties: tags (§6.9.1, including `!<verbatim>` and the
    non-specific `!`) and anchors (§6.9.2), with aliases (§7.1);
  - §9.2 streams: zero or more documents, `---` and `...` markers;
  - §10.3 the Core Schema for tag resolution of plain scalars.

What a JSON value cannot hold is refused, with the error that YAML-LD 1.0
§4.3 and §4.4 name (`L4Factoidal.YAMLLD` maps the errors to the YAML-LD
codes): a mapping key that is not a `tag:yaml.org,2002:str` scalar
(complex keys `?`, flow-collection keys, and plain keys that resolve to
null, a boolean or a number); an alias whose anchor is still being composed
(a cycle of the representation graph); `.inf` and `.nan`; and a tag outside
the Core Schema (unless `extended` is set, see `Env.extended`).

Not supported, and refused as malformed: tabs as indentation, the reserved
indicators `@` and the backquote at the start of a plain scalar. Duplicate
mapping keys are kept in input order (JSON permits them, RFC 8259 §4), so
that a JSON text loads as the same value through this loader and through
`L4Factoidal.JSON.parseJson`.

Termination: every function of the mutual block takes `fuel` and passes
`fuel - 1` to every call; `loadStream` starts with fuel `4 * size + 16`. The
loops over entries, characters and lines are tail calls (one frame per
nesting level of the document, not per item).
-/
import L4Factoidal.JSON.Value

namespace L4Factoidal.YAML

open L4Factoidal.JSON

abbrev Chars := Array Char

/-- Why a YAML stream does not load. `pos` is a character index. -/
inductive YamlError where
  /-- Not a well-formed YAML stream (YAML 1.2.2 §9.2), or not supported. -/
  | malformed (msg : String) (pos : Nat)
  /-- A mapping key that is not a string scalar (YAML-LD 1.0 §4.4.3). -/
  | mappingKey (pos : Nat)
  /-- A tag outside the YAML 1.2.2 Core Schema (YAML-LD 1.0 §4.3.2). -/
  | unknownTag (tag : String) (pos : Nat)
  /-- `.inf`, `-.inf`, `+.inf` or `.nan`: no JSON number (YAML-LD 1.0 §4.3.2). -/
  | notJsonNumber (lexeme : String) (pos : Nat)
  /-- An alias to an anchor whose node is not yet composed (YAML-LD 1.0 §4.3.1). -/
  | cycle (anchor : String) (pos : Nat)
  /-- An alias with no preceding anchor (YAML 1.2.2 §7.1). -/
  | undefinedAlias (anchor : String) (pos : Nat)
  /-- The fuel bound was reached (never for `loadStream`'s bound). -/
  | tooDeep (pos : Nat)
  deriving Repr, DecidableEq

def YamlError.message : YamlError → String
  | .malformed m p => s!"malformed YAML at character {p}: {m}"
  | .mappingKey p => s!"mapping key at character {p} is not a string"
  | .unknownTag t p => s!"tag {t} at character {p} is outside the YAML Core Schema"
  | .notJsonNumber l p => s!"{l} at character {p} has no JSON number"
  | .cycle a p => s!"alias *{a} at character {p} makes a cycle"
  | .undefinedAlias a p => s!"alias *{a} at character {p} has no anchor"
  | .tooDeep p => s!"nesting too deep at character {p}"

/-- The constant part of one document's parse. -/
structure Env where
  cs : Chars
  /-- `%TAG` handles of the current document: handle ↦ prefix. -/
  tags : List (String × String) := []
  /-- Informative YAML-LD Extended Profile mode: a tag outside the Core
  Schema is dropped and the node is resolved as if it had no tag. -/
  extended : Bool := false

/-- The changing part: position, composed anchors, anchors in progress. -/
structure St where
  pos : Nat
  anchors : List (String × Json) := []
  opening : List String := []

abbrev R (α : Type) := Except YamlError (α × St)

/-! ## Characters and lines -/

def at? (e : Env) (p : Nat) : Option Char := e.cs[p]?

def isSpTab (c : Char) : Bool := c == ' ' || c == '\t'

/-- Space, tab, line feed or end of input at `p`. -/
def blankAt (e : Env) (p : Nat) : Bool :=
  match at? e p with
  | none => true
  | some c => c == ' ' || c == '\t' || c == '\n'

def isFlowInd (c : Char) : Bool := c == ',' || c == '[' || c == ']' || c == '{' || c == '}'

/-- Index of the first character of the line that holds `p`. -/
def lineStartAux (cs : Chars) : Nat → Nat
  | 0 => 0
  | k + 1 => if cs[k]? == some '\n' then k + 1 else lineStartAux cs k

def col (e : Env) (p : Nat) : Nat := p - lineStartAux e.cs p

def skipSpAux (cs : Chars) (p : Nat) : Nat → Nat
  | 0 => p
  | f + 1 => match cs[p]? with
    | some ' ' | some '\t' => skipSpAux cs (p + 1) f
    | _ => p

def skipSp (e : Env) (p : Nat) : Nat := skipSpAux e.cs p (e.cs.size + 1)

def toEolAux (cs : Chars) (p : Nat) : Nat → Nat
  | 0 => p
  | f + 1 => match cs[p]? with
    | none | some '\n' => p
    | _ => toEolAux cs (p + 1) f

/-- Position of the line feed (or end of input) that ends `p`'s line. -/
def toEol (e : Env) (p : Nat) : Nat := toEolAux e.cs p (e.cs.size + 1)

/-- A `#` at `q` begins a comment when it starts a line or follows white
space (YAML 1.2.2 §6.6). -/
def commentAt (e : Env) (q : Nat) : Bool :=
  at? e q == some '#' &&
    (q == 0 || match at? e (q - 1) with
               | some c => c == ' ' || c == '\t' || c == '\n'
               | none => true)

/-- Nothing but white space and an optional comment from `p` to the end of the line. -/
def restEmpty (e : Env) (p : Nat) : Bool :=
  let q := skipSp e p
  match at? e q with
  | none | some '\n' => true
  | some '#' => commentAt e q
  | _ => false

/-- `---` or `...` at the start of a line, followed by a blank (§9.1.2). -/
def markerAt (e : Env) (p : Nat) (c : Char) : Bool :=
  col e p == 0 && at? e p == some c && at? e (p + 1) == some c && at? e (p + 2) == some c &&
    blankAt e (p + 3)

def docMarkerAt (e : Env) (p : Nat) : Bool := markerAt e p '-' || markerAt e p '.'

def skipToContentAux (e : Env) (p : Nat) : Nat → Nat
  | 0 => p
  | f + 1 =>
    let q := skipSp e p
    match at? e q with
    | some '\n' => skipToContentAux e (q + 1) f
    | some '#' => if commentAt e q then skipToContentAux e (toEol e q) f else q
    | _ => q

/-- Skip white space, comments and line breaks. -/
def skipToContent (e : Env) (p : Nat) : Nat := skipToContentAux e p (e.cs.size + 1)

def slice (e : Env) (a b : Nat) : String := String.ofList (e.cs.extract a b).toList

/-- Leading spaces of the line that starts at `p`. -/
def indentAt (e : Env) (p : Nat) : Nat := skipSpAux e.cs p (e.cs.size + 1) - p

/-- A block sequence entry indicator `-` followed by a blank (§8.2.1). -/
def seqIndAt (e : Env) (p : Nat) : Bool :=
  at? e p == some '-' && blankAt e (p + 1) && !markerAt e p '-'

/-! ## The Core Schema (YAML 1.2.2 §10.3) -/

def yamlTag (s : String) : String := "tag:yaml.org,2002:" ++ s

def isNullLex (s : String) : Bool := s == "" || s == "~" || s == "null" || s == "Null" || s == "NULL"

def boolLex? (s : String) : Option Bool :=
  if s == "true" || s == "True" || s == "TRUE" then some true
  else if s == "false" || s == "False" || s == "FALSE" then some false
  else none

def isDig (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isOctD (c : Char) : Bool := '0' ≤ c && c ≤ '7'
def isHexD (c : Char) : Bool := isDig c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def hexVal (c : Char) : Nat :=
  if isDig c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def digitsVal (base : Nat) (ds : List Char) : Nat := ds.foldl (fun a c => a * base + hexVal c) 0

def stripZeros (ds : List Char) : List Char :=
  match ds.dropWhile (· == '0') with
  | [] => ['0']
  | r => r

/-- `[-+]?[0-9]+`, `0o[0-7]+`, `0x[0-9a-fA-F]+` as a JSON number lexeme. -/
def intLex? (s : String) : Option String :=
  match s.toList with
  | '0' :: 'o' :: ds@(_ :: _) =>
    if ds.all isOctD then some (toString (digitsVal 8 ds)) else none
  | '0' :: 'x' :: ds@(_ :: _) =>
    if ds.all isHexD then some (toString (digitsVal 16 ds)) else none
  | '-' :: ds@(_ :: _) => if ds.all isDig then some ("-" ++ String.ofList (stripZeros ds)) else none
  | '+' :: ds@(_ :: _) => if ds.all isDig then some (String.ofList (stripZeros ds)) else none
  | ds@(_ :: _) => if ds.all isDig then some (String.ofList (stripZeros ds)) else none
  | [] => none

/-- `[eE][-+]?[0-9]+`, or nothing. -/
def expOk : List Char → Bool
  | [] => true
  | e :: rest =>
    (e == 'e' || e == 'E') &&
      match rest with
      | '+' :: ds | '-' :: ds => !ds.isEmpty && ds.all isDig
      | ds => !ds.isEmpty && ds.all isDig

/-- `[-+]?(\.[0-9]+|[0-9]+(\.[0-9]*)?)([eE][-+]?[0-9]+)?` as a JSON number
lexeme: the sign `+` is dropped, leading zeros of the integer part are
dropped, and an empty integer or fraction part becomes `0`. -/
def floatLex? (s : String) : Option String :=
  let cs := s.toList
  let (sign, body) := match cs with
    | '-' :: r => ("-", r)
    | '+' :: r => ("", r)
    | r => ("", r)
  let intP := body.takeWhile isDig
  let r1 := body.drop intP.length
  let (frac, hasDot, r2) := match r1 with
    | '.' :: r => let f := r.takeWhile isDig; (f, true, r.drop f.length)
    | r => ([], false, r)
  if intP.isEmpty && frac.isEmpty then none
  else if !expOk r2 then none
  else
    let ip := String.ofList (stripZeros intP)
    let fp := if hasDot then "." ++ String.ofList (if frac.isEmpty then ['0'] else frac) else ""
    some (sign ++ ip ++ fp ++ String.ofList r2)

def isInfNan (s : String) : Bool :=
  s == ".inf" || s == ".Inf" || s == ".INF" || s == "-.inf" || s == "-.Inf" || s == "-.INF" ||
  s == "+.inf" || s == "+.Inf" || s == "+.INF" || s == ".nan" || s == ".NaN" || s == ".NAN"

/-- Tag resolution of a plain scalar by the Core Schema (§10.3.2). -/
def resolvePlain (s : String) (pos : Nat) : Except YamlError Json :=
  if isNullLex s then .ok .null
  else match boolLex? s with
  | some b => .ok (.bool b)
  | none =>
    match intLex? s with
    | some l => .ok (.number l)
    | none =>
      if isInfNan s then .error (.notJsonNumber s pos)
      else match floatLex? s with
        | some l => .ok (.number l)
        | none => .ok (.string s)

/-- Construct a scalar from its text, its tag (`none`: no tag; `some "!"`:
the non-specific tag) and its style (`plain`). -/
def resolveScalar (e : Env) (tag : Option String) (plain : Bool) (text : String) (pos : Nat)
    : Except YamlError Json :=
  let untagged : Except YamlError Json := if plain then resolvePlain text pos else .ok (.string text)
  match tag with
  | none => untagged
  | some "!" => .ok (.string text)
  | some t =>
    if t == yamlTag "str" then .ok (.string text)
    else if t == yamlTag "null" then
      if isNullLex text then .ok .null else .error (.malformed s!"!!null {text}" pos)
    else if t == yamlTag "bool" then
      match boolLex? text with
      | some b => .ok (.bool b)
      | none => .error (.malformed s!"!!bool {text}" pos)
    else if t == yamlTag "int" then
      match intLex? text with
      | some l => .ok (.number l)
      | none => .error (.malformed s!"!!int {text}" pos)
    else if t == yamlTag "float" then
      if isInfNan text then .error (.notJsonNumber text pos)
      else match intLex? text with
        | some l => .ok (.number l)
        | none => match floatLex? text with
          | some l => .ok (.number l)
          | none => .error (.malformed s!"!!float {text}" pos)
    else if e.extended then untagged
    else .error (.unknownTag t pos)

/-- A collection's tag must be absent, non-specific, or the matching Core
Schema tag (`!!map`, `!!seq`). -/
def checkCollTag (e : Env) (tag : Option String) (kind : String) (pos : Nat) : Except YamlError Unit :=
  match tag with
  | none => .ok ()
  | some "!" => .ok ()
  | some t =>
    if t == yamlTag kind then .ok ()
    else if e.extended then .ok ()
    else .error (.unknownTag t pos)

/-! ## Node properties (§6.9) -/

def isNameChar (c : Char) : Bool := !(c == ' ' || c == '\t' || c == '\n' || isFlowInd c)

def takeNameAux (e : Env) (p : Nat) : Nat → Nat
  | 0 => p
  | f + 1 => match at? e p with
    | some c => if isNameChar c then takeNameAux e (p + 1) f else p
    | none => p

def takeName (e : Env) (p : Nat) : Nat := takeNameAux e p (e.cs.size + 1)

/-- `%XX` escapes of a tag suffix (§6.9.1: URI characters). -/
def uriDecodeAux : List Char → List Char → List Char
  | [], acc => acc.reverse
  | '%' :: a :: b :: rest, acc =>
    if isHexD a && isHexD b then uriDecodeAux rest (Char.ofNat (hexVal a * 16 + hexVal b) :: acc)
    else uriDecodeAux (a :: b :: rest) ('%' :: acc)
  | c :: rest, acc => uriDecodeAux rest (c :: acc)

def uriDecode (s : String) : String := String.ofList (uriDecodeAux s.toList [])

/-- Resolve a tag property's text (after the `!`) with the `%TAG` handles
of the document (§6.8.2.2 default handles `!` and `!!`). -/
def resolveTag (e : Env) (body : String) (pos : Nat) : Except YamlError String :=
  let cs := body.toList
  match cs with
  | [] => .ok "!"
  | '<' :: rest =>
    if rest.getLast? == some '>' then .ok (uriDecode (String.ofList rest.dropLast))
    else .error (.malformed "verbatim tag without >" pos)
  | _ =>
    match cs.findIdx? (· == '!') with
    | none =>
      -- primary handle `!`
      match e.tags.find? (·.1 == "!") with
      | some (_, pre) => .ok (pre ++ uriDecode body)
      | none => .ok ("!" ++ uriDecode body)
    | some i =>
      let handle := "!" ++ String.ofList (cs.take (i + 1))
      let suffix := uriDecode (String.ofList (cs.drop (i + 1)))
      match e.tags.find? (·.1 == handle) with
      | some (_, pre) => .ok (pre ++ suffix)
      | none =>
        if handle == "!!" then .ok (yamlTag suffix)
        else .error (.malformed s!"undefined tag handle {handle}" pos)

/-- Parse the properties at `p`: anchor and tag in either order. Returns
the anchor name, the resolved tag and the position after them. -/
def parseProps (e : Env) (p : Nat) : Except YamlError (Option String × Option String × Nat) :=
  let one (p : Nat) (anc tag : Option String) : Except YamlError (Option String × Option String × Nat × Bool) :=
    match at? e p with
    | some '&' =>
      let q := takeName e (p + 1)
      if q == p + 1 then .error (.malformed "empty anchor name" p)
      else .ok (some (slice e (p + 1) q), tag, q, true)
    | some '!' =>
      -- a verbatim tag may contain `,` and brackets inside `<…>`
      let q := if at? e (p + 1) == some '<' then
                 (match (e.cs.extract p e.cs.size).toList.findIdx? (· == '>') with
                  | some i => p + i + 1
                  | none => e.cs.size)
               else takeName e (p + 1)
      match resolveTag e (slice e (p + 1) q) p with
      | .ok t => .ok (anc, some t, q, true)
      | .error err => .error err
    | _ => .ok (anc, tag, p, false)
  match one p none none with
  | .error err => .error err
  | .ok (a, t, q, false) => .ok (a, t, q)
  | .ok (a, t, q, true) =>
    let q' := skipSp e q
    match one q' a t with
    | .error err => .error err
    | .ok (a2, t2, q2, true) => .ok (a2, t2, q2)
    | .ok (a2, t2, _, false) => .ok (a2, t2, q)

/-! ## Scalars -/

/-- Trim trailing spaces and tabs of a reversed character list. -/
def trimRevSp : List Char → List Char
  | c :: rest => if isSpTab c then trimRevSp rest else c :: rest
  | [] => []

def pushN (c : Char) : Nat → List Char → List Char
  | 0, acc => acc
  | n + 1, acc => pushN c n (c :: acc)

/-- Fold the line break at `p` inside a quoted or flow scalar (§6.5,
§7.3): returns the position of the next line's first non-blank and the
folded break (`' '` for one break, `n - 1` line feeds for `n`). -/
def foldBreakAux (e : Env) (p breaks : Nat) : Nat → Nat × Nat
  | 0 => (p, breaks)
  | f + 1 =>
    let q := skipSp e p
    if at? e q == some '\n' then foldBreakAux e (q + 1) (breaks + 1) f else (q, breaks)

def foldBreak (e : Env) (p : Nat) (acc : List Char) : Nat × List Char :=
  let (q, n) := foldBreakAux e (p + 1) 1 (e.cs.size + 1)
  let acc := trimRevSp acc
  (q, if n == 1 then ' ' :: acc else pushN '\n' (n - 1) acc)

def hexN (e : Env) (p n : Nat) : Option Nat :=
  let ds := (e.cs.extract p (p + n)).toList
  if ds.length == n && ds.all isHexD then some (digitsVal 16 ds) else none

/-- Double-quoted scalar body from `p` (after the opening quote). -/
def dqAux (e : Env) (p : Nat) (acc : List Char) : Nat → Except YamlError (String × Nat)
  | 0 => .error (.tooDeep p)
  | f + 1 =>
    match at? e p with
    | none => .error (.malformed "unterminated double-quoted scalar" p)
    | some '"' => .ok (String.ofList acc.reverse, p + 1)
    | some '\n' => let (q, acc') := foldBreak e p acc; dqAux e q acc' f
    | some '\\' =>
      match at? e (p + 1) with
      | some '\n' =>
        let q := skipSp e (p + 2)
        dqAux e q (trimRevSp acc) f
      | some c =>
        let simple : Option Char := match c with
          | '0' => some (Char.ofNat 0) | 'a' => some (Char.ofNat 7) | 'b' => some (Char.ofNat 8)
          | 't' => some '\t' | '\t' => some '\t' | 'n' => some '\n' | 'v' => some (Char.ofNat 11)
          | 'f' => some (Char.ofNat 12) | 'r' => some '\r' | 'e' => some (Char.ofNat 27)
          | ' ' => some ' ' | '"' => some '"' | '/' => some '/' | '\\' => some '\\'
          | 'N' => some (Char.ofNat 0x85) | '_' => some (Char.ofNat 0xA0)
          | 'L' => some (Char.ofNat 0x2028) | 'P' => some (Char.ofNat 0x2029)
          | _ => none
        match simple with
        | some ch => dqAux e (p + 2) (ch :: acc) f
        | none =>
          let width := if c == 'x' then 2 else if c == 'u' then 4 else if c == 'U' then 8 else 0
          if width == 0 then .error (.malformed s!"unknown escape \\{c}" p)
          else match hexN e (p + 2) width with
            | none => .error (.malformed "bad hexadecimal escape" p)
            | some v =>
              -- a UTF-16 surrogate pair written as two `\u` escapes (as JSON writes it)
              if c == 'u' && 0xD800 ≤ v && v < 0xDC00 &&
                  at? e (p + 6) == some '\\' && at? e (p + 7) == some 'u' then
                match hexN e (p + 8) 4 with
                | some lo =>
                  if 0xDC00 ≤ lo && lo < 0xE000 then
                    dqAux e (p + 12) (Char.ofNat (0x10000 + (v - 0xD800) * 0x400 + (lo - 0xDC00)) :: acc) f
                  else .error (.malformed "unpaired surrogate escape" p)
                | none => .error (.malformed "unpaired surrogate escape" p)
              else if 0xD800 ≤ v && v < 0xE000 then .error (.malformed "unpaired surrogate escape" p)
              else dqAux e (p + 2 + width) (Char.ofNat v :: acc) f
      | none => .error (.malformed "unterminated double-quoted scalar" p)
    | some c => dqAux e (p + 1) (c :: acc) f

/-- Single-quoted scalar body from `p` (after the opening quote). -/
def sqAux (e : Env) (p : Nat) (acc : List Char) : Nat → Except YamlError (String × Nat)
  | 0 => .error (.tooDeep p)
  | f + 1 =>
    match at? e p with
    | none => .error (.malformed "unterminated single-quoted scalar" p)
    | some '\'' =>
      if at? e (p + 1) == some '\'' then sqAux e (p + 2) ('\'' :: acc) f
      else .ok (String.ofList acc.reverse, p + 1)
    | some '\n' => let (q, acc') := foldBreak e p acc; sqAux e q acc' f
    | some c => sqAux e (p + 1) (c :: acc) f

def parseQuoted (e : Env) (p : Nat) : Except YamlError (String × Nat) :=
  if at? e p == some '"' then dqAux e (p + 1) [] (e.cs.size + 1)
  else sqAux e (p + 1) [] (e.cs.size + 1)

/-- Where a plain scalar's line segment stops (§7.3.3): at a line break, a
` #` comment, a `:` followed by a blank (or, in flow context, by a flow
indicator), or, in flow context, at a flow indicator. -/
def plainEndAux (e : Env) (flow : Bool) (p : Nat) : Nat → Nat
  | 0 => p
  | f + 1 =>
    match at? e p with
    | none | some '\n' => p
    | some ':' =>
      if blankAt e (p + 1) || (flow && (match at? e (p + 1) with
                                        | some c => isFlowInd c | none => true)) then p
      else plainEndAux e flow (p + 1) f
    | some '#' => if commentAt e p then p else plainEndAux e flow (p + 1) f
    | some c => if flow && isFlowInd c then p else plainEndAux e flow (p + 1) f

def plainEnd (e : Env) (flow : Bool) (p : Nat) : Nat := plainEndAux e flow p (e.cs.size + 1)

/-- One trimmed plain segment `[p, end)` and its end. -/
def plainSeg (e : Env) (flow : Bool) (p : Nat) : String × Nat :=
  let q := plainEnd e flow p
  (String.ofList (trimRevSp (e.cs.extract p q).toList.reverse).reverse, q)

/-- Continuation lines of a plain scalar (§7.3.3 multi-line plain scalars).
`acc` holds the text so far; a next line continues the scalar when it is
more indented than `pc` (block context) and is not a comment, a marker, or
empty input. Empty lines between fold to line feeds. -/
def plainMoreAux (e : Env) (flow : Bool) (pc : Int) (p : Nat) (acc : String) : Nat → Except YamlError (String × Nat)
  | 0 => .ok (acc, p)
  | f + 1 =>
    -- `p` is at the end of a segment
    let q := skipSp e p
    if at? e q != some '\n' then .ok (acc, p)
    else
      let (r, n) := foldBreakAux e (q + 1) 1 (e.cs.size + 1)
      let ok := match at? e r with
        | none => false
        | some c =>
          !docMarkerAt e r && !commentAt e r &&
            (if flow then !isFlowInd c && c != ':' else (col e r : Int) > pc)
      if !ok then .ok (acc, p)
      else
        let (seg, s) := plainSeg e flow r
        if seg.isEmpty then .ok (acc, p)
        else if !flow && at? e s == some ':' then .error (.malformed "implicit key in a multi-line plain scalar" s)
        else
          let sep := if n == 1 then " " else String.ofList (List.replicate (n - 1) '\n')
          plainMoreAux e flow pc s (acc ++ sep ++ seg) f

/-! ## Block scalars (§8.1) -/

/-- Lines of a block scalar with content indentation `k`, from the line
that starts at `p`. Each line keeps the characters after column `k`; an
empty or white line is `""`. Stops before the first non-empty line with
less indentation, or a document marker. -/
def blockLinesAux (e : Env) (k : Nat) (p : Nat) (acc : List String) : Nat → List String × Nat
  | 0 => (acc.reverse, p)
  | f + 1 =>
    if p ≥ e.cs.size then (acc.reverse, p)
    else if docMarkerAt e p then (acc.reverse, p)
    else
      let i := indentAt e p
      let eol := toEol e p
      let isWhite := p + i == eol
      if isWhite then
        let line := if i > k then slice e (p + k) eol else ""
        blockLinesAux e k (eol + 1) (line :: acc) f
      else if i < k then (acc.reverse, p)
      else blockLinesAux e k (eol + 1) (slice e (p + k) eol :: acc) f

/-- First non-white line's indentation from `p` (for auto-detection). -/
def firstIndentAux (e : Env) (p : Nat) : Nat → Option Nat
  | 0 => none
  | f + 1 =>
    if p ≥ e.cs.size then none
    else
      let i := indentAt e p
      let eol := toEol e p
      if p + i == eol then firstIndentAux e (eol + 1) f else some i

def foldLinesAux : List String → Option Bool → Nat → String → String
  | [], _, _, out => out
  | l :: rest, prev, empties, out =>
    if l.isEmpty then foldLinesAux rest prev (empties + 1) out
    else
      let isText := !(l.startsWith " " || l.startsWith "\t")
      let sep := match prev with
        | none => String.ofList (List.replicate empties '\n')
        | some prevText =>
          if prevText && isText then
            (if empties == 0 then " " else String.ofList (List.replicate empties '\n'))
          else String.ofList (List.replicate (empties + 1) '\n')
      foldLinesAux rest (some isText) 0 (out ++ sep ++ l)

def dropTrailingEmpty (ls : List String) : List String × Nat :=
  let rev := ls.reverse
  let t := (rev.takeWhile (·.isEmpty)).length
  ((rev.drop t).reverse, t)

/-- A block scalar whose indicator is at `p`; `pc` is the parent column. -/
def parseBlockScalar (e : Env) (pc : Int) (p : Nat) : Except YamlError (String × Nat) :=
  let literal := at? e p == some '|'
  let hdr := (e.cs.extract (p + 1) (toEol e p)).toList.takeWhile (fun c => c == '+' || c == '-' || isDig c)
  let chomp : Char := if hdr.contains '-' then '-' else if hdr.contains '+' then '+' else ' '
  let explicitInd := (hdr.find? (fun c => isDig c && c != '0')).map (fun c => c.toNat - '0'.toNat)
  let afterHdr := p + 1 + hdr.length
  if !restEmpty e afterHdr then .error (.malformed "text after a block scalar header" afterHdr)
  else
    let eol := toEol e afterHdr
    let start := eol + 1
    let n : Int := if pc < 0 then 0 else pc
    let k : Option Nat := match explicitInd with
      | some d => some (n + d).toNat
      | none =>
        match firstIndentAux e start (e.cs.size + 1) with
        | some i => if (i : Int) > pc then some i else none
        | none => none
    let (lines, endP) := match k with
      | some k => blockLinesAux e k start [] (e.cs.size + 1)
      | none => (([] : List String), if start > e.cs.size then e.cs.size else start)
    let (body, trailing) := dropTrailingEmpty lines
    let text :=
      if literal then String.intercalate "\n" body
      else foldLinesAux body none 0 ""
    let out :=
      if body.isEmpty then
        (if chomp == '+' then String.ofList (List.replicate trailing '\n') else "")
      else if chomp == '-' then text
      else if chomp == '+' then text ++ "\n" ++ String.ofList (List.replicate trailing '\n')
      else text ++ "\n"
    .ok (out, endP)

/-! ## Nodes -/

/-- How a block node is placed: at the top of a document, as a mapping
value, or as a sequence entry. A mapping value on the same line as its key
may not be an implicit key; a block sequence may be a mapping value at the
key's own column (§8.2.1, "compact" indentation). -/
inductive Ctx where
  | top | mapValue | seqEntry
  deriving DecidableEq

def openAnchor (anc : Option String) (st : St) : St :=
  match anc with
  | some a => { st with opening := a :: st.opening }
  | none => st

def closeAnchor (anc : Option String) (v : Json) (st : St) : St :=
  match anc with
  | some a => { st with anchors := (a, v) :: st.anchors, opening := st.opening.erase a }
  | none => st

def resolveAlias (e : Env) (p : Nat) (st : St) : R Json :=
  let q := takeName e (p + 1)
  let name := slice e (p + 1) q
  if name.isEmpty then .error (.malformed "empty alias name" p)
  else if st.opening.contains name then .error (.cycle name p)
  else match st.anchors.find? (·.1 == name) with
    | some (_, v) => .ok (v, { st with pos := q })
    | none => .error (.undefinedAlias name p)

def keyString (v : Json) (p : Nat) : Except YamlError String :=
  match v with
  | .string s => .ok s
  | _ => .error (.mappingKey p)

/-- Skip white space, line breaks and comments inside a flow collection. -/
def flowSkip (e : Env) (p : Nat) : Nat := skipToContent e p

mutual

/-- A flow node at `p` (§7). -/
def flowNode (e : Env) (fuel : Nat) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    let p := flowSkip e st.pos
    match parseProps e p with
    | .error err => .error err
    | .ok (anc, tag, q0) =>
      let q := if q0 == p then p else flowSkip e q0
      let st0 := openAnchor anc { st with pos := q }
      let res : R Json :=
        match at? e q with
        | some '[' =>
          match flowSeq e fuel [] { st0 with pos := q + 1 } with
          | .error err => .error err
          | .ok (v, st1) =>
            match checkCollTag e tag "seq" q with
            | .error err => .error err
            | .ok () => .ok (v, st1)
        | some '{' =>
          match flowMap e fuel [] { st0 with pos := q + 1 } with
          | .error err => .error err
          | .ok (v, st1) =>
            match checkCollTag e tag "map" q with
            | .error err => .error err
            | .ok () => .ok (v, st1)
        | some '*' => resolveAlias e q st0
        | some '"' | some '\'' =>
          match parseQuoted e q with
          | .error err => .error err
          | .ok (s, r) =>
            match resolveScalar e tag false s q with
            | .error err => .error err
            | .ok v => .ok (v, { st0 with pos := r })
        | some c =>
          if c == ',' || c == ']' || c == '}' || c == ':' then
            -- an empty node (only after properties)
            match resolveScalar e tag true "" q with
            | .error err => .error err
            | .ok v => .ok (v, st0)
          else
            let (seg, s) := plainSeg e true q
            match plainMoreAux e true (-1) s seg (e.cs.size + 1) with
            | .error err => .error err
            | .ok (text, r) =>
              match resolveScalar e tag true text q with
              | .error err => .error err
              | .ok v => .ok (v, { st0 with pos := r })
        | none => .error (.malformed "unterminated flow collection" q)
      match res with
      | .error err => .error err
      | .ok (v, st1) => .ok (v, closeAnchor anc v st1)

/-- Flow sequence entries after `[` (§7.4.1), including single-pair
mappings (§7.4.2). -/
def flowSeq (e : Env) (fuel : Nat) (acc : List Json) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    let p := flowSkip e st.pos
    if at? e p == some ']' then .ok (.array acc.reverse, { st with pos := p + 1 })
    else
      match flowNode e fuel { st with pos := p } with
      | .error err => .error err
      | .ok (v, st1) =>
        let q := flowSkip e st1.pos
        let pair : R Json :=
          if at? e q == some ':' then
            match keyString v p with
            | .error err => .error err
            | .ok k =>
              let r := flowSkip e (q + 1)
              if at? e r == some ',' || at? e r == some ']' then .ok (.object [(k, .null)], { st1 with pos := r })
              else match flowNode e fuel { st1 with pos := r } with
                | .error err => .error err
                | .ok (w, st2) => .ok (.object [(k, w)], st2)
          else .ok (v, st1)
        match pair with
        | .error err => .error err
        | .ok (item, st2) =>
          let r := flowSkip e st2.pos
          match at? e r with
          | some ',' => flowSeq e fuel (item :: acc) { st2 with pos := r + 1 }
          | some ']' => .ok (.array (item :: acc).reverse, { st2 with pos := r + 1 })
          | _ => .error (.malformed "expected , or ] in a flow sequence" r)

/-- Flow mapping entries after `{` (§7.4). -/
def flowMap (e : Env) (fuel : Nat) (acc : List (String × Json)) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    let p := flowSkip e st.pos
    if at? e p == some '}' then .ok (.object acc.reverse, { st with pos := p + 1 })
    else if at? e p == some '?' && blankAt e (p + 1) then .error (.mappingKey p)
    else if at? e p == some '[' || at? e p == some '{' then .error (.mappingKey p)
    else
      match flowNode e fuel { st with pos := p } with
      | .error err => .error err
      | .ok (kv, st1) =>
        match keyString kv p with
        | .error err => .error err
        | .ok k =>
          let q := flowSkip e st1.pos
          let val : R Json :=
            if at? e q == some ':' then
              let r := flowSkip e (q + 1)
              if at? e r == some ',' || at? e r == some '}' then .ok (.null, { st1 with pos := r })
              else flowNode e fuel { st1 with pos := r }
            else .ok (.null, { st1 with pos := q })
          match val with
          | .error err => .error err
          | .ok (v, st2) =>
            let r := flowSkip e st2.pos
            match at? e r with
            | some ',' => flowMap e fuel ((k, v) :: acc) { st2 with pos := r + 1 }
            | some '}' => .ok (.object ((k, v) :: acc).reverse, { st2 with pos := r + 1 })
            | _ => .error (.malformed "expected , or } in a flow mapping" r)

/-- A block node (§8). `st.pos` is just after the key's `:`, after a
sequence entry's `-`, or at the start of the document. `pc` is the column
of the parent collection (`-1` at the top). -/
def blockNode (e : Env) (fuel : Nat) (pc : Int) (ctx : Ctx) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    let q := skipSp e st.pos
    -- where the content is, and whether it may be an implicit key
    let place (p : Nat) (inline : Bool) : Option (Nat × Bool) :=
      if inline then some (p, ctx != .mapValue)
      else
        let r := skipToContent e p
        if r ≥ e.cs.size || docMarkerAt e r then none
        else if (col e r : Int) > pc || ((col e r : Int) == pc && ctx == .mapValue && seqIndAt e r)
        then some (r, true) else none
    match place q (!restEmpty e q) with
    | none => .ok (.null, { st with pos := q })
    | some (p, allowKey) =>
      match parseProps e p with
      | .error err => .error err
      | .ok (anc, tag, p1) =>
        let placed : Option (Nat × Bool) :=
          if p1 == p then some (p, allowKey)
          else
            let p2 := skipSp e p1
            if !restEmpty e p2 then some (p2, allowKey) else place p2 false
        let st0 := openAnchor anc st
        let res : R Json :=
          match placed with
          | none =>
            match resolveScalar e tag true "" p1 with
            | .error err => .error err
            | .ok v => .ok (v, { st0 with pos := p1 })
          | some (c0, allowKey) => blockContent e fuel pc ctx allowKey tag { st0 with pos := c0 }
        match res with
        | .error err => .error err
        | .ok (v, st1) => .ok (v, closeAnchor anc v st1)

/-- The content of a block node at `st.pos`, after its properties. -/
def blockContent (e : Env) (fuel : Nat) (pc : Int) (ctx : Ctx) (allowKey : Bool)
    (tag : Option String) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    let p := st.pos
    let c := col e p
    -- a block mapping whose first key `k` (string) ends at `q` (the `:`)
    let startMap (k : Json) (q : Nat) (st1 : St) : R Json :=
      if !allowKey then .error (.malformed "a mapping value may not start an implicit key" q)
      else match keyString k p with
        | .error err => .error err
        | .ok ks =>
          match mapEntries e fuel c [] ks { st1 with pos := q + 1 } with
          | .error err => .error err
          | .ok (v, st2) =>
            match checkCollTag e tag "map" p with
            | .error err => .error err
            | .ok () => .ok (v, st2)
    match at? e p with
    | some '-' =>
      if seqIndAt e p then
        if !allowKey && ctx == .mapValue then .error (.malformed "a block sequence may not start on its key's line" p)
        else match seqEntries e fuel c [] st with
          | .error err => .error err
          | .ok (v, st1) =>
            match checkCollTag e tag "seq" p with
            | .error err => .error err
            | .ok () => .ok (v, st1)
      else plainBlock e fuel pc allowKey tag startMap st
    | some '?' => if blankAt e (p + 1) then .error (.mappingKey p) else plainBlock e fuel pc allowKey tag startMap st
    | some ':' => if blankAt e (p + 1) then .error (.malformed "empty mapping key" p) else plainBlock e fuel pc allowKey tag startMap st
    | some '|' | some '>' =>
      match parseBlockScalar e pc p with
      | .error err => .error err
      | .ok (s, r) =>
        match resolveScalar e tag false s p with
        | .error err => .error err
        | .ok v => .ok (v, { st with pos := r })
    | some '[' | some '{' =>
      match flowNode e fuel st with
      | .error err => .error err
      | .ok (v, st1) =>
        let q := skipSp e st1.pos
        if at? e q == some ':' then
          if allowKey then .error (.mappingKey p) else .error (.malformed "unexpected :" q)
        else
          match checkCollTag e tag (if at? e p == some '[' then "seq" else "map") p with
          | .error err => .error err
          | .ok () => .ok (v, st1)
    | some '*' =>
      match resolveAlias e p st with
      | .error err => .error err
      | .ok (v, st1) =>
        let q := skipSp e st1.pos
        if at? e q == some ':' && blankAt e (q + 1) then startMap v q st1 else .ok (v, st1)
    | some '"' | some '\'' =>
      match parseQuoted e p with
      | .error err => .error err
      | .ok (s, r) =>
        let q := skipSp e r
        if at? e q == some ':' && (allowKey || blankAt e (q + 1)) then
          match resolveScalar e tag false s p with
          | .error err => .error err
          | .ok k => startMap k q { st with pos := r }
        else
          match resolveScalar e tag false s p with
          | .error err => .error err
          | .ok v => .ok (v, { st with pos := r })
    | some ch =>
      if ch == '@' || ch == '`' then .error (.malformed "reserved indicator" p)
      else if ch == ',' || ch == ']' || ch == '}' || ch == '%' then .error (.malformed s!"unexpected {ch}" p)
      else plainBlock e fuel pc allowKey tag startMap st
    | none => .ok (.null, st)

/-- A plain scalar in block context; an implicit key if a `: ` follows. -/
def plainBlock (e : Env) (fuel : Nat) (pc : Int) (_allowKey : Bool) (tag : Option String)
    (startMap : Json → Nat → St → R Json) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | _ + 1 =>
    let p := st.pos
    let (seg, s) := plainSeg e false p
    if at? e s == some ':' then
      match resolveScalar e tag true seg p with
      | .error err => .error err
      | .ok k => startMap k s { st with pos := s }
    else
      match plainMoreAux e false pc s seg (e.cs.size + 1) with
      | .error err => .error err
      | .ok (text, r) =>
        match resolveScalar e tag true text p with
        | .error err => .error err
        | .ok v => .ok (v, { st with pos := r })

/-- Block mapping entries at column `c` (§8.2.2). `st.pos` is after the
`:` of key `k`. -/
def mapEntries (e : Env) (fuel : Nat) (c : Nat) (acc : List (String × Json)) (k : String) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    match blockNode e fuel c .mapValue st with
    | .error err => .error err
    | .ok (v, st1) =>
      let acc := (k, v) :: acc
      let r := skipToContent e st1.pos
      if r ≥ e.cs.size || docMarkerAt e r || col e r < c then .ok (.object acc.reverse, { st1 with pos := r })
      else if col e r > c then .error (.malformed "bad indentation of a mapping entry" r)
      else
        match implicitKey e fuel { st1 with pos := r } with
        | .error err => .error err
        | .ok (k2, st2) => mapEntries e fuel c acc k2 st2

/-- A key of a block mapping at `st.pos`, through its `:` (§8.2.2). -/
def implicitKey (e : Env) (fuel : Nat) (st : St) : Except YamlError (String × St) :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | _ + 1 =>
    let p := st.pos
    match at? e p with
    | some '?' => if blankAt e (p + 1) then .error (.mappingKey p) else plainKey e p st
    | some '[' | some '{' => .error (.mappingKey p)
    | some '-' => if seqIndAt e p then .error (.malformed "a sequence entry inside a mapping" p) else plainKey e p st
    | some '*' =>
      match resolveAlias e p st with
      | .error err => .error err
      | .ok (v, st1) =>
        let q := skipSp e st1.pos
        if at? e q == some ':' && blankAt e (q + 1) then
          match keyString v p with
          | .error err => .error err
          | .ok ks => .ok (ks, { st1 with pos := q + 1 })
        else .error (.malformed "expected : after a mapping key" q)
    | _ => plainKey e p st

/-- A scalar key (with properties) at `p`, through its `:`. -/
def plainKey (e : Env) (p : Nat) (st : St) : Except YamlError (String × St) :=
  match parseProps e p with
  | .error err => .error err
  | .ok (anc, tag, p1) =>
    let p2 := if p1 == p then p else skipSp e p1
    let scalar : Except YamlError (Json × Nat) :=
      match at? e p2 with
      | some '"' | some '\'' =>
        match parseQuoted e p2 with
        | .error err => .error err
        | .ok (s, r) =>
          match resolveScalar e tag false s p2 with
          | .error err => .error err
          | .ok v => .ok (v, skipSp e r)
      | _ =>
        let (seg, s) := plainSeg e false p2
        match resolveScalar e tag true seg p2 with
        | .error err => .error err
        | .ok v => .ok (v, s)
    match scalar with
    | .error err => .error err
    | .ok (v, q) =>
      if at? e q != some ':' then .error (.malformed "expected : after a mapping key" q)
      else
        match keyString v p2 with
        | .error err => .error err
        | .ok ks => .ok (ks, closeAnchor anc v { st with pos := q + 1 })

/-- Block sequence entries at column `c` (§8.2.1). `st.pos` is at a `-`. -/
def seqEntries (e : Env) (fuel : Nat) (c : Nat) (acc : List Json) (st : St) : R Json :=
  match fuel with
  | 0 => .error (.tooDeep st.pos)
  | fuel + 1 =>
    match blockNode e fuel c .seqEntry { st with pos := st.pos + 1 } with
    | .error err => .error err
    | .ok (v, st1) =>
      let acc := v :: acc
      let r := skipToContent e st1.pos
      if r < e.cs.size && !docMarkerAt e r && col e r == c && seqIndAt e r then
        seqEntries e fuel c acc { st1 with pos := r }
      else if r < e.cs.size && !docMarkerAt e r && col e r > c then
        .error (.malformed "bad indentation of a sequence entry" r)
      else .ok (.array acc.reverse, { st1 with pos := r })

end

/-! ## Streams (§9.2) -/

/-- Parse the `%TAG` directive on the line at `p`. -/
def tagDirective (e : Env) (p : Nat) : Option (String × String) :=
  let line := slice e p (toEol e p)
  match (line.splitOn " ").filter (fun w => !w.isEmpty) with
  | "%TAG" :: h :: pre :: _ => some (h, pre)
  | _ => none

def directivesAux (e : Env) (p : Nat) (tags : List (String × String)) (seen : Bool) : Nat →
    List (String × String) × Nat × Bool
  | 0 => (tags, p, seen)
  | f + 1 =>
    let q := skipToContent e p
    if q < e.cs.size && col e q == 0 && at? e q == some '%' then
      let tags := match tagDirective e q with
        | some t => t :: tags
        | none => tags
      directivesAux e (toEol e q) tags true f
    else (tags, q, seen)

/-- The documents of a stream, each composed to a JSON value (an empty
document is `null`). `fuel` bounds the number of documents. -/
def streamAux (cs : Chars) (extended : Bool) (fuel : Nat) (p : Nat) (canImplicit : Bool)
    (acc : List Json) : Nat → Except YamlError (List Json)
  | 0 => .ok acc.reverse
  | n + 1 =>
    let e0 : Env := { cs := cs, extended := extended }
    let (tags, q, sawDirective) := directivesAux e0 p [] false (cs.size + 1)
    let e : Env := { cs := cs, tags := tags, extended := extended }
    if q ≥ cs.size then
      if sawDirective then .error (.malformed "directives without a document" q) else .ok acc.reverse
    else if markerAt e q '.' then
      if sawDirective then .error (.malformed "directives without a document" q)
      else streamAux cs extended fuel (q + 3) true acc n
    else
      let explicit := markerAt e q '-'
      if !explicit && (sawDirective || !canImplicit) then
        .error (.malformed "a document needs a --- marker here" q)
      else
        let start := if explicit then q + 3 else q
        match blockNode e fuel (-1) .top { pos := start } with
        | .error err => .error err
        | .ok (v, st) =>
          let r := skipToContent e st.pos
          if r ≥ cs.size then .ok (v :: acc).reverse
          else if markerAt e r '.' then streamAux cs extended fuel (r + 3) true (v :: acc) n
          else if markerAt e r '-' then streamAux cs extended fuel r false (v :: acc) n
          else .error (.malformed "unexpected content after a document" r)

/-- Line breaks normalised to `\n` (§5.4) and a leading byte order mark
dropped (§5.2). -/
def normalize (s : String) : Chars :=
  let rec go : List Char → Array Char → Array Char
    | [], out => out
    | '\r' :: '\n' :: rest, out => go rest (out.push '\n')
    | '\r' :: rest, out => go rest (out.push '\n')
    | c :: rest, out => go rest (out.push c)
  let cs := match s.toList with
    | '\uFEFF' :: rest => rest
    | l => l
  go cs (Array.mkEmpty s.length)

/-- Load a YAML stream: one JSON value per document. -/
def loadStream (s : String) (extended : Bool := false) : Except YamlError (List Json) :=
  let cs := normalize s
  streamAux cs extended (4 * cs.size + 16) 0 true [] (cs.size + 2)

/-! ## Checks -/

/-- The stream loads, to exactly `v`. -/
def loads (s : String) (v : List Json) : Bool :=
  match loadStream s with
  | .ok l => l == v
  | .error _ => false

#guard loads "a: 1\nb: [x, \"y\"]\n" [.object [("a", .number "1"), ("b", .array [.string "x", .string "y"])]]
#guard loads "- &A {\"@id\": x}\n- *A\n" [.array [.object [("@id", .string "x")], .object [("@id", .string "x")]]]
#guard loads "k: |\n  l1\n  l2\nm: >-\n  a\n  b\n\n  c\n" [.object [("k", .string "l1\nl2\n"), ("m", .string "a b\nc")]]
#guard loads "--- a\n--- b\n...\n" [.string "a", .string "b"]
#guard loads "" []
#guard loads "k:\n- a\n- b\nz: 0o17\n" [.object [("k", .array [.string "a", .string "b"]), ("z", .number "15")]]
#guard (loadStream "1: x\n" matches .error (.mappingKey _))
#guard (loadStream "a: &n\n  - *n\n" matches .error (.cycle _ _))
#guard (loadStream "a: .inf\n" matches .error (.notJsonNumber _ _))
#guard (loadStream "a: \"open\n" matches .error (.malformed _ _))
#guard loads "a: b # c\nd: \"e\" # f\n" [.object [("a", .string "b"), ("d", .string "e")]]
#guard loads "a: plain\n  more\n" [.object [("a", .string "plain more")]]
#guard loads "{\"a\":[1,2.5e3,-0,true,null,\"\\u00e9\\ud83d\\ude00\"]}" [.object [("a", .array [.number "1", .number "2.5e3", .number "-0", .bool true, .null,
                               .string "é😀"])]]

end L4Factoidal.YAML
