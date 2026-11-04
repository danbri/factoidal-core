/-
L4Factoidal.RelaxNG.Compact — the RELAX NG compact syntax, translated to
the XML syntax.

Specification: **RELAX NG Compact Syntax**, OASIS Committee Specification
21 November 2002 (https://relaxng.org/compact-20021121.html; the errata page
lists no errata). ISO/IEC 19757-2:2008 Amendment 1 restates it. Section
numbers below are of the 2002 text.

The module follows Appendix A:

  * A.2.2 to A.2.4 (`preprocess`): byte order mark, newline normalization
    (a newline marker is kept apart from a `#xA` character that an escape
    gives) and the `\x{N}` escapes, which must name an XML 1.0 `Char`.
  * A.2.5 (`lex`): tokens by longest match: identifiers (`\` quotes a
    keyword), `CName`, `nsName`, literal segments in one or three quotes,
    `##` documentation lines (adjacent lines joined with a newline), and
    the separators (whitespace and `#` comments).
  * A.1 (`parseTop`): the BNF with its translation. The value of each
    production is a sequence of XML elements (`X`); the operators `|`, `,`,
    `&` cannot be mixed without parentheses, and a `datatypeName - pattern`
    is a whole pattern (it takes no operator and no repetition). Each named
    constraint of A.1 is checked where its production is read.
  * The translation `X` is written as an `L4Factoidal.XML.Node` tree
    (`render`): RELAX NG elements in the default namespace, the declared
    namespace prefixes (except those bound to `inherit` or `""`) on the
    document element, as `element()` of A.1 requires for the context of
    every element, plus one prefix for the compatibility annotations
    namespace.

§6.1: a validator for the compact syntax is a validator for the XML syntax
applied to the translation. `simplifyCompact` is `simplifyNode` of
`L4Factoidal.RelaxNG.Simplify` applied to `translate`; schemas named by
`include` and `external` are read through a resolver that gives the text of
a compact schema and are translated in the same way.

§6.3: `looseEq` compares two simple-syntax grammars with the
context of `value` patterns removed. It is a sufficient test of loose
equivalence (equal grammars are loosely equivalent); it does not reorder or
rename definitions.

Recursion over the nesting of a schema takes a fuel argument that is the
number of tokens; every nested construct reads at least one token, so the
fuel does not run out on a correct schema, and running out is an error.
-/
import L4Factoidal.RelaxNG.Simplify

namespace L4Factoidal.RelaxNG.Compact

open L4Factoidal.XML
open L4Factoidal.RelaxNG

/-- The namespace of RELAX NG DTD Compatibility annotations (§5.2). -/
def compatNs : String := "http://relaxng.org/ns/compatibility/annotations/1.0"

/-- The namespace bound to the `xml` prefix (Namespaces in XML §3). -/
def xmlUri : String := "http://www.w3.org/XML/1998/namespace"

/-! ## A.2.2 to A.2.4: characters -/

/-- A character after newline normalization: `nl` marks a newline marker
(its `c` is `'\n'`); a `#xA` or `#xD` from an escape has `nl = false`. -/
structure LC where
  c : Char
  nl : Bool
deriving Inhabited

/-- The value of a hexadecimal digit. -/
def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- A.2.2 and A.2.3: strip a byte order mark and normalize newlines. -/
def normalizeNewlines (s : String) : Array LC := Id.run do
  let cs := match s.toList with
    | '﻿' :: rest => rest
    | l => l
  let mut out : Array LC := #[]
  let mut cr := false
  for c in cs do
    if c == '\r' then
      out := out.push ⟨'\n', true⟩
      cr := true
    else if c == '\n' then
      if !cr then out := out.push ⟨'\n', true⟩
      cr := false
    else
      out := out.push ⟨c, false⟩
      cr := false
  return out

/-- A.2.4: replace each escape `\x{N}` (one or more `x`) by its character.
A `\` that is followed by `x`s and `{` opens an escape, which must have
hexadecimal digits and `}` and name an XML 1.0 `Char`. Any other `\` stays. -/
def interpretEscapes (a : Array LC) : Except String (Array LC) := do
  let n := a.size
  let mut out : Array LC := #[]
  let mut i := 0
  while i < n do
    let x := a[i]!
    if x.c == '\\' && !x.nl then
      let mut j := i + 1
      while j < n && a[j]!.c == 'x' && !a[j]!.nl do j := j + 1
      if j > i + 1 && j < n && a[j]!.c == '{' && !a[j]!.nl then
        let mut k := j + 1
        let mut v := 0
        let mut digits := 0
        while k < n && a[k]!.c.isHexDigit && !a[k]!.nl do
          -- a value above U+10FFFF stays above it
          v := min (v * 16 + hexVal a[k]!.c) 0x110000
          digits := digits + 1
          k := k + 1
        if digits == 0 || k ≥ n || a[k]!.c != '}' || a[k]!.nl then
          throw "escape sequence \\x{ is not closed by hexadecimal digits and }"
        unless isXmlCharCode v do
          throw s!"escape sequence gives #x{String.ofList (Nat.toDigits 16 v)}, which is not an XML character"
        out := out.push ⟨Char.ofNat v, false⟩
        i := k + 1
      else
        out := out.push x
        i := i + 1
    else
      out := out.push x
      i := i + 1
  return out

/-- A.2.2 to A.2.4 in order. -/
def preprocess (s : String) : Except String (Array LC) :=
  interpretEscapes (normalizeNewlines s)

/-! ## A.2.5: tokens -/

/-- A token of A.2.5. `word` is an NCName (a keyword or an identifier);
`quoted` is set for `\NCName`, which is always an identifier. `sym` is one
of the literal terminals `{ } ( ) [ ] = |= &= | & , ? * + - ~ >>`. -/
inductive Tok where
  | word (s : String) (quoted : Bool)
  | cname (pfx lname : String)
  | nsName (pfx : String)
  | lit (s : String)
  | doc (s : String)
  | sym (s : String)
deriving Repr, BEq, Inhabited

/-- The keywords of §2. -/
def keywords : List String :=
  ["attribute", "default", "datatypes", "div", "element", "empty", "external",
   "grammar", "include", "inherit", "list", "mixed", "namespace", "notAllowed",
   "parent", "start", "string", "text", "token"]

def isKeyword (s : String) : Bool := keywords.contains s

/-- The `separator` characters of A.2.5 (a `#xD` from an escape is not one). -/
def isSepChar (x : LC) : Bool :=
  x.nl || x.c == ' ' || x.c == '\t' || x.c == '\n'

/-- End of a line: a newline marker or a `#xA` character. -/
def isLineEnd (x : LC) : Bool := x.nl || x.c == '\n'

/-- The end of the NCName that starts at `i` (`isNCNameChar4` of
`RelaxNG.Names`, Namespaces in XML 1999 with XML 1.0 Fourth Edition
classes). -/
def ncNameEnd (a : Array LC) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < a.size && !a[j]!.nl && isNCNameChar4 a[j]!.c && a[j]!.c != ':' do j := j + 1
  return j

def ncStart (x : LC) : Bool := !x.nl && (isLetter4 x.c || x.c == '_')

def sliceStr (a : Array LC) (i j : Nat) : String := Id.run do
  let mut s := ""
  for k in [i:j] do s := s.push a[k]!.c
  return s

/-- A `documentationLine` that starts at `i` (at its `##`): its content and
the position after it (before the line end). -/
def docLine (a : Array LC) (i : Nat) : String × Nat := Id.run do
  let mut j := i + 2
  while j < a.size && !a[j]!.nl && a[j]!.c == '#' do j := j + 1
  if j < a.size && !a[j]!.nl && a[j]!.c == ' ' then j := j + 1
  let st := j
  while j < a.size && !isLineEnd a[j]! do j := j + 1
  return (sliceStr a st j, j)

/-- Is there `##` at `i`? -/
def docAt (a : Array LC) (i : Nat) : Bool :=
  i + 1 < a.size && a[i]!.c == '#' && !a[i]!.nl && a[i+1]!.c == '#' && !a[i+1]!.nl

/-- A.2.5: the token sequence. -/
def lex (a : Array LC) : Except String (Array Tok) := do
  let n := a.size
  let mut out : Array Tok := #[]
  let mut i := 0
  while i < n do
    let x := a[i]!
    if isSepChar x then
      i := i + 1
    else if x.c == '#' then
      if docAt a i then
        -- documentation, with its continuation lines
        let (s0, j0) := docLine a i
        let mut s := s0
        let mut j := j0
        let mut more := true
        while more do
          more := false
          if j < n && isLineEnd a[j]! then
            let mut k := j + 1
            while k < n && !a[k]!.nl && (a[k]!.c == ' ' || a[k]!.c == '\t') do k := k + 1
            if docAt a k then
              let (s1, j1) := docLine a k
              s := s ++ "\n" ++ s1
              j := j1
              more := true
        out := out.push (.doc s)
        i := j
      else
        -- a comment: `#` to the end of the line
        let mut j := i + 1
        while j < n && !isLineEnd a[j]! do j := j + 1
        i := j
    else if x.c == '"' || x.c == '\'' then
      let q := x.c
      let triple := i + 2 < n && a[i+1]!.c == q && !a[i+1]!.nl && a[i+2]!.c == q && !a[i+2]!.nl
      if triple then
        let mut j := i + 3
        let mut s := ""
        let mut closed := false
        while !closed && j < n do
          if j + 2 < n && a[j]!.c == q && !a[j]!.nl && a[j+1]!.c == q && !a[j+1]!.nl &&
              a[j+2]!.c == q && !a[j+2]!.nl then
            closed := true
            j := j + 3
          else
            s := s.push a[j]!.c
            j := j + 1
        unless closed do throw "literal in three quotes is not closed"
        out := out.push (.lit s)
        i := j
      else
        let mut j := i + 1
        let mut s := ""
        let mut closed := false
        while !closed && j < n do
          let y := a[j]!
          if y.nl then throw "a newline in a literal delimited by one quote"
          if y.c == q then
            closed := true
          else
            s := s.push y.c
          j := j + 1
        unless closed do throw "literal is not closed"
        out := out.push (.lit s)
        i := j
    else if x.c == '\\' then
      if i + 1 < n && ncStart a[i+1]! then
        let j := ncNameEnd a (i + 1)
        out := out.push (.word (sliceStr a (i + 1) j) true)
        i := j
      else throw "\\ that starts neither an escape nor a quoted identifier"
    else if ncStart x then
      let j := ncNameEnd a i
      let w := sliceStr a i j
      if j + 1 < n && a[j]!.c == ':' && !a[j]!.nl && a[j+1]!.c == '*' && !a[j+1]!.nl then
        out := out.push (.nsName w)
        i := j + 2
      else if j + 1 < n && a[j]!.c == ':' && !a[j]!.nl && ncStart a[j+1]! then
        let k := ncNameEnd a (j + 1)
        out := out.push (.cname w (sliceStr a (j + 1) k))
        i := k
      else
        out := out.push (.word w false)
        i := j
    else
      let two := if i + 1 < n && !a[i+1]!.nl then String.ofList [x.c, a[i+1]!.c] else ""
      if two == "|=" || two == "&=" || two == ">>" then
        out := out.push (.sym two)
        i := i + 2
      else if "{}()[]=|&,?*+-~".toList.contains x.c then
        out := out.push (.sym (String.singleton x.c))
        i := i + 1
      else throw s!"unexpected character U+{String.ofList (Nat.toDigits 16 x.c.toNat)}"
  return out

/-! ## The translation: XML fragments -/

/-- An element of the translation, with names as (namespace URI, local
name). Attributes are (namespace URI, local name, value). -/
inductive X where
  | el (ns : String) (lname : String) (attrs : List (String × String × String)) (kids : List X)
  | txt (s : String)
deriving Repr, Inhabited

/-- A RELAX NG element `<foo x> y </foo>` of A.1. -/
def rng (l : String) (attrs : List (String × String)) (kids : List X) : X :=
  .el rngNs l (attrs.map (fun (k, v) => ("", k, v))) kids

/-- The value of `annotations`: attributes and initial elements. -/
structure Anno where
  attrs : List (String × String × String) := []
  elems : List X := []
deriving Inhabited

def Anno.isEmpty (a : Anno) : Bool := a.attrs.isEmpty && a.elems.isEmpty

/-- `applyAnnotations` of A.1, with the exception of §5.1: the annotation
elements of an element that cannot have element children (`value`,
`param`, `name`) follow it. -/
def applyAnno (a : Anno) : X → List X
  | .el ns l as ks =>
    if ns == rngNs && (l == "value" || l == "param" || l == "name") then
      .el ns l (a.attrs ++ as) ks :: a.elems
    else [.el ns l (a.attrs ++ as) (a.elems ++ ks)]
  | x => x :: a.elems

/-- `applyAnnotationsGroup` of A.1. -/
def applyAnnoGroup (a : Anno) (xs : List X) : List X :=
  if a.isEmpty then xs else applyAnno a (rng "group" [] xs)

/-- `applyAnnotationsChoice` of A.1. -/
def applyAnnoChoice (a : Anno) (xs : List X) : List X :=
  if a.isEmpty then xs else applyAnno a (rng "choice" [] xs)

/-! ## A.1: the environment -/

/-- The environment of A.1. A namespace prefix maps to a URI or to
`inherit` (`none`); `dflt` is `none` when no default namespace is
declared, which `lookupDefault` reads as `inherit`. -/
structure Env where
  ns : List (String × Option String) := []
  dflt : Option (Option String) := none
  dt : List (String × String) := []
deriving Inhabited

/-- `lookupPrefix`: `xml` is predeclared. -/
def Env.lookupPrefix (e : Env) (p : String) : Except String (Option String) :=
  match e.ns.lookup p with
  | some u => .ok u
  | none => if p == "xml" then .ok (some xmlUri) else .error s!"namespace prefix {p} is not declared"

def Env.lookupDefault (e : Env) : Option String := e.dflt.getD none

/-- `lookupDatatypePrefix`: `xsd` is predeclared. -/
def Env.lookupDatatypePrefix (e : Env) (p : String) : Except String String :=
  match e.dt.lookup p with
  | some u => .ok u
  | none => if p == "xsd" then .ok xsdLibUri else .error s!"datatype prefix {p} is not declared"

/-- `makeNsAttribute`. -/
def nsAttr : Option String → List (String × String)
  | some u => [("ns", u)]
  | none => []

/-! ## A.1: the parser -/

structure PS where
  toks : Array Tok
  pos : Nat
  env : Env

abbrev P := StateT PS (Except String)

def liftExc {α : Type} (e : Except String α) : P α := StateT.lift e

def peekAt (k : Nat) : P (Option Tok) := do
  let s ← get
  return s.toks[s.pos + k]?

def peek : P (Option Tok) := peekAt 0

def advance : P Unit := modify (fun s => { s with pos := s.pos + 1 })

def isSym (t : Option Tok) (x : String) : Bool := t == some (.sym x)

def atSym (x : String) : P Bool := do return isSym (← peek) x

def expectSym (x : String) : P Unit := do
  if ← atSym x then advance else
    let t ← peek
    throw s!"expected {x}, found {repr t}"

/-- An unquoted keyword. -/
def isKw (t : Option Tok) (k : String) : Bool := t == some (.word k false)

/-- `identifier`: an NCName that is not a keyword, or a quoted one. -/
def identOf : Option Tok → Option String
  | some (.word s q) => if q || !isKeyword s then some s else none
  | _ => none

/-- `identifierOrKeyword`. -/
def identOrKwOf : Option Tok → Option String
  | some (.word s _) => some s
  | _ => none

/-- `literal`: segments joined by `~`. -/
def pLiteral : P String := do
  match ← peek with
  | some (.lit s) =>
    advance
    let mut v := s
    while ← atSym "~" do
      advance
      match ← peek with
      | some (.lit t) => advance; v := v ++ t
      | t => throw s!"expected a literal after ~, found {repr t}"
    return v
  | t => throw s!"expected a literal, found {repr t}"

def isLit : Option Tok → Bool
  | some (.lit _) => true
  | _ => false

/-- `prefixedName` (constraint "annotation inherit"). -/
def prefixedName (p l : String) : P (String × String) := do
  match ← liftExc ((← get).env.lookupPrefix p) with
  | some u => return (u, l)
  | none => throw s!"prefix {p} of {p}:{l} is bound to inherit"

/-- Add an attribute, with the constraint "duplicate attributes". -/
def addAttr (as : List (String × String × String)) (a : String × String × String) :
    Except String (List (String × String × String)) :=
  if as.any (fun b => b.1 == a.1 && b.2.1 == a.2.1) then
    .error s!"duplicate annotation attribute {a.2.1}"
  else .ok (as ++ [a])

/-- `anyAttributeName` (constraint "xmlns namespace URI"; an unqualified
`xmlns` is a namespace declaration in the XML data model, not an
attribute). -/
def pAnyAttrName : P (String × String) := do
  match ← peek with
  | some (.word s _) =>
    advance
    if s == "xmlns" then throw "an annotation attribute cannot be named xmlns"
    return ("", s)
  | some (.cname p l) =>
    advance
    let n ← prefixedName p l
    if n.1 == xmlnsUri then throw "an annotation attribute is in the xmlns namespace"
    return n
  | t => throw s!"expected an attribute name, found {repr t}"

/-- `foreignAttributeName` (constraints "unqualified name", "RELAX NG
namespace URI", "xmlns namespace URI"). -/
def pForeignAttrName : P (String × String) := do
  match ← peek with
  | some (.cname p l) =>
    advance
    let n ← prefixedName p l
    if n.1 == "" then throw s!"annotation attribute {p}:{l} has no namespace"
    if n.1 == rngNs then throw s!"annotation attribute {p}:{l} is in the RELAX NG namespace"
    if n.1 == xmlnsUri then throw s!"annotation attribute {p}:{l} is in the xmlns namespace"
    return n
  | t => throw s!"expected a prefixed attribute name, found {repr t}"

/-- Can an annotation element start here (a name followed by `[`)? -/
def annoElemAhead (notKw : Bool) : P Bool := do
  let t ← peek
  let nameOk := match t with
    | some (.word s q) => !notKw || q || !isKeyword s
    | some (.cname ..) => true
    | _ => false
  return nameOk && isSym (← peekAt 1) "["

/-- An element name of an annotation; `foreign` forbids the RELAX NG
namespace (`foreignElementName`), otherwise any name (`anyElementName`). -/
def pElemName (foreign : Bool) : P (String × String) := do
  match ← peek with
  | some (.word s _) => advance; return ("", s)
  | some (.cname p l) =>
    advance
    let n ← prefixedName p l
    if foreign && n.1 == rngNs then throw s!"annotation element {p}:{l} is in the RELAX NG namespace"
    return n
  | t => throw s!"expected an element name, found {repr t}"

/-- `annotationAttributesContent` and its nested elements. -/
def pAttrsContent : Nat → P (List (String × String × String) × List X)
  | 0 => throw "annotation nested too deeply"
  | f + 1 => do
    expectSym "["
    let mut as : List (String × String × String) := []
    let mut go := true
    while go do
      let t ← peek
      let named := match t with | some (.word ..) | some (.cname ..) => true | _ => false
      if named && isSym (← peekAt 1) "=" then
        let n ← pAnyAttrName
        expectSym "="
        let v ← pLiteral
        as ← liftExc (addAttr as (n.1, n.2, v))
      else go := false
    let mut ks : Array X := #[]
    let mut go2 := true
    while go2 do
      let t ← peek
      if isLit t then
        ks := ks.push (.txt (← pLiteral))
      else if ← annoElemAhead false then
        let n ← pElemName false
        let (as', ks') ← pAttrsContent f
        ks := ks.push (.el n.1 n.2 as' ks')
      else go2 := false
    expectSym "]"
    return (as, ks.toList)

/-- `annotationElement` (a `foreignElementName`). -/
def pAnnoElement (f : Nat) : P X := do
  let n ← pElemName true
  let (as, ks) ← pAttrsContent f
  return .el n.1 n.2 as ks

/-- `annotations`: documentation, then `[ attributes elements ]`. -/
def pAnnotations (f : Nat) : P Anno := do
  let mut docs : Array X := #[]
  let mut go := true
  while go do
    match ← peek with
    | some (.doc s) =>
      advance
      docs := docs.push (.el compatNs "documentation" [] (if s.isEmpty then [] else [.txt s]))
    | _ => go := false
  if ← atSym "[" then
    advance
    let mut as : List (String × String × String) := []
    let mut go2 := true
    while go2 do
      let t ← peek
      if (match t with | some (.cname ..) => true | _ => false) && isSym (← peekAt 1) "=" then
        let n ← pForeignAttrName
        expectSym "="
        let v ← pLiteral
        as ← liftExc (addAttr as (n.1, n.2, v))
      else go2 := false
    let mut es : Array X := #[]
    let mut go3 := true
    while go3 do
      if ← annoElemAhead false then es := es.push (← pAnnoElement f)
      else go3 := false
    expectSym "]"
    return { attrs := as, elems := docs.toList ++ es.toList }
  return { elems := docs.toList }

/-- `followAnnotations`. -/
def pFollow (f : Nat) : P (List X) := do
  let mut out : Array X := #[]
  while ← atSym ">>" do
    advance
    out := out.push (← pAnnoElement f)
  return out.toList

/-- `assignOp`. -/
def pAssign : P (List (String × String)) := do
  match ← peek with
  | some (.sym "=") => advance; return []
  | some (.sym "|=") => advance; return [("combine", "choice")]
  | some (.sym "&=") => advance; return [("combine", "interleave")]
  | t => throw s!"expected =, |= or &=, found {repr t}"

/-- `anyURILiteral` (constraint "any URI": §3 and §4.5 of RELAX NG). -/
def pUriLiteral : P String := do
  let u ← pLiteral
  if u.contains '#' then throw s!"URI {u} has a fragment identifier"
  unless escapesOk u.toList do throw s!"{u} is not a URI reference"
  return u

/-- `optInherit`. -/
def pInherit : P (List (String × String)) := do
  if isKw (← peek) "inherit" then
    advance
    expectSym "="
    match identOrKwOf (← peek) with
    | some p =>
      advance
      return nsAttr (← liftExc ((← get).env.lookupPrefix p))
    | none => throw "expected a prefix after inherit ="
  return nsAttr (← get).env.lookupDefault

/-- A particle: `annotatedPrimary`, a `repeatedPrimary` with its following
annotations, or an `annotatedDataExcept` (a whole pattern by itself). -/
inductive Particle where
  | plain (xs : List X)
  | rep (e : X) (follow : List X)
  | dataExcept (xs : List X)

/-- The elements of a particle that is one operand of `|`, `,` or `&`. -/
def Particle.operand : Particle → Except String (List X)
  | .plain xs => .ok xs
  | .rep e fs => .ok (e :: fs)
  | .dataExcept _ => .error "datatypeName - pattern must be enclosed in parentheses here"

/-- `innerParticle(anno)` for a particle that is the whole pattern. -/
def Particle.single (a : Anno) : Particle → List X
  | .plain xs => applyAnnoGroup a xs
  | .rep e fs => applyAnno a e ++ fs
  | .dataExcept xs => applyAnnoGroup a xs

def opName : String → Option String
  | "|" => some "choice"
  | "," => some "group"
  | "&" => some "interleave"
  | _ => none

mutual

/-- `innerPattern(anno)`. -/
def pInnerPattern : Nat → Anno → P (List X)
  | 0, _ => throw "pattern nested too deeply"
  | f + 1, a => do
    let first ← pParticle f
    let t ← peek
    let op := match t with
      | some (.sym s) => opName s
      | _ => none
    match op with
    | none => return first.single a
    | some el =>
      let opTok := match t with | some (.sym s) => s | _ => ""
      let mut items := (← liftExc first.operand)
      while (← peek) == some (.sym opTok) do
        advance
        let p ← pParticle f
        items := items ++ (← liftExc p.operand)
      if let some (.sym s) ← peek then
        if (opName s).isSome then
          throw s!"operators {opTok} and {s} are mixed without parentheses"
      return applyAnno a (rng el [] items)

/-- `particle`: a primary with annotations, then a repetition. -/
def pParticle : Nat → P Particle
  | 0 => throw "pattern nested too deeply"
  | f + 1 => do
    let (lead, de) ← pLeadPrimary f true
    let fol ← pFollow f
    if de then
      if let some (.sym s) ← peek then
        if s == "*" || s == "+" || s == "?" then
          throw "datatypeName - pattern cannot be repeated without parentheses"
      return .dataExcept (lead ++ fol)
    match ← peek with
    | some (.sym "*") => advance; return .rep (rng "zeroOrMore" [] (lead ++ fol)) (← pFollow f)
    | some (.sym "+") => advance; return .rep (rng "oneOrMore" [] (lead ++ fol)) (← pFollow f)
    | some (.sym "?") => advance; return .rep (rng "optional" [] (lead ++ fol)) (← pFollow f)
    | _ => return .plain (lead ++ fol)

/-- `leadAnnotatedPrimary` and, when `allowDE`, `leadAnnotatedDataExcept`.
The flag of the result says that a `datatypeName - pattern` was read. -/
def pLeadPrimary : Nat → Bool → P (List X × Bool)
  | 0, _ => throw "pattern nested too deeply"
  | f + 1, allowDE => do
    let a ← pAnnotations f
    if ← atSym "(" then
      advance
      let xs ← pInnerPattern f a
      expectSym ")"
      return (xs, false)
    let t ← peek
    let env := (← get).env
    -- datatypeName
    let dtn : Option (String × String) ← match t with
      | some (.word "string" false) => pure (some ("", "string"))
      | some (.word "token" false) => pure (some ("", "token"))
      | some (.cname p l) => do
        let lib ← liftExc (env.lookupDatatypePrefix p)
        pure (some (lib, l))
      | _ => pure none
    match dtn with
    | some (lib, ty) =>
      advance
      let dattrs := [("datatypeLibrary", lib), ("type", ty)]
      if isLit (← peek) then
        let v ← pLiteral
        return (applyAnno a (rng "value" dattrs (if v.isEmpty then [] else [.txt v])), false)
      let mut params : Array X := #[]
      if ← atSym "{" then
        advance
        while !(← atSym "}") do
          let pa ← pAnnotations f
          match identOrKwOf (← peek) with
          | some pn =>
            advance
            expectSym "="
            let v ← pLiteral
            for x in applyAnno pa (rng "param" [("name", pn)] (if v.isEmpty then [] else [.txt v])) do
              params := params.push x
          | none => throw s!"expected a parameter name, found {repr (← peek)}"
        expectSym "}"
      if (← atSym "-") && allowDE then
        advance
        let (ex, _) ← pLeadPrimary f false
        return (applyAnno a (rng "data" dattrs (params.toList ++ [rng "except" [] ex])), true)
      return (applyAnno a (rng "data" dattrs params.toList), false)
    | none =>
    match t with
    | some (.lit _) =>
      let v ← pLiteral
      return (applyAnno a (rng "value" [] (if v.isEmpty then [] else [.txt v])), false)
    | some (.word "element" false) | some (.word "attribute" false) =>
      advance
      let isElem := t == some (.word "element" false)
      let nc ← pNameClass f isElem
      expectSym "{"
      let body ← pInnerPattern f {}
      expectSym "}"
      return (applyAnno a (rng (if isElem then "element" else "attribute") [] (nc ++ body)), false)
    | some (.word "mixed" false) | some (.word "list" false) =>
      advance
      expectSym "{"
      let body ← pInnerPattern f {}
      expectSym "}"
      return (applyAnno a (rng (if t == some (.word "mixed" false) then "mixed" else "list") [] body), false)
    | some (.word "empty" false) => advance; return (applyAnno a (rng "empty" [] []), false)
    | some (.word "notAllowed" false) => advance; return (applyAnno a (rng "notAllowed" [] []), false)
    | some (.word "text" false) => advance; return (applyAnno a (rng "text" [] []), false)
    | some (.word "parent" false) =>
      advance
      match identOf (← peek) with
      | some r => advance; return (applyAnno a (rng "parentRef" [("name", r)] []), false)
      | none => throw "expected an identifier after parent"
    | some (.word "grammar" false) =>
      advance
      expectSym "{"
      let body ← pGrammar f false
      expectSym "}"
      return (applyAnno a (rng "grammar" [] body), false)
    | some (.word "external" false) =>
      advance
      let u ← pUriLiteral
      let inh ← pInherit
      return (applyAnno a (rng "externalRef" ([("href", u)] ++ inh) []), false)
    | _ =>
      match identOf t with
      | some r => advance; return (applyAnno a (rng "ref" [("name", r)] []), false)
      | none => throw s!"expected a pattern, found {repr t}"

/-- `nameClass(isElem)`: `innerNameClass(anno := ())`. -/
def pNameClass : Nat → Bool → P (List X)
  | 0, _ => throw "name class nested too deeply"
  | f + 1, isElem => pInnerNameClass f isElem {}

/-- `innerNameClass(isElem, anno)`. -/
def pInnerNameClass : Nat → Bool → Anno → P (List X)
  | 0, _, _ => throw "name class nested too deeply"
  | f + 1, isElem, a => do
    let (first, exc) ← pNCOperand f isElem
    if exc then
      if ← atSym "|" then throw "a name class with - must be enclosed in parentheses here"
      return applyAnnoChoice a first
    if !(← atSym "|") then return applyAnnoChoice a first
    let mut items := first
    while ← atSym "|" do
      advance
      let (x, e) ← pNCOperand f isElem
      if e then throw "a name class with - must be enclosed in parentheses here"
      items := items ++ x
    if ← atSym "-" then throw "a name class choice cannot be followed by -"
    return applyAnno a (rng "choice" [] items)

/-- An operand of a name class: `annotatedSimpleNameClass` or
`annotatedExceptNameClass` (flag set). -/
def pNCOperand : Nat → Bool → P (List X × Bool)
  | 0, _ => throw "name class nested too deeply"
  | f + 1, isElem => do
    let a ← pAnnotations f
    if ← atSym "(" then
      advance
      let xs ← pInnerNameClass f isElem a
      expectSym ")"
      return (xs ++ (← pFollow f), false)
    let env := (← get).env
    let t ← peek
    let (e, exc) ← match t with
      | some (.nsName p) => do
        advance
        let u ← liftExc (env.lookupPrefix p)
        if ← atSym "-" then
          advance
          let ex ← pLeadSimpleNC f isElem
          pure (rng "nsName" (nsAttr u) [rng "except" [] ex], true)
        else pure (rng "nsName" (nsAttr u) [], false)
      | some (.sym "*") => do
        advance
        if ← atSym "-" then
          advance
          let ex ← pLeadSimpleNC f isElem
          pure (rng "anyName" [] [rng "except" [] ex], true)
        else pure (rng "anyName" [] [], false)
      | some (.cname p l) => do
        advance
        let u ← liftExc (env.lookupPrefix p)
        pure (rng "name" (nsAttr u) [.txt l], false)
      | some (.word s _) => do
        advance
        let u := if isElem then env.lookupDefault else some ""
        pure (rng "name" (nsAttr u) [.txt s], false)
      | _ => throw s!"expected a name class, found {repr t}"
    let fol ← pFollow f
    return (applyAnno a e ++ fol, exc)

/-- `leadAnnotatedSimpleNameClass`: the operand of `-` in a name class. -/
def pLeadSimpleNC : Nat → Bool → P (List X)
  | 0, _ => throw "name class nested too deeply"
  | f + 1, isElem => do
    let a ← pAnnotations f
    if ← atSym "(" then
      advance
      let xs ← pInnerNameClass f isElem a
      expectSym ")"
      return xs
    let env := (← get).env
    let t ← peek
    let e ← match t with
      | some (.nsName p) => do
        advance
        pure (rng "nsName" (nsAttr (← liftExc (env.lookupPrefix p))) [])
      | some (.sym "*") => do advance; pure (rng "anyName" [] [])
      | some (.cname p l) => do
        advance
        pure (rng "name" (nsAttr (← liftExc (env.lookupPrefix p))) [.txt l])
      | some (.word s _) => do
        advance
        pure (rng "name" (nsAttr (if isElem then env.lookupDefault else some "")) [.txt s])
      | _ => throw s!"expected a name class, found {repr t}"
    return applyAnno a e

/-- `grammar` (or `includeBody` when `inInclude`): the members up to a `}`
or the end of the tokens. -/
def pGrammar : Nat → Bool → P (List X)
  | 0, _ => throw "grammar nested too deeply"
  | f + 1, inInclude => do
    let mut out : Array X := #[]
    let mut go := true
    while go do
      let t ← peek
      if t.isNone || isSym t "}" then
        go := false
      else if ← annoElemAhead true then
        out := out.push (← pAnnoElement f)
      else
        let a ← pAnnotations f
        let t ← peek
        let comp ← match t with
          | some (.word "start" false) => do
            advance
            let op ← pAssign
            let p ← pInnerPattern f {}
            pure (rng "start" op p)
          | some (.word "div" false) => do
            advance
            expectSym "{"
            let body ← pGrammar f inInclude
            expectSym "}"
            pure (rng "div" [] body)
          | some (.word "include" false) => do
            if inInclude then throw "include inside include"
            advance
            let u ← pUriLiteral
            let inh ← pInherit
            let mut body : List X := []
            if ← atSym "{" then
              advance
              body ← pGrammar f true
              expectSym "}"
            pure (rng "include" ([("href", u)] ++ inh) body)
          | _ =>
            match identOf t with
            | some n => do
              advance
              let op ← pAssign
              let p ← pInnerPattern f {}
              pure (rng "define" ([("name", n)] ++ op) p)
            | none => throw s!"expected a grammar component, found {repr t}"
        for x in applyAnno a comp do out := out.push x
    return out.toList

end

/-! ## A.1: declarations and the top level -/

/-- `decl`s of the preamble, with the constraints "valid prefix", "xml
prefix", "xml namespace URI", "xsd prefix", "datatypes URI" and
"duplicate declaration". -/
def pPreamble : P Unit := do
  let mut go := true
  while go do
    let t ← peek
    let env := (← get).env
    if isKw t "namespace" || isKw t "default" then
      let isDefault := isKw t "default"
      advance
      if isDefault then
        unless isKw (← peek) "namespace" do throw "expected namespace after default"
        advance
      let pfx : Option String ← match identOrKwOf (← peek) with
        | some p => do advance; pure (some p)
        | none => pure none
      if !isDefault && pfx.isNone then throw "expected a prefix after namespace"
      expectSym "="
      let uri : Option String ←
        if isKw (← peek) "inherit" then do advance; pure none
        else do pure (some (← pLiteral))
      if let some p := pfx then
        if p == "xmlns" then throw "xmlns cannot be declared as a prefix"
        if p == "xml" && uri != some xmlUri then throw "the xml prefix must be bound to its namespace"
        if p != "xml" && uri == some xmlUri then throw s!"prefix {p} cannot be bound to the xml namespace"
        if (env.ns.lookup p).isSome then throw s!"duplicate declaration of prefix {p}"
      else if uri == some xmlUri then throw "the default namespace cannot be the xml namespace"
      if isDefault && env.dflt.isSome then throw "duplicate default namespace declaration"
      let ns' := match pfx with | some p => env.ns ++ [(p, uri)] | none => env.ns
      let dflt' := if isDefault then some uri else env.dflt
      modify (fun s => { s with env := { env with ns := ns', dflt := dflt' } })
    else if isKw t "datatypes" then
      advance
      let p ← match identOrKwOf (← peek) with
        | some p => do advance; pure p
        | none => throw "expected a prefix after datatypes"
      expectSym "="
      let u ← pLiteral
      if p == "xsd" && u != xsdLibUri then throw "the xsd prefix must be bound to the XML Schema datatypes URI"
      liftExc (checkLibUri u)
      if (env.dt.lookup p).isSome then throw s!"duplicate declaration of datatypes prefix {p}"
      modify (fun s => { s with env := { env with dt := env.dt ++ [(p, u)] } })
    else go := false

/-- Is the body a `grammar` (and not a `pattern`)? Documentation and one
`[ … ]` annotation are skipped; then a component, an annotation element or
the end of the text starts a grammar. -/
def grammarAhead : P Bool := do
  let s ← get
  let ts := s.toks
  let mut i := s.pos
  while (match ts[i]? with | some (.doc _) => true | _ => false) do i := i + 1
  let mut annotated := false
  if ts[i]? == some (.sym "[") then
    annotated := true
    let mut depth := 0
    let mut fin := false
    while !fin && i < ts.size do
      if ts[i]? == some (.sym "[") then depth := depth + 1
      if ts[i]? == some (.sym "]") then
        depth := depth - 1
        if depth == 0 then fin := true
      i := i + 1
  let t := ts[i]?
  let t1 := ts[i + 1]?
  if t.isNone then return true
  if isKw t "start" || isKw t "div" || isKw t "include" then return true
  let named := (identOf t).isSome || (match t with | some (.cname ..) => true | _ => false)
  if named && (isSym t1 "=" || isSym t1 "|=" || isSym t1 "&=") then return true
  if !annotated && named && isSym t1 "[" then return true
  return false

/-- The prefix → URI map written on the document element: the declared
namespace prefixes except `xml` and those bound to `inherit` or `""`, and
one prefix for the compatibility annotations namespace unless a declared
prefix names it. -/
def declsOf (env : Env) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  for (p, u) in env.ns do
    if let some uri := u then
      if p != "xml" && uri != "" then out := out ++ [(p, uri)]
  if !out.any (fun b => b.2 == compatNs) then
    let mut k := 0
    let mut p := "a"
    while env.ns.any (fun b => b.1 == p) do
      k := k + 1
      p := s!"a{k}"
    out := out ++ [(p, compatNs)]
  return out

/-- The prefix for a namespace URI. -/
def pfxOf (decls : List (String × String)) (uri : String) : Option String :=
  if uri == xmlUri then some "xml" else (decls.find? (fun b => b.2 == uri)).map (·.1)

mutual

/-- Write an element of the translation as an XML node. `dflt` is the
default namespace in scope. -/
def render (decls : List (String × String)) (dflt : String) : X → Node
  | .txt s => .text s
  | .el uri l as ks =>
    let (tag, own, dflt') :=
      if uri == dflt then (l, ([] : List Attribute), dflt)
      else if uri == "" || uri == rngNs then (l, [⟨"xmlns", uri⟩], uri)
      else match pfxOf decls uri with
        | some p => (p ++ ":" ++ l, [], dflt)
        | none => ("ns0:" ++ l, [⟨"xmlns:ns0", uri⟩], dflt)
    let atts := as.map (fun (u, ln, v) =>
      if u == "" then (⟨ln, v⟩ : Attribute)
      else match pfxOf decls u with
        | some p => ⟨p ++ ":" ++ ln, v⟩
        | none => ⟨"ns1:" ++ ln, v⟩)
    let extra := if as.any (fun a => a.1 != "" && (pfxOf decls a.1).isNone) then
      (as.find? (fun a => a.1 != "" && (pfxOf decls a.1).isNone)).toList.map
        (fun a => (⟨"xmlns:ns1", a.1⟩ : Attribute))
      else []
    .element tag (own ++ extra ++ atts) (renderAll decls dflt' [] ks)

/-- `render` over siblings; a tail call per sibling. -/
def renderAll (decls : List (String × String)) (dflt : String) (acc : List Node) :
    List X → List Node
  | [] => acc.reverse
  | x :: xs => renderAll decls dflt (render decls dflt x :: acc) xs

end

/-- Translate a schema in the compact syntax (the text of one file) to the
document element of its XML syntax. -/
def translate (txt : String) : Except String Node := do
  let a ← preprocess txt
  let ts ← lex a
  let body : P X := do
    pPreamble
    let fuel := 4 * ts.size + 8
    if ← grammarAhead then
      let g ← pGrammar fuel false
      unless (← peek).isNone do throw s!"unexpected {repr (← peek)}"
      return rng "grammar" [] g
    else
      let xs ← pInnerPattern fuel {}
      unless (← peek).isNone do throw s!"unexpected {repr (← peek)}"
      match xs with
      | [x] => return x
      | _ => throw "the top-level pattern translates to more than one element"
  let (x, st) ← body.run { toks := ts, pos := 0, env := {} }
  let decls := declsOf st.env
  match render decls "" x with
  | .element t as ks =>
    let nsDecls := decls.map (fun (p, u) => (⟨"xmlns:" ++ p, u⟩ : Attribute))
    return .element t (as ++ nsDecls) ks
  | n => return n

/-! ## Writing XML text -/

def escText (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '>' => acc ++ "&gt;"
    | '\r' => acc ++ "&#13;" | c => acc.push c) ""

def escAttr (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '&' => acc ++ "&amp;" | '<' => acc ++ "&lt;" | '"' => acc ++ "&quot;"
    | '\t' => acc ++ "&#9;" | '\n' => acc ++ "&#10;" | '\r' => acc ++ "&#13;"
    | c => acc.push c) ""

mutual

/-- Append the XML text of a node to `acc`. -/
def serNode (acc : String) : Node → String
  | .text t | .cdata t => acc ++ escText t
  | .element t attrs kids =>
    let open_ := attrs.foldl (fun a at_ => a ++ " " ++ at_.name ++ "=\"" ++ escAttr at_.value ++ "\"")
      (acc ++ "<" ++ t)
    serNodes (open_ ++ ">") kids ++ "</" ++ t ++ ">"
  | _ => acc

/-- `serNode` over siblings; a tail call per sibling. -/
def serNodes (acc : String) : List Node → String
  | [] => acc
  | n :: ns => serNodes (serNode acc n) ns

end

/-- The XML syntax of a compact schema, as text. -/
def translateToXml (txt : String) : Except String String := do
  return serNode "" (← translate txt)

/-! ## §6.1 and §6.3 -/

/-- §6.1: simplify a schema in the compact syntax. `resolve` gives the text
of the compact schemas that `include` and `external` name (by their URI
resolved against `base`); each is translated before it is read. -/
def simplifyCompact (resolve : String → Option String) (base : String) (txt : String) :
    Except String Grammar := do
  let root ← translate txt
  let resolveXml := fun (u : String) => (resolve u).bind (fun t => (translateToXml t).toOption)
  simplifyNode resolveXml base root

/-- §6.2: a text form of a schema after pass 1 and pass 2 of the
simplifier (§4.1 to §4.8 and §4.10; `include` and `externalRef` are
replaced by the documents they name, as §6.2 compares the referenced
documents and not the `href`s), with §4.9 applied: `name`, `nsName` and
`value` carry their `ns` attribute, inherited when absent, and no other
element carries one. Attributes are sorted by name; the context (namespace
declarations, base URI) is left out. `inh` is the inherited `ns`. -/
def strictKey : Nat → String → RE → String
  | 0, _, _ => "!"
  | f + 1, inh, .mk n as _ t ks =>
    let nsv := (as.lookup "ns").getD inh
    let as1 := as.filter (·.1 != "ns")
    let as2 := if n == "name" || n == "nsName" || n == "value" then as1 ++ [("ns", nsv)] else as1
    let sorted := (as2.toArray.qsort (fun a b => a.1 < b.1)).toList
    let kids := ks.foldl (fun acc k => acc ++ strictKey f nsv k ++ ";") ""
    s!"({n} {sorted} {repr t} [{kids}])"

/-- §6.2: the text form of a schema in the XML syntax (`strictKey`). Two
schemas whose forms are equal are strictly equivalent, except that foreign
elements and attributes (annotations) are not compared. -/
def strictForm (resolve : String → Option String) (base : String) (root : Node) :
    Except String String := do
  let r ← readSchemaNode base root
  let r ← expand resolve 64 [base] r
  return strictKey (r.size + 1) "" r

/-- §6.2 for a compact schema: `strictForm` of its translation. -/
def strictFormCompact (resolve : String → Option String) (base : String) (txt : String) :
    Except String String := do
  let root ← translate txt
  strictForm (fun u => (resolve u).bind (fun t => (translateToXml t).toOption)) base root

/-- A pattern with the context of every `value` removed (§6.3: "the
context of elements is ignored"). -/
def eraseCx : Pattern → Pattern
  | .value dt v _ => .value dt v { ns := [] }
  | .choice a b => .choice (eraseCx a) (eraseCx b)
  | .interleave a b => .interleave (eraseCx a) (eraseCx b)
  | .group a b => .group (eraseCx a) (eraseCx b)
  | .oneOrMore p => .oneOrMore (eraseCx p)
  | .list p => .list (eraseCx p)
  | .dataExcept dt ps e => .dataExcept dt ps (eraseCx e)
  | .attribute nc p => .attribute nc (eraseCx p)
  | .element nc p => .element nc (eraseCx p)
  | .after a b => .after (eraseCx a) (eraseCx b)
  | p => p

/-- §6.3, sufficient test: the two simplified grammars are equal once the
contexts are removed. -/
def looseEq (g h : Grammar) : Bool :=
  eraseCx g.start == eraseCx h.start &&
    g.defs.map (fun (n, nc, p) => (n, nc, eraseCx p)) ==
    h.defs.map (fun (n, nc, p) => (n, nc, eraseCx p))

end L4Factoidal.RelaxNG.Compact
