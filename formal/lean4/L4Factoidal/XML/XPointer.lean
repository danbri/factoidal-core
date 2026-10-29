/-
L4Factoidal.XML.XPointer — the XPointer Framework and its element() and
xmlns() schemes, over the XML parse tree (`L4Factoidal.XML.Document`).

Specifications (each W3C Recommendation 25 March 2003):

* XPointer Framework, https://www.w3.org/TR/2003/REC-xptr-framework-20030325/
  — the pointer grammar (§3.1, `[1] Pointer` to `[8] NormalChar`), the
  shorthand pointer (§3.2), the evaluation of scheme-based pointers from
  left to right (§3.3), and the escaping of `^`, `(` and `)` (§3.1);
* XPointer element() Scheme, https://www.w3.org/TR/2003/REC-xptr-element-20030325/
  — `[1] ElementSchemeData ::= (NCName ChildSequence?) | ChildSequence`,
  `[2] ChildSequence ::= ('/' [1-9] [0-9]*)+`;
* XPointer xmlns() Scheme, https://www.w3.org/TR/2003/REC-xptr-xmlns-20030325/
  — `[1] XmlnsSchemeData ::= NCName S? '=' S? EscapedNamespaceName`; a
  part of this scheme never identifies a subresource, and binds a prefix
  for the parts to its right.

The xpointer() scheme (W3C Working Draft 19 December 2002) is an XPath
1.0 extension, so it is evaluated by the XPath engine, which sits above
this module: the caller gives it as a `SchemeHook`
(`L4Factoidal.XML.XPointerXPath.xpointerScheme`). This keeps the module
below `L4Factoidal.XPath4.XInclude`, which the XPath engine imports.

What identifies an element (Framework §3.2, "determined by"): an
attribute that the DTD declares of type `ID` (XML 1.0 §3.3.1), and
`xml:id` (xml:id 1.0, W3C Recommendation 9 September 2005, §4, value
normalized). Schema-determined IDs are not read.

Every walk over input-proportional data is a tail call (the pointer
characters, the parts, the search for an ID).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.Document

namespace L4Factoidal.XML.XPointer

open L4Factoidal.XML

/-! ## Names -/

/-- `NCName` (Namespaces in XML 1.0 §3 `[4]`): a Name with no colon. -/
def isNCName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => c != ':' && isNameStartChar c && cs.all (fun c => c != ':' && isNameChar c)

/-- `QName` (Namespaces in XML 1.0 §4 `[7]`). -/
def isQName (s : String) : Bool :=
  match s.splitOn ":" with
  | [l] => isNCName l
  | [p, l] => isNCName p && isNCName l
  | _ => false

/-! ## The pointer grammar (Framework §3.1) -/

/-- `[4] PointerPart ::= SchemeName '(' SchemeData ')'`, with the scheme
data unescaped (`^(`, `^)` and `^^` read as `(`, `)` and `^`). -/
structure Part where
  scheme : String
  data : String
deriving DecidableEq, Repr, Inhabited

/-- `[1] Pointer ::= Shorthand | SchemeBased`. -/
inductive Pointer where
  /-- `[2] Shorthand ::= NCName`. -/
  | shorthand (name : String)
  /-- `[3] SchemeBased ::= PointerPart (S? PointerPart)*`. -/
  | schemeBased (parts : List Part)
deriving DecidableEq, Repr, Inhabited

/-- `[6] SchemeData ::= EscapedData*`,
`[7] EscapedData ::= NormalChar | '^(' | '^)' | '^^' | '(' SchemeData ')'`:
read up to the `)` that closes the part. `depth` counts the unescaped
`(` that are open; `acc` holds the unescaped data in reverse. The result
is the data and the characters after the closing `)`. -/
def schemeData : List Char → Nat → List Char → Except String (String × List Char)
  | [], _, _ => .error "a pointer part has no closing parenthesis"
  | '^' :: c :: rest, d, acc =>
      if c == '(' || c == ')' || c == '^' then schemeData rest d (c :: acc)
      else .error ("'^' before '" ++ c.toString ++ "' is not an escape (Framework §3.1)")
  | ['^'], _, _ => .error "'^' at the end of the pointer"
  | '(' :: rest, d, acc => schemeData rest (d + 1) ('(' :: acc)
  | ')' :: rest, 0, acc => .ok (String.ofList acc.reverse, rest)
  | ')' :: rest, d + 1, acc => schemeData rest d (')' :: acc)
  | c :: rest, d, acc => schemeData rest d (c :: acc)

/-- Drop `[3] S` characters. -/
def dropS : List Char → List Char
  | c :: rest => if isXmlSpace c then dropS rest else c :: rest
  | [] => []

/-- The characters of a scheme name (`[5] SchemeName ::= QName`): up to
the `(`. `acc` is in reverse. -/
def schemeName : List Char → List Char → String × List Char
  | '(' :: rest, acc => (String.ofList acc.reverse, '(' :: rest)
  | c :: rest, acc => if isXmlSpace c then (String.ofList acc.reverse, c :: rest)
      else schemeName rest (c :: acc)
  | [], acc => (String.ofList acc.reverse, [])

/-- `PointerPart (S? PointerPart)*`; `acc` holds the parts read, in
reverse. The recursion is on the characters left (each part reads at
least `name(` and `)`). -/
def parts (cs : List Char) (acc : List Part) : Except String (List Part) :=
  match dropS cs with
  | [] => if acc.isEmpty then .error "an empty pointer" else .ok acc.reverse
  | c :: cs' =>
    let (n, rest) := schemeName (c :: cs') []
    if !isQName n then .error ("'" ++ n ++ "' is not a scheme name (Framework §3.1 [5])")
    else match rest with
      | '(' :: body =>
        match schemeData body 0 [] with
        | .ok (data, rest') =>
          if rest'.length < cs.length then parts rest' ({ scheme := n, data } :: acc)
          else .error "the pointer does not advance"
        | .error m => .error m
      | _ => .error ("the scheme name '" ++ n ++ "' is not followed by '('")
termination_by cs.length

/-- `[1] Pointer ::= Shorthand | SchemeBased`. A pointer that matches
neither production is an error (Framework §3.1: "the pointer is in
error"). -/
def parse (s : String) : Except String Pointer :=
  if isNCName s then .ok (.shorthand s)
  else (parts s.toList []).map Pointer.schemeBased

/-- Write `s` as scheme data: `^`, `(` and `)` escaped with `^`. -/
def escapeData (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    if c == '^' || c == '(' || c == ')' then ['^', c] else [c]))

/-! ## Locations -/

/-- A node that a pointer identifies. `inscope` holds the namespace
bindings that the node's ancestors declare (newest first): they are not
attributes of the node, and an XInclude processor needs them to keep
the node's names (XInclude 1.1 §4.5.4). -/
inductive Hit where
  | node (n : Node) (inscope : List (String × String))
  | attr (a : Attribute)
  | nsNode (pfx uri : String)
deriving Repr, Inhabited

/-- The scheme data of a scheme that this module does not evaluate, with
the namespace bindings of the xmlns() parts to its left (newest first);
`none` when the part identifies no subresource or its data is in
error. -/
abbrev SchemeHook := Document → List (String × String) → String → Option (List Hit)

/-- The schemes evaluated outside this module (the xpointer() scheme). -/
structure Schemes where
  xpointer : Option SchemeHook := none

/-- The namespace bindings that an element's attributes add to `sc`. -/
def scopeOf (sc : List (String × String)) (attrs : List Attribute) : List (String × String) :=
  attrs.foldl (fun sc a =>
    if a.name == "xmlns" then ("", a.value) :: sc
    else if a.name.startsWith "xmlns:" then ((a.name.drop 6).toString, a.value) :: sc
    else sc) sc

/-- xml:id 1.0 §4: leading and trailing spaces removed, inner runs of
spaces collapsed to one. -/
def normalizeSpace (s : String) : String :=
  String.intercalate " " ((s.split isXmlSpace).toList.map (·.toString) |>.filter (· != ""))

/-- The attribute `a` of element `tag` is an ID (DTD type `ID`, or
`xml:id`) with the value `v`. -/
def isIdAttr (idAttrs : List (String × String)) (tag : String) (v : String) (a : Attribute) : Bool :=
  (a.name == "xml:id" || idAttrs.contains (tag, a.name)) && normalizeSpace a.value == v

/-- The element children of a node. -/
def elementKids (kids : List Node) : List Node :=
  kids.filter (fun k => match k with
    | .element .. => true
    | _ => false)

/-- The first element, in document order, that carries the ID `v`.
`work` holds the nodes still to visit with the bindings their ancestors
declare, in document order; the search is a tail call per node, and
`fuel` bounds the nodes visited. -/
def findId (idAttrs : List (String × String)) (v : String) :
    Nat → List (Node × List (String × String)) → Option (Node × List (String × String))
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, (n, sc) :: work =>
    match n with
    | .element tag attrs kids =>
      if attrs.any (isIdAttr idAttrs tag v) then some (n, sc)
      else
        let sc' := scopeOf sc attrs
        findId idAttrs v f (kids.map (fun k => (k, sc')) ++ work)
    | _ => findId idAttrs v f work

/-- A bound on the nodes the ID search visits. -/
def searchFuel : Nat := 2 ^ 48

/-- The ID-typed attributes that the document's DTD declares. -/
def idDecls (d : Document) : List (String × String) :=
  match d.doctype with
  | some dt => dt.idAttrs
  | none => []

/-- The element with ID `v` (Framework §3.2), with the bindings its
ancestors declare. -/
def elementById (d : Document) (v : String) : Option (Node × List (String × String)) :=
  findId (idDecls d) v searchFuel [(d.root, [])]

/-! ## The element() scheme -/

/-- `[1] ElementSchemeData`: an optional NCName and the child sequence. -/
structure ElementData where
  start : Option String
  steps : List Nat
deriving DecidableEq, Repr

/-- `[2] ChildSequence ::= ('/' [1-9] [0-9]*)+`, one step. -/
def childStep (s : String) : Option Nat :=
  match s.toList with
  | c :: cs =>
    if '1' ≤ c && c ≤ '9' && cs.all (fun c => '0' ≤ c && c ≤ '9') then s.toNat? else none
  | [] => none

/-- Read `[1] ElementSchemeData`; `none` when the data is in error, so
that the part fails (element() §3). -/
def parseElementData (s : String) : Option ElementData :=
  match s.splitOn "/" with
  | [] => none
  | first :: rest =>
    let start := if first == "" then none else some first
    if first != "" && !isNCName first then none
    else if first == "" && rest.isEmpty then none
    else match rest.mapM childStep with
      | some steps => if start.isNone && steps.isEmpty then none else some { start, steps }
      | none => none

/-- Follow a child sequence: step `k` selects the `k`-th element child
(element() §3). The recursion is on the steps. -/
def followSteps : List Nat → Node × List (String × String) → Option (Node × List (String × String))
  | [], here => some here
  | k :: ks, (n, sc) =>
    match n with
    | .element _ attrs kids =>
      match (elementKids kids)[k - 1]? with
      | some c => if k == 0 then none else followSteps ks (c, scopeOf sc attrs)
      | none => none
    | _ => none

/-- Evaluate element() scheme data. A child sequence that begins with
`/` starts at the document node, whose only element child is the
document element. -/
def evalElement (d : Document) (e : ElementData) : Option (Node × List (String × String)) :=
  match e.start with
  | some n => (elementById d n).bind (followSteps e.steps)
  | none =>
    match e.steps with
    | 1 :: ks => followSteps ks (d.root, [])
    | _ => none

/-! ## The xmlns() scheme -/

/-- `[1] XmlnsSchemeData ::= NCName S? '=' S? EscapedNamespaceName`:
the binding, or `none` when the data is in error. The prefixes `xml`
and `xmlns` are not rebound (xmlns() §3: such a part "has no effect"). -/
def parseXmlnsData (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | p :: rest@(_ :: _) =>
    let p := p.trimAscii.toString
    let u := (String.intercalate "=" rest).trimAsciiStart.toString
    if isNCName p && p != "xml" && p != "xmlns" then some (p, u) else none
  | _ => none

/-! ## Evaluation (Framework §3.3) -/

/-- Evaluate the parts from left to right. `ns` holds the bindings of
the xmlns() parts read so far (newest first). The first part that
identifies a subresource gives the result; a part of an unknown scheme,
a part in error, and an xmlns() part identify none. -/
def evalParts (sch : Schemes) (d : Document) (ns : List (String × String)) :
    List Part → Option (List Hit)
  | [] => none
  | p :: ps =>
    if p.scheme == "xmlns" then
      match parseXmlnsData p.data with
      | some b => evalParts sch d (b :: ns) ps
      | none => evalParts sch d ns ps
    else if p.scheme == "element" then
      match (parseElementData p.data).bind (evalElement d) with
      | some (n, sc) => some [.node n sc]
      | none => evalParts sch d ns ps
    else if p.scheme == "xpointer" then
      match sch.xpointer.bind (fun h => h d ns p.data) with
      | some (h :: hs) => some (h :: hs)
      | _ => evalParts sch d ns ps
    else evalParts sch d ns ps

/-- Evaluate a pointer: the nodes it identifies, or `none` (no
subresource, Framework §3.3). -/
def evaluate (sch : Schemes) (d : Document) : Pointer → Option (List Hit)
  | .shorthand n => (elementById d n).map (fun (n, sc) => [.node n sc])
  | .schemeBased ps => evalParts sch d [] ps

/-- The outcome of resolving a pointer string against a document. -/
inductive Outcome where
  | hits (hs : List Hit)
  /-- The pointer is well-formed and identifies no subresource. -/
  | noSubresource
  /-- The pointer does not match `[1] Pointer`. -/
  | syntaxError (msg : String)
deriving Repr, Inhabited

def resolve (sch : Schemes) (d : Document) (s : String) : Outcome :=
  match parse s with
  | .error m => .syntaxError m
  | .ok p =>
    match evaluate sch d p with
    | some hs => .hits hs
    | none => .noSubresource

/-! ## Tests: the pointer forms of the W3C XInclude test suite -/

#guard (parse "foo").toOption ==
  some (.shorthand "foo")
#guard (parse "element(/1/1)").toOption ==
  some (.schemeBased [{ scheme := "element", data := "/1/1" }])
#guard (parse "test:xpath(somedata)element(/1/1)").toOption ==
  some (.schemeBased [{ scheme := "test:xpath", data := "somedata" },
                     { scheme := "element", data := "/1/1" }])
#guard (parse "xpointer(id('f2'))element(/1/2)").toOption ==
  some (.schemeBased [{ scheme := "xpointer", data := "id('f2')" },
                     { scheme := "element", data := "/1/2" }])
#guard (parse "a(x^(y^)z^^) b(((q)))").toOption ==
  some (.schemeBased [{ scheme := "a", data := "x(y)z^" }, { scheme := "b", data := "((q))" }])
-- unbalanced, a bad escape, a pointer that is neither form
#guard (parse "element(/1/1)element(/1/2").toOption.isNone
#guard (parse "element(/1/1)element(^^^)").toOption.isNone
#guard (parse "element(p^l/2/3)").toOption.isNone
#guard (parse "/1/1").toOption.isNone
-- element() data in error: the part fails, the pointer is well-formed
#guard parseElementData "/1/%32" == none
#guard parseElementData "***" == none
#guard parseElementData "///" == none
#guard parseElementData "rose red/1/1" == none
#guard parseElementData "p:l/2/3" == none
#guard parseElementData "/1/12/3" == some { start := none, steps := [1, 12, 3] }
#guard parseElementData "p1/1/2" == some { start := some "p1", steps := [1, 2] }
#guard parseElementData "chapter" == some { start := some "chapter", steps := [] }
#guard parseXmlnsData "x = http://e/^)" == some ("x", "http://e/^)")
#guard parseXmlnsData "xml=http://e/" == none
#guard escapeData "a(b)^" == "a^(b^)^^"

end L4Factoidal.XML.XPointer
