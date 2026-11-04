/-
L4Factoidal.RelaxNG.Simplify — from a schema in the XML syntax of RELAX NG
to the simple syntax, with the checks that make a schema incorrect.

Specification: RELAX NG Specification, OASIS Committee Specification
3 December 2001 (https://relaxng.org/spec-20011203.html), equal in content
to ISO/IEC 19757-2:2008. Section numbers below are of that text.

The work is done in four passes. Each one returns `Except String`; an error
is the verdict "the schema is incorrect" with a message.

1. `conv` reads one XML document (the tree of `L4Factoidal.XML.Parser`) into
   an `RE` tree of RELAX NG elements. It does §4.1 (foreign elements and
   attributes are removed; an attribute qualified with the RELAX NG
   namespace and an unqualified attribute that the element does not allow
   are errors), §4.2 (whitespace of `name`, `type` and `combine` attributes
   and of `name` elements), §4.3 (`datatypeLibrary` inheritance, with the
   §3 check that the URI is absolute and has no fragment), §4.4 (`value`
   with no `type`), the `xml:base` and `href` part of §4.5, §4.8 (the `name`
   attribute becomes a `name` child) and §4.10 (a QName is resolved with
   the namespace declarations in scope). `check3` then checks the element
   grammar of §3 (which elements may appear where, and how many children).
2. `expand` does §4.5-§4.7: `externalRef` and `include` load a document
   through a resolver function, apply pass 1 to it, and put it in place.
   A document that refers to itself, directly or through others, is an
   error. `include` overrides `start` and `define` components (§4.7).
3. `trTop` turns the tree into `Pattern`s: §4.9 (`ns` inheritance), §4.11
   (`div`), §4.12-§4.15 (number of children, `mixed`, `optional`,
   `zeroOrMore`), §4.16 (name class constraints and datatypes), §4.17
   (`combine`) and §4.18 (nested grammars: each `define` gets a name unique
   in the schema; `ref` and `parentRef` are resolved in the nearest and the
   parent grammar).
4. `finish` does §4.19 (every `element` gets its own `define`, a `ref` to a
   `define` whose content is not an `element` is replaced by that content,
   a loop of such references is an error, unreachable `define`s are
   removed), §4.20 (`notAllowed`) and §4.21 (`empty`), and then checks the
   restrictions of §7: prohibited paths (§7.1), string sequences (§7.2),
   duplicate attributes (§7.3) and `interleave` (§7.4).

Recursion over a tree takes a fuel argument of the size of the tree plus
one, so it never runs out on a tree of that size; when it does, the result
is an error, never a silent answer.
-/
import Std.Data.HashMap
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Namespaces
import L4Factoidal.RelaxNG.Datatypes
import L4Factoidal.RelaxNG.Names

namespace L4Factoidal.RelaxNG

open L4Factoidal.XML

/-! ## Strings and URIs -/

/-- Remove XML whitespace (`[3] S`) at both ends (§4.2). -/
def trimWs (s : String) : String :=
  let drop (l : List Char) := l.dropWhile isXmlSpace
  String.ofList (drop (drop s.toList).reverse).reverse

/-- Is the string made of XML whitespace only? -/
def allWs (s : String) : Bool := s.toList.all isXmlSpace

/-- The scheme of a URI reference (RFC 2396 §3.1: `alpha *( alpha | digit |
"+" | "-" | "." ) ":"`), when it has one. -/
def uriScheme? (s : String) : Option String :=
  let cs := s.toList
  let sch := cs.takeWhile (fun c => c != ':' && c != '/' && c != '?' && c != '#')
  if sch.length < cs.length && cs[sch.length]? == some ':' then
    match sch with
    | c :: rest =>
      if c.isAlpha && rest.all (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.')
      then some (String.ofList sch) else none
    | [] => none
  else none

/-- Each `%` starts an escape of two hexadecimal digits (RFC 2396 §2.4.1). -/
def escapesOk : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest => a.isHexDigit && b.isHexDigit && escapesOk rest
  | '%' :: _ => false
  | _ :: rest => escapesOk rest

/-- §3: a `datatypeLibrary` attribute is the empty string or an absolute
URI (RFC 2396) with no fragment identifier. -/
def checkLibUri (s : String) : Except String Unit :=
  if s == "" then .ok ()
  else if s.contains '#' then .error s!"datatypeLibrary {s} has a fragment identifier"
  else if !escapesOk s.toList then .error s!"datatypeLibrary {s} is not a URI"
  else
    let cs := s.toList
    let colonInScheme := (cs.takeWhile (· != ':')).all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.')
    match uriScheme? s with
    | some sch =>
      if sch.length + 1 == s.length then .error s!"datatypeLibrary {s} is not a URI"
      else .ok ()
    | none =>
      if cs.contains ':' && !colonInScheme then .error s!"datatypeLibrary {s} is not a URI"
      else .error s!"datatypeLibrary {s} is not an absolute URI"

/-- Remove `.` and `..` segments of a path (RFC 3986 §5.2.4). -/
def removeDots (p : String) : String :=
  let segs := p.splitOn "/"
  let n := segs.length
  let (acc, _) := segs.foldl (fun (st : List String × Nat) seg =>
    let (acc, i) := st
    let last := i + 1 == n
    if seg == "." then ((if last then "" :: acc else acc), i + 1)
    else if seg == ".." then
      let acc' := match acc with
        | [""] => [""]
        | _ :: r => r
        | [] => []
      ((if last then "" :: acc' else acc'), i + 1)
    else (seg :: acc, i + 1)) ([], 0)
  String.intercalate "/" acc.reverse

/-- Resolve a URI reference against a base (RFC 3986 §5.2, for the forms the
schema documents use: a reference with a scheme is absolute, one starting
with `/` replaces the path, any other replaces the last segment). -/
def resolveUri (base ref : String) : String :=
  if (uriScheme? ref).isSome then ref
  else if ref == "" then base
  else if ref.startsWith "/" then
    match uriScheme? base with
    | some sch => sch ++ ":" ++ removeDots ref
    | none => removeDots ref
  else
    let bl := base.toList
    let dir := (bl.reverse.dropWhile (· != '/')).reverse
    removeDots (String.ofList dir ++ ref)

/-! ## Pass 1: XML to RELAX NG elements -/

/-- A RELAX NG element after pass 1: local name, unqualified attributes
(after §4.2 trimming), the namespace declarations in scope, the character
data (for `name`, `value` and `param`; whitespace elsewhere is dropped) and
the RELAX NG element children. -/
inductive RE where
  | mk (name : String) (attrs : List (String × String)) (scope : NsScope)
      (text : String) (kids : List RE)
deriving Inhabited

namespace RE
def name : RE → String | .mk n .. => n
def attrs : RE → List (String × String) | .mk _ a .. => a
def scope : RE → NsScope | .mk _ _ s .. => s
def text : RE → String | .mk _ _ _ t _ => t
def kids : RE → List RE | .mk _ _ _ _ k => k
def attr? (e : RE) (k : String) : Option String := e.attrs.lookup k
/-- The number of elements in the tree; the fuel of every walk. -/
def size : RE → Nat
  | .mk _ _ _ _ ks => ks.foldl (fun a k => a + k.size) 1
end RE

/-- The elements of the RELAX NG vocabulary (§3). -/
def knownElements : List String :=
  ["element", "attribute", "group", "interleave", "choice", "optional",
   "zeroOrMore", "oneOrMore", "list", "mixed", "ref", "parentRef", "empty",
   "text", "value", "data", "notAllowed", "externalRef", "grammar", "param",
   "except", "div", "include", "start", "define", "name", "anyName", "nsName"]

/-- The unqualified attributes §3 allows on each element, besides `ns` and
`datatypeLibrary`, which every element may carry. -/
def allowedAttrs : String → List String
  | "element" | "attribute" | "ref" | "parentRef" | "param" => ["name"]
  | "define" => ["name", "combine"]
  | "start" => ["combine"]
  | "value" | "data" => ["type"]
  | "externalRef" | "include" => ["href"]
  | _ => []

/-- Elements whose content is character data only. -/
def textOnly (n : String) : Bool := n == "name" || n == "value" || n == "param"

/-- Is `s` an NCName (Namespaces in XML 1999 [4], with the character
classes of XML 1.0 Fourth Edition Appendix B; see `RelaxNG.Names`)? -/
def ncName (s : String) : Bool := isNCName4 s

/-- §4.10: resolve a QName written in a schema with the namespace
declarations in scope. A prefixed name gives its namespace URI; an
unprefixed one gives `none` (its namespace comes from `ns`, §4.9). -/
def resolveQName (scope : NsScope) (q : String) : Except String (Option String × String) :=
  match splitQName q with
  | .simple l => if ncName l then .ok (none, l) else .error s!"{q} is not a QName"
  | .prefixed p l =>
    if !ncName p || !ncName l then .error s!"{q} is not a QName"
    else match lookupPrefix scope p with
      | some u => .ok (some u, l)
      | none => .error s!"prefix {p} of {q} is not declared"
  | .malformed => .error s!"{q} is not a QName"

/-- The `name` child of §4.8 for a `name` attribute. For `attribute`
without an `ns` attribute the child gets `ns=""`. -/
def nameChild (owner : String) (attrs : List (String × String)) (scope : NsScope)
    (q : String) : Except String RE := do
  let (u, l) ← resolveQName scope q
  let nsA : List (String × String) :=
    match u with
    | some uri => [("ns", uri)]
    | none =>
      if owner == "attribute" then [("ns", (attrs.lookup "ns").getD "")] else []
  pure (.mk "name" nsA scope l [])

/-- Pass 1 on one element (§4.1-§4.4, §4.5 `xml:base`, §4.8, §4.10).
`base` is the base URI, `scope` the namespace declarations of the parent,
`lib` the inherited `datatypeLibrary`. A foreign element gives `none`. -/
def conv (base : String) (scope : NsScope) (lib : String) (n : Node) :
    Except String (Option RE) :=
  match n with
  | .element tag attrs children => do
    let scope' := (applyDeclarations "1.0" scope attrs).getD scope
    let some en := resolveElementName scope' tag
      | throw s!"element {tag}: prefix not declared"
    if en.namespace_ != some rngNs then return none
    let L := en.localPart
    unless knownElements.contains L do throw s!"{L} is not an element of RELAX NG"
    let mut kept : List (String × String) := []
    let mut base' := base
    for a in attrs do
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then continue
      match splitQName a.name with
      | .prefixed p l =>
        match lookupPrefix scope' p with
        | some u =>
          if u == rngNs then throw s!"attribute {a.name} is in the RELAX NG namespace"
          if u == xmlNsUri && l == "base" then base' := resolveUri base a.value
        | none => throw s!"attribute {a.name}: prefix not declared"
      | .simple l =>
        unless (allowedAttrs L).contains l || l == "ns" || l == "datatypeLibrary" do
          throw s!"attribute {l} is not allowed on {L}"
        let v := if l == "name" || l == "type" || l == "combine" then trimWs a.value else a.value
        kept := kept ++ [(l, v)]
      | .malformed => throw s!"attribute name {a.name} is not a QName"
    let mut lib' := lib
    match kept.lookup "datatypeLibrary" with
    | some d => checkLibUri d; lib' := d
    | none => pure ()
    let mut txt := ""
    let mut kids : Array RE := #[]
    for c in children do
      match c with
      | .text s => txt := txt ++ s
      | .cdata s => txt := txt ++ s
      | .element .. =>
        if textOnly L then throw s!"{L} must not have element children"
        match ← conv base' scope' lib' c with
        | some r => kids := kids.push r
        | none => pure ()
      | _ => pure ()
    unless textOnly L || allWs txt do throw s!"{L} must not have character data"
    let withoutLib := kept.filter (fun p => p.1 != "datatypeLibrary")
    -- §4.3, §4.4
    let mut attrs' := withoutLib
    if L == "data" then attrs' := attrs' ++ [("datatypeLibrary", lib')]
    if L == "value" then
      if (kept.lookup "type").isNone then
        attrs' := attrs' ++ [("type", "token"), ("datatypeLibrary", "")]
      else attrs' := attrs' ++ [("datatypeLibrary", lib')]
    if L == "data" || L == "value" then
      if let some t := kept.lookup "type" then
        unless ncName t do throw s!"type {t} is not an NCName"
    if L == "ref" || L == "parentRef" || L == "define" || L == "param" then
      if let some nm := kept.lookup "name" then
        unless ncName nm do throw s!"name {nm} is not an NCName"
    if let some c := kept.lookup "combine" then
      unless c == "choice" || c == "interleave" do throw s!"combine {c} is not allowed"
    -- §4.5: href is resolved against the base URI
    if L == "externalRef" || L == "include" then
      if let some h := kept.lookup "href" then
        if h.contains '#' then throw s!"href {h} has a fragment identifier"
        unless escapesOk h.toList do throw s!"href {h} is not a URI reference"
        attrs' := attrs'.map (fun p => if p.1 == "href" then ("href", resolveUri base' h) else p)
    -- §4.8, §4.10
    let mut kids' := kids.toList
    if L == "element" || L == "attribute" then
      if let some q := kept.lookup "name" then
        kids' := (← nameChild L kept scope' q) :: kids'
        attrs' := attrs'.filter (fun p => p.1 != "name")
    if L == "name" then
      let (u, l) ← resolveQName scope' (trimWs txt)
      match u with
      | some uri => attrs' := (attrs'.filter (fun p => p.1 != "ns")) ++ [("ns", uri)]
      | none => pure ()
      txt := l
    if L != "value" && L != "param" && L != "name" then txt := ""
    return some (.mk L attrs' scope' txt kids')
  | _ => return none

/-! ### §3: the element grammar -/

/-- Where an element stands: a pattern, a name class, the content of a
`grammar`, or the content of an `include`. -/
inductive Role where
  | pattern | nameClass | grammarContent | includeContent
deriving DecidableEq

/-- §3: check the element grammar of the RELAX NG XML syntax. -/
def check3 : Nat → Role → RE → Except String Unit
  | 0, _, _ => .error "schema nested too deeply"
  | k + 1, role, .mk n attrs _ _ kids => do
    let need (a : String) : Except String Unit :=
      if (attrs.lookup a).isSome then .ok () else .error s!"{n} needs attribute {a}"
    let noKids : Except String Unit :=
      if kids.isEmpty then .ok () else .error s!"{n} must be empty"
    let pats (ps : List RE) : Except String Unit := do
      for p in ps do check3 k .pattern p
    let exceptOf (role' : Role) (ex : RE) : Except String Unit := do
      unless ex.name == "except" do throw s!"{ex.name} is not allowed in {n}"
      if ex.kids.isEmpty then throw "except must not be empty"
      for c in ex.kids do check3 k role' c
    match role with
    | .pattern =>
      match n with
      | "element" =>
        match kids with
        | nc :: ps => do
          check3 k .nameClass nc
          if ps.isEmpty then throw "element needs a pattern"
          pats ps
        | [] => throw "element needs a name"
      | "attribute" =>
        match kids with
        | nc :: ps => do
          check3 k .nameClass nc
          if ps.length > 1 then throw "attribute has more than one pattern"
          pats ps
        | [] => throw "attribute needs a name"
      | "group" | "interleave" | "choice" | "optional" | "zeroOrMore"
      | "oneOrMore" | "list" | "mixed" =>
        if kids.isEmpty then throw s!"{n} needs a pattern"
        pats kids
      | "ref" | "parentRef" => need "name"; noKids
      | "empty" | "text" | "notAllowed" | "value" => noKids
      | "data" =>
        need "type"
        let params := kids.takeWhile (fun c => c.name == "param")
        let rest := kids.dropWhile (fun c => c.name == "param")
        for p in params do
          unless (p.attr? "name").isSome do throw "param needs a name"
          unless p.kids.isEmpty do throw "param must not have element children"
        match rest with
        | [] => pure ()
        | [ex] => exceptOf .pattern ex
        | _ => throw "data has extra children"
      | "externalRef" => need "href"; noKids
      | "grammar" => for c in kids do check3 k .grammarContent c
      | _ => throw s!"{n} is not a pattern"
    | .nameClass =>
      match n with
      | "name" => noKids
      | "anyName" | "nsName" =>
        match kids with
        | [] => pure ()
        | [ex] => exceptOf .nameClass ex
        | _ => throw s!"{n} has extra children"
      | "choice" =>
        if kids.isEmpty then throw "choice needs a name class"
        for c in kids do check3 k .nameClass c
      | _ => throw s!"{n} is not a name class"
    | .grammarContent | .includeContent =>
      match n with
      | "start" =>
        match kids with
        | [p] => check3 k .pattern p
        | _ => throw "start needs exactly one pattern"
      | "define" =>
        need "name"
        if kids.isEmpty then throw "define needs a pattern"
        pats kids
      | "div" => for c in kids do check3 k role c
      | "include" =>
        if role == .includeContent then throw "include is not allowed in include"
        need "href"
        for c in kids do check3 k .includeContent c
      | _ => throw s!"{n} is not allowed in a grammar"

/-- Read one schema document: pass 1 and the §3 check. The document element
must be a pattern. -/
def readSchemaNode (base : String) (root : Node) : Except String RE := do
  let some r ← conv base initialScope "" root
    | throw "the document element is not a RELAX NG element"
  check3 (r.size + 1) .pattern r
  return r

/-- Read one schema document from text. -/
def readSchemaText (base : String) (txt : String) : Except String RE := do
  match parseXML txt with
  | .error e => throw s!"{base}: not well-formed: {e.message}"
  | .ok d => readSchemaNode base d.root

/-! ## Pass 2: `externalRef` and `include` (§4.5-§4.7) -/

/-- Apply `f` to every element, children first. -/
def bottomUp (f : RE → Except String RE) : Nat → RE → Except String RE
  | 0, _ => .error "schema nested too deeply"
  | k + 1, .mk n a s t ks => do
    let mut out : Array RE := #[]
    for c in ks do out := out.push (← bottomUp f k c)
    f (.mk n a s t out.toList)

/-- Does this grammar content have a `start` component (in it or in a
`div`)? -/
def hasStart : Nat → List RE → Bool
  | 0, _ => false
  | k + 1, cs => cs.foldl (fun acc c =>
      acc || c.name == "start" || (c.name == "div" && hasStart k c.kids)) false

/-- The names of the `define` components of grammar content. -/
def defineNames : Nat → List RE → List String
  | 0, _ => []
  | k + 1, cs => cs.foldl (fun acc c =>
      if c.name == "define" then acc ++ [(c.attr? "name").getD ""]
      else if c.name == "div" then acc ++ defineNames k c.kids
      else acc) []

/-- §4.7: remove the components an `include` overrides. -/
def removeComponents (dropStart : Bool) (names : List String) : Nat → List RE → List RE
  | 0, cs => cs
  | k + 1, cs => cs.foldr (fun c acc =>
      if c.name == "start" && dropStart then acc
      else if c.name == "define" && names.contains ((c.attr? "name").getD "") then acc
      else if c.name == "div" then
        (.mk "div" c.attrs c.scope c.text (removeComponents dropStart names k c.kids)) :: acc
      else c :: acc) []

/-- §4.5-§4.7: replace every `externalRef` and `include` by the document it
names. `stack` holds the URIs of the documents being read, to refuse a
document that refers to itself. `fuel` bounds the depth of references. -/
def expand (resolve : String → Option String) : Nat → List String → RE → Except String RE
  | 0, _, _ => .error "externalRef and include nested too deeply"
  | fuel + 1, stack, e => bottomUp (fun node =>
      match node with
      | .mk "externalRef" a _ _ _ => do
        let href := (a.lookup "href").getD ""
        if stack.contains href then throw s!"{href} refers to itself"
        let some txt := resolve href | throw s!"cannot read {href}"
        let r ← readSchemaText href txt
        let r ← expand resolve fuel (href :: stack) r
        match r, a.lookup "ns" with
        | .mk rn ra rs rt rk, some nsv =>
          if (ra.lookup "ns").isNone then return .mk rn (ra ++ [("ns", nsv)]) rs rt rk
          else return r
        | _, none => return r
      | .mk "include" a s _ ks => do
        let href := (a.lookup "href").getD ""
        if stack.contains href then throw s!"{href} refers to itself"
        let some txt := resolve href | throw s!"cannot read {href}"
        let r ← readSchemaText href txt
        unless r.name == "grammar" do throw s!"{href}: an included document must be a grammar"
        let r ← expand resolve fuel (href :: stack) r
        let sz := r.size + 1
        let incStart := hasStart (e.size + 1) ks
        let incDefs := defineNames (e.size + 1) ks
        if incStart && !hasStart sz r.kids then
          throw s!"{href}: include overrides start, which the grammar does not have"
        let gDefs := defineNames sz r.kids
        for d in incDefs do
          unless gDefs.contains d do
            throw s!"{href}: include overrides define {d}, which the grammar does not have"
        let gk := removeComponents incStart incDefs sz r.kids
        let gdiv := RE.mk "div" r.attrs r.scope "" gk
        return .mk "div" (a.filter (fun p => p.1 != "href")) s "" (gdiv :: ks)
      | other => pure other) (e.size + 1) e

/-! ## Pass 3: patterns (§4.9, §4.11-§4.18) -/

/-- The state of pass 3: a counter for unique names, and the `define`s
read so far under their unique names. -/
structure TState where
  next : Nat := 0
  defs : Array (String × Pattern) := #[]

abbrev TM := StateT TState (Except String)

/-- The name classes inside a name class that §4.16 constrains. -/
def NameClass.hasAnyName : NameClass → Bool
  | .anyName | .anyNameExcept _ => true
  | .nsNameExcept _ e => e.hasAnyName
  | .choice a b => a.hasAnyName || b.hasAnyName
  | _ => false

def NameClass.hasNsName : NameClass → Bool
  | .nsName _ | .nsNameExcept _ _ => true
  | .anyNameExcept e => e.hasNsName
  | .choice a b => a.hasNsName || b.hasNsName
  | _ => false

/-- §4.16: the name class of an attribute names no `xmlns` attribute. -/
def NameClass.attrOk : NameClass → Bool
  | .name ns l => !(ns == "" && l == "xmlns") && ns != xmlnsUri
  | .nsName ns => ns != xmlnsUri
  | .nsNameExcept ns e => ns != xmlnsUri && e.attrOk
  | .anyNameExcept e => e.attrOk
  | .anyName => true
  | .choice a b => a.attrOk && b.attrOk

/-- A choice of the name classes in a list (§4.12, left to right). -/
def ncChoice : List NameClass → Except String NameClass
  | [] => .error "empty name class choice"
  | c :: cs => .ok (cs.foldl NameClass.choice c)

/-- §4.9, §4.12, §4.16: the name class of an element. `ns` is the
inherited `ns`. -/
def trNC : Nat → String → RE → Except String NameClass
  | 0, _, _ => .error "schema nested too deeply"
  | k + 1, ns, e => do
    let ns' := (e.attr? "ns").getD ns
    let exceptOf (ex : RE) : Except String NameClass := do
      let mut cs : Array NameClass := #[]
      for c in ex.kids do cs := cs.push (← trNC k ns' c)
      ncChoice cs.toList
    match e.name with
    | "name" => pure (.name ns' e.text)
    | "anyName" =>
      match e.kids with
      | [ex] => do
        let x ← exceptOf ex
        if x.hasAnyName then throw "anyName in the except of anyName"
        pure (.anyNameExcept x)
      | _ => pure .anyName
    | "nsName" =>
      match e.kids with
      | [ex] => do
        let x ← exceptOf ex
        if x.hasAnyName || x.hasNsName then throw "anyName or nsName in the except of nsName"
        pure (.nsNameExcept ns' x)
      | _ => pure (.nsName ns')
    | "choice" => do
      let mut cs : Array NameClass := #[]
      for c in e.kids do cs := cs.push (← trNC k ns' c)
      ncChoice cs.toList
    | n => throw s!"{n} is not a name class"

/-- The context of a `value` element (§4.9): its in-scope prefixes, with
its `ns` attribute as the default namespace. -/
def valueContext (scope : NsScope) (ns : String) : Context :=
  let step (acc : List (String × String) × List String) (b : String × Option String) :=
    let (out, seen) := acc
    if b.1 == "" || seen.contains b.1 then acc
    else match b.2 with
      | some u => (out ++ [(b.1, u)], b.1 :: seen)
      | none => (out, b.1 :: seen)
  let (prefixes, _) := scope.foldl step ([], [])
  { ns := ("", ns) :: prefixes }

/-- Fold a list with a binary constructor, left to right (§4.12). -/
def foldBin (f : Pattern → Pattern → Pattern) : List Pattern → Except String Pattern
  | [] => .error "a pattern is missing"
  | p :: ps => .ok (ps.foldl f p)

/-- A fresh number. -/
def fresh : TM Nat := modifyGet (fun s => (s.next, { s with next := s.next + 1 }))

/-- §4.17: the patterns of the components with one name (or of `start`)
combined. At most one component lacks `combine`; the others agree. -/
def combineAll (what : String) (items : List (Option String × Pattern)) : Except String Pattern := do
  let withC := items.filterMap (fun i => i.1)
  let noC := items.filter (fun i => i.1.isNone)
  if noC.length > 1 then throw s!"{what} is defined more than once without combine"
  let method ← match withC with
    | [] => pure "choice"
    | c :: cs => if cs.all (· == c) then pure c else throw s!"{what}: combine methods differ"
  let ps := items.map (fun i => i.2)
  if method == "interleave" then foldBin .interleave ps else foldBin .choice ps

/-- §4.11: the components of grammar content, with the `ns` each inherits;
`div` elements are flattened. -/
def components : Nat → String → List RE → List (RE × String)
  | 0, _, _ => []
  | k + 1, ns, cs => cs.foldl (fun acc c =>
      if c.name == "div" then acc ++ components k ((c.attr? "ns").getD ns) c.kids
      else acc ++ [(c, ns)]) []

mutual

/-- Pass 3 on a pattern element. `env` holds, innermost first, the map from
`define` names to unique names of each enclosing grammar. -/
def trP : Nat → List (List (String × String)) → String → RE → TM Pattern
  | 0, _, _, _ => throw "schema nested too deeply"
  | k + 1, env, ns, e => do
    let ns' := (e.attr? "ns").getD ns
    match e.name with
    | "element" =>
      match e.kids with
      | nc :: ps => do
        let c ← trNC k ns' nc
        let body ← trGroup k env ns' ps
        pure (.element c body)
      | [] => throw "element needs a name"
    | "attribute" =>
      match e.kids with
      | nc :: ps => do
        let c ← trNC k ns' nc
        unless c.attrOk do throw "attribute name class names xmlns"
        let body ← if ps.isEmpty then pure .text else trGroup k env ns' ps
        pure (.attribute c body)
      | [] => throw "attribute needs a name"
    | "group" => trSeq k env ns' .group e.kids
    | "interleave" => trSeq k env ns' .interleave e.kids
    | "choice" => trSeq k env ns' .choice e.kids
    | "optional" => do pure (.choice (← trGroup k env ns' e.kids) .empty)
    | "zeroOrMore" => do pure (.choice (.oneOrMore (← trGroup k env ns' e.kids)) .empty)
    | "oneOrMore" => do pure (.oneOrMore (← trGroup k env ns' e.kids))
    | "list" => do pure (.list (← trGroup k env ns' e.kids))
    | "mixed" => do pure (.interleave (← trGroup k env ns' e.kids) .text)
    | "ref" =>
      let n := (e.attr? "name").getD ""
      match env with
      | g :: _ =>
        match g.lookup n with
        | some u => pure (.ref u)
        | none => throw s!"ref {n}: no define of that name"
      | [] => throw s!"ref {n} outside a grammar"
    | "parentRef" =>
      let n := (e.attr? "name").getD ""
      match env with
      | _ :: g :: _ =>
        match g.lookup n with
        | some u => pure (.ref u)
        | none => throw s!"parentRef {n}: no define of that name in the parent grammar"
      | _ => throw s!"parentRef {n} without a parent grammar"
    | "empty" => pure .empty
    | "text" => pure .text
    | "notAllowed" => pure .notAllowed
    | "value" =>
      let dt : Datatype := ⟨(e.attr? "datatypeLibrary").getD "", (e.attr? "type").getD ""⟩
      let cx := valueContext e.scope ns'
      match checkValue dt e.text cx with
      | .ok () => pure (.value dt e.text cx)
      | .error m => throw m
    | "data" =>
      let dt : Datatype := ⟨(e.attr? "datatypeLibrary").getD "", (e.attr? "type").getD ""⟩
      let params := (e.kids.filter (fun c => c.name == "param")).map
        (fun c => ((c.attr? "name").getD "", c.text))
      match checkDatatype dt params with
      | .error m => throw m
      | .ok () =>
        match e.kids.filter (fun c => c.name == "except") with
        | [ex] => do pure (.dataExcept dt params (← trSeq k env ns' .choice ex.kids))
        | _ => pure (.data dt params)
    | "grammar" => trGrammar k env ns' e.kids
    | n => throw s!"{n} is not a pattern"

/-- §4.12: several patterns in a group. -/
def trGroup : Nat → List (List (String × String)) → String → List RE → TM Pattern
  | k, env, ns, ps => trSeq k env ns .group ps

/-- Several patterns combined with a binary constructor, left to right. -/
def trSeq : Nat → List (List (String × String)) → String →
    (Pattern → Pattern → Pattern) → List RE → TM Pattern
  | 0, _, _, _, _ => throw "schema nested too deeply"
  | k + 1, env, ns, f, ps => do
    let mut out : Array Pattern := #[]
    for p in ps do out := out.push (← trP k env ns p)
    match foldBin f out.toList with
    | .ok r => pure r
    | .error m => throw m

/-- §4.17, §4.18: a grammar. Its `define`s are stored under unique names;
the result is its `start` pattern. -/
def trGrammar : Nat → List (List (String × String)) → String → List RE → TM Pattern
  | 0, _, _, _ => throw "schema nested too deeply"
  | k + 1, env, ns, kids => do
    let comps := components (k + 1) ns kids
    let mut names : List String := []
    for (c, _) in comps do
      if c.name == "define" then
        let n := (c.attr? "name").getD ""
        unless names.contains n do names := names ++ [n]
    let mut scope : List (String × String) := []
    for n in names do
      let i ← fresh
      scope := scope ++ [(n, s!"{n}#{i}")]
    let env' := scope :: env
    for (n, u) in scope do
      let mut items : Array (Option String × Pattern) := #[]
      for (c, cns) in comps do
        if c.name == "define" && (c.attr? "name").getD "" == n then
          let p ← trGroup k env' ((c.attr? "ns").getD cns) c.kids
          items := items.push (c.attr? "combine", p)
      match combineAll s!"define {n}" items.toList with
      | .ok p => modify (fun s => { s with defs := s.defs.push (u, p) })
      | .error m => throw m
    let mut starts : Array (Option String × Pattern) := #[]
    for (c, cns) in comps do
      if c.name == "start" then
        let p ← trGroup k env' ((c.attr? "ns").getD cns) c.kids
        starts := starts.push (c.attr? "combine", p)
    if starts.isEmpty then throw "grammar has no start"
    match combineAll "start" starts.toList with
    | .ok p => pure p
    | .error m => throw m

end

/-- Pass 3 on the whole schema: the start pattern and the `define`s under
unique names (§4.18: a schema that is not a grammar is the start of one). -/
def trTop (e : RE) : Except String (Pattern × Array (String × Pattern)) := do
  let (p, st) ← (trP (2 * e.size + 4) [] "" e).run {}
  return (p, st.defs)

/-! ## Pass 4: §4.19-§4.21 and §7 -/

/-- The state of the element lifting of §4.19. -/
structure LState where
  next : Nat := 0
  edefs : Array (String × NameClass × Pattern) := #[]

/-- §4.19: give every `element` its own `define` (named `element#i`) and
put a `ref` in its place. -/
def lift : Pattern → StateM LState Pattern
  | .element nc p => do
    let p' ← lift p
    let s ← get
    let n := s!"element#{s.next}"
    set { s with next := s.next + 1, edefs := s.edefs.push (n, nc, p') }
    pure (.ref n)
  | .choice a b => do pure (.choice (← lift a) (← lift b))
  | .interleave a b => do pure (.interleave (← lift a) (← lift b))
  | .group a b => do pure (.group (← lift a) (← lift b))
  | .oneOrMore p => do pure (.oneOrMore (← lift p))
  | .list p => do pure (.list (← lift p))
  | .dataExcept dt ps e => do pure (.dataExcept dt ps (← lift e))
  | .attribute nc p => do pure (.attribute nc (← lift p))
  | .after a b => do pure (.after (← lift a) (← lift b))
  | p => pure p

/-- §4.19: replace each `ref` to a `define` whose content is not an
`element` by that content. A reference that reaches its own `define` again
is a loop with no `element` in it, an error. The fuel is the number of
`define`s, the longest chain of such references with no repetition. -/
def inline (defs : Std.HashMap String Pattern) : Nat → List String → Pattern → Except String Pattern
  | fuel, vis, .ref n =>
    match defs[n]? with
    | some b =>
      if vis.contains n then .error s!"define {n} refers to itself with no element between"
      else match fuel with
        | 0 => .error s!"define {n} refers to itself with no element between"
        | f + 1 => inline defs f (n :: vis) b
    | none => .ok (.ref n)
  | fuel, vis, .choice a b => do pure (.choice (← inline defs fuel vis a) (← inline defs fuel vis b))
  | fuel, vis, .interleave a b => do
    pure (.interleave (← inline defs fuel vis a) (← inline defs fuel vis b))
  | fuel, vis, .group a b => do pure (.group (← inline defs fuel vis a) (← inline defs fuel vis b))
  | fuel, vis, .oneOrMore p => do pure (.oneOrMore (← inline defs fuel vis p))
  | fuel, vis, .list p => do pure (.list (← inline defs fuel vis p))
  | fuel, vis, .dataExcept dt ps e => do pure (.dataExcept dt ps (← inline defs fuel vis e))
  | fuel, vis, .attribute nc p => do pure (.attribute nc (← inline defs fuel vis p))
  | fuel, vis, .element nc p => do pure (.element nc (← inline defs fuel vis p))
  | fuel, vis, .after a b => do pure (.after (← inline defs fuel vis a) (← inline defs fuel vis b))
  | _, _, p => .ok p
termination_by fuel _ p => (fuel, sizeOf p)

/-- §4.20 and §4.21: move `notAllowed` up and remove `empty`. -/
def norm : Pattern → Pattern
  | .attribute nc p =>
    match norm p with
    | .notAllowed => .notAllowed
    | p' => .attribute nc p'
  | .list p =>
    match norm p with
    | .notAllowed => .notAllowed
    | p' => .list p'
  | .group a b =>
    match norm a, norm b with
    | .notAllowed, _ => .notAllowed
    | _, .notAllowed => .notAllowed
    | .empty, b' => b'
    | a', .empty => a'
    | a', b' => .group a' b'
  | .interleave a b =>
    match norm a, norm b with
    | .notAllowed, _ => .notAllowed
    | _, .notAllowed => .notAllowed
    | .empty, b' => b'
    | a', .empty => a'
    | a', b' => .interleave a' b'
  | .choice a b =>
    match norm a, norm b with
    | .notAllowed, b' => b'
    | a', .notAllowed => a'
    | .empty, .empty => .empty
    | a', .empty => .choice .empty a'
    | a', b' => .choice a' b'
  | .oneOrMore p =>
    match norm p with
    | .notAllowed => .notAllowed
    | .empty => .empty
    | p' => .oneOrMore p'
  | .dataExcept dt ps e =>
    match norm e with
    | .notAllowed => .data dt ps
    | e' => .dataExcept dt ps e'
  | .element nc p => .element nc (norm p)
  | p => p

/-- The names a pattern refers to, added to `acc`. -/
def refsOf (acc : List String) : Pattern → List String
  | .ref n => n :: acc
  | .choice a b | .interleave a b | .group a b | .after a b => refsOf (refsOf acc a) b
  | .oneOrMore p | .list p | .attribute _ p | .element _ p => refsOf acc p
  | .dataExcept _ _ e => refsOf acc e
  | _ => acc

/-- The element `define`s reachable from `start` (§4.19, §4.20). -/
def reachable (defs : Std.HashMap String (NameClass × Pattern)) (start : Pattern) : List String := Id.run do
  let mut seen : List String := []
  let mut todo := refsOf [] start
  for _ in [0:defs.size + 1] do
    let mut next : List String := []
    for n in todo do
      unless seen.contains n do
        seen := n :: seen
        if let some (_, p) := defs[n]? then next := refsOf next p
    todo := next
  return seen.reverse

/-! ### §7 restrictions -/

/-- The paths of §7.1 that lead to the pattern being checked. -/
structure Path7 where
  inAttr : Bool := false
  inOneOrMore : Bool := false
  inOneOrMoreGroup : Bool := false
  inList : Bool := false
  inExcept : Bool := false
  inStart : Bool := false

/-- §7.1: prohibited paths. -/
def check71 (c : Path7) : Pattern → Except String Unit
  | .attribute _ p => do
    if c.inAttr then throw "attribute//attribute"
    if c.inOneOrMoreGroup then throw "oneOrMore//group//attribute or oneOrMore//interleave//attribute"
    if c.inList then throw "list//attribute"
    if c.inExcept then throw "data/except//attribute"
    if c.inStart then throw "start//attribute"
    check71 { c with inAttr := true } p
  | .ref _ => do
    if c.inAttr then throw "attribute//ref"
    if c.inList then throw "list//ref"
    if c.inExcept then throw "data/except//ref"
  | .oneOrMore p => do
    if c.inExcept then throw "data/except//oneOrMore"
    if c.inStart then throw "start//oneOrMore"
    check71 { c with inOneOrMore := true } p
  | .group a b => do
    if c.inExcept then throw "data/except//group"
    if c.inStart then throw "start//group"
    let c' := if c.inOneOrMore then { c with inOneOrMoreGroup := true } else c
    check71 c' a; check71 c' b
  | .interleave a b => do
    if c.inList then throw "list//interleave"
    if c.inExcept then throw "data/except//interleave"
    if c.inStart then throw "start//interleave"
    let c' := if c.inOneOrMore then { c with inOneOrMoreGroup := true } else c
    check71 c' a; check71 c' b
  | .list p => do
    if c.inList then throw "list//list"
    if c.inExcept then throw "data/except//list"
    if c.inStart then throw "start//list"
    check71 { c with inList := true } p
  | .text => do
    if c.inList then throw "list//text"
    if c.inExcept then throw "data/except//text"
    if c.inStart then throw "start//text"
  | .data _ _ => do
    if c.inStart then throw "start//data"
  | .dataExcept _ _ e => do
    if c.inStart then throw "start//data"
    check71 { c with inExcept := true } e
  | .value .. => do
    if c.inStart then throw "start//value"
  | .empty => do
    if c.inExcept then throw "data/except//empty"
    if c.inStart then throw "start//empty"
  | .choice a b => do check71 c a; check71 c b
  | _ => pure ()

/-- §7.2: content types, ordered `empty < complex < simple`. -/
inductive CT where
  | empty | complex | simple
deriving DecidableEq

def CT.rank : CT → Nat
  | .empty => 0 | .complex => 1 | .simple => 2

def CT.max (a b : CT) : CT := if a.rank ≥ b.rank then a else b

/-- §7.2: two content types are groupable when one is empty or both are
complex. -/
def CT.groupable (a b : CT) : Bool :=
  a == .empty || b == .empty || (a == .complex && b == .complex)

/-- §7.2: the content type of a pattern, `none` when it has none. -/
def contentType : Pattern → Option CT
  | .value .. | .data .. | .list _ => some .simple
  | .dataExcept _ _ e => (contentType e).map (fun _ => .simple)
  | .text | .ref _ => some .complex
  | .empty | .notAllowed => some .empty
  | .attribute _ p => (contentType p).map (fun _ => .empty)
  | .group a b | .interleave a b => do
    let x ← contentType a
    let y ← contentType b
    if x.groupable y then some (x.max y) else none
  | .choice a b => do
    let x ← contentType a
    let y ← contentType b
    some (x.max y)
  | .oneOrMore p => do
    let x ← contentType p
    if x.groupable x then some x else none
  | _ => none

/-- An illegal local name and namespace URI: no XML name equals them. -/
def illegalName : String := "\x01"

/-- Representative names of a name class, for the overlap test of §7.3 and
§7.4. -/
def NameClass.reps : NameClass → List QN
  | .name ns l => [⟨ns, l⟩]
  | .nsName ns => [⟨ns, illegalName⟩]
  | .nsNameExcept ns e => ⟨ns, illegalName⟩ :: e.reps
  | .anyName => [⟨illegalName, illegalName⟩]
  | .anyNameExcept e => ⟨illegalName, illegalName⟩ :: e.reps
  | .choice a b => a.reps ++ b.reps

/-- Do two name classes contain a common name? -/
def overlap (a b : NameClass) : Bool :=
  (a.reps ++ b.reps).any (fun q => a.contains q && b.contains q)

/-- Does a name class contain infinitely many names? -/
def NameClass.infinite : NameClass → Bool
  | .anyName | .anyNameExcept _ | .nsName _ | .nsNameExcept _ _ => true
  | .choice a b => a.infinite || b.infinite
  | _ => false

/-- The name classes of the attributes of a pattern (not inside elements). -/
def attrNCs (acc : List NameClass) : Pattern → List NameClass
  | .attribute nc _ => nc :: acc
  | .choice a b | .interleave a b | .group a b => attrNCs (attrNCs acc a) b
  | .oneOrMore p => attrNCs acc p
  | _ => acc

/-- §7.3: no two attributes of a `group` or `interleave` can have the same
name, and an attribute with an infinite name class repeats. -/
def check73 (inOne : Bool) : Pattern → Except String Unit
  | .attribute nc _ =>
    if nc.infinite && !inOne then .error "attribute with anyName or nsName outside oneOrMore"
    else .ok ()
  | .group a b | .interleave a b => do
    check73 inOne a
    check73 inOne b
    for x in attrNCs [] a do
      for y in attrNCs [] b do
        if overlap x y then throw "duplicate attribute"
  | .choice a b => do check73 inOne a; check73 inOne b
  | .oneOrMore p => check73 true p
  | _ => .ok ()

/-- The name classes of the elements a pattern refers to (not inside
elements), and whether it holds `text`. -/
def elemNCs (defs : Std.HashMap String (NameClass × Pattern)) (acc : List NameClass × Bool) :
    Pattern → List NameClass × Bool
  | .ref n => match defs[n]? with
    | some (nc, _) => (nc :: acc.1, acc.2)
    | none => acc
  | .text => (acc.1, true)
  | .choice a b | .interleave a b | .group a b => elemNCs defs (elemNCs defs acc a) b
  | .oneOrMore p => elemNCs defs acc p
  | _ => acc

/-- §7.4: the two sides of an `interleave` have no element name and no
`text` in common. -/
def check74 (defs : Std.HashMap String (NameClass × Pattern)) : Pattern → Except String Unit
  | .interleave a b => do
    check74 defs a
    check74 defs b
    let (xa, ta) := elemNCs defs ([], false) a
    let (xb, tb) := elemNCs defs ([], false) b
    if ta && tb then throw "text in both sides of interleave"
    for x in xa do
      for y in xb do
        if overlap x y then throw "element name in both sides of interleave"
  | .group a b | .choice a b => do check74 defs a; check74 defs b
  | .oneOrMore p => check74 defs p
  | _ => .ok ()

/-- Pass 4: from the start pattern and the uniquely named `define`s to the
simple syntax, with the checks of §7. -/
def finish (start : Pattern) (defs : Array (String × Pattern)) : Except String Grammar := do
  -- §4.19: lift elements
  let (start1, defs1, ls) := Id.run do
    let mut st : LState := {}
    let (s1, st1) := (lift start).run st
    st := st1
    let mut out : Array (String × Pattern) := #[]
    for (n, p) in defs do
      let (p1, st2) := (lift p).run st
      st := st2
      out := out.push (n, p1)
    return (s1, out, st)
  let table : Std.HashMap String Pattern :=
    defs1.foldl (fun m (n, p) => m.insert n p) {}
  let fuel := defs1.size + 1
  let start2 ← inline table fuel [] start1
  let mut edefs : Std.HashMap String (NameClass × Pattern) := {}
  for (n, nc, p) in ls.edefs do
    let p' ← inline table fuel [] p
    edefs := edefs.insert n (nc, norm p')
  let start3 := norm start2
  let keep := reachable edefs start3
  let kept := keep.filterMap (fun n => (edefs[n]?).map (fun (nc, p) => (n, nc, p)))
  -- §7
  check71 { inStart := true } start3
  for (_, _, p) in kept do
    check71 {} p
    if (contentType p).isNone then throw "string sequence in element content"
    check73 false p
    check74 edefs p
  return { start := start3, defs := kept }

/-- Simplify a schema whose document element is `root`, with base URI
`base`; `resolve` gives the text of the documents that `externalRef` and
`include` name (by their resolved URI). -/
def simplifyNode (resolve : String → Option String) (base : String) (root : Node) :
    Except String Grammar := do
  let r ← readSchemaNode base root
  let r ← expand resolve 64 [base] r
  let (start, defs) ← trTop r
  finish start defs

/-- Simplify a schema given as text. -/
def simplifyText (resolve : String → Option String) (base : String) (txt : String) :
    Except String Grammar := do
  match parseXML txt with
  | .error e => throw s!"not well-formed: {e.message}"
  | .ok d => simplifyNode resolve base d.root

end L4Factoidal.RelaxNG
