/-
L4Factoidal.XML.C14n — the three XML canonicalization methods of XML
Signature, over a DOCUMENT SUBSET (an XPath 1.0 node-set), with and
without comments:

  * Canonical XML Version 1.0, W3C Recommendation 15 March 2001,
    https://www.w3.org/TR/2001/REC-xml-c14n-20010315
    (`http://www.w3.org/TR/2001/REC-xml-c14n-20010315`, and `#WithComments`);
  * Canonical XML Version 1.1, W3C Recommendation 2 May 2008,
    https://www.w3.org/TR/2008/REC-xml-c14n11-20080502/
    (`http://www.w3.org/2006/12/xml-c14n11`, and `#WithComments`);
  * Exclusive XML Canonicalization Version 1.0, W3C Recommendation
    18 July 2002, https://www.w3.org/TR/2002/REC-xml-exc-c14n-20020718/
    (`http://www.w3.org/2001/10/xml-exc-c14n#`, and `#WithComments`).

The input is the node table of `L4Factoidal.XPath4.Doc` (the XDM view of
the parse tree of `L4Factoidal.XML.Parser`) with the XPath 1.0 NAMESPACE
NODES added (`C14nDoc.ofDoc`: one per in-scope binding of each element,
XPath 1.0 §5.4), and a node-set given as a predicate on node indices.
Any producer of a node-set may be used: the whole document
(`wholeDocument`), an XPath filter (`L4Factoidal.XML.C14nXPath`), or the
subtree of one element (XML Signature same-document references).

The three methods share one function, `canonCore`. They differ in two
parameters only:

  * the namespace rule: inclusive (Canonical XML 1.0 and 1.1 §2.3,
    "Namespace Nodes") or exclusive (Exclusive XML Canonicalization §3,
    "visibly utilizes", with the InclusiveNamespaces PrefixList);
  * the attributes in the `xml` namespace that an element whose parent
    is omitted from the node-set takes from its ancestors: all of them in
    1.0 (§2.4); `xml:lang` and `xml:space`, and the `xml:base` fix-up, in
    1.1 (§2.4); none in the exclusive method (§3, item 2 of the list of
    differences).

So the theorems at the end of this file follow from the structure: on a
node-set in which no element's parent element is omitted, 1.0 and 1.1
give the same octets; the form without comments is the form with
comments of the node-set without its comment nodes.

Character escaping, attribute order and the namespace bookkeeping of the
exclusive method are those of `L4Factoidal.XML.Canonical` and
`L4Factoidal.XML.ExcC14n`, which this module reuses.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XPath4.Doc
import L4Factoidal.XML.ExcC14n
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XML.C14n

open L4Factoidal.XPath4
open L4Factoidal.XML.Canonical (Scope escText escAttr sortBy strLt pairLt xmlNamespace declText)

/-! ## Methods -/

/-- The specification, with its version. A later version is a new
constructor, not a change to an existing one. -/
inductive Version where
  /-- Canonical XML Version 1.0 (W3C Recommendation 2001-03-15). -/
  | c14n10
  /-- Canonical XML Version 1.1 (W3C Recommendation 2008-05-02). -/
  | c14n11
  /-- Exclusive XML Canonicalization Version 1.0 (W3C Recommendation 2002-07-18). -/
  | exc10
deriving DecidableEq, Repr, Inhabited

structure Method where
  version : Version
  comments : Bool := false
  /-- The InclusiveNamespaces PrefixList (Exclusive §3); `#default` is the
      default namespace. Ignored by the inclusive methods. -/
  inclusivePrefixes : List String := []
deriving Repr, Inhabited

/-- The algorithm identifiers of the three Recommendations. -/
def Method.ofUri? (u : String) : Option Method :=
  if u == "http://www.w3.org/TR/2001/REC-xml-c14n-20010315" then some { version := .c14n10 }
  else if u == "http://www.w3.org/TR/2001/REC-xml-c14n-20010315#WithComments" then
    some { version := .c14n10, comments := true }
  else if u == "http://www.w3.org/2006/12/xml-c14n11" then some { version := .c14n11 }
  else if u == "http://www.w3.org/2006/12/xml-c14n11#WithComments" then
    some { version := .c14n11, comments := true }
  else if u == "http://www.w3.org/2001/10/xml-exc-c14n#" then some { version := .exc10 }
  else if u == "http://www.w3.org/2001/10/xml-exc-c14n#WithComments" then
    some { version := .exc10, comments := true }
  else none

/-! ## The node table with namespace nodes -/

/-- The namespace nodes of an element (XPath 1.0 §5.4): one per prefix in
scope, the nearest declaration winning, and none for a prefix whose
nearest declaration is empty (`xmlns=""` undeclares the default
namespace). `NRec.inscope` lists the newest declaration first. -/
def nsBindings (r : NRec) : List (String × String) :=
  let firsts := r.inscope.foldl (fun acc b =>
    if acc.any (fun x => x.1 == b.1) then acc else acc ++ [b]) []
  firsts.filter (fun b => b.2 != "")

/-- A node table with namespace nodes, and the number of nodes it had
before they were added (those are the nodes of the document in document
order; the namespace nodes come after them). -/
structure C14nDoc where
  doc : Doc
  n0 : Nat

/-- Add one namespace node per binding of `nsBindings` to every element,
before its attribute nodes (XDM: an element's namespace nodes, then its
attributes). The node's name is the prefix (`""` for the default
namespace) and its value is the namespace name. -/
def C14nDoc.ofDoc (d : Doc) : C14nDoc := Id.run do
  let n := d.nodes.size
  let mut a := d.nodes
  for i in [0:n] do
    let r := a.getD i default
    if r.kind != .element then continue
    let mut ids : Array Nat := #[]
    for (p, u) in nsBindings r do
      ids := ids.push a.size
      a := a.push { kind := .namespace, name := { uri := "", loc := p }, value := u,
                    parent := some i, last := a.size }
    a := a.modify i (fun r => { r with attrs := ids ++ r.attrs })
  pure { doc := { d with nodes := a }, n0 := n }

/-- Parse a document and build its node table. -/
def C14nDoc.ofString? (s : String) : Except String C14nDoc :=
  (Doc.ofString s).map C14nDoc.ofDoc

/-- The document as a node-set: every node. -/
def wholeDocument : Nat → Bool := fun _ => true

/-! ## Navigation -/

def kindOf (d : Doc) (i : Nat) : NKind := (d.get i).kind

/-- The parent of a node when it is an element. -/
def parentElem? (d : Doc) (i : Nat) : Option Nat :=
  match (d.get i).parent with
  | some p => if (d.get p).kind == .element then some p else none
  | none => none

/-- The ancestor elements of a node, nearest first. A loop over the
parent links, bounded by the size of the table. -/
def ancestorElems (d : Doc) (i : Nat) : List Nat :=
  go d.nodes.size (d.get i).parent []
where
  go : Nat → Option Nat → List Nat → List Nat
    | 0, _, acc => acc.reverse
    | _, none, acc => acc.reverse
    | f + 1, some j, acc =>
        if (d.get j).kind == .element then go f (d.get j).parent (j :: acc) else acc.reverse

def nsNodes (d : Doc) (i : Nat) : List Nat :=
  (d.get i).attrs.toList.filter (fun j => (d.get j).kind == .namespace)

def attrNodes (d : Doc) (i : Nat) : List Nat :=
  (d.get i).attrs.toList.filter (fun j => (d.get j).kind == .attribute)

/-- The QName of an element or attribute as written. -/
def qnameText (q : QN) : String := if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc

/-- The `xml:*` attributes of an element: local name and value. -/
def xmlAttrs (d : Doc) (k : Nat) : List (String × String) :=
  (attrNodes d k).filterMap fun j =>
    let r := d.get j
    if r.name.uri == nsXML then some (r.name.loc, r.value) else none

/-! ## The namespace axis -/

/-- Canonical XML 1.0 and 1.1 §2.3 Namespace Nodes, for an element `i` in
the node-set: its namespace nodes in the node-set, less the `xml` binding,
less those that the nearest ancestor element in the node-set also has in
the node-set with the same prefix and value; and `xmlns=""` when `i` has
no default namespace node in the node-set and that ancestor has one. -/
def inclusiveDecls (d : Doc) (set : Nat → Bool) (i : Nat) : List (String × String) :=
  let pairs (k : Nat) := ((nsNodes d k).filter set).map fun j => ((d.get j).name.loc, (d.get j).value)
  let mine := (pairs i).filter (fun b => !(b.1 == "xml" && b.2 == xmlNamespace))
  let ancNs := match (ancestorElems d i).find? set with
    | some a => pairs a
    | none => []
  let kept := mine.filter (fun b => !ancNs.contains b)
  let undecl := if mine.all (·.1 != "") && ancNs.any (fun b => b.1 == "" && b.2 != "")
    then [("", "")] else []
  sortBy (fun a b => strLt a.1 b.1) (kept ++ undecl)

/-- Exclusive XML Canonicalization §3, for an element `i` in the node-set
below output ancestors that rendered `rendered`: the declarations of the
prefixes that `i` visibly utilizes (its own prefix, `""` when it has
none, and the prefixes of its attributes in the node-set), and of the
InclusiveNamespaces prefixes, by `ExcC14n.declFor`. `none`: a utilized
prefix that no namespace node binds. -/
def exclusiveDecls (incl : List String) (d : Doc) (set : Nat → Bool) (rendered : Scope)
    (i : Nat) : Option (List (String × String)) :=
  let own : Scope := (nsNodes d i).map fun j => ((d.get j).name.loc, (d.get j).value)
  let r := d.get i
  let attrPfx := ((attrNodes d i).filter set).filterMap fun j =>
    let p := (d.get j).name.pfx
    if p == "" || p == "xml" then none else some p
  let used := ((r.name.pfx :: attrPfx).eraseDups).filter (· != "xml")
  let extra := (incl.map ExcC14n.prefixOfToken).eraseDups.filter
    (fun p => p != "xml" && !used.contains p)
  let step (req : Bool) (acc : Option (List (String × String))) (p : String) :=
    acc.bind fun ds => (ExcC14n.declFor own rendered req p).map fun dd => ds ++ dd.toList
  let ds := extra.foldl (step false) (used.foldl (step true) (some []))
  ds.map (sortBy (fun a b => strLt a.1 b.1))

/-! ## Attributes in the `xml` namespace (§2.4 of both versions) -/

/-- The element's parent is an element omitted from the node-set. -/
def parentOmitted (d : Doc) (set : Nat → Bool) (i : Nat) : Bool :=
  match parentElem? d i with
  | some p => !set p
  | none => false

/-- The nearest occurrence on the ancestor axis of each `xml:*` attribute
whose local name satisfies `keep`, whether or not the ancestor or the
attribute is in the node-set, less the names on `i`'s own attribute
axis. -/
def nearestXmlAttrs (d : Doc) (i : Nat) (keep : String → Bool) : List (String × String) :=
  let own := (xmlAttrs d i).map (·.1)
  let found := (ancestorElems d i).foldl (fun acc k =>
    acc ++ (xmlAttrs d k).filter (fun b => keep b.1 && !acc.any (·.1 == b.1))) []
  found.filter (fun b => !own.contains b.1)

/-- An override of an element's `xml:*` attributes: local name, and the
value to render (`none`: render none). -/
abbrev XmlFix := List (String × Option String)

/-- Canonical XML 1.0 §2.4: all `xml:*` attributes are inherited. -/
def fix10 (d : Doc) (set : Nat → Bool) (i : Nat) : XmlFix :=
  if set i && parentOmitted d set i then
    (nearestXmlAttrs d i (fun _ => true)).map fun b => (b.1, some b.2)
  else []

/-! ### The xml:base fix-up of Canonical XML 1.1 §2.4 -/

/-- Canonical XML 1.1 §2.4, the modified RFC 3986 §5.2.4 "Remove Dot
Segments": consecutive `/` become one, leading `../` segments are kept,
a trailing `..` gets a `/`, and a relative path stays relative. The
`#guard`s below are the Appendix table of the Recommendation. -/
def removeDotSegments11 (path : String) : String :=
  let abs := path.startsWith "/"
  let segs := (path.splitOn "/").filter (· != "")
  let trailing := path.endsWith "/" ||
    (match segs.getLast? with | some s => s == "." || s == ".." | none => false)
  let stack := segs.foldl (fun (st : List String) s =>
    if s == "." then st
    else if s == ".." then
      match st with
      | t :: rest => if t == ".." then ".." :: st else rest
      | [] => if abs then [] else [".."]
    else s :: st) []
  let body := String.intercalate "/" stack.reverse
  if stack.isEmpty then (if abs then "/" else "")
  else (if abs then "/" else "") ++ body ++ (if trailing then "/" else "")

/-- RFC 3986 §5.2.2 with the modifications of Canonical XML 1.1 §2.4: the
dot segments are removed by `removeDotSegments11`; the parsing, the merge
and the recomposition are those of `Syntax.IriResolve`. -/
def transform11 (base r : Syntax.IriParts) : Syntax.IriParts :=
  let rds := removeDotSegments11
  match r.scheme with
  | some _ => { r with path := rds r.path }
  | none =>
      match r.authority with
      | some _ => { r with scheme := base.scheme, path := rds r.path }
      | none =>
          if r.path.isEmpty then
            { scheme := base.scheme, authority := base.authority, path := base.path,
              query := (match r.query with | some _ => r.query | none => base.query),
              fragment := r.fragment }
          else
            let p := if r.path.startsWith "/" then rds r.path
                     else rds (Syntax.mergePaths base r.path)
            { scheme := base.scheme, authority := base.authority, path := p,
              query := r.query, fragment := r.fragment }

/-- The "join-URI-References" function of Canonical XML 1.1 §2.4: the
base may have no scheme; a trailing `..` segment of the base becomes
`../`; the fragment of the reference is ignored. -/
def joinUriRefs (base ref : String) : String :=
  let base := if base == ".." || base.endsWith "/.." then base ++ "/" else base
  let r := { Syntax.parseIri ref with fragment := none }
  Syntax.recompose (transform11 (Syntax.parseIri base) r)

/-- The `xml:base` values that the fix-up of element `i` combines, from
the outermost to the innermost: those of the contiguously omitted
ancestors `E1 ... En` (§2.4: the walk up the ancestor axis stops at the
first ancestor in the node-set), then `i`'s own. `none`: none of them
has an `xml:base`, so there is no fix-up.

Example §3.8 of the Recommendation shows `something/bar/foo` on `e3`,
which also takes the `xml:base` of `doc` above the included `e1`; the
text of §2.4 ("only e2 in the example in Section 3.8") and the interop
case `xmlbase-c14n11spec2-102`, the same input, which all five
implementations canonicalized alike, give `bar/foo`. This function
follows §2.4 (https://github.com/danbri/factoidal/issues/1168). -/
def baseChain (d : Doc) (set : Nat → Bool) (i : Nat) : Option (List String) :=
  let base (k : Nat) := ((xmlAttrs d k).find? (·.1 == "base")).map (·.2)
  let omitted := ((ancestorElems d i).takeWhile (fun k => !set k)).reverse.filterMap base
  if omitted.isEmpty then none else some (omitted ++ (base i).toList)

/-- Reduce the values in reverse document order: `Xm` with `Xm-1`, then
the result with `Xm-2`, and so on. -/
def joinChain : List String → String
  | [] => ""
  | xs => match xs.reverse with
    | [] => ""
    | x :: rest => rest.foldl (fun acc b => joinUriRefs b acc) x

/-- Canonical XML 1.1 §2.4: `xml:lang` and `xml:space` are inherited;
`xml:id` is not; `xml:base` is fixed up; an empty result renders no
`xml:base`. -/
def fix11 (d : Doc) (set : Nat → Bool) (i : Nat) : XmlFix :=
  if set i && parentOmitted d set i then
    let simple := (nearestXmlAttrs d i (fun n => n == "lang" || n == "space")).map
      fun b => (b.1, some b.2)
    match baseChain d set i with
    | some xs => let v := joinChain xs
                 simple ++ [("base", if v.isEmpty then none else some v)]
    | none => simple
  else []

/-! ## The canonical form -/

/-- An element whose end tag is still to come. -/
structure Open where
  last : Nat
  shown : Bool
  tag : String
  /-- Exclusive method: the bindings rendered by this element and its
      output ancestors. -/
  rendered : Scope

/-- Close the elements whose subtrees end before node `i`. A tail call
per element closed. -/
def closeBefore (i : Nat) : List Open → String → String × List Open
  | [], out => (out, [])
  | o :: rest, out =>
      if o.last < i then
        closeBefore i rest (if o.shown then out ++ "</" ++ o.tag ++ ">" else out)
      else (out, o :: rest)

/-- §2.3 Element Nodes: the attributes in the node-set, with the `xml:*`
override applied, sorted by namespace name and then local name. -/
def attrsText (d : Doc) (set : Nat → Bool) (fix : XmlFix) (i : Nat) : String :=
  let plain := ((attrNodes d i).filter set).filterMap fun j =>
    let r := d.get j
    if r.name.uri == nsXML && fix.any (·.1 == r.name.loc) then none
    else some ((r.name.uri, r.name.loc), qnameText r.name, r.value)
  let extra := fix.filterMap fun (l, v) =>
    v.map fun v => ((nsXML, l), "xml:" ++ l, v)
  let sorted := sortBy (fun a b => pairLt a.1 b.1) (plain ++ extra)
  String.join (sorted.map fun (_, n, v) => " " ++ n ++ "=\"" ++ escAttr v ++ "\"")

/-- The canonical form of node-set `set` of `cd`. `exclusive`: the
namespace rule of Exclusive XML Canonicalization, with PrefixList
`incl`; otherwise that of Canonical XML. `fix`: the `xml:*` attributes an
element takes from its ancestors. The nodes are visited in document
order, one loop iteration each; the open elements are a list.
`.error`: an element in the node-set uses a prefix that no namespace
node binds (exclusive method only). -/
def canonCore (exclusive : Bool) (incl : List String) (fix : Nat → XmlFix)
    (cd : C14nDoc) (set : Nat → Bool) : Except String String := Id.run do
  let d := cd.doc
  let rootEl := ((d.get 0).children.toList.find? (fun c => kindOf d c == .element)).getD 0
  let mut out := ""
  let mut stack : List Open := []
  for i in [0:cd.n0] do
    let r := d.get i
    if r.kind == .attribute || r.kind == .namespace || r.kind == .document then continue
    let (o, s) := closeBefore i stack out
    out := o
    stack := s
    let top := (d.get (r.parent.getD 0)).kind == .document
    let wrap (t : String) : String :=
      if !top then t else if i < rootEl then t ++ "\n" else "\n" ++ t
    match r.kind with
    | .text => if set i then out := out ++ escText r.value
    | .comment => if set i then out := out ++ wrap ("<!--" ++ r.value ++ "-->")
    | .pi =>
        if set i then
          out := out ++ wrap ("<?" ++ r.name.loc ++ (if r.value.isEmpty then "" else " " ++ r.value) ++ "?>")
    | .element =>
        let rendered := match stack with | o :: _ => o.rendered | [] => []
        let tag := qnameText r.name
        if set i then
          let decls ← if exclusive then
              match exclusiveDecls incl d set rendered i with
              | some ds => pure ds
              | none => return .error ("unbound prefix on element " ++ tag)
            else pure (inclusiveDecls d set i)
          out := out ++ "<" ++ tag ++ declText decls ++ attrsText d set (fix i) i ++ ">"
          stack := { last := r.last, shown := true, tag,
                     rendered := decls.foldl ExcC14n.setRendered rendered } :: stack
        else
          stack := { last := r.last, shown := false, tag, rendered } :: stack
    | _ => pure ()
  let (o, _) := closeBefore cd.n0 stack out
  return .ok o

/-- The node-set a method canonicalizes: without comments, the comment
nodes are removed (Canonical XML 1.0 §2.1, "the canonical form omits
comments": the node-set less its comment nodes). -/
def effectiveSet (m : Method) (cd : C14nDoc) (set : Nat → Bool) : Nat → Bool :=
  if m.comments then set else fun i => set i && kindOf cd.doc i != .comment

def fixFor (v : Version) (cd : C14nDoc) (set : Nat → Bool) : Nat → XmlFix :=
  match v with
  | .c14n10 => fix10 cd.doc set
  | .c14n11 => fix11 cd.doc set
  | .exc10 => fun _ => []

/-- The canonical form of a node-set by a method. -/
def canonicalize (m : Method) (cd : C14nDoc) (set : Nat → Bool) : Except String String :=
  let s := effectiveSet m cd set
  canonCore (m.version == .exc10) m.inclusivePrefixes (fixFor m.version cd s) cd s

/-- The canonical form of a whole document given as text. -/
def canonString? (m : Method) (src : String) : Except String String :=
  (C14nDoc.ofString? src).bind fun cd => canonicalize m cd wholeDocument

/-- The node-set of one element and everything below it (its attribute
and namespace nodes included): the subset that an XML Signature
reference to an element produces. -/
def subtreeSet (cd : C14nDoc) (apex : Nat) : Nat → Bool := fun i =>
  let last := (cd.doc.get apex).last
  (apex ≤ i && i ≤ last) ||
  (i ≥ cd.n0 && match (cd.doc.get i).parent with
                | some p => apex ≤ p && p ≤ last
                | none => false)

/-! ## Theorems relating the versions -/

/-- No element in the node-set has a parent element omitted from it. The
whole document is such a node-set, and so is every node-set that an
XPath filter `ancestor-or-self::X` selects below the document element. -/
def ParentClosed (cd : C14nDoc) (set : Nat → Bool) : Prop :=
  ∀ i p, set i = true → parentElem? cd.doc i = some p → set p = true

theorem parentElem?_kind {d : Doc} {i p : Nat} (h : parentElem? d i = some p) :
    (d.get p).kind = .element := by
  unfold parentElem? at h
  split at h
  · split at h
    · rename_i hk; cases h; exact of_decide_eq_true hk
    · cases h
  · cases h

theorem parentOmitted_false_of_closed {cd : C14nDoc} {set : Nat → Bool}
    (h : ParentClosed cd set) (i : Nat) (hi : set i = true) :
    parentOmitted cd.doc set i = false := by
  unfold parentOmitted
  split
  · rename_i p hp; simp [h i p hi hp]
  · rfl

theorem fix10_closed {cd : C14nDoc} {set : Nat → Bool} (h : ParentClosed cd set) :
    fix10 cd.doc set = fun _ => [] := by
  funext i
  unfold fix10
  cases hi : set i with
  | false => simp
  | true => simp [parentOmitted_false_of_closed h i hi]

theorem fix11_closed {cd : C14nDoc} {set : Nat → Bool} (h : ParentClosed cd set) :
    fix11 cd.doc set = fun _ => [] := by
  funext i
  unfold fix11
  cases hi : set i with
  | false => simp
  | true => simp [parentOmitted_false_of_closed h i hi]

/-- Removing the comment nodes keeps a node-set parent-closed: a parent
element is not a comment. -/
theorem effectiveSet_closed (m : Method) {cd : C14nDoc} {set : Nat → Bool}
    (h : ParentClosed cd set) : ParentClosed cd (effectiveSet m cd set) := by
  intro i p hi hp
  unfold effectiveSet at *
  cases hc : m.comments with
  | true => simp [hc] at hi ⊢; exact h i p hi hp
  | false =>
      simp [hc] at hi ⊢
      refine ⟨h i p hi.1 hp, ?_⟩
      simp [kindOf, parentElem?_kind hp]

/-- Canonical XML 1.1 (2008) and Canonical XML 1.0 (2001) give the same
octets on every node-set in which no element's parent element is
omitted, with comments or without: the two versions differ only in the
`xml:*` attributes of an element whose parent is omitted (Canonical XML
1.1 §1.1 and §2.4). -/
theorem c14n11_eq_c14n10_of_parentClosed (c : Bool) (cd : C14nDoc) (set : Nat → Bool)
    (h : ParentClosed cd set) :
    canonicalize { version := .c14n11, comments := c } cd set
      = canonicalize { version := .c14n10, comments := c } cd set := by
  have h' := effectiveSet_closed { version := .c14n11, comments := c } h
  simp only [canonicalize, fixFor]
  have e : effectiveSet { version := .c14n11, comments := c } cd set
      = effectiveSet { version := .c14n10, comments := c } cd set := rfl
  rw [← e, fix11_closed h', fix10_closed h']
  rfl

theorem wholeDocument_closed (cd : C14nDoc) : ParentClosed cd wholeDocument :=
  fun _ _ _ _ => rfl

/-- For a whole document, Canonical XML 1.1 equals Canonical XML 1.0. -/
theorem c14n11_eq_c14n10_wholeDocument (c : Bool) (cd : C14nDoc) :
    canonicalize { version := .c14n11, comments := c } cd wholeDocument
      = canonicalize { version := .c14n10, comments := c } cd wholeDocument :=
  c14n11_eq_c14n10_of_parentClosed c cd wholeDocument (wholeDocument_closed cd)

/-- The form without comments is the form with comments of the node-set
less its comment nodes, for each of the three Recommendations
(Canonical XML 1.0 §2.1, 1.1 §2.1, Exclusive §1). -/
theorem uncommented_eq_commented (v : Version) (incl : List String) (cd : C14nDoc)
    (set : Nat → Bool) :
    canonicalize { version := v, comments := false, inclusivePrefixes := incl } cd set
      = canonicalize { version := v, comments := true, inclusivePrefixes := incl } cd
          (fun i => set i && kindOf cd.doc i != .comment) := rfl

/-- The exclusive method takes no `xml:*` attribute from an ancestor
(Exclusive XML Canonicalization §3, the second difference from
Canonical XML). -/
theorem exc10_no_xml_inheritance (cd : C14nDoc) (set : Nat → Bool) :
    fixFor .exc10 cd set = fun _ => [] := rfl

/-! ## Checks -/

def c10 : Method := { version := .c14n10 }
def c10c : Method := { version := .c14n10, comments := true }
def c11 : Method := { version := .c14n11 }
def e10 : Method := { version := .exc10 }

/-- The same check through the whole-document functions of
`L4Factoidal.XML.Canonical`. -/
def viaCanonical? (comments : Bool) (s : String) : Option String :=
  match parseXML s with
  | .ok d => some (if comments then Canonical.canonDocument d else Canonical.canonDocumentNoComments d)
  | .error _ => none

def viaSubset? (m : Method) (s : String) : Option String :=
  match canonString? m s with
  | .ok o => some o
  | .error _ => none

-- Whole documents: this module agrees with `XML.Canonical`.
#guard viaSubset? c10c "<!--a--><?p d?><doc xmlns:p=\"u\" b=\"2\" a=\"1\"><p:e xmlns:p=\"u\"/>x<!--c--></doc><!--z-->"
  == viaCanonical? true "<!--a--><?p d?><doc xmlns:p=\"u\" b=\"2\" a=\"1\"><p:e xmlns:p=\"u\"/>x<!--c--></doc><!--z-->"
#guard viaSubset? c10 "<!--a--><doc xmlns=\"u\"><e xmlns=\"\"/>x<!--c--></doc>"
  == viaCanonical? false "<!--a--><doc xmlns=\"u\"><e xmlns=\"\"/>x<!--c--></doc>"
#guard viaSubset? c10 "<a xmlns=\"u\"><b xmlns=\"\"/></a>" == some "<a xmlns=\"u\"><b xmlns=\"\"></b></a>"
#guard viaSubset? c10 "<a><b xmlns=\"\"/></a>" == some "<a><b></b></a>"
-- Exclusive, whole document: agrees with `XML.ExcC14n`.
#guard viaSubset? e10 "<a xmlns:p=\"u\" xmlns:q=\"v\"><p:b/></a>"
  == ExcC14n.canonText? [] "<a xmlns:p=\"u\" xmlns:q=\"v\"><p:b/></a>"
#guard viaSubset? e10 "<a xmlns=\"u\"><b xmlns=\"\"/></a>" == some "<a xmlns=\"u\"><b xmlns=\"\"></b></a>"
#guard viaSubset? { version := .exc10, inclusivePrefixes := ["xs"] }
    "<a xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"><b/></a>"
  == some "<a xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"><b></b></a>"

-- The subtree of an element: 1.0 imports the xml:* attributes of the
-- ancestors, 1.1 only xml:lang and xml:space, exclusive none.
def subtreeCanon? (m : Method) (s : String) (apexName : String) : Option String :=
  match C14nDoc.ofString? s with
  | .ok cd =>
      let apex := (List.range cd.n0).find? fun i =>
        kindOf cd.doc i == .element && (cd.doc.get i).name.loc == apexName
      apex.bind fun a => match canonicalize m cd (subtreeSet cd a) with
        | .ok o => some o
        | .error _ => none
  | .error _ => none

#guard subtreeCanon? c10 "<r xml:lang=\"en\" xml:id=\"x\" xmlns:p=\"u\"><p:a/></r>" "a"
  == some "<p:a xmlns:p=\"u\" xml:id=\"x\" xml:lang=\"en\"></p:a>"
#guard subtreeCanon? c11 "<r xml:lang=\"en\" xml:id=\"x\" xmlns:p=\"u\"><p:a/></r>" "a"
  == some "<p:a xmlns:p=\"u\" xml:lang=\"en\"></p:a>"
#guard subtreeCanon? e10 "<r xml:lang=\"en\" xml:id=\"x\" xmlns:p=\"u\" xmlns:q=\"v\"><p:a/></r>" "a"
  == some "<p:a xmlns:p=\"u\"></p:a>"
-- The inclusive methods render every in-scope binding on the apex.
#guard subtreeCanon? c10 "<r xmlns:p=\"u\" xmlns:q=\"v\"><p:a/></r>" "a"
  == some "<p:a xmlns:p=\"u\" xmlns:q=\"v\"></p:a>"

-- The Appendix table of Canonical XML 1.1 (modified Remove Dot Segments).
#guard removeDotSegments11 "no/.././/pseudo-netpath/seg/file.ext" == "pseudo-netpath/seg/file.ext"
#guard removeDotSegments11 "yes/no//..//.///pseudo-netpath/seg/file.ext" == "yes/pseudo-netpath/seg/file.ext"
#guard removeDotSegments11 "../../no/../.." == "../../../"
#guard removeDotSegments11 "no/.." == ""
#guard removeDotSegments11 "/a/b/c/./../../g" == "/a/g"
#guard removeDotSegments11 "..yes/..no/..no/..no/../../../..yes" == "..yes/..yes"
#guard removeDotSegments11 "//no/.." == "/"
#guard removeDotSegments11 "/../../.." == "/"
#guard removeDotSegments11 ".." == "../"
-- §2.4: "abc/" and "../" give ""; "../" and "../" give "../../";
-- the example a/b/c/d gives "../../x".
#guard joinUriRefs "abc/" "../" == ""
#guard joinUriRefs "../" "../" == "../../"
#guard joinUriRefs ".." ".." == "../../"
#guard joinChain ["..", "..", "x"] == "../../x"

end L4Factoidal.XML.C14n
