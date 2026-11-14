/-
L4Factoidal.DOM.XPath.Project — the browser's DOM as the XPath 1.0 data model.

DOM XPath (`document.evaluate`, DOM §8) is evaluated by the tree's own XPath 1.0
evaluator, `L4Factoidal.XPath.Full` (`XPath/Data.lean`, `XPath/Eval.lean`), the one
XSLT 1.0 uses. There is no second evaluator. That evaluator works on `XML.Node` trees
and names a node by its address (the child indices from the document node, and a slot
for an attribute). This module is the adapter between the DOM arena and that model:

* `projDoc` projects the tree of a root in the arena to the evaluator's document, one
  `XML.Node` for each DOM node and in the same order;
* `pathOf` / `itemOfRef` give the address of a DOM node (the context node);
* `domOfPath` / `refOfItem` give the DOM node of an address (the result nodes).

Why a projection and not a tree interface: the evaluator's node identity, document
order (`Loc.key`) and all thirteen axes are stated over addresses in an `XML.Node`
tree, and XSLT, XPointer and the conformance suites depend on them as they are. Making
the evaluator generic over a tree interface would change every one of those functions.
A projection changes none of them, and the proof duty is small and local: the
projection keeps child order and child count, so an address means the same node on
both sides (`PROVED`/`TESTED` list in docs/designissues/2026-11-14-browser-xml-dom.md).

The differences between the two models, and what the projection does about each:

* A DocumentType is not a node of the XPath data model (XPath 1.0 §5). The projection
  leaves it out, and child indices count the other children (`xkids`).
* The DOM gives an element its namespace directly; `XML.Node` gives it by `xmlns`
  declarations. The projection writes the declarations that make the evaluator's
  namespace resolution (`XPath.Full.expandedName`) give the DOM's namespace: one for
  the element's own name when it differs from the inherited default, and one for each
  prefixed attribute. The DOM's own `xmlns` attributes are not attribute nodes: XPath
  has none for namespace declarations (§5.3). Of them the projection keeps, as
  declarations, each `xmlns:p` whose prefix no name of the element uses.
* A tree whose root is a Document or a DocumentFragment (a shadow root is one) projects
  to the evaluator's document node. A tree with any other root (an element that is not
  in a document) projects under a document node that stands for no DOM node (`wrapped`).
* Namespace nodes are not exposed by the DOM (it has no interface for them), so an
  address of one maps to no DOM node (`refOfItem`).

Recursion: `projNode` follows the nesting of the tree (one frame per level), as the
evaluator's own functions over `XML.Node` do. The address functions are loops.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.XPath.Eval

namespace L4Factoidal.DOM.XPathDom

open L4Factoidal.DOM

/-- The children of `id` that are nodes of the XPath data model: all but a DocumentType. -/
def xkids (d : Dom) (id : NodeId) : List NodeId :=
  (d.get id).kids.toList.filter fun c => (d.get c).type != .doctype

/-- The name the projection writes for an attribute in a namespace: its own prefix, `xml`
for the XML namespace, and a made prefix (no XML document can declare it: it holds a
space-free marker and the attribute's index) for an attribute that has a namespace and
no prefix (`setAttributeNS(ns, "local", v)`). -/
def attrPrefix (a : Attr) (i : Nat) : String :=
  -- the XML namespace has one prefix, `xml`, whatever prefix the DOM node carries
  -- (Namespaces in XML §3: no other prefix may be bound to it)
  if a.ns == some xmlNS then "xml" else
  match a.pfx with
  | some p => p
  | none => s!"_xpns{i}"

/-- The qualified name of an attribute in the projection. -/
def attrName (a : Attr) (i : Nat) : String :=
  match a.ns with
  | none => a.lname
  | some _ => attrPrefix a i ++ ":" ++ a.lname

/-- An attribute that the projection reads as a namespace declaration: one in the XMLNS
namespace, or one whose projected name is `xmlns` or begins `xmlns:`. -/
def isNsDeclAttr (a : Attr) (i : Nat) : Bool :=
  a.ns == some xmlnsNS || attrName a i == "xmlns" || (attrName a i).startsWith "xmlns:"

/-- The attributes of an element that are attribute nodes of the XPath data model, each
with its index in the element's attribute list, in that order. -/
def plainAttrs (n : Node) : List (Nat × Attr) :=
  (n.attrs.toList.zipIdx.map fun (a, i) => (i, a)).filter fun (i, a) => !isNsDeclAttr a i

/-- The index in the element's attribute list of the attribute at `slot` of the projection. -/
def attrDomIndex (n : Node) (slot : Nat) : Option Nat :=
  ((plainAttrs n)[slot]?).map (·.1)

/-- The slot in the projection of the attribute at index `idx` of the element's list. -/
def attrSlot (n : Node) (idx : Nat) : Option Nat :=
  (plainAttrs n).findIdx? fun x => x.1 == idx

/-- The prefix of an element in the projection: its own, but `xml` for an element in the
XML namespace (no other prefix and no default declaration may name that namespace, so
the DOM's `createElementNS(xmlNamespace, "foo")` is written `xml:foo`). -/
def elemPrefix (n : Node) : Option String :=
  if n.ns == some xmlNS then some "xml" else n.pfx

/-- The tag of an element in the projection: its qualified name. -/
def elemTag (n : Node) : String :=
  match elemPrefix n with
  | some p => p ++ ":" ++ n.lname
  | none => n.lname

/-- The namespace declarations the projection writes on an element so that the
evaluator's resolution gives the DOM's namespaces. `dflt` is the default namespace the
element inherits in the projection. -/
def elemDecls (n : Node) (dflt : Option String) : List XML.Attribute :=
  let own : List XML.Attribute := match elemPrefix n, n.ns with
    | some p, some u =>
      if p == "xml" || p == "xmlns" then []
      else [({ name := "xmlns:" ++ p, value := u } : XML.Attribute)]
    | some _, none => []
    | none, _ =>
      if n.ns == dflt then []
      else [({ name := "xmlns", value := n.ns.getD "" } : XML.Attribute)]
  let named := (plainAttrs n).foldl (fun (acc : List XML.Attribute) (x : Nat × Attr) =>
    match x.2.ns with
    | none => acc
    | some u =>
      let p := attrPrefix x.2 x.1
      if p == "xml" || p == "xmlns" || acc.any (fun y => y.name == "xmlns:" ++ p) then acc
      else acc ++ [({ name := "xmlns:" ++ p, value := u } : XML.Attribute)]) own
  -- The element's own `xmlns:p` attributes, for the prefixes that no name of the element
  -- uses: they are in scope for the element's content (a prefix in an XSLT stylesheet's
  -- expressions; the namespace axis). A declaration the evaluator's namespace layer
  -- would refuse (a reserved prefix or namespace name, an empty value) is left out.
  -- Where a DOM declaration and a node's own namespace disagree, the node's wins.
  n.attrs.toList.foldl (fun (acc : List XML.Attribute) (a : Attr) =>
    if a.ns == some xmlnsNS && a.pfx == some "xmlns" && a.lname != "xml" && a.lname != "xmlns"
        && a.value != "" && a.value != xmlNS && a.value != xmlnsNS
        && !acc.any (fun y => y.name == "xmlns:" ++ a.lname) then
      acc ++ [({ name := "xmlns:" ++ a.lname, value := a.value } : XML.Attribute)]
    else acc) named

/-- The attribute list of an element in the projection: its attribute nodes in order,
then the namespace declarations (`elemDecls`). The evaluator numbers attribute slots by
this list, so slot `i` is the `i`-th of `plainAttrs`. -/
def elemAttrs (n : Node) (dflt : Option String) : List XML.Attribute :=
  (plainAttrs n).map (fun x => ({ name := attrName x.2 x.1, value := x.2.value } : XML.Attribute)) ++
    elemDecls n dflt

/-- The default namespace the children of an element inherit in the projection. -/
def childDefault (n : Node) (dflt : Option String) : Option String :=
  match elemPrefix n with
  | some _ => dflt
  | none => n.ns

/-- The `XML.Node` of DOM node `id`, with its subtree. `fuel` bounds the nesting; a tree
of the arena is never deeper than the arena's size. -/
def projNode (d : Dom) : Nat → Option String → NodeId → XML.Node
  | 0, _, _ => XML.Node.text ""
  | fuel + 1, dflt, id =>
    let n := d.get id
    match n.type with
    | .element =>
      XML.Node.element (elemTag n) (elemAttrs n dflt)
        ((xkids d id).map fun c => projNode d fuel (childDefault n dflt) c)
    | .cdata => XML.Node.cdata n.data
    | .comment => XML.Node.comment n.data
    | .pi => XML.Node.pi n.lname n.data
    | _ => XML.Node.text n.data

/-- The root of a tree is not a Document or a DocumentFragment: the projection puts it
under a document node that stands for no DOM node. -/
def wrapped (d : Dom) (root : NodeId) : Bool :=
  !((d.get root).type == .document || (d.get root).type == .fragment)

/-- The evaluator's document of the tree of `root`. -/
def projDoc (d : Dom) (root : NodeId) : XPath.Full.Doc :=
  if wrapped d root then [projNode d (d.size + 1) none root]
  else (xkids d root).map fun c => projNode d (d.size + 1) none c

/-- The child indices from the root of `n` down to `n`, found from `n` upward. -/
def pathUp (d : Dom) : Nat → NodeId → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    match (d.get n).parent with
    | none => acc
    | some p =>
      match (xkids d p).findIdx? (fun c => c == n) with
      | some i => pathUp d fuel p (i :: acc)
      | none => acc

/-- The address in `projDoc d root` of node `n` of that tree. -/
def pathOf (d : Dom) (root n : NodeId) : List Nat :=
  let p := pathUp d (d.size + 1) n []
  if wrapped d root then 0 :: p else p

/-- The node that a list of child indices reaches from `start`. -/
def nodeAtPath (d : Dom) (start : NodeId) : List Nat → Option NodeId
  | [] => some start
  | i :: rest =>
    match (xkids d start)[i]? with
    | some c => nodeAtPath d c rest
    | none => none

/-- The DOM node at an address of `projDoc d root`. -/
def domOfPath (d : Dom) (root : NodeId) (path : List Nat) : Option NodeId :=
  if wrapped d root then
    match path with
    | 0 :: rest => nodeAtPath d root rest
    | _ => none
  else nodeAtPath d root path

/-- A node as the page has it: a node of the arena, or an attribute of an element (the
index in the element's attribute list). -/
inductive Ref where
  | node (id : NodeId)
  | attr (el : NodeId) (idx : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The DOM node of an item of the evaluator. A namespace node has none; neither has the
document node above a `wrapped` root. -/
def refOfItem (d : Dom) (root : NodeId) : XPath.Full.Item → Option Ref
  | .doc _ _ => if wrapped d root then none else some (Ref.node root)
  | .tree l _ => (domOfPath d root l.path).map Ref.node
  | .attr l _ =>
    match domOfPath d root l.path, l.slot with
    | some el, some (true, i) => (attrDomIndex (d.get el) i).map (Ref.attr el)
    | _, _ => none
  | .ns _ _ _ => none

/-- The evaluator's item of a DOM node of the tree of `root`, where `doc` is
`projDoc d root`. -/
def itemOfRef (d : Dom) (root : NodeId) (doc : XPath.Full.Doc) : Ref → Option XPath.Full.Item
  | .node n =>
    if n == root && !wrapped d root then some (XPath.Full.Item.doc doc 0)
    else XPath.Full.itemAt doc { path := pathOf d root n }
  | .attr el idx =>
    match attrSlot (d.get el) idx with
    | some s => XPath.Full.itemAt doc { path := pathOf d root el, slot := some (true, s) }
    | none => none

end L4Factoidal.DOM.XPathDom
