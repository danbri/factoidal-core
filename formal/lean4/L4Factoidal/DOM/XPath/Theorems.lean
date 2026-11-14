/-
L4Factoidal.DOM.XPath.Theorems — what is proved and what is tested about the DOM
adapter of the XPath 1.0 evaluator (`DOM/XPath/Project.lean`, `DOM/XPath/Evaluate.lean`),
the XML serialization (`DOM/XmlSerialize.lean`) and the script-facing XML document
builder (`DOM/OfXmlFull.lean`).

The duty of the adapter: an address of the evaluator names the same node on both sides.
The evaluator's axes and its document order are functions of addresses (`XPath/Data.lean`:
`childrenOf` gives child `i` the address `path ++ [i]`, `Loc.key` orders by address), so
it is enough that the projection keeps the children of every node, in order
(`projNode_child`), leaves a DocumentType out (`xkids_not_doctype`), and that the map
back from an address reads the same child lists (`nodeAtPath_cons`).

PROVED here: `refOfItem_ns`, `xkids_not_doctype`, `projNode_element`, `projNode_child`,
`nodeAtPath_nil`, `nodeAtPath_cons`, `domOfPath_rooted`, `htmlNameTest_not_name`,
`answerOf_number`, `answerOf_string`, `answerOf_boolean`, `serializeNode_text`.
TESTED here (`#guard`): evaluation through the adapter on small arenas (child, attribute,
descendant, following, preceding, parent, document order of a union, the HTML name test),
the prefixes of an expression, the serialization cases of WPT, the document builder.
OPEN: listed in docs/designissues/2026-11-14-browser-xml-dom.md.
-/
import L4Factoidal.DOM.XPath.Evaluate
import L4Factoidal.DOM.XmlSerialize
import L4Factoidal.DOM.OfXmlFull

namespace L4Factoidal.DOM.XPathDom

open L4Factoidal.DOM

/-- Kind: adapter contract (totality of the map back).
Says: a namespace node of the evaluator maps to no DOM node, whatever the arena and root:
the namespace axis gives the page nothing, as the DOM has no interface for such nodes.
Does not say: that `count(namespace::*)` is zero; the evaluator still counts the nodes. -/
theorem refOfItem_ns (d : Dom) (root : NodeId) (l : XPath.Full.Loc) (p u : String) :
    refOfItem d root (XPath.Full.Item.ns l p u) = none := rfl

/-- Kind: adapter contract (data model).
Says: no child that the projection keeps is a DocumentType, so a DocumentType is never a
node of the evaluator's tree and never takes a child index.
Does not say: that every other child is kept (it is, by the definition of `xkids` as a
filter; `projNode_child` uses the same list). -/
theorem xkids_not_doctype (d : Dom) (id c : NodeId) (h : c ∈ xkids d id) :
    (d.get c).type ≠ NodeType.doctype := by
  intro hd
  have hk : ((d.get c).type != NodeType.doctype) = true := (List.mem_filter.mp h).2
  rw [hd] at hk
  exact absurd hk (by decide)

/-- Kind: adapter contract (shape of the projection).
Says: with fuel left, the projection of an element is an element whose children are the
projections of its XPath children (`xkids`), one for one and in the same order.
Does not say: anything of a tree deeper than the fuel (`projDoc` gives the arena's size
plus one, which no tree of a well-formed arena exceeds; that bound is not proved here). -/
theorem projNode_element (d : Dom) (fuel : Nat) (dflt : Option String) (id : NodeId)
    (h : (d.get id).type = NodeType.element) :
    projNode d (fuel + 1) dflt id =
      XML.Node.element (elemTag (d.get id)) (elemAttrs (d.get id) dflt)
        ((xkids d id).map fun c => projNode d fuel (childDefault (d.get id) dflt) c) := by
  simp [projNode, h]

/-- Kind: adapter contract (same node order, same child axis).
Says: child index `i` of a projected element names the projection of the `i`-th XPath
child of the DOM element, and names nothing exactly when the DOM element has no such
child. The evaluator's `childrenOf`, and through it `descendant`, `following`, `preceding`
and document order, read children only by this index.
Does not say: that the evaluator's axes are right; that is the evaluator's own duty. -/
theorem projNode_child (d : Dom) (fuel : Nat) (dflt : Option String) (id : NodeId) (i : Nat)
    (h : (d.get id).type = NodeType.element) :
    (XPath.Full.kidsOf (projNode d (fuel + 1) dflt id))[i]? =
      ((xkids d id)[i]?).map (fun c => projNode d fuel (childDefault (d.get id) dflt) c) := by
  rw [projNode_element d fuel dflt id h]
  simp [XPath.Full.kidsOf]

/-- Kind: adapter contract (map back). Says: the empty address from a node is that node. -/
theorem nodeAtPath_nil (d : Dom) (start : NodeId) : nodeAtPath d start [] = some start := rfl

/-- Kind: adapter contract (map back).
Says: the map from an address to a DOM node takes child index `i` in the same list
(`xkids`) that the projection numbers its children by, then follows the rest.
Does not say: that `pathOf` is its inverse on every arena (tested below; open as a
theorem: it needs the arena invariant that a child's `parent` is the node it is a kid of). -/
theorem nodeAtPath_cons (d : Dom) (start : NodeId) (i : Nat) (rest : List Nat) :
    nodeAtPath d start (i :: rest) =
      ((xkids d start)[i]?).bind (fun c => nodeAtPath d c rest) := by
  simp only [nodeAtPath]
  cases (xkids d start)[i]? <;> rfl

/-- Kind: adapter contract (map back).
Says: when the root is a Document or a DocumentFragment, an address is read from the root
itself; the document node of the evaluator is the root.
Does not say: anything of a `wrapped` root, whose document node is no DOM node. -/
theorem domOfPath_rooted (d : Dom) (root : NodeId) (path : List Nat) (h : wrapped d root = false) :
    domOfPath d root path = nodeAtPath d root path := by
  simp [domOfPath, h]

/-- Kind: conservativity (the HTML name test).
Says: for every node test that is not a QName (`*`, `p:*`, `node()`, `text()`,
`comment()`, `processing-instruction()`), the node test of HTML documents is XPath 1.0's
`matchesTest`: the rule of HTML documents changes QName tests and nothing else.
Does not say: what a QName test selects in an HTML document (tested below). -/
theorem htmlNameTest_not_name (d : XPath.Full.Doc) (nsctx : List (String × String))
    (ax : XPath.Full.Ax) (it : XPath.Full.Item) (p : String) (t : Option String) :
    htmlNameTest d nsctx ax XPath.Full.NodeTest.anyName it =
      XPath.Full.matchesTest d nsctx ax XPath.Full.NodeTest.anyName it ∧
    htmlNameTest d nsctx ax (XPath.Full.NodeTest.anyInPrefix p) it =
      XPath.Full.matchesTest d nsctx ax (XPath.Full.NodeTest.anyInPrefix p) it ∧
    htmlNameTest d nsctx ax XPath.Full.NodeTest.nodeT it =
      XPath.Full.matchesTest d nsctx ax XPath.Full.NodeTest.nodeT it ∧
    htmlNameTest d nsctx ax XPath.Full.NodeTest.textT it =
      XPath.Full.matchesTest d nsctx ax XPath.Full.NodeTest.textT it ∧
    htmlNameTest d nsctx ax XPath.Full.NodeTest.commentT it =
      XPath.Full.matchesTest d nsctx ax XPath.Full.NodeTest.commentT it ∧
    htmlNameTest d nsctx ax (XPath.Full.NodeTest.piT t) it =
      XPath.Full.matchesTest d nsctx ax (XPath.Full.NodeTest.piT t) it :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: result conversion.
Says: a request for NUMBER_TYPE answers the evaluator's `number()` conversion of the
value, whatever the value's type; no node-set check is made.
Does not say: that the conversion is XPath 1.0's (that is `XPath.Full.Value.toNum`). -/
theorem answerOf_number (d : Dom) (root : NodeId) (v : XPath.Full.Value) :
    answerOf d root 1 v = "1" ++ sep ++ v.toNum.toXString := rfl

/-- Kind: result conversion. Says: a request for STRING_TYPE answers the evaluator's
`string()` conversion of the value. Does not say: that the conversion is XPath 1.0's. -/
theorem answerOf_string (d : Dom) (root : NodeId) (v : XPath.Full.Value) :
    answerOf d root 2 v = "2" ++ sep ++ v.toStr := rfl

/-- Kind: result conversion. Says: a request for BOOLEAN_TYPE answers the evaluator's
`boolean()` conversion of the value. Does not say: that the conversion is XPath 1.0's. -/
theorem answerOf_boolean (d : Dom) (root : NodeId) (v : XPath.Full.Value) :
    answerOf d root 3 v = "3" ++ sep ++ (if v.toBool then "1" else "0") := rfl

/-- Kind: serialization (leaves).
Says: with fuel left, a Text node serializes as its data with `&`, `<` and `>` escaped,
whatever the namespace state, and leaves the generated prefix index as it was.
Does not say: anything of an element (tested below against the cases of WPT). -/
theorem serializeNode_text (d : Dom) (fuel : Nat) (id : NodeId) (inh : Option String)
    (m : XmlSerialize.PrefixMap) (idx : Nat) (h : (d.get id).type = NodeType.text) :
    XmlSerialize.serializeNode d (fuel + 1) id inh m idx =
      (XmlSerialize.escText (d.get id).data, idx) := by
  simp [XmlSerialize.serializeNode, h]

#print axioms refOfItem_ns
#print axioms xkids_not_doctype
#print axioms projNode_element
#print axioms projNode_child
#print axioms nodeAtPath_nil
#print axioms nodeAtPath_cons
#print axioms domOfPath_rooted
#print axioms htmlNameTest_not_name
#print axioms answerOf_number
#print axioms answerOf_string
#print axioms answerOf_boolean
#print axioms serializeNode_text

/-! ## Tests: evaluation through the adapter -/

/-- `<a x="1"><b/>t<c><b/></c></a>` in an XML document, with a doctype before `a`. -/
private def xmlDemo : Dom := { nodes := #[
  { type := .document, htmlDoc := false, kids := #[7, 1] },
  { type := .element, lname := "a", parent := some 0, kids := #[2, 3, 4],
    attrs := #[{ lname := "x", value := "1" }] },
  { type := .element, lname := "b", parent := some 1 },
  { type := .text, data := "t", parent := some 1 },
  { type := .element, lname := "c", parent := some 1, kids := #[5] },
  { type := .element, lname := "b", parent := some 4 },
  { type := .comment, data := "unused" },
  { type := .doctype, lname := "a", parent := some 0 } ] }

-- child, descendant, attribute, parent; the doctype takes no index
#guard evaluate xmlDemo (.node 0) "count(//b)" [] 1 == "1\x012"
#guard evaluate xmlDemo (.node 1) "b" [] 7 == "7\x012"
#guard evaluate xmlDemo (.node 0) "//b" [] 7 == "7\x012\x015"
#guard evaluate xmlDemo (.node 1) "@x" [] 7 == "7\x01a1\x02\x02x"
#guard evaluate xmlDemo (.attr 1 0) ".." [] 7 == "7\x011"
#guard evaluate xmlDemo (.node 5) "/" [] 7 == "7\x010"
#guard evaluate xmlDemo (.node 1) "string(.)" [] 0 == "2\x01t"
-- following and preceding agree with tree order in the arena
#guard evaluate xmlDemo (.node 2) "following::*" [] 7 == "7\x014\x015"
#guard evaluate xmlDemo (.node 5) "preceding::node()" [] 7 == "7\x012\x013"
-- a union is in document order whatever the order written
#guard evaluate xmlDemo (.node 1) "(c | b | text())[last()]" [] 7 == "7\x014"
-- result types and errors
#guard evaluate xmlDemo (.node 1) "count(b) + 1" [] 0 == "1\x012"
#guard evaluate xmlDemo (.node 1) "b" [] 3 == "3\x011"
#guard evaluate xmlDemo (.node 1) "string(.)" [] 7 == "!TypeError"
#guard evaluate xmlDemo (.node 1) "b[" [] 0 == "!SyntaxError"
#guard evaluate xmlDemo (.node 7) "." [] 0 == "!NotSupportedError"
-- the address maps are inverse on this arena
#guard domOfPath xmlDemo 0 (pathOf xmlDemo 0 5) == some 5
#guard domOfPath xmlDemo 0 (pathOf xmlDemo 0 3) == some 3
#guard pathOf xmlDemo 0 5 == [0, 2, 0]

/-- An HTML document: `<html><body><div id="x"></div><svg><path/></svg></body></html>`. -/
private def htmlDemo : Dom := { nodes := #[
  { type := .document, htmlDoc := true, kids := #[1] },
  { type := .element, ns := some htmlNS, lname := "html", parent := some 0, kids := #[2] },
  { type := .element, ns := some htmlNS, lname := "body", parent := some 1, kids := #[3, 4] },
  { type := .element, ns := some htmlNS, lname := "div", parent := some 2,
    attrs := #[{ lname := "id", value := "x" }] },
  { type := .element, ns := some svgNS, lname := "svg", parent := some 2, kids := #[5] },
  { type := .element, ns := some svgNS, lname := "path", parent := some 4 } ] }

-- the name test of HTML documents (WPT domxpath/text-html-elements.html, -attributes.html)
#guard evaluate htmlDemo (.node 0) "//div" [] 7 == "7\x013"
#guard evaluate htmlDemo (.node 0) "//DiV" [] 7 == "7\x013"
#guard evaluate htmlDemo (.node 0) "//path" [] 7 == "7"
#guard evaluate htmlDemo (.node 0) "//s:path" [("s", svgNS)] 7 == "7\x015"
#guard evaluate htmlDemo (.node 0) "//s:PatH" [("s", svgNS)] 7 == "7"
#guard evaluate htmlDemo (.node 0) "//h:div" [("h", htmlNS)] 7 == "7\x013"
#guard evaluate htmlDemo (.node 0) "//*[@Id]" [] 7 == "7\x013"
#guard evaluate htmlDemo (.node 0) "namespace-uri(//div)" [] 2 == "2\x01http://www.w3.org/1999/xhtml"

-- the prefixes of an expression, in the order written
#guard prefixesOf "a:b/@c:d | e:*" == some ["a", "c", "e"]
#guard prefixesOf "child::x[@y='p:q']" == some []
#guard prefixesOf "//(" == none

/-! ## Tests: XML serialization (WPT domparsing/XMLSerializer-serializeToString.html) -/

/-- `root` (no namespace) > `another` (urn:foo) > `child1` (no namespace) > text. -/
private def serDemo : Dom := { nodes := #[
  { type := .document, htmlDoc := false, kids := #[1] },
  { type := .element, lname := "root", parent := some 0, kids := #[2] },
  { type := .element, ns := some "urn:foo", lname := "another", parent := some 1, kids := #[3] },
  { type := .element, lname := "child1", parent := some 2, kids := #[4] },
  { type := .text, data := "a<b&c", parent := some 3 } ] }

#guard XmlSerialize.serialize serDemo 1 ==
  "<root><another xmlns=\"urn:foo\"><child1 xmlns=\"\">a&lt;b&amp;c</child1></another></root>"

/-- An attribute in a namespace with no prefix on an element with no declarations. -/
private def serAttr : Dom := { nodes := #[
  { type := .document, htmlDoc := false, kids := #[1] },
  { type := .element, lname := "root", parent := some 0,
    attrs := #[{ ns := some xlinkNS, lname := "href", value := "v" }] } ] }

#guard XmlSerialize.serialize serAttr 1 ==
  "<root xmlns:ns1=\"http://www.w3.org/1999/xlink\" ns1:href=\"v\"/>"

-- the script-facing document builder keeps prefixes, declarations and CDATA sections
#guard (match parseXmlDocumentFull "<p:a xmlns:p='u' p:x='1'><![CDATA[t]]></p:a>" true with
  | .ok d =>
    let e := d.get 1
    (e.ns, e.pfx, e.lname, e.attrs.size, (d.get 2).type == NodeType.cdata) ==
      (some "u", some "p", "a", 2, true) &&
    XmlSerialize.serialize d 0 == "<p:a xmlns:p=\"u\" p:x=\"1\"><![CDATA[t]]></p:a>"
  | .error _ => false)

end L4Factoidal.DOM.XPathDom
