/-
L4Factoidal.DOM.OfXmlFull — the DOM arena of an XML document as a script sees it
(`DOMParser.parseFromString` with an XML type, `XMLHttpRequest.responseXML`): HTML
§8.5.1 "DOM parsing", which runs an XML parser with XML scripting support disabled.

`DOM.OfXml.parseXmlDocument` builds the arena of a page in the XML syntax for style and
layout: it keeps no prefix and no namespace declaration, and a CDATA section is a Text
node. A script reads more of the document than layout does, so this builder keeps:

* the prefix of each element and attribute (`Element.prefix`, `tagName`, and `name()`
  of DOM XPath);
* each namespace declaration as an attribute in the XMLNS namespace (DOM §4.9; Namespaces
  in XML §3: a declaration is an attribute of the element): `xmlns` has no prefix and the
  local name `xmlns`, `xmlns:p` the prefix `xmlns` and the local name `p`;
* a CDATA section as a CDATASection node, when `cdata` is set;
* the comments and processing instructions before and after the document element.

The source is read by the same XML parser, with the same resolver for the entity
declarations of the XHTML document types, and is refused unless it is namespace
well-formed, as `parseXmlDocument` refuses it. The document type declaration is not kept
(as before). The tree is built with a work list, one loop step per node.
-/
import L4Factoidal.DOM.OfXml

namespace L4Factoidal.DOM

/-- The DOM attribute of an attribute of the source, with the namespace bindings in
scope on its element. A namespace declaration is in the XMLNS namespace. An unprefixed
attribute has no namespace (Namespaces in XML §6.2). -/
def xmlFullAttr (scope : XML.NsScope) (a : XML.Attribute) : Attr :=
  match XML.splitQName a.name with
  | .prefixed p l =>
    if p == "xmlns" then { ns := some xmlnsNS, pfx := some "xmlns", lname := l, value := a.value }
    else { ns := XML.lookupPrefix scope p, pfx := some p, lname := l, value := a.value }
  | _ =>
    if a.name == "xmlns" then { ns := some xmlnsNS, lname := "xmlns", value := a.value }
    else { lname := a.name, value := a.value }

/-- The DOM node of one node of the source under `parent`, and the namespace bindings in
scope for its children. `scope` is the bindings in scope for the node. -/
def xmlFullNode (version : String) (cdata : Bool) (parent : NodeId) (scope : XML.NsScope) :
    XML.Node → DOM.Node × XML.NsScope
  | .element tag attrs _ =>
    let inner := (XML.applyDeclarations version scope attrs).getD scope
    let dattrs := (attrs.map (xmlFullAttr inner)).toArray
    (match XML.splitQName tag with
     | .prefixed p l =>
       ({ type := .element, ns := XML.lookupPrefix inner p, pfx := some p, lname := l,
          attrs := dattrs, parent := some parent }, inner)
     | _ =>
       ({ type := .element, ns := XML.lookupPrefix inner "", lname := tag,
          attrs := dattrs, parent := some parent }, inner))
  | .text t => ({ type := .text, data := t, parent := some parent }, scope)
  | .cdata t =>
    ({ type := if cdata then .cdata else .text, data := t, parent := some parent }, scope)
  | .comment c => ({ type := .comment, data := c, parent := some parent }, scope)
  | .pi target data => ({ type := .pi, lname := target, data := data, parent := some parent }, scope)

/-- Parse an XML document into a DOM arena for scripts; node 0 is the Document. Every
node of the tree comes from at least one character of the source, so the loop bound
`src.length + 2` is never reached by a parsed tree. -/
def parseXmlDocumentFull (src : String) (cdata : Bool) : Except String Dom := do
  let doc ← (XML.parseXMLWith (xhtmlResolver src) src).mapError
    (fun e => s!"XML: {e.message} at {e.position}")
  if !doc.namespaceWellFormed then throw "XML namespace well-formedness violation"
  let version := (doc.decl.map (·.version)).getD "1.0"
  let mut d : Dom := { nodes := #[{ type := .document, htmlDoc := false }] }
  let mut work : List (NodeId × XML.NsScope × XML.Node) :=
    (doc.prolog ++ (doc.root :: doc.epilog)).map fun n => (0, XML.initialScope, n)
  for _ in [0:src.length + 2] do
    match work with
    | [] => return d
    | (parent, scope, node) :: rest =>
      let (dn, inner) := xmlFullNode version cdata parent scope node
      let (d1, id) := d.push dn
      d := d1.setNode parent fun p => { p with kids := p.kids.push id }
      work := match node with
        | .element _ _ kids => kids.map (fun k => (id, inner, k)) ++ rest
        | _ => rest
  throw "XML: the tree has more nodes than its source has characters"

end L4Factoidal.DOM
