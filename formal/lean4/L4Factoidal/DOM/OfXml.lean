/-
L4Factoidal.DOM.OfXml — the DOM arena of a document in the XML syntax of HTML
(HTML §14, "The XML syntax"), as a browser builds it for `application/xhtml+xml`.

The source is read by the namespace-aware XML parser (`XML.parseNamespaceView`:
XML 1.0 well-formedness and Namespaces in XML 1.0 well-formedness). A document
that is not namespace well-formed is refused with the parser's message, as an
XML user agent shows a parse error and no page.

Node 0 is an XML Document (`htmlDoc := false`). Elements keep their namespace
name and local name; attributes keep their namespace name (namespace declarations
are not attributes in the namespace view). A CDATA section becomes a Text node
with its character data: this arena's consumers (style sheets, layout) read the
data of Text nodes, and DOM §4.13 makes CDATASection a kind of Text. The
document type declaration is not kept.

The tree is built with an explicit work list, one loop step per node, never one
stack frame per level of nesting.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.XML.NamespaceView

namespace L4Factoidal.DOM

open L4Factoidal.XML

private def xmlAttr (a : NamespaceAttribute) : Attr :=
  { ns := a.name.namespace_, lname := a.name.localPart, value := a.value }

/-- The DOM node of one namespace-view node, under `parent`. -/
private def xmlNode (parent : NodeId) : NamespaceNode → DOM.Node
  | .element name attrs _ =>
    { type := .element, ns := name.namespace_, lname := name.localPart,
      attrs := (attrs.map xmlAttr).toArray, parent := some parent }
  | .other (.text t) | .other (.cdata t) => { type := .text, data := t, parent := some parent }
  | .other (.comment c) => { type := .comment, data := c, parent := some parent }
  | .other (.pi target data) => { type := .pi, lname := target, data, parent := some parent }
  -- The namespace view gives every element as `.element`.
  | .other (.element ..) => { type := .comment, parent := some parent }

/-- Parse a document in the XML syntax of HTML into a DOM arena; node 0 is the Document.
Every node of the tree comes from at least one character of the source, so the loop
bound `src.length + 2` is never reached by a parsed tree. -/
def parseXmlDocument (src : String) : Except String Dom := do
  let root ← parseNamespaceView src
  let mut d : Dom := { nodes := #[{ type := .document, htmlDoc := false }] }
  let mut work : List (NodeId × NamespaceNode) := [(0, root)]
  for _ in [0:src.length + 2] do
    match work with
    | [] => return d
    | (parent, node) :: rest =>
      let (d1, id) := d.push (xmlNode parent node)
      d := d1.setNode parent fun p => { p with kids := p.kids.push id }
      work := match node with
        | .element _ _ kids => kids.map (id, ·) ++ rest
        | .other _ => rest
  throw "XHTML: the tree has more nodes than its source has characters"

/-- A URL whose path ends in `.xht` or `.xhtml` (any case): the file name extensions
that the `application/xhtml+xml` registration lists (RFC 3236 §2). -/
def isXhtmlPath (url : String) : Bool :=
  let path := ((url.splitOn "#").headD "").splitOn "?" |>.headD ""
  let lower := path.toLower
  lower.endsWith ".xht" || lower.endsWith ".xhtml"

end L4Factoidal.DOM
