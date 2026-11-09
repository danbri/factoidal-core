/-
L4Factoidal.DOM.OfHtml — the DOM arena of a document or fragment that the HTML
parser (`L4Factoidal/HTML/TreeBuilder.lean`) built.

The tree builder keeps its own small arena (`TB.dom`, an array of `DNode`),
whose `template` elements hold their contents as children. `ofTreeBuilder`
gives a DOM arena with the same node indexes: node `i` of the parser arena is
node `i` of the DOM arena, and each `template` element gets a new
DocumentFragment (its template contents, HTML §4.12.3) at the end of the arena,
which takes the element's children. The namespace and attribute names follow
"adjust foreign attributes" (HTML §13.2.6.1).

The DOM arena is checked against the web-platform-tests tree construction tests
by `l4html5lib dom-tree` (`tests/dom/run.sh`): the dump of the DOM arena must be
the expected tree, as the dump of the parser arena is.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.DOM.Shadow
import L4Factoidal.HTML.TreeBuilder

namespace L4Factoidal.DOM

open L4Factoidal.HTML

def nsUri : NS → String
  | .html => htmlNS
  | .svg => svgNS
  | .math => mathmlNS

/-- "Adjust foreign attributes" (HTML §13.2.6.1, table): the namespace, prefix
and local name of an attribute of an SVG or MathML element. The parser stores
the attribute name string; an HTML element's attributes have no namespace. -/
def attrOf (foreign : Bool) (name value : String) : Attr :=
  if !foreign then { lname := name, value } else
  match name with
  | "xlink:actuate" | "xlink:arcrole" | "xlink:href" | "xlink:role" | "xlink:show" | "xlink:title"
  | "xlink:type" => { ns := some xlinkNS, pfx := some "xlink", lname := (name.drop 6).toString, value }
  | "xml:lang" | "xml:space" => { ns := some xmlNS, pfx := some "xml", lname := (name.drop 4).toString, value }
  | "xmlns" => { ns := some xmlnsNS, lname := "xmlns", value }
  | "xmlns:xlink" => { ns := some xmlnsNS, pfx := some "xmlns", lname := "xlink", value }
  | _ => { lname := name, value }

def nodeOfDNode (n : DNode) : Node :=
  let type : NodeType := match n.kind with
    | .doc => .document | .elem => .element | .text => .text | .comment => .comment
    | .doctype => .doctype | .pi => .pi
  { type, doc := 0, parent := n.parent, kids := n.kids,
    ns := if n.kind == .elem then some (nsUri n.ns) else none,
    lname := n.name, data := n.data, pubId := n.pubId, sysId := n.sysId,
    attrs := n.attrs.map fun (k, v) => attrOf (n.ns != .html) k v }

/-- The mode of a declarative shadow root (HTML §4.12.3 `shadowrootmode`, ASCII
case-insensitive): `some closed`, or none for a `template` element with no valid one. -/
def declarativeMode (x : Node) : Option Bool :=
  match (Dom.plainAttr x "shadowrootmode").toLower with
  | "open" => some false
  | "closed" => some true
  | _ => none

/-- A declarative shadow root (HTML §13.2.6.4.4, "in head", a `template` start tag with a
`shadowrootmode`): template `t` whose parent is an element other than the root element,
with no shadow root yet, gets a shadow root (`Dom.attachShadow`, declarative) that takes
the template's children, and the template leaves the tree. When the parent can not host a
shadow root, none: the template stays a template. -/
def declarativeShadow (d : Dom) (t : NodeId) : Option Dom := do
  let x := d.get t
  let closed ← declarativeMode x
  let p ← x.parent
  let host := d.get p
  if host.type != .element || host.parent == some 0 || host.shadow.isSome then none
  let focus := Dom.hasAttr x "shadowrootdelegatesfocus"
  let clone := Dom.hasAttr x "shadowrootclonable"
  let serial := Dom.hasAttr x "shadowrootserializable"
  let init : ShadowInit :=
    { closed := closed, declarative := true, delegatesFocus := focus, clonable := clone, serializable := serial }
  match d.attachShadow p init with
  | (_, .error _) => none
  | (d, .ok sr) =>
    let d := d.setNode sr fun y => { y with kids := x.kids }
    let d := x.kids.foldl (fun d k => d.setNode k fun y => { y with parent := some sr }) d
    let d := d.setNode p fun y => { y with kids := y.kids.filter (· != t) }
    some (d.setNode t fun y => { y with parent := none, kids := #[] })

/-- The DOM arena of a parser arena; node indexes are kept. With `shadow` (a document whose
"allow declarative shadow roots" is true), `template` elements with a `shadowrootmode` make
declarative shadow roots (`declarativeShadow`). -/
def ofTreeBuilder (dom : Array DNode) (shadow : Bool := false) : Dom := Id.run do
  let mut d : Dom := { nodes := dom.map nodeOfDNode }
  for i in [0:dom.size] do
    let x := d.get i
    if shadow && Dom.isHtmlElement x "template" && (declarativeMode x).isSome then
      if let some d' := declarativeShadow d i then
        d := d'
        continue
    if Dom.isHtmlElement x "template" then
      let (d1, c) := d.push { type := .fragment, doc := 0, host := some i, kids := x.kids }
      d := d1
      for k in x.kids do d := d.setNode k fun y => { y with parent := some c }
      d := d.setNode i fun y => { y with kids := #[], content := some c }
  return d

/-- Parse an HTML document (HTML §13.2) into a DOM arena; node 0 is the Document. With
`shadow` (the default: a document a browsing context loads), declarative shadow roots are
attached; `DOMParser` passes `false` (HTML §8.5.1.1). -/
def parseHtmlDocument (src : String) (scripting : Bool := false) (shadow : Bool := true) : Dom :=
  ofTreeBuilder (parseDocumentState src scripting).dom shadow

end L4Factoidal.DOM
