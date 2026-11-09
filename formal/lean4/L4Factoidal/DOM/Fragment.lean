/-
L4Factoidal.DOM.Fragment — markup in and out of the DOM arena: the HTML fragment parsing
algorithm into a DocumentFragment of a document, and the HTML fragment serialization
algorithm.

Specification: HTML Living Standard (whatwg/html `93967771`, the commit of `DOM.Arena`):
§13.4 "Parsing HTML fragments" (the parser is `HTML.TreeBuilder.parseFragmentState`, tested
with the html5lib and WPT tree construction tests), §13.3 "Serializing HTML fragments", and
the DOM Parsing and Serialization algorithms that use them: the `innerHTML` and
`outerHTML` setters, `insertAdjacentHTML` and `Range.createContextualFragment`
("fragment parsing algorithm steps" for an HTML document). The host
(`WasmVM.Hosts.Dom`, `createKind` 13 and `node_query` op 15) and prelude.js use these;
the tree changes that follow a parse are the usual typed commands.

Not here: the XML fragment parsing and XML serialization of an XML document (an XML
document's markup is parsed and serialized as HTML), shadow roots, and custom elements.
-/
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.DOM.Fragment
open L4Factoidal.DOM L4Factoidal.HTML

/-- The parser's namespace of a context element. -/
def nsOf (ns : String) : NS :=
  if ns == svgNS then .svg else if ns == mathmlNS then .math else .html

/-- The HTML fragment parsing algorithm (§13.4) of `src` for a context element with
namespace `ns` and local name `name`, joined to arena `d`: a new DocumentFragment of
document `doc` whose children are the nodes of the parse. The parse's own document, `html`
root and context element stay in the arena as unconnected nodes. -/
def parseInto (d : Dom) (doc : NodeId) (ns name src : String) : Dom × NodeId := Id.run do
  let (tb, _) := parseFragmentState (nsOf ns) name src
  let (d, base) := d.graft (ofTreeBuilder tb.dom)
  let html := base + 1
  let (d, frag) := d.createDocumentFragment doc
  let kids := (d.get html).kids
  let mut d := d.setNode html fun x => { x with kids := #[] }
  for k in kids do d := d.setNode k fun x => { x with parent := some frag }
  d := d.setNode frag fun x => { x with kids }
  return (d.setNodeDocument frag doc, frag)

/-! ## Serializing HTML fragments (§13.3) -/

def voidElements : List String :=
  ["area", "base", "basefont", "bgsound", "br", "col", "embed", "frame", "hr", "img", "input", "keygen",
   "link", "meta", "param", "source", "track", "wbr"]

def rawTextParents : List String :=
  ["style", "script", "xmp", "iframe", "noembed", "noframes", "plaintext"]

/-- "Escaping a string" (§13.3): `&`, U+00A0, `<` and `>`; in attribute mode `"` too, and
`<` and `>` as well (the escaping of 2025). -/
def escape (s : String) (attr : Bool) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | ' ' => acc ++ "&nbsp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => if attr then acc ++ "&quot;" else acc.push c
    | _ => acc.push c

/-- The serialized name of an attribute (§13.3). -/
def attrName (a : Attr) : String :=
  match a.ns with
  | none => a.lname
  | some ns =>
    if ns == xmlNS then "xml:" ++ a.lname
    else if ns == xmlnsNS then (if a.lname == "xmlns" then "xmlns" else "xmlns:" ++ a.lname)
    else if ns == xlinkNS then "xlink:" ++ a.lname
    else a.qname

/-- The tag name of an element in a serialization: the local name in the HTML, SVG and
MathML namespaces, else the qualified name. -/
def tagName (x : Node) : String :=
  if x.ns == some htmlNS || x.ns == some svgNS || x.ns == some mathmlNS then x.lname
  else match x.pfx with
    | some p => p ++ ":" ++ x.lname
    | none => x.lname

/-- The children that a serialization of `n` walks: a `template` element's are its
template contents' children. -/
def serialKids (d : Dom) (n : NodeId) : Array NodeId :=
  let x := d.get n
  match x.content with
  | some c => if Dom.isHtmlElement x "template" then (d.get c).kids else x.kids
  | none => x.kids

/-- An item of the serialization work list: a node to open, or an end tag to write. -/
inductive Item where
  | node (n : NodeId)
  | close (s : String)

/-- The HTML serialization of the nodes `top` (§13.3 "serializing HTML fragments" of their
parent): a loop over a work list, so deep trees use no stack. -/
def serializeNodes (d : Dom) (top : Array NodeId) : String := Id.run do
  let mut out := ""
  let mut work : List Item := top.toList.map .node
  -- each node is opened once and closed once
  for _ in [0:2 * d.size + 2] do
    match work with
    | [] => break
    | .close s :: rest => out := out ++ s; work := rest
    | .node k :: rest =>
      work := rest
      let x := d.get k
      match x.type with
      | .element =>
        let t := tagName x
        out := out ++ "<" ++ t
        for a in x.attrs do out := out ++ " " ++ attrName a ++ "=\"" ++ escape a.value true ++ "\""
        out := out ++ ">"
        if x.ns == some htmlNS && voidElements.contains x.lname then continue
        work := (serialKids d k).toList.map .node ++ [Item.close ("</" ++ t ++ ">")] ++ work
      | .text | .cdata =>
        let raw : Bool := match x.parent with
          | some p => let px := d.get p
            px.type == .element && px.ns == some htmlNS && rawTextParents.contains px.lname
          | none => false
        out := out ++ (if raw then x.data else escape x.data false)
      | .comment => out := out ++ "<!--" ++ x.data ++ "-->"
      | .pi => out := out ++ "<?" ++ x.lname ++ " " ++ x.data ++ ">"
      | .doctype => out := out ++ "<!DOCTYPE " ++ x.lname ++ ">"
      | .document | .fragment => work := (serialKids d k).toList.map .node ++ work
  return out

/-- `innerHTML` (the children of `n`) or `outerHTML` (`n` itself). -/
def serialize (d : Dom) (n : NodeId) (outer : Bool) : String :=
  if outer then serializeNodes d #[n] else serializeNodes d (serialKids d n)

#guard (let d := parseHtmlDocument "<p id=a title='x&quot;y'>a&amp;b<br>c<!--k--></p>"
  serialize d (((d.getElementById 0 "a")).getD 0) true) == "<p id=\"a\" title=\"x&quot;y\">a&amp;b<br>c<!--k--></p>"
#guard (let d := parseHtmlDocument "<script>a<b</script>"
  serialize d 0 false) == "<html><head><script>a<b</script></head><body></body></html>"
#guard (let (d, f) := parseInto (parseHtmlDocument "") 0 htmlNS "tr" "<td>a<td>b"
  serialize d f false) == "<td>a</td><td>b</td>"
#guard (let (d, f) := parseInto (parseHtmlDocument "") 0 htmlNS "div" "<template><b>x</b></template>"
  serialize d f false) == "<template><b>x</b></template>"

end L4Factoidal.DOM.Fragment
