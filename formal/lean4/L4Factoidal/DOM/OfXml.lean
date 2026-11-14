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
document type declaration is not kept. For the public identifiers of HTML §14.2 the
HTML entity names are declared (`xhtmlResolver`).

The tree is built with an explicit work list, one loop step per node, never one
stack frame per level of nesting.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.XML.NamespaceView
import L4Factoidal.HTML.Entities
import Std.Data.HashSet

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

/-- The public identifiers for which an XML parser of a user agent uses the HTML entity
declarations in place of the external subset (HTML §14.2 "Parsing XML documents"). -/
def xhtmlEntityPublicIds : List String :=
  ["-//W3C//DTD XHTML 1.0 Transitional//EN", "-//W3C//DTD XHTML 1.1//EN",
   "-//W3C//DTD XHTML 1.0 Strict//EN", "-//W3C//DTD XHTML 1.0 Frameset//EN",
   "-//W3C//DTD XHTML Basic 1.0//EN", "-//W3C//DTD XHTML 1.1 plus MathML 2.0//EN",
   "-//W3C//DTD XHTML 1.1 plus MathML 2.0 plus SVG 1.1//EN", "-//W3C//DTD MathML 2.0//EN",
   "-//WAPFORUM//DTD XHTML Mobile 1.0//EN",
   -- Not in the list this session read from HTML §14.2. WPT tests them
   -- (html/the-xhtml-syntax/parsing-xhtml-documents/xhtml-mathml-dtd-entity-11.htm and -12.htm)
   -- and Chrome, Firefox and Safari pass those tests (wpt.fyi, WPT fea36e49ddda).
   "-//WAPFORUM//DTD XHTML Mobile 1.1//EN", "-//WAPFORUM//DTD XHTML Mobile 1.2//EN"]

/-- One `<!ENTITY name "...">` declaration for each HTML named character reference that
ends with a semicolon: the content of the DTD that HTML §14.2 names. `&` and `<` in a
value are written as a reference to a character reference (`&#38;#60;`), as that DTD
writes them, so that the replacement text is well-formed. -/
def xhtmlEntityDtd : Thunk String := Thunk.mk fun _ =>
  let one (c : Char) : String :=
    if c == '&' || c == '<' then s!"&#38;#{c.toNat};" else s!"&#{c.toNat};"
  HTML.entityMap.get.fold (fun acc name value =>
    acc ++ "<!ENTITY " ++ name ++ " \"" ++ String.join (value.toList.map one) ++ "\">\n") ""

/-- The declarations of `xhtmlEntityDtd` that `src` can use: one for each distinct name that
`src` writes as `&name;` and that the table has. A declaration nothing references changes
no parse, so the document reads the same as with the whole DTD; the cost follows the
document's references, not the table's 2,125 names (a DOMParser call parsed all of them). -/
def xhtmlEntityDtdFor (src : String) : String :=
  let one (c : Char) : String :=
    if c == '&' || c == '<' then s!"&#38;#{c.toNat};" else s!"&#{c.toNat};"
  let names := ((src.splitOn "&").drop 1).filterMap fun part =>
    match part.splitOn ";" with
    | name :: _ :: _ => if name.isEmpty || name.length > 40 then none else some name
    | _ => none
  (names.foldl (fun (seen, acc) name =>
    if seen.contains name then (seen, acc) else
    match HTML.namedRef? name with
    | some value => (seen.insert name, acc ++ "<!ENTITY " ++ name ++ " \"" ++ String.join (value.toList.map one) ++ "\">\n")
    | none => (seen.insert name, acc)) (({} : Std.HashSet String), "")).2

#guard xhtmlEntityDtdFor "a &nbsp; &nbsp; &bogus; &lt; b" == "<!ENTITY nbsp \"&#160;\">\n<!ENTITY lt \"&#38;#60;\">\n"

/-- A quoted literal at the start of `cs` (after white space): its text and the rest. -/
private def quoted (cs : List Char) : Option (String × List Char) :=
  match cs.dropWhile Char.isWhitespace with
  | q :: rest =>
    if q == '"' || q == '\'' then
      let lit := rest.takeWhile (· != q)
      some (String.ofList lit, rest.drop (lit.length + 1))
    else none
  | [] => none

/-- The public and system identifiers of the document type declaration of `src`, when it
has the form `<!DOCTYPE name PUBLIC "public" "system"`. The scan reads the text between
the first `<!DOCTYPE` and the first `>` or `[` after it; the XML parser decides
well-formedness, not this function. -/
def doctypePublicSystem (src : String) : Option (String × String) :=
  match src.splitOn "<!DOCTYPE" with
  | _ :: after :: _ =>
    let head := after.toList.takeWhile (fun c => c != '>' && c != '[')
    match (String.ofList head).splitOn "PUBLIC" with
    | _ :: rest :: _ =>
      match quoted rest.toList with
      | some (pub, more) => (quoted more).map fun (sys, _) => (pub, sys)
      | none => none
    | _ => none
  | _ => none

/-- The resolver of a user agent for the XML syntax of HTML: when the document type
declaration has one of `xhtmlEntityPublicIds`, its system identifier is answered with
the part of `xhtmlEntityDtd` the document uses (`xhtmlEntityDtdFor`); nothing else is read. -/
def xhtmlResolver (src : String) : Resolver :=
  match doctypePublicSystem src with
  | some (pub, sys) =>
    if xhtmlEntityPublicIds.contains pub then fun id => if id == sys then some (xhtmlEntityDtdFor src) else none
    else fun _ => none
  | none => fun _ => none

/-- Parse a document in the XML syntax of HTML into a DOM arena; node 0 is the Document.
Every node of the tree comes from at least one character of the source, so the loop
bound `src.length + 2` is never reached by a parsed tree. -/
def parseXmlTree (src : String) : Except String Dom := do
  let root ← parseNamespaceViewWith (xhtmlResolver src) src
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

/-- An XML source as a document (`parseXmlTree`). A document whose root element is in the
HTML namespace is an XHTML document: its content type is `application/xhtml+xml` (a caller
that knows the content type sets it after), so that `createElement` in it makes HTML
elements (DOM §4.5 "createElement" step 5). Before, the page's own XHTML document had no
content type, and every element a script created in it was in no namespace: an `iframe`
made by a script never loaded. -/
def parseXmlDocument (src : String) : Except String Dom := do
  let d ← parseXmlTree src
  let rootNs := ((d.get 0).kids.find? fun k => (d.get k).type == .element).bind fun k => (d.get k).ns
  -- an SVG document (root `svg` element, read from an `.svg` path) is `image/svg+xml` (SVG 2
  -- Appendix P), as the page's `document.contentType` tells its scripts; another XML
  -- document is `application/xml`
  let contentType := if rootNs == some htmlNS then "application/xhtml+xml"
    else if rootNs == some svgNS then "image/svg+xml" else "application/xml"
  return d.setNode 0 fun n => { n with contentType := contentType }

#guard ((parseXmlDocument "<svg xmlns='http://www.w3.org/2000/svg'/>").toOption.map fun d => (d.get 0).contentType) == some "image/svg+xml"
#guard ((parseXmlDocument "<html xmlns='http://www.w3.org/1999/xhtml'/>").toOption.map fun d => (d.get 0).contentType) == some "application/xhtml+xml"
#guard ((parseXmlDocument "<r/>").toOption.map fun d => (d.get 0).contentType) == some "application/xml"

/-- A URL whose document the XML parser reads: its path ends in `.xht` or `.xhtml` (any
case), the file name extensions that the `application/xhtml+xml` registration lists
(RFC 3236 §2), or in `.xml`, the extension of `application/xml` and `text/xml` (RFC 7303
§9.1). The host gives no Content-Type, so the path decides. -/
def isXhtmlPath (url : String) : Bool :=
  let path := ((url.splitOn "#").headD "").splitOn "?" |>.headD ""
  let lower := path.toLower
  lower.endsWith ".xht" || lower.endsWith ".xhtml" || lower.endsWith ".xml"

#guard isXhtmlPath "http://h/common/dummy.xml" && isXhtmlPath "/a/B.XHTML?x=1#f" && !isXhtmlPath "/a.xml.html" && !isXhtmlPath "/a.svg"

/-- A URL whose document is read in the XML syntax: `isXhtmlPath`, or a path that ends in
`.svg` (any case), the file name extension of the `image/svg+xml` registration (SVG 2
Appendix P), so an SVG document is an XML document whose root is `svg`. -/
def isXmlPath (url : String) : Bool :=
  isXhtmlPath url ||
    ((((url.splitOn "#").headD "").splitOn "?" |>.headD "").toLower.endsWith ".svg")

#guard isXmlPath "http://a.example/x.svg" && isXmlPath "http://a.example/x.SVG?q=.html#f" && isXmlPath "a.xht"
#guard !isXmlPath "http://a.example/x.svg.html" && !isXmlPath "http://a.example/svg" && !isXhtmlPath "a.svg"

/-- The text of the first Text node of a parsed document, for the checks below. -/
private def firstText (src : String) : Option String :=
  (parseXmlDocument src).toOption.bind fun d => (d.nodes.find? (·.type == .text)).map (·.data)

-- HTML §14.2: with a listed public identifier the HTML entity names are declared.
#guard firstText "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"foo\"><html><body>&nbsp;</body></html>" == some "\u00a0"
#guard firstText "<!DOCTYPE html PUBLIC \"-//W3C//DTD MathML 2.0//EN\" \"foo\"><html><body>&nvlt;</body></html>" == some "<\u20d2"
-- Without one, a reference to an undeclared entity is not well-formed.
#guard (parseXmlDocument "<!DOCTYPE html><html><body>&nbsp;</body></html>").toOption.isNone
#guard doctypePublicSystem "<!DOCTYPE html PUBLIC '-//W3C//DTD XHTML 1.1//EN' \"x y\">" == some ("-//W3C//DTD XHTML 1.1//EN", "x y")

end L4Factoidal.DOM
