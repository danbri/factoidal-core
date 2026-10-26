/-
L4Factoidal.XSLT.TransformTests — build-time checks for the XSLT 1.0
engine, end to end: a stylesheet string and a source string in, the
serialised result tree out.

Each check pins a rule the vendored `xslt30-test` subset caught this
module getting wrong, and names the case that caught it. Every one of
them produced a document of the RIGHT SHAPE with the wrong content,
which is the failure mode that reads as a near miss.
-/
import L4Factoidal.XSLT.Transform

namespace L4Factoidal.XSLT

open L4Factoidal.XML

/-- Run a transform, or report the refusal, as one string. -/
def run (style src : String) : String :=
  match parseXML style, parseXML src with
  | .error e, _ => "STYLESHEET NOT WELL FORMED: " ++ e.message
  | _, .error e => "SOURCE NOT WELL FORMED: " ++ e.message
  | .ok st, .ok sr =>
      match transform st sr with
      | .produced t => t
      | .refused r  => "REFUSED: " ++ r

private def ss (body : String) : String :=
  "<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" version=\"1.0\">"
  ++ body ++ "</xsl:stylesheet>"

/-! ## The built-in template rules (§5.8) -/

-- With no template at all, the built-ins walk to the text.
#guard run (ss "") "<doc><a>one</a><a>two</a></doc>" == "onetwo"

/-! ## Instantiation -/

#guard run (ss "<xsl:template match=\"doc\"><out><xsl:value-of select=\"a\"/></out></xsl:template>")
           "<doc><a>one</a><a>two</a></doc>" == "<out>one</out>"

#guard run (ss "<xsl:template match=\"doc\"><out><xsl:for-each select=\"a\"><i><xsl:value-of select=\"position()\"/></i></xsl:for-each></out></xsl:template>")
           "<doc><a/><a/><a/></doc>" == "<out><i>1</i><i>2</i><i>3</i></out>"

-- An element with no content is EMPTY, so it serialises as `<i/>`.
-- An empty text node kept as a child made it `<i></i>`: the same
-- infoset, a different document under a canonical comparison
-- (position-8101).
#guard run (ss "<xsl:template match=\"doc\"><i><xsl:value-of select=\"missing\"/></i></xsl:template>")
           "<doc/>" == "<i/>"

/-! ## Attribute value templates (§7.6.2) -/

#guard run (ss "<xsl:template match=\"doc\"><out n=\"{count(a)}\"/></xsl:template>")
           "<doc><a/><a/></doc>" == "<out n=\"2\"/>"

/-! ## Sorting (§10) -/

-- `data-type` is an AVT. Reading it literally made `{$t}` neither
-- `number` nor `text`, and the engine fell back to a TEXT sort: a
-- correctly ordered list under the wrong ordering (sort-041/042/043).
#guard run (ss "<xsl:template match=\"doc\"><xsl:param name=\"t\" select=\"'number'\"/><out><xsl:for-each select=\"n\"><xsl:sort data-type=\"{$t}\"/><xsl:value-of select=\".\"/><xsl:text> </xsl:text></xsl:for-each></out></xsl:template>")
           "<doc><n>10</n><n>9</n><n>100</n></doc>" == "<out>9 10 100 </out>"

-- Sorting is STABLE, and two NaN keys are equal to nothing including
-- each other, so they keep document order in BOTH directions
-- (sort-001).
#guard run (ss "<xsl:template match=\"doc\"><out><xsl:for-each select=\"n\"><xsl:sort data-type=\"number\"/><xsl:value-of select=\".\"/><xsl:text> </xsl:text></xsl:for-each></out></xsl:template>")
           "<doc><n>Hello</n><n>7</n><n>x</n></doc>" == "<out>Hello x 7 </out>"

/-! ## Conflict resolution (§5.5) -/

-- A `|` pattern is equivalent to ONE TEMPLATE RULE PER ALTERNATIVE,
-- so `b` here matches at priority 0 and beats `*` at -0.5. Taking the
-- maximum over the alternatives instead would let the specific
-- alternative raise the general one.
#guard run (ss "<xsl:template match=\"doc\"><xsl:apply-templates/></xsl:template><xsl:template match=\"*\">W</xsl:template><xsl:template match=\"a|b\">S</xsl:template>")
           "<doc><a/><c/></doc>" == "SW"

/-! ## What the engine refuses -/

-- An XSLT element outside the implemented set REFUSES the whole
-- transform rather than emitting a document with the instruction's
-- output missing.
#guard (run (ss "<xsl:template match=\"doc\"><out><xsl:number/></out></xsl:template>")
            "<doc/>").startsWith "REFUSED: unimplemented XSLT element(s): xsl:number"

-- `document(uri)` is answered from a map the CALLER supplies, so a
-- URI nobody supplied is a refusal and not an empty tree that the
-- stylesheet would quietly transform into nothing (select-5901).
#guard (run (ss "<xsl:template match=\"doc\"><xsl:copy-of select=\"document('x.xml')\"/></xsl:template>")
            "<doc/>").startsWith "REFUSED:"

/-! ## The two XSLT/XPath 2.0 features the corpus exercises -/

-- Value comparisons: two numbers compare numerically, anything else
-- as strings (boolean-026, boolean-027).
#guard run (ss "<xsl:template match=\"doc\"><out a=\"{1 eq 1.0}\" b=\"{'20' lt '180.3'}\" c=\"{1.0e2 ne 1e3}\"/></xsl:template>")
           "<doc/>" == "<out a=\"true\" b=\"false\" c=\"true\"/>"

-- `copy-namespaces="no"` strips the declarations from the copied
-- subtree. Ignoring the attribute is the one option that is certainly
-- wrong: it copies namespaces where the test asks for them to be
-- dropped (copy-0601).
#guard run (ss "<xsl:template match=\"/\"><out><xsl:copy-of select=\"*\" copy-namespaces=\"no\"/></out></xsl:template>")
           "<doc xmlns:p=\"http://p.example/\"><a/></doc>" == "<out><doc><a/></doc></out>"
#guard run (ss "<xsl:template match=\"/\"><out><xsl:copy-of select=\"*\"/></out></xsl:template>")
           "<doc xmlns:p=\"http://p.example/\"><a/></doc>"
           == "<out><doc xmlns:p=\"http://p.example/\"><a/></doc></out>"

/-! ## Namespaces (§7.1.1) -/

-- A literal result element carries the namespace declarations in
-- scope on it in the stylesheet...
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:p=\"http://p.example/\" version=\"1.0\">"
            ++ "<xsl:template match=\"doc\"><out/></xsl:template></xsl:stylesheet>")
           "<doc/>" == "<out xmlns:p=\"http://p.example/\"/>"

-- ...except those `exclude-result-prefixes` names (copy-3301).
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:p=\"http://p.example/\" version=\"1.0\" exclude-result-prefixes=\"p\">"
            ++ "<xsl:template match=\"doc\"><out/></xsl:template></xsl:stylesheet>")
           "<doc/>" == "<out/>"

-- `xsl:element` with an unprefixed name and no `namespace` attribute
-- lands in the DEFAULT namespace, which may be none — and it must
-- say so, or it inherits the enclosing result element's default
-- namespace and becomes a different element (namespace-4501).
#guard run (ss "<xsl:template match=\"doc\"><xsl:element name=\"outer\" namespace=\"http://x.example/\"><xsl:element name=\"inner\"/></xsl:element></xsl:template>")
           "<doc/>" == "<outer xmlns=\"http://x.example/\"><inner xmlns=\"\"/></outer>"

-- Exclusion removes namespace NODES; it never moves the element itself
-- out of its namespace. With `#default` excluded, `out` is still in
-- `http://b.example/` and must say so; `in` inherits it from `out`
-- (namespace-4801).
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns=\"http://b.example/\" version=\"1.0\" exclude-result-prefixes=\"#default\">"
            ++ "<xsl:template match=\"doc\"><out><in/></out></xsl:template></xsl:stylesheet>")
           "<doc/>" == "<out xmlns=\"http://b.example/\"><in/></out>"
-- The same for an excluded PREFIX that the element and an attribute use.
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:p=\"http://p.example/\" version=\"1.0\" exclude-result-prefixes=\"p\">"
            ++ "<xsl:template match=\"doc\"><p:out p:a=\"1\"/></xsl:template></xsl:stylesheet>")
           "<doc/>" == "<p:out xmlns:p=\"http://p.example/\" p:a=\"1\"/>"
-- A literal result element in NO namespace, inside a result element
-- that has a default namespace, undeclares it.
#guard run (ss "<xsl:template match=\"doc\"><xsl:element name=\"outer\" namespace=\"http://x.example/\"><plain/></xsl:element></xsl:template>")
           "<doc/>" == "<outer xmlns=\"http://x.example/\"><plain xmlns=\"\"/></outer>"

/-! ## Nodes of another document (§12.1 `document()`)

A node's identity includes its DOCUMENT. Before it did, a node of
`document('')` was looked up at the same child-index path in the
SOURCE document: its namespaces, its parent and `/` all came from the
wrong tree, and a union with a source node at the same path counted
one node. -/

-- `xsl:copy` copies the namespaces in scope on the node in ITS document
-- (the stylesheet: `p` and `xsl`), not those of the source element at
-- the same path (`q`) (namespace-4801).
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:p=\"http://p.example/\" version=\"1.0\" exclude-result-prefixes=\"p\">"
            ++ "<xsl:template match=\"doc\"><out><xsl:for-each select=\"document('')//p:item\"><xsl:copy/></xsl:for-each></out></xsl:template>"
            ++ "<p:item/></xsl:stylesheet>")
           "<doc xmlns:q=\"http://q.example/\"><a/><b/></doc>"
  == "<out><p:item xmlns:p=\"http://p.example/\" xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\"/></out>"
-- Two documents' document elements are two nodes.
#guard run (ss "<xsl:template match=\"doc\"><out n=\"{count(/doc | document('')/*)}\"/></xsl:template>")
           "<doc/>" == "<out n=\"2\"/>"
-- `/` and `..` from a stylesheet node stay in the stylesheet.
#guard run (ss "<xsl:template match=\"doc\"><out><xsl:for-each select=\"document('')/*/*[1]\"><xsl:value-of select=\"name(/*)\"/>,<xsl:value-of select=\"name(..)\"/></xsl:for-each></out></xsl:template>")
           "<doc/>" == "<out>xsl:stylesheet,xsl:stylesheet</out>"
-- A template is matched against the node's own document: `p:item` is
-- the first child of the stylesheet element, at the same path as the
-- source's `x`, and the `x` template must not fire for it.
#guard run ("<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" xmlns:p=\"http://p.example/\" version=\"1.0\"><p:item/>"
            ++ "<xsl:template match=\"/\"><out><xsl:apply-templates select=\"document('')//p:item\"/></out></xsl:template>"
            ++ "<xsl:template match=\"x\">X</xsl:template><xsl:template match=\"p:item\">I</xsl:template></xsl:stylesheet>")
           "<doc><x/></doc>" == "<out xmlns:p=\"http://p.example/\">I</out>"

/-! ## Whitespace (§3.4) -/

-- A comment between two runs of character data in the stylesheet is
-- removed, and the runs then MERGE. Stripping whitespace-only text
-- before merging deleted indentation the transform is supposed to
-- emit (axes-090, id-016).
#guard run (ss "<xsl:template match=\"doc\"><out>\n  <!--k-->\nx</out></xsl:template>")
           "<doc/>" == "<out>\n  \nx</out>"

-- §7.1.1: excluded bindings still required by element/attribute names survive.
#guard run "<x:stylesheet xmlns:x='http://www.w3.org/1999/XSL/Transform' xmlns='urn:out' version='1.0' exclude-result-prefixes='#default'><x:template match='/'><out/></x:template></x:stylesheet>" "<doc/>" == "<out xmlns=\"urn:out\"/>"
-- §7.5: copying a stylesheet node must use the stylesheet's namespace scope.
-- Namespace declarations use main's fixed prefix presentation order (p, x).
#guard run "<x:stylesheet xmlns:x='http://www.w3.org/1999/XSL/Transform' xmlns:p='urn:p' version='1.0'><x:template match='/'><x:for-each select=\"document('')//p:a\"><x:copy/></x:for-each></x:template><p:a/></x:stylesheet>" "<doc/>" == "<p:a xmlns:p=\"urn:p\" xmlns:x=\"http://www.w3.org/1999/XSL/Transform\"/>"
-- An unqualified copied element must not inherit a result parent's default.
#guard run (ss "<xsl:template match='/'><out xmlns='urn:o'><xsl:copy-of select='doc/a'/></out></xsl:template>") "<doc><a/></doc>" == "<out xmlns=\"urn:o\"><a xmlns=\"\"/></out>"

private def externalRejected (docs : List (String × XPath.Full.Doc))
    (imports : List (String × Node)) : Bool :=
  match parseXML (ss ""), parseXML "<doc/>" with
  | .ok st, .ok src => match transform st src docs imports with
    | .refused _ => true
    | _ => false
  | _, _ => false
#guard externalRejected [("bad", [.element "p:doc" [] []])] []
#guard externalRejected [] [("bad", .element "x:stylesheet" [] [])]

-- External provenance survives variable storage, parent steps and copy-of.
#guard run "<x:stylesheet xmlns:x='http://www.w3.org/1999/XSL/Transform' xmlns:p='urn:p' version='1.0'><x:template match='/'><x:variable name='v' select=\"document('')//p:a\"/><x:for-each select='$v'><x:value-of select='namespace-uri(.)'/><x:value-of select='name(..)'/><x:copy-of select='.'/></x:for-each></x:template><p:a/></x:stylesheet>" "<doc/>" == "urn:px:stylesheet<p:a xmlns:p=\"urn:p\" xmlns:x=\"http://www.w3.org/1999/XSL/Transform\"/>"
end L4Factoidal.XSLT
