/-
L4Factoidal.XML.Canonical — Canonical XML Version 1.0, the inclusive
form WITH comments, over the parse tree of `L4Factoidal.XML.Parser`.

Spec: Canonical XML Version 1.0, W3C Recommendation 15 March 2001,
https://www.w3.org/TR/2001/REC-xml-c14n-20010315 . Section numbers
below cite it.

## What the canonical form changes (§1.1, §2.3)

  * a CDATA section becomes its character content;
  * an empty element becomes a start-end tag pair;
  * attribute values are delimited by `"`, and the special characters
    of text and attribute values become character references (§2.3,
    "Text Nodes" and "Attribute Nodes");
  * the XML declaration and the document type declaration are removed;
  * an element writes a namespace declaration only where the binding is
    not already in force on its parent (superfluous declarations are
    removed), and writes `xmlns=""` only where its parent has a default
    namespace and it has none (§2.3, "Namespace Nodes");
  * namespace declarations come first, sorted by prefix, the default
    namespace first; the attributes follow, sorted by namespace URI and
    then by local name (§2.3, "Element Nodes"). Lexicographic order here
    is by Unicode code point, which is the order of `String.lt`.

Character references and entity references are already replaced, and
line ends already normalised, by the parser. So are DTD defaults: the
parser supplies the default of an attribute a start tag leaves out (XML
1.0 §3.3.2, §5.1), and Canonical XML §2.3 writes it like a specified
attribute ("the attribute nodes of the element, including defaulted
ones": the node set is that of the XPath data model, which has them).

## What it does not do

  * Document subsets and the exclusive variant. Exclusive XML
    Canonicalization is `L4Factoidal.RDF.XmlCanon`, which the RDF
    XMLLiteral value space requires; it drops namespace declarations
    that the element does not use, and this module keeps them, as
    Canonical XML 1.0 does.

## Why it is here

The W3C XSLT and XQuery test suites define `assert-xml` as a comparison
of canonical forms: "The assertion is true if the result of parsing and
canonicalizing the XML given in the body of the assert-xml element is
the same (byte-for-byte) as the result of canonicalizing the XML result
of the query" (catalog-schema.xsd of w3c/xslt30-test). Attribute order
and namespace-declaration order are therefore not part of what a test
checks, and a text comparison that treats them as significant reports
a failure the suite does not state.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XML.Canonical

open L4Factoidal.XML

/-- The namespace bindings in force on an element: prefix to namespace
    name, with `""` for the default namespace. -/
abbrev Scope := List (String × String)

/-- The XML namespace. Namespaces in XML §3 binds the `xml` prefix to it
    on every element; §2.3 never renders that binding. -/
def xmlNamespace : String := "http://www.w3.org/XML/1998/namespace"

/-- §2.3 Text Nodes: `&`, `<`, `>` and `#xD` become references. -/
def escText (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;"
    else if c == '>' then "&gt;" else if c == '\r' then "&#xD;"
    else c.toString))

/-- §2.3 Attribute Nodes: `&`, `<`, `"`, `#x9`, `#xA` and `#xD` become
    references. -/
def escAttr (s : String) : String :=
  String.join (s.toList.map (fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;"
    else if c == '"' then "&quot;" else if c == '\t' then "&#x9;"
    else if c == '\n' then "&#xA;" else if c == '\r' then "&#xD;"
    else c.toString))

/-- Is this attribute a namespace declaration? -/
def isNsDeclName (n : String) : Bool :=
  n == "xmlns" || n.startsWith "xmlns:"

/-- The namespace declarations among an element's attributes. -/
def nsDecls (attrs : List Attribute) : Scope :=
  attrs.filterMap (fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:" then some (String.ofList (a.name.toList.drop 6), a.value)
    else none)

def lookup (sc : Scope) (p : String) : Option String :=
  (sc.find? (fun b => b.1 == p)).map (·.2)

/-- The bindings in force on an element: the parent's, with the
    element's own declarations applied. An EMPTY value removes the
    binding: `xmlns=""` undeclares the default namespace (Namespaces in
    XML §6.2), and so does `xmlns:p=""` for `p` in XML 1.1. -/
def extendScope (sc : Scope) (ds : Scope) : Scope :=
  ds.foldl (fun acc (p, u) =>
    let rest := acc.filter (fun b => b.1 != p)
    if u.isEmpty then rest else rest ++ [(p, u)]) sc

/-- Split a QName at its first colon: `(prefix, local part)`, with an
    empty prefix for an unprefixed name. -/
def splitQName (q : String) : String × String :=
  match q.toList.findIdx? (· == ':') with
  | some i => (String.ofList (q.toList.take i), String.ofList (q.toList.drop (i + 1)))
  | none   => ("", q)

/-- Insertion sort by a strict order. Total and structural; the lists it
    sorts are one element's declarations or attributes. -/
def insertBy (lt : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if lt y x then y :: insertBy lt x ys else x :: y :: ys

def sortBy (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (insertBy lt) []

def strLt (a b : String) : Bool := decide (a < b)

def pairLt (a b : String × String) : Bool :=
  strLt a.1 b.1 || (a.1 == b.1 && strLt a.2 b.2)

/-- §2.3 Namespace Nodes, for a whole document: an element renders a
    binding unless its parent has the same prefix bound to the same
    namespace name; it renders `xmlns=""` when the parent has a default
    namespace and the element has none. The `xml` binding is never
    rendered. Sorted by prefix, so the default namespace (prefix `""`)
    comes first. -/
def renderedDecls (parent own : Scope) : List (String × String) :=
  let kept := own.filter (fun (p, u) => p != "xml" && lookup parent p != some u)
  let undecl := if (lookup own "").isNone && (lookup parent "").isSome then [("", "")] else []
  sortBy (fun a b => strLt a.1 b.1) (kept ++ undecl)

/-- §2.3 Element Nodes: the attribute sort key is the namespace URI,
    then the local name. An unprefixed attribute is in no namespace
    (Namespaces in XML §6.2), so its URI is empty and it sorts first. A
    prefix with no binding keeps the prefix itself as its key, so the
    order is still total. -/
def attrKey (sc : Scope) (name : String) : String × String :=
  let (p, l) := splitQName name
  if p == "" then ("", name) else ((lookup sc p).getD p, l)

def declText (ds : List (String × String)) : String :=
  String.join (ds.map (fun (p, u) =>
    " " ++ (if p == "" then "xmlns" else "xmlns:" ++ p) ++ "=\"" ++ escAttr u ++ "\""))

def attrText (sc : Scope) (as : List Attribute) : String :=
  let plain := as.filter (fun a => !isNsDeclName a.name)
  let sorted := sortBy (fun a b => pairLt (attrKey sc a.name) (attrKey sc b.name)) plain
  String.join (sorted.map (fun a => " " ++ a.name ++ "=\"" ++ escAttr a.value ++ "\""))

mutual

/-- The canonical form of one node, given the bindings in force on its
    parent element. -/
def canonNode (parent : Scope) : Node → String
  | .text s     => escText s
  | .cdata s    => escText s
  | .comment b  => "<!--" ++ b ++ "-->"
  | .pi t d     => "<?" ++ t ++ (if d.isEmpty then "" else " " ++ d) ++ "?>"
  | .element t attrs kids =>
      let own := extendScope parent (nsDecls attrs)
      "<" ++ t ++ declText (renderedDecls parent own) ++ attrText own attrs ++ ">"
        ++ canonNodesAcc own kids "" ++ "</" ++ t ++ ">"

/-- The canonical forms of `ns` appended to `acc`, one sibling at a time:
the self-call is a tail call, so the number of siblings costs no stack
and each sibling is appended once (the readable form appended after its
recursive call, one frame per sibling) (https://github.com/danbri/factoidal/issues/746). -/
def canonNodesAcc (sc : Scope) : List Node → String → String
  | [],      acc => acc
  | n :: ns, acc => canonNodesAcc sc ns (acc ++ canonNode sc n)

end

/-- The canonical forms of a list of sibling nodes, concatenated. -/
def canonNodes (sc : Scope) (ns : List Node) : String := canonNodesAcc sc ns ""

theorem canonNodesAcc_eq (sc : Scope) (ns : List Node) :
    ∀ acc : String, canonNodesAcc sc ns acc = acc ++ canonNodes sc ns := by
  induction ns with
  | nil => intro acc; simp [canonNodes, canonNodesAcc, String.append_empty]
  | cons n ns ih =>
      intro acc
      simp only [canonNodes, canonNodesAcc]
      rw [ih, ih ("" ++ canonNode sc n)]
      simp [String.append_assoc, String.empty_append]

theorem canonNodes_nil (sc : Scope) : canonNodes sc [] = "" := rfl

theorem canonNodes_cons (sc : Scope) (n : Node) (ns : List Node) :
    canonNodes sc (n :: ns) = canonNode sc n ++ canonNodes sc ns := by
  simp only [canonNodes, canonNodesAcc]
  rw [canonNodesAcc_eq]; simp [String.empty_append]; rfl

/-- The bindings in force above the document element: only `xml`. -/
def rootScope : Scope := [("xml", xmlNamespace)]

/-- The canonical form of an element and its subtree, as a whole
    document's document element. -/
def canonElement (n : Node) : String := canonNode rootScope n

/-- §2.3 Root Node: a comment or processing instruction before the
    document element is followed by `#xA`; one after it is preceded by
    `#xA`. The XML and document type declarations are not output. -/
def canonDocument (d : Document) : String :=
  String.join (d.prolog.map (fun n => canonNode rootScope n ++ "\n"))
    ++ canonNode rootScope d.root
    ++ String.join (d.epilog.map (fun n => "\n" ++ canonNode rootScope n))

mutual

/-- A node with every comment below it removed. -/
def dropComments : Node → Node
  | .element t attrs kids => .element t attrs (dropCommentsListAcc kids [])
  | n => n

/-- The non-comment nodes of a list with their comments removed, after
`acc` (earlier ones, newest first): a tail call per sibling (https://github.com/danbri/factoidal/issues/746). -/
def dropCommentsListAcc : List Node → List Node → List Node
  | [], acc => acc.reverse
  | n :: rest, acc =>
      match n with
      | .comment _ => dropCommentsListAcc rest acc
      | n => dropCommentsListAcc rest (dropComments n :: acc)

end

/-- A list of sibling nodes without its comments, every comment below
them removed too. -/
def dropCommentsList (ns : List Node) : List Node := dropCommentsListAcc ns []

theorem dropCommentsListAcc_eq (ns : List Node) :
    ∀ acc : List Node, dropCommentsListAcc ns acc = acc.reverse ++ dropCommentsList ns := by
  induction ns with
  | nil => intro acc; simp [dropCommentsList, dropCommentsListAcc]
  | cons n rest ih =>
      intro acc
      cases n <;> simp only [dropCommentsList, dropCommentsListAcc] <;> simp only [ih] <;> simp

theorem dropCommentsList_nil : dropCommentsList [] = [] := rfl

theorem dropCommentsList_comment (b : String) (rest : List Node) :
    dropCommentsList (.comment b :: rest) = dropCommentsList rest := by
  rfl

theorem dropCommentsList_cons (n : Node) (rest : List Node) (h : ∀ b, n ≠ .comment b) :
    dropCommentsList (n :: rest) = dropComments n :: dropCommentsList rest := by
  cases n with
  | comment b => exact absurd rfl (h b)
  | _ =>
      show dropCommentsListAcc rest [dropComments _] = _
      rw [dropCommentsListAcc_eq]; rfl

/-- Canonical XML 1.0 WITHOUT comments, the form the Recommendation names
    "Canonical XML (omits comments)": the document with every comment
    removed, canonicalised. -/
def canonDocumentNoComments (d : Document) : String :=
  canonDocument
    { d with prolog := dropCommentsList d.prolog, root := dropComments d.root,
             epilog := dropCommentsList d.epilog }

/-- Canonicalise a FRAGMENT: a string that may hold several top-level
    nodes, or text, and so need not be a well-formed document. It is
    wrapped in one element and the wrapper is canonicalised with it,
    which is how the xslt30-test catalog says to compare an `assert-xml`
    body ("converting the string into a well-formed document by adding a
    wrapper element"). `none` when even the wrapped string is not
    well-formed. -/
def canonicalFragment? (s : String) : Option String :=
  match parseXML ("<fragment>" ++ s ++ "</fragment>") with
  | .ok d    => some (canonDocument d)
  | .error _ => none

/-! ## Checks

The first is the Recommendation's own example §3.3 ("Start and End
Tags"), without its document type declaration; the second is the same
example with it, which defaults `attr="default"` on `e9`. -/

#guard canonicalFragment?
    ("<doc>\n   <e1   />\n   <e2   ></e2>\n" ++
     "   <e3   name = \"elem3\"   id=\"elem3\"   />\n" ++
     "   <e4   name=\"elem4\"   id=\"elem4\"   ></e4>\n" ++
     "   <e5 a:attr=\"out\" b:attr=\"sorted\" attr2=\"all\" attr=\"I'm\"\n" ++
     "      xmlns:b=\"http://www.ietf.org\"\n" ++
     "      xmlns:a=\"http://www.w3.org\"\n" ++
     "      xmlns=\"http://example.org\"/>\n" ++
     "   <e6 xmlns=\"\" xmlns:a=\"http://www.w3.org\">\n" ++
     "      <e7 xmlns=\"http://www.ietf.org\">\n" ++
     "         <e8 xmlns=\"\" xmlns:a=\"http://www.w3.org\">\n" ++
     "            <e9 xmlns=\"\" xmlns:a=\"http://www.ietf.org\"/>\n" ++
     "         </e8>\n      </e7>\n   </e6>\n</doc>")
  == some ("<fragment><doc>\n   <e1></e1>\n   <e2></e2>\n" ++
     "   <e3 id=\"elem3\" name=\"elem3\"></e3>\n" ++
     "   <e4 id=\"elem4\" name=\"elem4\"></e4>\n" ++
     "   <e5 xmlns=\"http://example.org\" xmlns:a=\"http://www.w3.org\" " ++
     "xmlns:b=\"http://www.ietf.org\" attr=\"I'm\" attr2=\"all\" " ++
     "b:attr=\"sorted\" a:attr=\"out\"></e5>\n" ++
     "   <e6 xmlns:a=\"http://www.w3.org\">\n" ++
     "      <e7 xmlns=\"http://www.ietf.org\">\n" ++
     "         <e8 xmlns=\"\">\n" ++
     "            <e9 xmlns:a=\"http://www.ietf.org\"></e9>\n" ++
     "         </e8>\n      </e7>\n   </e6>\n</doc></fragment>")

-- The same example with its document type declaration: the attribute the
-- DTD defaults on `e9` is in the canonical form (Canonical XML §3.3).
#guard (match parseXML
    ("<!DOCTYPE doc [<!ATTLIST e9 attr CDATA \"default\">]>\n" ++
     "<doc>\n   <e1   />\n   <e2   ></e2>\n" ++
     "   <e3   name = \"elem3\"   id=\"elem3\"   />\n" ++
     "   <e4   name=\"elem4\"   id=\"elem4\"   ></e4>\n" ++
     "   <e5 a:attr=\"out\" b:attr=\"sorted\" attr2=\"all\" attr=\"I'm\"\n" ++
     "      xmlns:b=\"http://www.ietf.org\"\n" ++
     "      xmlns:a=\"http://www.w3.org\"\n" ++
     "      xmlns=\"http://example.org\"/>\n" ++
     "   <e6 xmlns=\"\" xmlns:a=\"http://www.w3.org\">\n" ++
     "      <e7 xmlns=\"http://www.ietf.org\">\n" ++
     "         <e8 xmlns=\"\" xmlns:a=\"http://www.w3.org\">\n" ++
     "            <e9 xmlns=\"\" xmlns:a=\"http://www.ietf.org\"/>\n" ++
     "         </e8>\n      </e7>\n   </e6>\n</doc>") with
  | .ok d => some (canonDocument d)
  | .error _ => none)
  == some ("<doc>\n   <e1></e1>\n   <e2></e2>\n" ++
     "   <e3 id=\"elem3\" name=\"elem3\"></e3>\n" ++
     "   <e4 id=\"elem4\" name=\"elem4\"></e4>\n" ++
     "   <e5 xmlns=\"http://example.org\" xmlns:a=\"http://www.w3.org\" " ++
     "xmlns:b=\"http://www.ietf.org\" attr=\"I'm\" attr2=\"all\" " ++
     "b:attr=\"sorted\" a:attr=\"out\"></e5>\n" ++
     "   <e6 xmlns:a=\"http://www.w3.org\">\n" ++
     "      <e7 xmlns=\"http://www.ietf.org\">\n" ++
     "         <e8 xmlns=\"\">\n" ++
     "            <e9 xmlns:a=\"http://www.ietf.org\" attr=\"default\"></e9>\n" ++
     "         </e8>\n      </e7>\n   </e6>\n</doc>")
-- ...and without the declaration it is not there.
#guard (match parseXML "<doc><e9 xmlns:a=\"http://www.ietf.org\"/></doc>" with
  | .ok d => some (canonDocument d)
  | .error _ => none) == some "<doc><e9 xmlns:a=\"http://www.ietf.org\"></e9></doc>"

-- Canonical XML WITHOUT comments drops every comment, keeps processing
-- instructions, and puts nothing in a comment's place.
#guard (match parseXML "<!--c1--><?p d?><a><!--c2-->x<!--c3--><b><!--c4--></b></a><!--c5-->" with
  | .ok d => some (canonDocumentNoComments d)
  | .error _ => none) == some "<?p d?>\n<a>x<b></b></a>"
-- ...and the form WITH comments keeps them.
#guard (match parseXML "<!--c1--><a><!--c2--></a>" with
  | .ok d => some (canonDocument d)
  | .error _ => none) == some "<!--c1-->\n<a><!--c2--></a>"

-- Attribute order and declaration order are not significant.
#guard canonicalFragment? "<a y=\"1\" x=\"2\"/>" == canonicalFragment? "<a x=\"2\" y=\"1\"/>"
#guard canonicalFragment? "<a xmlns:q=\"v\" xmlns:p=\"u\"/>"
    == canonicalFragment? "<a xmlns:p=\"u\" xmlns:q=\"v\"/>"
-- A redeclaration of a binding already in force is superfluous.
#guard canonicalFragment? "<a xmlns:p=\"u\"><b xmlns:p=\"u\"/></a>"
    == canonicalFragment? "<a xmlns:p=\"u\"><b/></a>"
-- An empty element and a CDATA section have the same canonical form as
-- the tag pair and the escaped text.
#guard canonicalFragment? "<a/>" == canonicalFragment? "<a></a>"
#guard canonicalFragment? "<a><![CDATA[x<y]]></a>" == canonicalFragment? "<a>x&lt;y</a>"
-- `xmlns=""` is significant only under a default namespace.
#guard canonicalFragment? "<a><b xmlns=\"\"/></a>" == canonicalFragment? "<a><b/></a>"

-- Negative cases: each of these is a different document.
#guard canonicalFragment? "<a x=\"1\"/>" != canonicalFragment? "<a x=\"2\"/>"
#guard canonicalFragment? "<a xmlns=\"u\"/>" != canonicalFragment? "<a/>"
#guard canonicalFragment? "<a xmlns=\"u\"><b xmlns=\"\"/></a>"
    != canonicalFragment? "<a xmlns=\"u\"><b/></a>"
#guard canonicalFragment? "<p:a xmlns:p=\"u\"/>" != canonicalFragment? "<p:a xmlns:p=\"v\"/>"
-- An unused declaration is KEPT: this is the inclusive form.
#guard canonicalFragment? "<a xmlns:p=\"u\"/>" != canonicalFragment? "<a/>"
#guard canonicalFragment? "<a> </a>" != canonicalFragment? "<a></a>"
#guard canonicalFragment? "<a><b/><c/></a>" != canonicalFragment? "<a><c/><b/></a>"
-- Not well-formed even when wrapped.
#guard canonicalFragment? "<a>" == none

end L4Factoidal.XML.Canonical
