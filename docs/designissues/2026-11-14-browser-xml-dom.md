# The browser's XML APIs over the tree's XML stack (2026-11-14)

Scope: WPT `domxpath/`, the XML side of `domparsing/`, and `xml/` (with `xml/xslt/`), on
BubblePopJS. This record says what was built, why it is built that way, what was measured,
and what is proved, tested only, and open.

## Decision 1: DOM XPath is the tree's XPath 1.0 evaluator, through a projection

The tree has two XPath evaluators: `L4Factoidal.XPath.Full` (XPath 1.0 over `XML.Node`, used
by XSLT 1.0, XPointer and the XPath 1.0 conformance run) and `L4Factoidal.XPath4` (XPath 4.0
over XDM, with an XPath 1.0 compatibility mode). DOM XPath is XPath 1.0 (DOM §8 names the
interfaces of DOM Level 3 XPath), so the browser uses `XPath.Full`:

- its value model is exactly the four XPath 1.0 types and the 1.0 conversion and comparison
  rules (`Value.toStr`, `toNum`, `toBool`, `cmpValues`); the compatibility mode of XPath 4.0
  is close to these rules and not equal to them (XPath 4.0 Appendix on incompatibilities);
- its node identity is an address in a tree (child indices from the document node, a slot for
  an attribute), which is cheap to map to and from a DOM arena;
- the XSLT 1.0 processor already depends on it, so `XSLTProcessor` uses one projection.

The evaluator is not generic over a tree interface: its axes, document order (`Loc.key`) and
node identity are stated over addresses in an `XML.Node` tree, and XSLT, XPointer and the
suites rely on them as they are. The adapter is therefore a **projection**
(`L4Factoidal/DOM/XPath/Project.lean`): the tree of the context node's root is projected to
the evaluator's document, one `XML.Node` for each DOM node and in the same order; the
context node's address goes in, and each result address is mapped back to its DOM node. The
evaluator itself is unchanged in what it computes.

Differences between the two data models and what the projection does:

| DOM | XPath 1.0 data model | Projection |
| --- | --- | --- |
| DocumentType is a child of the Document | no such node (§5) | left out; child indices count the other children (`xkids`) |
| an element has a namespace; declarations are attributes | names resolve through `xmlns` declarations in scope | the declarations that give each node the DOM's namespace are written (`elemDecls`); DOM `xmlns` attributes are not attribute nodes (§5.3) |
| a tree's root may be an element, a DocumentFragment or a shadow root | the root is the document node | a Document or DocumentFragment root is the document node; any other root is put under a document node that maps to no DOM node (`wrapped`) |
| no namespace nodes | namespace axis | an address of a namespace node maps to no DOM node (`refOfItem`), so the axis gives the page nothing, as in Chrome and Firefox |
| adjacent Text nodes may exist | text nodes are maximal | each DOM Text node is one node (open, below) |

What DOM XPath adds to XPath 1.0 (`L4Factoidal/DOM/XPath/Evaluate.lean`):

- the prefixes of an expression, which the page's XPathNSResolver resolves (`prefixesOf`,
  from the evaluator's own tokens);
- the name test of HTML documents (`htmlNameTest`): an unprefixed name test selects HTML
  elements by their local name in ASCII lower case, and no element of another or no
  namespace; an unprefixed attribute test on an HTML element is compared in ASCII lower
  case. The evaluator takes it as a parameter (`Ctx.nameTest?`, default: XPath 1.0 §2.3) and
  knows nothing of HTML;
- the result types of `XPathResult` and the errors (`answerOf`, `evaluate`).

Changes in the evaluator (each is XPath 1.0, and holds for XSLT too):

- a name may hold the name characters of XML outside ASCII (`XPath/Expr.lean`); before, the
  expression `//dØdd` did not parse;
- `id()` selects the first element in document order that has an ID (§5.2.1: a second element
  with the same ID has no ID); before, every element with the ID was selected;
- `normalize` (sort into document order, drop duplicates) drops duplicates in one pass; the
  result is the same list (not proved; the suites decide).

## Decision 2: `XSLTProcessor` is the tree's XSLT 1.0 processor on the same projection

`L4Factoidal/DOM/XPath/Xslt.lean` gives `XSLT.transform` the stylesheet and the source as the
`XML.Document`s of their projections, and answers the serialised result and the output method.
The page's script layer hands the text to the engine's HTML or XML parser for that method and
makes the Document or DocumentFragment. Nothing of XSLT is decided outside `XSLT.transform`.

## Decision 3: a script-facing XML document builder

`DOM.OfXml.parseXmlDocument` builds the arena of a page for style and layout: no prefixes, no
namespace declarations, CDATA as Text. `DOMParser` and `responseXML` documents are read by
scripts, so `L4Factoidal/DOM/OfXmlFull.lean` keeps prefixes, namespace declarations as
attributes in the XMLNS namespace, CDATASection nodes, and the comments and processing
instructions around the document element. Pages keep the first builder (no change to
rendering).

The source bound of `DOMParser` (`create_node` kinds 11 and 12) is 16 MiB (`Hosts.Dom.maxDocument`);
it was the 64 KiB bound of every script string, which refused `domxpath/xml_xpath_tests.xml`
(2.3 MB). Other kinds keep 64 KiB.

## Decision 4: `XMLSerializer` is the XML serialization algorithm in the engine

`L4Factoidal/DOM/XmlSerialize.lean` is DOM Parsing §3.2, with its state (namespace prefix map,
local prefixes map, generated prefix index). Two choices where the text and the tests leave
one are stated in the module's header (an `xmlns` attribute with no namespace is read as a
default namespace declaration; an attribute keeps its prefix when that prefix is bound to
nothing).

## Wire (`Hosts.DomOps`, `node_query`)

121 prefixes of an expression; 122 evaluate; 123 the DOM's change count (iterator
invalidation); 124 XML serialization; 127 XSLT transform. `prelude.js` section `xmlweb`
declares `XPathEvaluator`, `XPathExpression`, `XPathResult`, `XMLSerializer`, `XSLTProcessor`
and the three methods of `Document`; it calls the page's resolver, marshals arguments and
makes result objects.

## Cost

A page that calls none of these APIs runs none of this code: the ops are reached only from
the new interfaces; the script prelude grows by about 12 KB of source. An evaluation costs one
projection of the context node's tree (linear in its size) and the evaluator's own cost.
Timings: see "Measured".

## Measured

See the table in the night report of this work; this section is filled from cloud runs only.

MEASURED_PLACEHOLDER

## Proved / tested only / open

PTO_PLACEHOLDER
