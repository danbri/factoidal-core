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

Proved (`L4Factoidal/DOM/XPath/Theorems.lean`). The first seven and the module's `#guard`s
were compiled by the cloud engine build of run 43562441059 (the module imported by
`Hosts.DomOps` on the check branch `wip/xml-specs-xmlweb-thm`; `WEB_RENDER_BUILD_RC=0`);
the last five and `#print axioms` are in proof check 2 (PROOF2_STATUS):

- `projNode_element`: with fuel left, the projection of an element is an element whose
  children are the projections of its XPath children, one for one and in order.
- `projNode_child`: child index `i` of a projected element names the projection of the
  `i`-th XPath child of the DOM element, and nothing exactly when there is no such child.
  The evaluator reads children only by this index (`childrenOf`), and `descendant`,
  `following`, `preceding` and document order are functions of the addresses it gives.
- `xkids_not_doctype`: a DocumentType is never a node of the projection.
- `nodeAtPath_nil`, `nodeAtPath_cons`, `domOfPath_rooted`: the map from an address to a DOM
  node reads the same child lists as the projection, index by index.
- `refOfItem_ns`: a namespace node maps to no DOM node.
- `htmlNameTest_not_name`: the node test of HTML documents equals XPath 1.0's for every
  node test that is not a QName; the HTML rule changes QName tests only.
- `answerOf_number`, `answerOf_string`, `answerOf_boolean`: a request for the number,
  string or boolean result type answers the evaluator's conversion of the value.
- `serializeNode_text`: a Text node serializes as its escaped data and leaves the generated
  prefix index unchanged.

Tested only (`#guard` in the same module, and the WPT runs above):

- evaluation through the adapter on small arenas: child, descendant, attribute, parent,
  following, preceding, the document order of a union, result types and errors;
- `pathOf` and `domOfPath` are inverse on the test arena (not proved: it needs the arena
  invariant that a node's `parent` lists it among its `kids`);
- the HTML name test (the cases of WPT `text-html-elements.html`, `text-html-attributes.html`);
- the prefixes of an expression;
- the XML serialization (cases of WPT `XMLSerializer-serializeToString.html`);
- the script-facing XML document builder (prefix, declarations, CDATA; round trip through
  the serialization);
- `XPath.Full.normalize` after its one-pass rewrite, `id()` with duplicate IDs, non-ASCII
  names: by the suites only.

Open:

- No theorem yet that evaluating on the projection equals evaluating through a direct tree
  interface (there is no such interface); the statement proved is the one the projection
  makes true locally (children, order, addresses). A theorem that `pathOf` inverts
  `domOfPath` on well-formed arenas is the next step.
- The fuel of `projNode` (`d.size + 1`) is not proved to exceed the depth of every tree of a
  well-formed arena.
- Adjacent Text nodes are separate XPath nodes (XPath 1.0 has maximal text nodes); CDATASection
  nodes are text nodes of the evaluator.
- A root that is not a Document or DocumentFragment (a detached element): `/` selects a
  document node that is no DOM node, so `/` gives nothing and `/*` gives the root element.
- Namespaces of a DOM tree that no XML document can spell (an element and its attribute
  using one prefix for two namespaces; an attribute with a namespace and no prefix gets a
  made prefix, which `name()` shows).
- `count(namespace::*)` counts the evaluator's namespace nodes although the page can get none.
- Cost: `XPath.Full` is quadratic in places (`followingOf`, `descendantsOf` per step), and each
  name test walks the declarations from the root (`scopeAtPath`). Fine for the suites; a page
  that evaluates over a large document needs the evaluator's axes made linear.
- XSLT: parameters do not reach the stylesheet; `key`, `format-number` and
  `unparsed-entity-uri` are not implemented (3 subtests of `functions.tentative`); output
  method `html` gives the HTML parser XML-serialised text, so an empty non-void element
  (`<div/>`) reads as an open tag; `xsl:import`/`xsl:include` load nothing; `<?xml-stylesheet?>`
  in a page is the lab's existing path (`WebXslt`), not changed here.
- XML serialization: the require well-formed flag (the InvalidStateError cases of `innerHTML`
  in XML documents) is not implemented; two choices against the letter of the specification
  are stated in the module.
- XML fragment parsing: `innerHTML` and `outerHTML` setters, `insertAdjacentHTML` and
  `createContextualFragment` in an XML document still use the HTML fragment parser.
- `DOMParser` documents: the document type declaration is not kept; the URL recorded is the
  page's URL at load (`State.url`), which `history.pushState` does not change; a parser of
  another frame's realm is not supported.
- Cross-realm tests of `domxpath/` need a frame's window objects in the parent's realm.
