# RDFa 1.1 and Microdata to RDF, with no web platform dependency

Date: 2026-10-28. Status: design, no code. Tracking:
https://github.com/danbri/factoidal/issues/1165 (spec coverage; section "RDFa
1.1 and Microdata to RDF"). Owner condition, 2026-10-28, verbatim from that
issue: "only if the design is not tied to a browser".

## Result

The condition is met. The HTML parser that the issue asks a design record
about exists in Lean already:

- `formal/lean4/L4Factoidal/HTML/Tokenizer.lean` (518 lines, WHATWG HTML
  §13.2.5), `HTML/TreeBuilder.lean` (1,725 lines, §13.2.6: all insertion
  modes, foreign content, adoption agency, foster parenting, `template`),
  `HTML/Entities.lean` and `HTML/EntityData.lean` (the full named character
  reference table), `HTML/Tests.lean` (`#guard`s).
- `formal/lean4/L4Factoidal/XPath4/Html.lean` maps the HTML DOM to an
  `L4Factoidal.XML.Node` tree with XHTML, SVG and MathML namespaces
  (`toXml`, F&O 4.0 §17.3.1), with encoding detection. It serves
  `fn:parse-html` and `fn:html-doc`. Commit `f263632e`, 2026-10-28.

So the decision "implement the WHATWG tokenizer and tree builder in Lean, or
take a DOM from the host" is already made by the code: Lean parses HTML. The
RDFa and Microdata processors take an `XML.Node` tree. The host DOM is an
optional second source of that tree, never a requirement (section 5).

## 1. Target specifications (version-aware)

| Name in Lean | Specification | Status |
|---|---|---|
| `RdfaCore11` | RDFa Core 1.1, Third Edition, W3C Recommendation 2015-03-17 | target |
| `XhtmlRdfa11` | XHTML+RDFa 1.1, Third Edition, Recommendation 2015-03-17 | target |
| `HtmlRdfa11` | HTML+RDFa 1.1, Second Edition, Recommendation 2015-03-17 | target |
| `RdfaLite11` | RDFa Lite 1.1, Second Edition, Recommendation 2015-03-17 | subset of Core; a theorem, not a second processor |
| `RdfaCore10` | RDFa in XHTML 1.0, Recommendation 2008-10-14 | later; the suite has 1.0 cases |
| `Microdata2Rdf` | Microdata to RDF, Second Edition, W3C Interest Group Note 2014-12-16 | target |
| `HtmlMicrodata` | HTML Microdata, W3C Working Group Note 2021-01-28 (and WHATWG HTML §5) | the item model that `Microdata2Rdf` reads |

RDF output is RDF 1.1 abstract syntax (`L4Factoidal.RDF` terms). RDFa has no
triple-term syntax; an RDF 1.2 extension is out of these specifications.

## 2. Test suites (vendor with provenance, iron rule 6)

- **rdfa.info test suite**: https://github.com/rdfa/rdfa.github.io,
  directory `test-suite/` (manifest `manifest.jsonld`, test files per host
  language `xml`, `xhtml1`, `xhtml5`, `html4`, `html5`, `svg` and per version
  `rdfa1.0`, `rdfa1.1`, `rdfa1.1-vocab`, `rdfa1.1-proc`). Each case has an
  input document and a SPARQL ASK query (`.sparql`) that must answer true
  (or false for negative cases). The SPARQL 1.1/1.2 engine in Lean runs
  the ASK queries, so no new result format is needed.
  Vendor to `third_party/testing/rdfa/` with a `PROVENANCE.md` that records
  the repository commit and the licence that the repository states.
- **Microdata to RDF tests**: https://github.com/w3c/microdata-rdf, directory
  `tests/` (manifest `manifest.jsonld`; HTML input and expected Turtle or
  N-Quads output; some cases set a registry and the `vocab_expansion` option).
  Comparison is graph isomorphism (`RDF/Isomorphism` already used by the
  N-Triples and Turtle runners). Vendor to `third_party/testing/microdata-rdf/`.
- **HTML parser**: the QT4 `misc/HtmlTestSuite` (2,758 cases, in
  `third_party/testing/qt4tests`, already vendored) checks `fn:parse-html`
  against JSoup-produced XHTML. html5lib-tests
  (https://github.com/html5lib/html5lib-tests, `tokenizer/` and
  `tree-construction/`) is the direct
  conformance suite for the tokenizer and tree builder; it is not vendored
  yet. Stage 1 vendors it and adds a runner, so the RDFa-in-HTML scores rest
  on a measured parser.

## 3. Model and rendering split

There is no rendering. RDFa and Microdata are extraction: tree in, graph out.
The only browser question is where the tree comes from:

| Source | Status | Trust |
|---|---|---|
| XML parser (`XML.Parser`) for XHTML, SVG and other XML host languages | exists | checked in Lean |
| Lean HTML parser (`HTML.parseHtml` then `XPath4.toXml`) for HTML | exists | checked in Lean, measured by html5lib-tests |
| Host DOM (a browser `Document`, serialised to the same node form at the wasm ABI) | optional, later | a named assumption in the evidence record (owner decision of 2026-10-25 on freeform composition) |

The host DOM path is useful only for a page that scripts have changed after
load. It is opt-in, and its evidence record says "tree from host DOM,
unchecked".

## 4. Reuse

- Tree: `XML.Node` and `XML.NamespaceView` (namespace-resolved view).
- IRI resolution: the RFC 3986 resolver that Turtle and JSON-LD use.
- CURIEs, `@prefix`, `@vocab`: the RDFa initial context table. Part of it
  exists in `CSVW/MetadataParse.lean` (the CSVW prefixes, taken from the RDFa
  Core initial context). Stage 2 moves that table to one module
  (`RDFa/InitialContext.lean`) and CSVW imports it; no second copy.
- Literals and datatypes: `XSD` lexical forms; `rdf:XMLLiteral` serialisation
  through `XML` canonical output; `rdf:HTML` through the XHTML serialiser of
  `XPath4/Serialize.lean` (method `html`).
- Vocabulary expansion (`rdfa1.1-vocab`): the RDFS closure rules of
  `RDFS/FullClosure.lean` restricted to the rules RDFa Core §10.2 lists.
- Output and comparison: `L4Factoidal.RDF`, the SPARQL engine for the ASK
  queries, the graph isomorphism of the existing runners.
- Microdata item model: the HTML DOM after `toXml`; `itemid`, `itemtype`,
  `itemprop`, `itemref` are attribute reads.

## 5. Theorems to aim for

All statements name the specification versions in the module or the
statement, so a later version is a new theorem.

1. **XHTML and HTML agree** (the issue's request). Let `d` be a document
   that the XML parser reads (well-formed XHTML) and that the HTML parser
   reads with no parse error. If `XPath4.toXml (HTML.parseHtml d)` and the
   XML tree are equal after namespace normalisation, then
   `rdfa XhtmlRdfa11 tree = rdfa HtmlRdfa11 tree` up to blank node renaming,
   except for the host-language rules that differ (HTML+RDFa §3.1: `xml:lang`
   against `lang`, the `@version` and `@profile` rules, `rdf:HTML` literals).
   The theorem has two parts: (a) one processor `rdfaCore : HostRules →
   Node → Graph`, and both host languages are values of `HostRules`;
   (b) `HostRules` agree on every element that does not use the differing
   attributes. Part (b) is a lemma over the rule record, so the theorem is
   a congruence, not a proof over documents.
2. **Tree equality for the shared fragment**: for the XHTML documents in the
   rdfa.info suite that are also valid HTML, the two parsers give equal
   trees. This is a test (`#guard` per case or a runner check), not a
   theorem: the HTML tree builder has too many states for a general proof.
3. **RDFa Lite is a subset**: on documents that use only the RDFa Lite
   attributes, `rdfaCore` gives the same graph as the RDFa Lite processing
   rules.
4. **Microdata to RDF is a function of the item graph**: the RDF depends only
   on the item model (items, properties, values), not on element order
   outside `itemref` resolution. This is the property that makes the host DOM
   path substitutable.
5. **Set semantics** (anti-pattern 37): the output is a `CertifiedDataset`;
   a test counts triples for a document that states one triple twice.

## 6. Staged plan

| Stage | Work | Measure |
|---|---|---|
| 1 | Vendor html5lib-tests; add `l4html5lib` runner (tokenizer and tree-construction); file issues for each failing group | tree construction pass, fail (out of N); the HTML parser headers list unimplemented states (script data escaped, fragment parsing) and each becomes an issue with expected failures |
| 2 | `RDFa/InitialContext.lean` (move the CSVW table); `RDFa/Core.lean`: the RDFa Core 1.1 §7.5 sequence as a loop over an explicit stack of evaluation contexts (tail recursion rule) | `#guard`s from the RDFa Core examples |
| 3 | Vendor the rdfa.info suite; `l4rdfa` runner; host languages `xml`, `xhtml1`, `svg` first (XML parser) | rdfa1.1 xml/xhtml1/svg: pass, fail (out of N) |
| 4 | Host languages `html4`, `html5` through `HTML.parseHtml`; theorem 1 | rdfa1.1 html5: pass, fail (out of N); theorem 1 builds and `#print axioms` is clean |
| 5 | Vendor microdata-rdf tests; `Microdata/ToRdf.lean`; `l4microdata` runner | pass, fail (out of N) |
| 6 | Wasm op and npm `parse` format names `rdfa` and `microdata`; hub cell that extracts RDF from a pasted page | npm tests |
| 7 | Optional host DOM source, opt-in, with its evidence record entry | host test in Node with a DOM shim, browser test in `tests/web-demos` |

Each stage is one PR. Scores go to the W3C completeness ledger.

## 7. Decisions recorded here (coordinator, not owner)

- HTML is parsed in Lean, because the parser exists and serves `fn:parse-html`
  already. A host DOM is an optional source.
- The RDFa processor is one function over a host-language rule record, not one
  processor per host language, so theorem 1 is a congruence.
