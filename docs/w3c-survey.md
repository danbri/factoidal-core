# W3C standards survey and implementation dependency map

Survey date: 12 October 2026. Based on the W3C catalogue inspected on
11 October 2026 and a source/import audit of `formal/lean4/L4Factoidal/`.

This document brings together the standards inventory, a high-level dependency
map, and opportunities to share implementation work in Factoidal. It is not a
conformance assessment. No implementation changes or conformance-suite runs
were performed for the initial survey. Implementation changes and validation
on 21–22 October 2026 are recorded in the updates below. Earlier maps and findings
remain the initial audit snapshot, not a description of the updated code.

## Current implementation overview (22 October 2026)

The implementation updates below now share XML namespace resolution, XSD
lexical/calendar parsing, regex profiles, hexadecimal decoding, RDF term
identity and SPARQL/SHACL comparisons. Numeric equality, EBV, type tests,
arithmetic, unary functions and numeric constructors use shared XSD/F&O values.
RIF datatype membership, literal identity, matching and numeric operations now
reuse those layers. Native RIF and SPARQL/RIF also share RDF conversion and
declared-import loading, with explicit incomplete-result handling. CSVW and
JSON Schema share the supported ECMA regex profile and preserve unsupported
outcomes. These are concrete dependencies; not every consumer has migrated.
Edition selection, decimal precision, nonnumeric equality, legacy store/join
equality, regex completeness and QName context remain active work.

This is the implementation on the survey's working branch. A fresh fetch on
22 October found newer, separate implementations on `origin/main`, including
`Fn.Casting` and additional RIF built-ins. This branch has no Git merge base
with that mainline. Its results must not be reported as mainline results;
the [PR review record](20261022-standards-reuse-review.md) records that boundary
and the work needed to reconcile both implementations.

The initial inventory and diagrams below are historical audit snapshots.
Dated implementation sections record which findings have since been repaired,
with reproducible tests and remaining limits. No full-standards conformance
claim follows from these finite corpus runs.

## Scope and status

The scope is W3C technical Recommendations useful to servers, libraries,
validators, authoring tools and standalone processors. Formats also consumed by
browsers are included; browser-specific APIs, DOM/CSS platform implementation
and browser UI requirements are outside the main inventory.

The inventory groups editions and companion documents by family rather than
treating every primer, test collection or edition as a separate implementation
target. It is a broad family-level survey, not yet a complete, machine-checked
register of every Recommendation and its publication history.

An old Recommendation is not necessarily rescinded. Conversely, retaining
Recommendation status does not establish that a document is the preferred
choice for new implementation. A future per-document register should distinguish
Recommendation, superseded Recommendation, obsolete Recommendation and
rescinded Recommendation, as well as drafts, candidate Recommendations and Notes.
Do not infer status from a technology family or from a document's age.

Sources: [W3C catalogue](https://www.w3.org/TR/) and
[W3C document statuses](https://www.w3.org/standards/types/).

## Standards families

**RDF and linked-data formats.** RDF 1.1 comprises Concepts, Semantics, RDF
Schema, Turtle, TriG, N-Triples, N-Quads and RDF/XML. RDF Dataset Canonicalization,
JSON-LD 1.1 with its processing algorithms and framing, and RDFa Core/Lite with
HTML and XHTML bindings cover normalization, JSON interchange and embedded data.
Older RDF specifications and `rdf:PlainLiteral` matter for compatibility. RDF
1.2 draft and candidate documents must be tracked separately from Recommendations.
See [RDF Concepts](https://www.w3.org/TR/rdf11-concepts/),
[Canonicalization](https://www.w3.org/TR/rdf-canon/),
[JSON-LD](https://www.w3.org/TR/json-ld11/) and
[RDFa](https://www.w3.org/TR/rdfa-core/).

**Graph queries and services.** SPARQL 1.1 includes Query, Update, Federation,
Entailment Regimes, Service Description, the query/update Protocol, Graph Store
HTTP Protocol, and XML, JSON, CSV and TSV results. Each deserves its own map node
because endpoints implement different subsets. Linked Data Platform adds HTTP
conventions for RDF resources and containers. See the
[SPARQL family](https://www.w3.org/TR/sparql11-overview/) and
[LDP](https://www.w3.org/TR/ldp/).

**Ontologies, constraints and rules.** OWL 2 includes structural/functional
syntax, XML syntax, RDF mapping, direct and RDF-based semantics, conformance,
and EL, QL and RL profiles. SHACL supplies graph validation. RIF includes Core,
Basic Logic and Production Rule dialects, the logic-dialect framework, Datatypes
and Built-ins, and RDF/OWL Compatibility. Older OWL Recommendations belong in
the compatibility layer. See [OWL 2](https://www.w3.org/TR/owl2-overview/),
[SHACL](https://www.w3.org/TR/shacl/) and
[RIF built-ins](https://www.w3.org/TR/rif-dtb/).

**Tabular and relational data.** CSVW comprises the tabular data model, metadata
vocabulary, CSV-to-JSON and CSV-to-RDF transformations. R2RML and Direct Mapping
connect relational databases to RDF. These share datatype, lexical conversion,
identifier and URI-template dependencies. See
[CSVW](https://www.w3.org/TR/tabular-data-model/),
[R2RML](https://www.w3.org/TR/r2rml/) and
[Direct Mapping](https://www.w3.org/TR/rdb-direct-mapping/).

**Data vocabularies and discovery.** DCAT 3 describes datasets, distributions
and data services; SKOS describes concept schemes, taxonomies and thesauri.
Other Recommendations include the Organization Ontology, RDF Data Cube, Semantic
Sensor Network ontology and Ontology for Media Resources. POWDER supplies
resource descriptions, grouping rules and formal semantics. These are vocabulary
and semantic contracts even where no dedicated execution engine is required.
See [DCAT](https://www.w3.org/TR/vocab-dcat-3/),
[SKOS](https://www.w3.org/TR/skos-reference/) and
[POWDER](https://www.w3.org/TR/powder-dr/).

**Provenance, permissions and annotations.** PROV comprises PROV-DM,
PROV-Constraints, PROV-N and PROV-O: model, constraints, notation and ontology.
ODRL supplies a permissions/prohibitions/duties model and vocabulary. Web
Annotation supplies a data model, vocabulary and HTTP protocol for annotating
resources and fragments. See [PROV](https://www.w3.org/TR/prov-dm/),
[ODRL](https://www.w3.org/TR/odrl-model/) and
[Web Annotation](https://www.w3.org/TR/annotation-model/).

**Identity and credentials.** Include DID Core, Controlled Identifiers,
Verifiable Credentials Data Model 2.0, VC Data Integrity, ECDSA and EdDSA
cryptosuites, credential security through JOSE/COSE, and Bitstring Status List.
VC 1.1 remains a compatibility target. Dependencies include key representation,
canonicalization, signatures, identifiers, timestamps and status processing.
See [DIDs](https://www.w3.org/TR/did/),
[Controlled Identifiers](https://www.w3.org/TR/cid-1.0/) and
[VC 2.0](https://www.w3.org/TR/vc-data-model-2.0/).

**Social publishing and federation.** Activity Streams 2.0 and Activity
Vocabulary represent activities; ActivityPub defines client/server and
server/server interactions. WebSub handles subscriptions and delivery, Micropub
publishing, Webmention link notifications, and Linked Data Notifications inbox
delivery. See [ActivityPub](https://www.w3.org/TR/activitypub/),
[WebSub](https://www.w3.org/TR/websub/),
[Micropub](https://www.w3.org/TR/micropub/),
[Webmention](https://www.w3.org/TR/webmention/) and
[LDN](https://www.w3.org/TR/ldn/).

**XML foundations and assembly.** XML 1.0/1.1, their Namespaces specifications,
XML Infoset, XML Base and `xml:id` form the foundation. Add XInclude, XLink,
XPointer Framework and its `element()` and `xmlns()` schemes, stylesheet
association, and XML Entity Definitions for Characters. DTD processing belongs
to XML itself. See [XML](https://www.w3.org/TR/xml/),
[XInclude](https://www.w3.org/TR/xinclude/),
[XLink](https://www.w3.org/TR/xlink11/) and
[XPointer](https://www.w3.org/TR/xptr-framework/).

**Schemas and datatypes.** XSD 1.0 and 1.1 separate Structures from Datatypes:
document validation versus lexical/value spaces, facets, regex, numbers, dates,
durations and binary values. Service Modeling Language and its interchange
format add validation over XML and inter-document references. See
[XSD Structures](https://www.w3.org/TR/xmlschema11-1/),
[XSD Datatypes](https://www.w3.org/TR/xmlschema11-2/) and
[SML](https://www.w3.org/TR/sml/).

**Query, transformation and pipelines.** Include XPath 1.0/2.0/3.0/3.1,
XQuery 1.0/3.0/3.1 and XSLT 1.0/2.0/3.0. Companion specifications cover the
shared data model, Functions and Operators, serialization, XQueryX, older formal
semantics, Full Text and XQuery Update Facility 1.0. XProc 1.0 defines pipelines;
GRDDL extracts RDF using transformations. The repository's XPath 1.0 evaluator
is a substantially smaller target than XPath 3.1. See
[Functions and Operators](https://www.w3.org/TR/xpath-functions-31/),
[XQuery](https://www.w3.org/TR/xquery-31/),
[XSLT](https://www.w3.org/TR/xslt-30/),
[XProc](https://www.w3.org/TR/xproc/) and
[GRDDL](https://www.w3.org/TR/grddl/).

**XML compression and security.** EXI includes the binary XML format, a profile
limiting dynamic memory and Canonical EXI. XML security includes Canonical XML
1.0/1.1, Exclusive Canonicalization, XML Signature 1.1, Signature Properties,
XPath Filter 2.0, XML Encryption 1.1, Decryption Transform and XKMS with bindings.
These are distinct from credential cryptosuites. See
[EXI](https://www.w3.org/TR/exi/),
[XML Signature](https://www.w3.org/TR/xmldsig-core1/),
[XML Encryption](https://www.w3.org/TR/xmlenc-core1/) and
[XKMS](https://www.w3.org/TR/xkms2/).

**Enterprise messaging.** SOAP 1.2 includes the messaging framework and adjuncts,
MTOM, XML-binary Optimized Packaging, Resource Representation header and
SOAP-over-JMS. WSDL 2.0 describes services. The WS family adds Addressing, Policy
and Attachment, Metadata Exchange, Transfer, Enumeration, Eventing, Event
Descriptions, Fragment and SOAP Assertions. SAWSDL links descriptions to semantic
annotations. See [SOAP](https://www.w3.org/TR/soap12-part1/),
[WSDL](https://www.w3.org/TR/wsdl20/),
[WS-Policy](https://www.w3.org/TR/ws-policy/) and
[SAWSDL](https://www.w3.org/TR/sawsdl/).

**IoT and devices.** Web of Things includes Architecture 1.1, Thing Description
1.1 and Discovery, with 1.0 documents relevant to compatibility. These cover
capabilities, interactions, security metadata and discovery. Older device
Recommendations include CC/PP capability/preference profiles and the Device
Description Repository API. See
[Thing Description](https://www.w3.org/TR/wot-thing-description11/),
[Discovery](https://www.w3.org/TR/wot-discovery/),
[CC/PP](https://www.w3.org/TR/CCPP-struct-vocab/) and
[Device Description Repository](https://www.w3.org/TR/DDR-Simple-API/).

**Publishing, graphics and mathematics.** EPUB 3.3, Reading Systems and
Accessibility form the ebook family; Publication Manifest and Audiobooks cover
publication metadata and audio publications. Formats include PNG, SVG 1.1 and
mobile/Tiny profiles, MathML 3, WOFF 1/2 and WebCGM 2.1. XSL 1.1 supplies paginated
formatting through XSL-FO. These have non-browser encoders, validators, converters,
typesetters and readers. See [EPUB](https://www.w3.org/TR/epub-33/),
[Audiobooks](https://www.w3.org/TR/audiobooks/),
[PNG](https://www.w3.org/TR/png-3/),
[MathML](https://www.w3.org/TR/MathML3/) and
[XSL formatting](https://www.w3.org/TR/xsl11/).

**Timed media, speech and multimodal interaction.** TTML1/2, IMSC caption/subtitle
profiles and the IMSC render model cover timed text. SMIL covers synchronization
and animation; Media Fragments identifies portions of media. Speech includes
SSML, recognition grammars, semantic interpretation and pronunciation lexicons,
plus VoiceXML and CCXML call control. InkML, EmotionML, EMMA and Multimodal
Architecture cover handwriting, emotion and interaction data. See
[TTML](https://www.w3.org/TR/ttml2/),
[SMIL](https://www.w3.org/TR/SMIL3/),
[SSML](https://www.w3.org/TR/speech-synthesis11/),
[VoiceXML](https://www.w3.org/TR/voicexml21/) and
[EMMA](https://www.w3.org/TR/emma/).

**Forms and state machines.** XForms 1.1 combines XML instance data, XPath,
bindings, constraints and submission. SCXML defines executable hierarchical
state machines. XML Events provides declarative event handling. See
[XForms](https://www.w3.org/TR/xforms11/),
[SCXML](https://www.w3.org/TR/scxml/) and
[XML Events](https://www.w3.org/TR/xml-events/).

**Internationalization, accessibility and quality.** Character Model Fundamentals
and ITS 1.0/2.0 address text interoperability and localization metadata. WCAG
2.0/2.1/2.2, ATAG 1.0/2.0 and ACT Rules Format cover content, authoring tools and
accessibility testing. Architecture of the Web, Data on the Web Best Practices
and QA Specification Guidelines are Recommendations providing architecture or
conformance guidance rather than executable-language definitions. See
[ITS](https://www.w3.org/TR/its20/),
[WCAG](https://www.w3.org/TR/WCAG22/),
[ATAG](https://www.w3.org/TR/ATAG20/),
[ACT](https://www.w3.org/TR/act-rules-format-1.1/) and
[Data best practices](https://www.w3.org/TR/dwbp/).

**Infrastructure and portable execution.** Trace Context defines distributed
tracing headers. WebAssembly Core 1.0 is a Recommendation useful to standalone
runtimes independently of browser integration. Browser-facing standards with
server obligations, especially WebAuthn and CSP, belong in a boundary category
if the scope expands. See [Trace Context](https://www.w3.org/TR/trace-context-1/)
and the [WebAssembly Recommendation](https://www.w3.org/TR/2019/REC-wasm-core-1-20191205/).

## External standards and status boundaries

RML and ShEx are community specifications; JSON Schema is developed by the JSON
Schema project; Schematron and Common Logic are ISO standards. None should be
counted as a W3C Recommendation. IETF URI/IRI, HTTP, language-tag, JSON and date
standards, ECMA-262 regex and Unicode specifications must be explicit external
nodes. Community Group reports, Working Group Notes and newer drafts do not
inherit Recommendation status from a related family.

## Specification dependencies

This is a selected semantic map of the families closest to the implementation,
not a complete graph of normative references. `A --> B` means A uses or builds
on B; the relationship can depend on the version, profile or feature.

```text
W3C graph stack
  Turtle / TriG / N-Triples / N-Quads --> RDF
  RDF/XML ----------------------------> RDF + XML + Namespaces
  JSON-LD ----------------------------> RDF + JSON + IRI resolution
  RDF / RDFS -------------------------> datatype interpretations --> XSD
  OWL --------------------------------> RDF/RDFS + XSD
  SPARQL -----------------------------> RDF + XSD
      +-------------------------------> XPath Functions & Operators
      |                                     |
      |                                     +--> XSD-derived regex
      +-------------------------------> IETF HTTP / URI / language tags
  SHACL ------------------------------> RDF + XSD + SPARQL / regex

W3C XML stack
  XPath ------------------------------> XML + Namespaces
  XSLT -------------------------------> XPath + XML
  XForms -----------------------------> XPath + XML + datatype constraints
  GRDDL ------------------------------> XML/XHTML + transformations --> RDF
  MathML -----------------------------> XML

Tabular / mapping / validation
  CSVW -------------------------------> XSD + JSON + RDF
      +-------------------------------> Unicode UAX35 date patterns
      +-------------------------------> ECMA-262 duration / other regex formats
      +-------------------------------> IETF URI Templates
  RML [community] --------------------> RDF + source formats / selectors
  ShEx [community] -------------------> RDF + XSD lexical spaces
  Schematron [ISO] ------------------> XML + query binding, commonly XPath
  JSON Schema [JSON Schema project] -> JSON + ECMA-262 regex
      +-------------------------------> IETF formats, e.g. RFC3339 dates

Credentials / logic
  VC + Data Integrity [W3C] ---------> JSON/JSON-LD + cryptographic suites
  Common Logic [ISO] ----------------> logical syntax / model theory
```

Important dialect boundaries are explicit in the specifications: SPARQL uses
XPath/XQuery regex, JSON Schema uses ECMA-262 regex, and CSVW uses both ECMA-262
regex formats and Unicode date patterns with XSD canonical representations. See
[SPARQL](https://www.w3.org/TR/sparql11-query/),
[JSON Schema regex](https://json-schema.org/understanding-json-schema/reference/regular_expressions)
and [CSVW](https://www.w3.org/TR/tabular-data-model/).

## Lean dependencies

Selected existing imports and call paths, relative to
`formal/lean4/L4Factoidal/`. Upward arrows point from consumers to dependencies.
No arrow establishes full conformance or a proof of equivalence to a standard.

```text
Regex.Syntax
    ^
    +-- Regex.Derivative / Exec
    +-- Regex.XSDPattern
              ^
              +-- Regex.XPath
                      ^
                      +-- SPARQL.Expr
                      +-- SHACL.Validation
                      +-- CSVW.Formats <-------- ShEx.XsdLexical
                      +-- JSONSchema.Validate   [dialect mismatch risk]

XSD.Datatypes ----------------------> RDF + XML
XSD.SimpleType / Facets ------------> XSD machinery + Regex
OWL -------------------------------> XSD

Separate datatype/date paths:
  RDF.Datatypes       [restricted datatype/value model]
  SHACL.Validation    [lexical checks + millisecond date parser]
  SPARQL.Expr         [positional date component extraction]
  CSVW.Formats        [lexical checks + formatted date parsing]
       ^
       +-- ShEx.XsdLexical

XML.Document / Parser / Namespaces
       ^
       +-- XPath.Data / Expr / Eval
       |       ^
       |       +-- XSLT
       |       +-- XForms
       +-- MathML
       +-- Syntax.RdfXml
       +-- Schematron.FromXml

JSON.Value <-------- JSONLD / JSONSchema / CSVW / RML / VC
Syntax.IriResolve <- JSONLD / JSONSchema / SPARQL / other consumers
Crypto <------------ RDF canonicalization / SPARQL / Storage / VC
```

Collapsing imports to directory names produces apparent cycles such as
`RDF <-> SPARQL`, `RDF <-> Storage` and `RDFS <-> OWL`. These are grouping cycles,
not evidence of cyclic Lean module imports. Foundational and integration modules
share broad directory labels; any architectural reorganization should inspect
the individual module graph first.

## Duplication and interoperability opportunities

Dates and datatype handling are duplicated. Regex already has substantial reuse,
but its dialect boundaries need attention.

| Area | Source evidence | Opportunity |
| --- | --- | --- |
| Dates | XSD has structured parsing and ordering; SHACL has a millisecond parser; SPARQL extracts fixed-position components | Share parsed values, calendar arithmetic and ordering |
| Datatypes | RDF, XSD, SHACL and CSVW contain overlapping lexical/value machinery | Shared datatype service with explicit consumer policies |
| ShEx | Imports CSVW format machinery for XSD checks | Remove accidental ShEx-to-CSVW coupling |
| Regex | SPARQL, SHACL, CSVW and JSON Schema share Regex.XPath | Share execution with explicit dialect frontends |
| Language ranges | Separate SPARQL, SHACL validation and SHACL node-expression helpers | Share RFC4647 basic filtering |
| URI encoding | Separate expression, protocol and template implementations | Share UTF-8 encoding with policy-specific allowed sets |
| CSV | CSVW and SPARQL result handling have separate paths | Consider common quoting/scanning primitives |

### Dates and datatype models

[XSD/Datatypes.lean](../formal/lean4/L4Factoidal/XSD/Datatypes.lean) provides
structured date/time parsing, arbitrary-precision decimal components and partial
ordering. [SHACL/Validation.lean](../formal/lean4/L4Factoidal/SHACL/Validation.lean)
instead parses timestamps to milliseconds, truncates finer fractional seconds
and treats mixed timezone presence as incomparable. XSD tests already exercise
a mixed-timezone comparison that is determinable. This is a candidate for a
cross-consumer regression test, not yet a reproduced conformance failure.

[SPARQL/Expr.lean](../formal/lean4/L4Factoidal/SPARQL/Expr.lean) extracts date
components at fixed positions. Negative and extended years need targeted checks
before replacing that path with parsed components.

[CSVW/Formats.lean](../formal/lean4/L4Factoidal/CSVW/Formats.lean) owns additional
lexical checks and date-format parsing. Its UAX35 input adapter is useful distinct
functionality, but its resulting XSD lexical/value checks could be shared.
[ShEx/XsdLexical.lean](../formal/lean4/L4Factoidal/ShEx/XsdLexical.lean) explicitly
documents that its dependency on CSVW should eventually move to a common home.

[RDF/Datatypes.lean](../formal/lean4/L4Factoidal/RDF/Datatypes.lean) has a separate,
restricted value model. Consolidation must preserve RDF datatype recognition,
lexical spelling, whitespace policy and treatment of unknown datatypes rather
than assuming every consumer applies the same validation contract.

### Regex dialects

[Regex/XSDPattern.lean](../formal/lean4/L4Factoidal/Regex/XSDPattern.lean)
documents a supported fragment: Unicode category escapes and backreferences are
unsupported, and `\w` uses an ECMAScript-style ASCII definition. This is evidence
of an explicit implementation boundary, not equivalent support for all XSD,
XPath and ECMA-262 expressions.

[JSONSchema/Validate.lean](../formal/lean4/L4Factoidal/JSONSchema/Validate.lean)
uses the XPath regex entry point for patterns. The shared engine saves work, but
ECMA-262 requires a separate semantic adapter and an explicit supported-feature
policy. Unsupported syntax should be distinguishable from a valid expression
that fails to match.

JSON Schema `format` needs vocabulary-aware handling: annotation-only behavior
can be correct. Blanket date validation would introduce a different interop bug.
See [JSON Schema validation](https://json-schema.org/draft/2020-12/json-schema-validation).

### Proposed shared architecture

```text
SPEC-SPECIFIC ADAPTERS                      SHARED IMPLEMENTATION

XSD lexical rules --------------------+
RDF datatype recognition policy ------+
SHACL validation/error policy --------+--> Datatype values / exact decimals
ShEx datatype constraints ------------+    Calendar / timezone / partial order
SPARQL casts + accessors --------------+
CSVW UAX35 input formatting -----------+

XSD regex frontend -------------------+
XPath regex frontend + flags ---------+--> Regex AST / derivatives / execution
ECMA-262 supported frontend -----------+
                                           ^
                            explicit unsupported-feature result

SPARQL / SHACL / CSVW / JSONLD --------> URI, Unicode, language-tag primitives
```

Prioritize dates and datatype consolidation, then regex dialect separation.
Keep specification-specific adapters and errors explicit. Share primitives
where semantics coincide; do not merge consumers merely because their functions
have similar names.

## Next steps for a complete map

1. Build a per-document register with exact edition, dated URL, W3C status,
   family, implementation roles and external standards references.
2. Separate normative dependencies from informative references and architectural
   relationships; make profile/version conditions explicit.
3. Generate the exact Lean module import graph and annotate the relevant
   specification sections, implemented fragments and proof boundaries.
4. Add cross-consumer tests for fractional seconds, timezone comparisons,
   negative/extended years, numeric lexical spaces, regex dialects, language
   ranges and UTF-8 URI encoding.
5. Assess the additional families above against existing implementation coverage
   before assigning new work or claiming that a whole family is implemented.

## Implementation update: XML namespace correctness, 21 October 2026

Normative references identify semantic contracts, not mandatory one-to-one Lean
imports. SPARQL borrows scalar Functions and Operators semantics without needing
an XML document traversal engine. A namespace-sensitive XML reader, however,
must distinguish namespace names, not merely strip a prefix. XML Infoset can be
represented by a data model and invariants; XML Namespaces also requires scope,
name-resolution and validation operations.

The initial audit found those operations in `XML.Namespaces`, while several
readers bypassed them. The implementation now uses this boundary:

```text
XML.Document + XML.Parser + XML.Wellformedness (NCName)
                         |
                   XML.Namespaces
          declarations / scopes / expanded names
                         |
                 XML.NamespaceView
            checked, resolved namespace tree
                         |
          per-vocabulary internal projection
                         |
          +--------------+----------------+
          |              |                |
     SPARQL SRX       MathML         Schematron

XML.NamespaceView.scopeAtPath + XML.Namespaces name resolution
                         |
                 XPath document adapter
                         |
                      XSLT

RDF/XML ----------------> XML.Namespaces (existing direct use retained)
```

The shared view leaves the plain XML parser unchanged. It resolves declarations
before the element's own name and attributes. Vocabulary projections retain
foreign names as distinct internal names and preserve their text and descendants;
they are reader adapters, not XML suitable for serialization. Bare attributes
remain in no namespace, XML attributes retain their fixed namespace identity,
and foreign qualified attributes cannot impersonate bare vocabulary attributes.

| Contract | Lean owner / consumers | Evidence and limits |
| --- | --- | --- |
| Namespaces in XML §§3, 6: QNames, declarations, expanded names, attribute uniqueness | `XML.Namespaces`, `XML.Wellformedness`, `XML.NamespaceView` | NCName validation reused; tests cover shadowing, undeclaration, duplicate expanded attributes, reserved bindings, PI targets and internal general-entity names |
| SPARQL XML Results §2 vocabulary identity | `SPARQL.ResultsXml` through `XML.NamespaceView` | Accepts arbitrary correctly bound prefixes and default namespace; rejects foreign/no-namespace elements and unbound prefixes, including nested rebinding |
| MathML 3 chapter 4 vocabulary | `MathML.FromXml` through the shared view | Matching requires MathML namespace; qualified foreign attributes cannot become bare attributes; Content MathML subset unchanged |
| ISO Schematron §5.4 vocabulary | `Schematron.FromXml` through the shared view | Foreign root rejected; foreign child constructs are not interpreted as Schematron; unsupported schema constructs remain outside the reader's subset |
| XPath 1.0 §5.4 namespace nodes and §2.3 name tests | `XPath.Data.namespaceScope`, `XPath.Eval.expandedName` | Uses shared declaration/resolution rules, retains XPath node identity and expression-name semantics; unprefixed expression names still have no default namespace |
| XSLT source/stylesheet namespace precondition | `XSLT.Transform` | Checks namespace well-formedness of main source and stylesheet before processing; imported trees and external documents remain caller-supplied inputs |

XPath's `Doc` does not carry an XML declaration. Its scope adapter allows the
1.1 undeclaration operation; callers must validate the actual document version
before evaluation. XSLT now does so for its main documents. Direct callers that
construct raw XPath contexts remain responsible for this precondition.

### Validation and remaining gaps

The SRX negative tests were run against the original code first and failed for
wrong namespace URIs, missing declarations and nested namespace changes. They
pass with the shared reader. New namespace tests are imported by the existing
XML, SPARQL results and MathML test modules, so normal library builds include
them. Existing Schematron and XPath test modules also include regression cases.

The project-authored scalar MathML corpus previously omitted the namespace in
55 of 56 documents. Those fixtures now declare the MathML default namespace;
expected values and case count are unchanged. This is a fixture correction,
not a change to third-party W3C test expectations. Unqualified MathML and
Schematron document roots are no longer accepted as their respective vocabularies.

Validation: the complete `lake build` passed (853 jobs), including the
namespace regressions and existing RDF/XML tests. `git diff --check` passed.
The final native MathML, Schematron and XSLT runner results were:

- Scalar MathML: **56 pass, 0 fail, 0 unread**. This is the project-authored,
  Recommendation-cited evaluation corpus, not a W3C conformance suite.
- Schematron: **8 pass, 0 fail, 0 undecided** in the existing local manifest.
- Vendored XSLT subset: **84 pass, 3 fail, 1 refused out of 88**. An isolated
  baseline build using the original `XPath.Data`, `XPath.Eval` and
  `XSLT.Transform` produced the same failures and output. The existing failures
  are `copy/copy-3102`, `namespace/namespace-4801` and `node/node-1601`; the
  refusal is `select/select-5901` (missing external document). Two failures are
  lexical namespace/attribute ordering differences; `namespace-4801` exposes
  substantive namespace copying/fixup gaps. None is counted as a pass.

A one-off manifest-driven check of the vendored eduni namespace 1.0, 1.1 and
first-edition errata suites scored **52 pass, 2 fail out of 54** required-verdict
UTF-8 cases. Three optional-error cases and two non-UTF8 cases were excluded.
The remaining failures are `1.0/012.xml` and `1.0/044.xml`, described below.
This check used the actual manifest expectations and files, not synthesized
stand-ins. The script was temporary; the retained regression modules cover the
shared adapter and consumer behavior rather than providing a new suite runner.

The namespace validation substrate still has DTD-related limits. The parser does
not retain notation declarations or all attribute-type information, so notation
NCName checking and DTD-driven normalization of namespace declarations are not
provided by this view. This work does not claim full Namespaces conformance.

The new shared traversal and projection are total Lean definitions; no new
`partial`, user `axiom`, `sorry`, native proof oracle or host implementation was
introduced. Tests and compiler checks do not constitute a general equivalence
proof between the new adapters and the normative specifications.

Follow-up work remains: namespace copying/fixup in XSLT, the DTD substrate gaps,
namespace validation for externally supplied XPath/XSLT trees, and the separate
datatype/date and regex-dialect work identified above. SPARQL scalar semantics
must track the actual referenced F&O version and SPARQL's adaptations, not
automatically adopt the latest XPath evaluator.

## Shared semantics OKRs: implementation follow-through (2026-10-21)

This section supersedes the remaining-work snapshot immediately above. The
objective is to share executable semantics while keeping specification editions,
consumer error policies and assurance boundaries visible. A normative reference
is evidence for a semantic dependency; it is not by itself a requirement for a
separate Lean package or an import of an entire evaluator.

### O1 — namespace correctness

The two outstanding namespace cases are fixed. XML's parser retains notation
names and each attribute's first declared type. It applies the final non-CDATA
space-collapse step after entity expansion, before namespace resolution. This is
[XML 1.0 Fifth Edition §3.3.3](https://www.w3.org/TR/2008/REC-xml-20081126/#AVNormalize),
not a namespace-specific whitespace workaround. Character-reference tabs remain
tabs; only spaces are collapsed at that step. Notation names are checked by the
namespace layer under [Namespaces 1.0 Third Edition §7](https://www.w3.org/TR/2009/REC-xml-names-20091208/#Conformance).
Plain XML still permits colons in notation names.

The retained runner is `formal/lean4/Harness/NamespaceRun.lean`, built as
`l4xml-namespaces`. From the repository root:

```sh
formal/lean4/.lake/build/bin/l4xml-namespaces
```

It reads the three vendored eduni manifests on every run and reports missing
files, malformed manifests and unexpected verdict types as errors. Its measured
result is **54 pass, 0 fail, 3 optional, 2 non-UTF8, 0 errors**. Optional/error
cases and encoding exclusions are named; neither contributes a pass. This is
namespace-suite coverage, not a claim to implement every XML 1.1 production or
the full DTD validation/defaulting machinery.

XSLT now checks raw external documents and imported stylesheet trees as
Namespaces 1.0 before processing. XPath's public `eval`/`evalText` entry points
also check supplied document collections. Raw trees have no XML declaration;
callers needing 1.1 must validate a `Document` with its actual version before
using the lower-level evaluator. XSLT's main documents retain their actual
version checks.

Copying now retains the owning document on external XPath node addresses, so a
stylesheet node selected with `document('')` resolves its namespaces against the
stylesheet. Literal result elements retain namespace bindings needed by their
names even when the prefix is excluded, and unqualified copied elements emit a
default-namespace reset when necessary. These implement the relevant
[XSLT 1.0 §§7.1.1 and 7.5](https://www.w3.org/TR/1999/REC-xslt-19991116#copying)
contracts. Regression tests cover variables, parent steps, copy-of and shallow
copy across this boundary.

This provenance fix carries document values, not URI identities. Equal-content
documents at distinct URIs and cross-document `generate-id()` remain limitations
of the XPath model. It does not claim full XDM document identity or a general
namespace-fixup algorithm for every dynamically constructed attribute conflict.

### O2 — shared datatype and date values

The new adapter is `XSD/Lexical.lean`, above the existing total
`XSD/Datatypes.lean` and `XSD/IEEE754.lean`. It requires an explicit XSD edition.
The calendar uses astronomical years internally; the XSD 1.0 adapter rejects
lexical year zero and translates BCE years to/from that calendar. This matters
for leap years and midnight rollover as well as the spelling of YEAR results.
The edition difference is specified in
[XSD 1.0 Second Edition §3.2.7](https://www.w3.org/TR/2004/REC-xmlschema-2-20041028/#dateTime)
and [XSD 1.1 §3.3.7](https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#dateTime).

```text
XSD.IEEE754                 XML.Document
      |                         |
      +------> XSD.Datatypes <--+
               Dec / DTValue / lexical maps / partial order
                         |
                    XSD.Lexical
             explicit XSD 1.0 / 1.1 adapters
                         |
         +---------------+----------------+----------------+
         |               |                |                |
     SPARQL.Expr    SHACL.Validation   CSVW.Formats    ShEx.XsdLexical
     components     exact date order  formatted cells  lexical checks
         |               |                |                |
     SPARQL errors  mixed-zone policy  CSVW outcomes   unknown = none
                         |
              RDF.Datatypes: shared numeric parsing
              XSD.Facets: exact millisecond projection
```

The arrows from `XSD.Lexical` denote reuse, not import of a consumer's policy.
`ShEx.Validation` also uses its exact decimal/exponent helper; there is now **no
ShEx → CSVW import or qualified call**.

| Consumer | Shared operation / edition | Consumer-specific boundary |
| --- | --- | --- |
| SPARQL 1.1 §17.4.5 | `parseDateTimeFor .xsd10` for all dateTime components | Return types remain SPARQL results; absent TIMEZONE is an error, TZ preserves its validated lexical spelling; NOW remains supplied by the caller |
| SHACL 2017 §§4.1.2, 4.3 | Shared numeric lexical maps and exact dateTime comparison via the SPARQL/XSD 1.0 profile | Mixed timezone presence remains undecided; no implicit timezone is invented |
| CSVW 2015 value parsing / metadata facets | XSD 1.1 numeric/date lexical checks; shared date partial order for bounds | CSVW format patterns, grouping, percent scaling and lexical output remain CSVW operations; arbitrary fractional length is accepted without enumerating nine patterns |
| ShEx 2.0 §5.4.3 | Edition-aware lexical checks; shared exact decimal/exponent comparison | XSD 1.0 `+INF` rejection retained; unknown datatype remains `none`; QName context and the existing permissive string-family handling remain gaps |
| RDF datatype entailment | Shared integer/decimal lexical parsing | Existing recognized datatype set and RDF literal term identity remain unchanged; this does not add dateTime D-entailment |
| OWL datatype interval adapter (`XSD.Facets`) | Shared XSD 1.1 dateTime parser and timeline | Solver still uses integer milliseconds: missing timezones and sub-millisecond instants return no exact key, rather than truncating distinct values together |

The regression module `XSD/InteropTests.lean` is imported by the library root.
It checks negative/extended years, exact long fractions, invalid calendar dates,
invalid timezone offsets, timezone equivalence and uncertainty, year-zero and
`+INF` edition differences, dateTimeStamp's timezone requirement and CSVW bounds.
It also records the definitional theorem that RDF's integer adapter delegates to
the shared parser. That theorem proves delegation, not normative completeness.

Numeric expression arithmetic still has consumer-specific representations
(SPARQL scaled numerics, RDF values, OWL interval domains). This work removes
repeated parsing and date semantics; it does not equate those different domains
or claim that every numeric helper in the repository has been consolidated.

### O3 — specification-to-code contracts and regex profiles

`Regex/Profiles.lean` exposes explicit XSD 1.0, XPath 2.0 and ECMA-262 2020
profiles over the existing derivative engine. It returns a match result or an
explicit invalid/unsupported error. Its limited grammar is documented in code.
This prevents the engine's historical mixture of XSD whitespace and ECMA word
characters from silently defining every consumer's regex language.

| Contract | Owner / current consumers | Evidence / assurance boundary |
| --- | --- | --- |
| XML 2008 §3.3.3 normalization | `XML.Parser` → namespace and XML consumers | DTD regression guards and eduni manifest runner; defaults/DTD validity are not implemented by this change |
| Namespaces 2009 §§4, 6, 7 | `XML.Namespaces`, `XML.NamespaceView` → SRX, MathML, Schematron, RDF/XML, XPath/XSLT | Shared checks plus consumer regressions; full XML 1.1 is not established |
| XSD 2004 §3.2.7 and XSD 2012 §3.3.7 | `XSD.Datatypes` + `XSD.Lexical` → date consumers above | Exact values and explicit editions; authored cross-consumer tests, no general parser-correctness theorem |
| XSD 2004 Appendix F regex membership | `Regex.Profiles.compileXsd10` → `XSD.SimpleType` | Whole-string membership; literal `^`/`$`; unsupported Unicode categories/word classes are reported by the existing unreadable-pattern mechanism |
| F&O 2.0, 2010 §7.6.2 matching; SPARQL 2013 §17.4.3.14 | `Regex.Profiles.matchSparql` → SPARQL REGEX | Substring matching, normative i/s/m/x flags; existing q quote mode is retained explicitly as a XPath 3.0 extension; category-sensitive non-ASCII cases and non-ASCII case folding are refused |
| JSON Schema 2020-12 validation §6.3.3 / ECMA-262 11th edition §21.2 | `Regex.Profiles.matchWith .ecma2020` → JSON Schema pattern, patternProperties, additionalProperties | Conservative flag-free BMP subset; unsupported lookaround, escapes or Unicode behavior produces `unsupported`, including property applicability |

The normative regex references are
[XSD 1.0 Appendix F](https://www.w3.org/TR/2004/REC-xmlschema-2-20041028/#regexs),
[F&O 2.0 Second Edition §7.6](https://www.w3.org/TR/2010/REC-xpath-functions-20101214/#string.match),
[JSON Schema 2020-12 validation §6.3.3](https://json-schema.org/draft/2020-12/json-schema-validation#name-pattern),
and [ECMA-262 11th edition §21.2](https://262.ecma-international.org/11.0/#sec-regexp-regular-expression-objects).
The ECMA adapter is a declared implementation subset, not a claim that JSON
Schema mandates that particular ECMA edition.

`Regex/ProfileTests.lean` tests the different matching/anchor meanings and error
propagation. Remaining regex migrations include SPARQL REPLACE's capture and
replacement semantics, SHACL/ShEx boolean pattern APIs, and CSVW string formats.
Those still use the historical engine directly; the new profile is not a blanket
conformance certificate for them. General Unicode category tables, full ECMA
lookaround/backreferences, and full XSD character-class subtraction remain open.

New shared definitions introduce no `partial`, user axiom, `sorry`, native proof
oracle or FFI. Existing XPath/XSLT evaluator definitions remain partial. Axiom
prints for the new shared adapters and delegation theorem report only Lean's
standard foundations (`propext`, `Classical.choice`, `Quot.sound`). The test
results below distinguish suite execution from these proof boundaries.

The current vendored SPARQL regex corpus includes `q` and `iq` cases. The
SPARQL adapter retains those existing extensions using
[F&O 3.0 §5.6.1.1](https://www.w3.org/TR/2014/REC-xpath-functions-30-20140408/#flags),
while the strict XPath 2.0 profile rejects `q`. This is precisely why editions
and consumer adaptations belong on dependency edges, not just module names.

### Verification record

All counts below were measured during this follow-through; an unavailable suite
was not counted as passing. CSVW, ShEx and SHACL were initially absent in this
checkout, then fetched as archives of the exact gitlink commits into
`/tmp/factoidal-okr-fixtures`, without changing submodule pins:

- CSVW: `2bc84f937be11d313766ae0892c08c923a5a3799`.
- ShEx: `0f45c5113acdea42459071b47be34027c13e7102`.
- SHACL: `08adb3776709a014bc3062ede793c36275b22446`.

| Check | Measured result |
| --- | --- |
| Full Lean build, including imported regression modules | 864 jobs; final build log `/tmp/factoidal-okr-build-final.log` |
| Namespaces eduni manifests | 54/54 scored pass; 3 optional, 2 non-UTF8, 0 errors |
| CSVW RDF / JSON manifests | 270/270 each, no failures/skips; RDF compared by graph isomorphism |
| ShEx validation manifest | 1182/1182; no unread cases |
| SHACL Core, full report comparison | 98/98; no unsupported cases |
| JSON Schema vendored draft-07 manifest | 770/770; no undetermined cases in this corpus |
| SPARQL 1.1 functions | 75/75 |
| SPARQL regex corpus | 21/21, including q/iq extension cases |
| RDF 1.1 rdf-mt | 39/39 |
| SPARQL 1.0 expr-builtin | 17 pass, 7 fail / 24 |
| XSLT vendored subset, unchanged comparison policy | 84 pass, 3 fail, 1 refusal / 88 |
| Broader plain XML conformance profile | 1840 pass, 22 fail / 1862 scored; out-of-profile cases separately reported |

The seven `expr-builtin` failures concern STR lexical preservation, language-tag
case comparison and sameTerm. A controlled run compiling the original HEAD
`SPARQL/Expr.lean` in an isolated module tree, with the same surrounding modules,
produced **the identical seven failure lines**; both versions pass all 75
functions and 21 regex tests. This is a comparison of the changed SPARQL module,
not a claim to have rebuilt an entirely clean historical checkout.

The XSLT failures remain `copy-3102`, `namespace-4801` and `node-1601`. A separate
expanded-name tree/content comparison of each produced and expected document
now reports equality for all three. The suite's byte/whitespace comparator still
reports failure because namespace/attribute order differs; its expectations and
score have not been changed. The refusal remains the absent `select-59.xml`.
Full XML conformance and full SPARQL expression conformance are not claimed.

Logs are `/tmp/factoidal-okr-{csvw-rdf,csvw-json,shex,shacl,jsonschema}.log`,
`/tmp/factoidal-okr-sparql-{baseline,final}.log`,
`/tmp/factoidal-okr-xslt-final.log`, and `/tmp/factoidal-okr-xmlconf.log`.
Temporary logs/fixtures may be removed by the operating system; the commands,
pinned commits, retained harness and imported tests are the reproducibility
record. No conformance expectation was rewritten to make a failing test pass.

## Redundancy detection and reuse, second pass (2026-10-21)

`tools/lean-reuse-audit.py` makes the source audit repeatable. From the repository
root, run:

```sh
python3 tools/lean-reuse-audit-test.py
python3 tools/lean-reuse-audit.py --output /tmp/factoidal-reuse-audit.json
```

The JSON records cross-family helper-name candidates with source locations and
actual direct imports of selected shared modules. Nested comments and string /
character literals are masked; test and proof files are excluded. It is a
heuristic source inventory, not a Lean elaborator or semantic clone detector.
Identical names can denote intentional wrappers or unrelated operations;
differently named copies can escape detection. An import proves availability,
not a call or a normative dependency. `--all-names` includes generic names beyond
the default datatype, encoding, namespace and URI keywords. A missing source
tree raises an error rather than producing an empty success report.

### Reuse that removes a behavioural divergence

CSVW binary length facets now use XSD's decoded octets. The former arithmetic
on encoded text accepted odd-length hex and invalid base64 padding and could
miscount legal whitespace. `facetLength` now returns `Option Nat`; invalid binary
lexicals fail the facet boundary even with no explicit length constraint.
The CSVW `binary` alias follows `base64Binary`. ShEx now uses the same XSD hex
and base64 decisions: base64 changes from unmodelled (`none`) to a positive or
negative lexical decision. This follows the binary value spaces in
[XSD 1.1 Part 2 §§3.3.15–16](https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#base64Binary)
and byte lengths in
[CSVW data model §4.6.1](https://www.w3.org/TR/2015/REC-tabular-data-model-20151217/#length-constraints).
These changes have authored regressions for malformed padding, whitespace,
odd-length hex and the alias; failing cases were observed before the repair.

SHACL's supported-datatype policy remains explicit, but its separate integer
range table is gone. XSD owns all bounds and lexical decisions; RDF's `int`
bounds also delegate there. Cross-consumer guards check both endpoints and
neighbouring values for every integer subtype through SHACL, ShEx and CSVW.
Unknown datatype policies are retained. ShEx's fractionDigits uses XSD's exact
decimal model; its totalDigits zero convention remains a separately recorded
question, since the existing ShEx test expects zero digits for zero while XSD's
helper returns one. Unifying those without deciding the contract would hide a
behaviour change.

### Reuse below the standards-family boundary

`Encoding/Hex.lean` is a new import-free primitive, used by JSON, RDF syntax,
ShExC, HTTP query decoding, XSD and VC multibase. It recognises an ASCII hex digit
and returns its value or failure. It imposes no choice of Unicode escape width,
percent decoding, whitespace, padding, or output letter case. That placement
avoids making JSON or HTTP depend on the whole XSD implementation merely to
share hex arithmetic. The contracts come from
[RFC 3986 §2.1](https://www.rfc-editor.org/rfc/rfc3986#section-2.1),
[RFC 8259 §7](https://www.rfc-editor.org/rfc/rfc8259#section-7), and XSD's hex
lexical grammar. Local adapter names remain for consumers and existing proofs.

```text
JSON strings ----\
RDF syntax -------\
ShExC escapes -----+--> Encoding.Hex.digitValue (no imports)
HTTP query --------+
XSD hexBinary -----+
VC multibase ------/

SHACL datatype ----\
RDF xsd:int --------+--> XSD bounds / lexical mappings
ShEx binary -------+--> XSD binary decoders
CSVW byte lengths -/
```

Authored tests cover the complete 0–255 character range plus selected non-ASCII
characters against an independent alphabet table. Delegation theorems for JSON,
XSD and VC hold for every input by definitional equality; JSON and VC axiom
prints are empty. These establish shared implementation, not conformance of the
surrounding parsers. XSD's uppercase hex output and VC's lowercase output remain
different and tested.

### Review queue: what the detector does not settle

| Area | Evidence / next integration boundary | Contract to keep explicit |
| --- | --- | --- |
| Regex | SHACL, ShEx and CSVW still import `Regex.XPath` directly | Unsupported syntax needs a refusal channel; it must not silently become a non-match or a validation success. |
| Numeric facets | ShEx `totalDigitsOf`, XSD `Dec.totalDigits`; SPARQL/SHACL scaled values and XSD exact decimals | Zero convention, sub-unit leading zeros, IEEE rounding and RDF lexical identity need separate decisions and regressions. |
| QName datatypes and XForms binds | ShEx's `stringLikeBases` accepts QName/NOTATION broadly; XForms recognises literal `xs:`/`xsd:` spellings | Namespace binding context must reach datatype lookup. `NamespaceView` is useful infrastructure, but syntax recognition alone does not resolve a QName. |
| Hex and escaping | Regex's codepoint decoder, XML and SPARQL protocol still have local hex helpers | Share the digit primitive first; retain invalid-input policy, Unicode scalar checks, byte decoding and output case. |
| URI processing | Nine modules already import `Syntax.IriResolve` directly in this snapshot | Resolution, percent encoding, form decoding and IRI validation are different contracts. Matching helper names are not evidence that they can all be replaced by one function. |
| Vocabulary constants | The scan reports repeated RDF and XSD IRI definitions across families | Low-risk reuse opportunity, but less urgent than duplicated parsers that can disagree on accepted input. |

The intended integration test is observable agreement at the shared boundary,
plus explicit tests for deliberate differences. The number of helper names need
not shrink: a local public wrapper can remain while its implementation delegates
to one owner. Successful reuse therefore needs source inspection and delegation
proofs/tests as well as the name inventory.

XForms numeric MIP checks and SPARQL cast lexical checks now delegate to XSD as
well. XForms retains the XSD 1.0 spelling policy used by the existing module;
SPARQL casts retain their existing `+INF` extension, tested as a deliberate
adapter difference. The XForms mapping relates to
[XForms 1.1 datatype support](https://www.w3.org/TR/2009/REC-xforms-20091020/#model-datatypes).
The older RDF decimal normalizer and digit accumulator, now unused after shared
parsing, were removed. XSD's XML-whitespace predicate delegates to XML's, with a
regression showing that non-breaking space is not XML whitespace.

The repeatable scan at this point covers **372 runtime source modules** and
reports **55 cross-family helper-name groups**. The number includes vocabulary
constants, generic-name false positives and intentional delegation wrappers.
Selected direct-import counts are:

| Shared module | Direct importing modules | Families |
| --- | ---: | --- |
| `Encoding.Hex` | 6 | HTTP, JSON, ShEx, Syntax, VC, XSD |
| `XSD.Lexical` | 7 | CSVW, RDF, SHACL, SPARQL, ShEx, XForms, XSD |
| `Regex.Profiles` | 3 | JSONSchema, SPARQL, XSD |
| `XML.NamespaceView` | 4 | MathML, SPARQL, Schematron, XPath |
| `Syntax.IriResolve` | 9 | CSVW, JSONLD, JSONSchema, RML, SPARQL, ShEx, Syntax |

These counts exclude tests and transitive consumers. For example, SHACL now
imports `XSD.Lexical` directly instead of obtaining it incidentally through
SPARQL. Making that edge explicit helps the source graph reflect the intended
owner even when the compiler would allow an indirect import.

### A missing dependency became a measured cast bug

The native SPARQL cast corpus exposed `xsd:dateTime("string")` succeeding:
`evalXsdCast` fell through to constructing an arbitrary typed literal. The
manifest returned seven rows where only the valid date row was expected.
`castDateTime` now accepts the supported string/simple-literal and dateTime
source types only, then calls the same XSD 1.0 parser as the date accessors.
Invalid calendar dates, language-tagged input, numeric/IRI input and a leading
plus on a year produce errors; extended years and absent timezones remain
supported. Numeric cast sign handling no longer touches date lexicals.
This implements the supported dateTime edge of
[SPARQL 1.1 §17.5](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#FunctionMapping).
The fallback for other unimplemented constructor types remains a coverage gap.
The native failure and new authored guards were observed before the fix.

### VC fixture provenance for this run

The checkout lacks the five context files expected by `VC.Context`. Running the
native probe without them produced 44 passes and 17 failures, with explicit
missing-context warnings. For this validation, the contexts were fetched from
the IRIs listed in `VC.Context.vendoredContextFiles` into
`/tmp/factoidal-reuse-vc-fixtures/third_party/contexts`. A `CLAUDE.md` sentinel
made that directory the probe's fixture root, and its `tests` directory was a
symlink to this checkout's `tests`. The same executable then passed **58/58**:
22 RFC 8032 checks, 8 did:key checks, 8 Data Integrity round-trip checks, and
20 specification-vector checks. The probe follows different branches on
fixture-loading failure, so the failing run's total of 61 is not a fixed test
manifest denominator. This run does not provision contexts in a fresh checkout.

The files were fetched on 2026-10-21. Their SHA-256 hashes (pin these bodies when
reproducing the run, rather than assuming the live URLs remain unchanged) are:

| File | SHA-256 |
| --- | --- |
| `credentials-v2.jsonld` | `59955ced6697d61e03f2b2556febe5308ab16842846f5b586d7f1f7adec92734` |
| `credentials-examples-v2.jsonld` | `57393fbc69d6efb9b9b5dc9cb6b9880b0944360abfe2eaf459c9e58cf2279d7c` |
| `security-data-integrity-v2.jsonld` | `67f21e6e33a6c14e5ccfd2fc7865f7474fb71a04af7e94136cb399dfac8ae8f4` |
| `security-multikey-v1.jsonld` | `ba2c182de2d92f7e47184bcca8fcf0beaee6d3986c527bf664c195bbc7c58597` |
| `credentials-v1.jsonld` | `ab4ddd9a531758807a79a5b450510d61ae8d147eab966cc9a200c07095b0cdcc` |

Run the absolute path to `formal/lean4/.lake/build/bin/l4vc-probe` with that
temporary root as the working directory. It reads the contexts offline; fetching
is outside the pure Lean library. Logs are `/tmp/factoidal-reuse-vc.log` and
`/tmp/factoidal-reuse-vc-contexts.log`.

### Second-pass verification

The final untargeted `lake build` passed **867 jobs**, including the dateTime
cast repair and imported cross-consumer regressions. The three audit-scanner
regressions pass. `git diff --check` and new-file whitespace checks pass.

| Native suite | Measured result |
| --- | --- |
| CSVW RDF / JSON, same pinned manifests as above | 270/270 each |
| ShEx validation, same pinned manifest | 1182/1182; no unread cases |
| SHACL Core full reports, same pinned manifest | 98/98 |
| JSON Schema vendored draft-07 | 770/770 |
| SPARQL functions / regex / casts | 75/75, 21/21, **7/7**; casts improved from 6/7 |
| RDF 1.1 rdf-mt | 39/39 |
| VC probe with the recorded temporary contexts | 58/58 |

The final SPARQL/RDF command was:

```sh
formal/lean4/.lake/build/bin/l4w3c --quiet \
  third_party/testing/w3c/sparql/sparql11/functions/manifest.ttl \
  third_party/testing/w3c/sparql/sparql10/regex/manifest.ttl \
  third_party/testing/w3c/sparql/sparql10/cast/manifest.ttl \
  third_party/testing/w3c/rdf/rdf11/rdf-mt/manifest.ttl
```

It reports 142/142, with no skipped, unsupported or missing manifests. These are
finite corpus results, not complete conformance claims. The separate historical
SPARQL expr-builtin and broader XML/XSLT gaps recorded above remain open.
Logs: `/tmp/factoidal-reuse-build-cast.log`,
`/tmp/factoidal-reuse-{csvw-rdf,csvw-json,shex,shacl,jsonschema}.log`,
`/tmp/factoidal-reuse-sparql-final.log`, and the VC logs listed above.
The binary and cast red-test logs are `/tmp/factoidal-reuse-red.log` and
`/tmp/factoidal-reuse-cast-red.log`.


## RDF identity and operator reuse, third pass (2026-10-22)

This pass found an over-shared operation as well as duplicated code: SPARQL
variable lookup converted RDF literals to numeric/boolean values before the
consumer could choose its semantics. `STR`, `DATATYPE`, `sameTerm`, projection,
`IF` and `COALESCE` consequently lost lexical spelling or datatype information.
SHACL pre-binding copied the conversion logic to reproduce that behaviour.
Moving conversion to value-consuming operators removes this duplicate and fixes
the underlying identity loss.

The normative distinction is between [SPARQL sameTerm (§17.4.1.8)](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#func-sameTerm),
[operator mapping (§17.3)](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#OperatorMapping),
and [grouping/set functions (§18.5.1)](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#aggregateAlgebra).
Those references need different implementation contracts even where they share
RDF term and XSD value types. The checked-in SPARQL 1.2 `grouping/group01` fixture
provides a concrete regression: integer `001` and integer `1` must occupy separate
groups. These 1.2 corpus results do not assert Recommendation status for 1.2.

### Shared code and explicit policy boundaries

Arrows below mean implementation use; the SHACL-to-expression edge is indirect
through its existing evaluator integration, not a new direct import.

```text
SHACL pre-binding ----------> SPARQL expressions retain RDF terms
                                     |
                       +-------------+------------------+
                       |                                |
                 term consumers                   value consumers
                       |                                |
                EvalResult.toTerm?              promoteLiteral / toNumeric?
                       |                                |
              RDF.Term.sameTerm                  XSD lexical parsing
                       |                                |
              +--------+---------+             +--------+---------+
              |        |         |             |                  |
           sameTerm  GROUP BY  aggregate      numeric           ORDER BY
                       |       DISTINCT      operators         MIN / MAX
                 HashGrouping
              exact key encoder
```

[`RDF/TermIdentity.lean`](../formal/lean4/L4Factoidal/RDF/TermIdentity.lean)
now owns term identity without datatype conversion or XML canonicalization.
It preserves lexical spelling and datatype, folds language-tag case, retains
base direction, and recurses through triple terms. SPARQL `sameTerm`, grouping
and aggregate DISTINCT use this relation. Grouping separately treats two
failed/unbound keys as one group; expression `sameTerm` propagates an error.
Aggregate inputs remove errors before DISTINCT.

[`SPARQL/Expr.lean`](../formal/lean4/L4Factoidal/SPARQL/Expr.lean) now preserves
bound terms and converts at arithmetic, numeric comparison/function, substring
index and cast boundaries. Numeric EBV reads shared XSD lexical values instead
of comparing a few zero spellings. The parser preserves noncanonical integer
expression spellings such as `01`. `STR(true)` returns a string, and `STR` of a
blank node reports an error. SHACL substitution now emits literal expressions
without a parallel numeric/boolean conversion table.

The hash grouping encoder now observes `toTerm?` too. It encodes computed
numbers and their identical projected RDF terms uniformly, normalizes language
tag case, and includes direction. Triple-term keys retain the exact fallback.
The kernel-checked `atom_exact`, `key_exact`, `groupSolutionsFast_eq` and
`selectPostFast_eq` theorems still establish agreement for arbitrary inputs;
the optimization is not justified solely by examples. Existing policy guards
that pinned numeric fallback, case-sensitive tags and ignored direction were
updated alongside the semantics. New guards distinguish `001` from `1` for
both variable and expression grouping, and check computed/stored key agreement.

Two older expression guards also pinned known incorrect outcomes: typed `1`
versus `01` comparing unequal, and a numeric STRDT comparison returning no row.
They now expect the corrected results. No upstream corpus expectations were
changed. Refinement lemmas now state their actual premises: unpromoted literal
reflexivity and different-datatype type errors do not apply indiscriminately to
numeric values. EBV table agreement shares XSD parsing; it is not an independent
proof of that parser. No new `sorry`, axioms, `native_decide`, partial definitions
or FFI were introduced.

### Better detection, without equating names with semantics

`tools/lean-reuse-audit.py` now inventories selected equality/conversion
identifier mentions with file, line and spelling, in addition to cross-family
helper names and direct shared imports. Its shared-owner list includes
`RDF.TermIdentity`. This makes mixed use of `sameTerm`, `eqb`, `termEq`,
`literalPromote`, `toTerm?`, `sparqlOrder` and shared XSD parsers reviewable even
when the names differ. It masks comments and literals. These are textual
mentions, including declarations, not name-resolved calls or proven clones.
The scan reports **373 runtime modules and 55 cross-family name groups**;
more groups disappearing is not inherently better, since thin adapters are
legitimate reuse. Four scanner regressions pass.

### Verification and remaining work

Untargeted `lake build` passes **870 jobs**. The native results below use the
rebuilt executables and unchanged fixtures. The before/after comparison of
SPARQL 1.0 failure names finds eight fixed cases and no new failures.

| Corpus | Before this pass | After this pass |
| --- | --- | --- |
| SPARQL 1.0 expr-builtin, included in the next row | 17 pass / 7 fail | **24 pass / 0 fail** |
| SPARQL 1.0 manifest-evaluation | 207 pass / 75 fail | **215 pass / 67 fail** |
| SPARQL 1.1 manifest-all + SPARQL 1.2 manifest | 885 pass / 0 fail | **885 pass / 0 fail** |
| SHACL Core, full reports | 98 pass / 0 fail | **98 pass / 0 fail** |
| SHACL SPARQL, full reports | no baseline measured in this pass | **22 pass / 0 fail** |

The eight fixes are `str-1`, `str-2`, `lang-case-insensitive-eq`,
`lang-case-insensitive-ne`, `sameTerm-eq`, `sameTerm-not-eq`, `sameTerm-simple`
and `open-eq-07`. The 67 remaining SPARQL 1.0 failures include ten unsupported
expected-result `.rdf` files; the total is not solely evaluator failures.
No skipped, unsupported or missing-manifest cases were reported by these runs
(the unsupported result format is reported as a failure). These finite corpora
are not a complete conformance claim. This supersedes the earlier statement
that the seven expr-builtin failures remain open.

Reproduction, from the repository root after `cd formal/lean4 && lake build`:

```sh
formal/lean4/.lake/build/bin/l4w3c --quiet \
  third_party/testing/w3c/sparql/sparql11/manifest-all.ttl \
  third_party/testing/w3c/sparql/sparql12/manifest.ttl
formal/lean4/.lake/build/bin/l4w3c --quiet \
  third_party/testing/w3c/sparql/sparql10/manifest-evaluation.ttl
python3 tools/lean-reuse-audit-test.py
python3 tools/lean-reuse-audit.py --output /tmp/factoidal-identity-reuse-audit.json
```

Run `l4shacl` separately for each absolute manifest path: the Core and SPARQL
manifests are under the previously recorded pinned data-shapes checkout,
`/tmp/factoidal-okr-fixtures/data-shapes-08adb3776709a014bc3062ede793c36275b22446/data-shapes-test-suite/tests/{core,sparql}/manifest.ttl`.
The executable uses one manifest argument. Logs are
`/tmp/factoidal-identity-build-final.log`,
`/tmp/factoidal-identity-{wide,sparql10,shacl}-final.log` and
`/tmp/factoidal-identity-shacl-sparql.log`. Baseline logs use `before` in place
of `final` for the two SPARQL manifests; the focused baseline is
`/tmp/factoidal-identity-before.log`.

The next reuse objectives have concrete acceptance criteria:

1. **Audit equality contracts across validators and storage.** SHACL
   `termMem`/`dedupTerms`, ShEx neighbourhood matching, SPARQL joins and SELECT
   DISTINCT still use historical `Term.eqb`, which canonicalizes XMLLiteral.
   `Literal.termEq` is a third relation with case-sensitive tag comparison.
   Classify each caller against its normative contract, then migrate consumers
   with distinguishing XMLLiteral/language/direction regressions and matching
   index/hash correctness proofs. Do not replace `eqb` globally: existing join
   keys and refinement proofs deliberately agree with its current relation.
2. **Finish numeric value reuse.** SPARQL still has `parseToScaled` and
   `parseDoubleToScaled` alongside XSD numeric parsers. Pin invalid lexicals,
   signed zero, exponent/precision behaviour and NaN/INF before adapting to a
   common value representation. Retain native suite baselines and explicitly
   repair remaining comparison/type-error cases rather than claiming lexical
   parser reuse already makes arithmetic conformant.
3. **Finish regex and QName contracts.** Migrate remaining boolean pattern
   adapters to explicit dialect/error results, with caller-specific treatment
   of unsupported constructs. Validate QName expansion using namespace context;
   syntactic acceptance alone is insufficient. The second-pass review queue
   remains applicable to these unfinished areas.


## SHACL identity consumers and fixture integrity (2026-10-22)

The next dependency audit connected SHACL's RDF-node operations to the shared
identity owner. This is a normative-reference dependency with executable
consequences: [SHACL property-pair constraints](https://www.w3.org/TR/2017/REC-shacl-20170720/#property-pair-components)
and [membership constraints](https://www.w3.org/TR/2017/REC-shacl-20170720/#InConstraintComponent)
operate over RDF nodes. [RDF literal identity](https://www.w3.org/TR/2014/REC-rdf11-concepts-20140225/#section-Graph-Literal)
preserves lexical form even when two literals denote the same value.

Previously `SHACL.termMem`, `dedupTerms` and inverse graph lookup used the
engine's XML-canonical `Term.eqb`. For example, `<e/>` and `<e></e>` as
`rdf:XMLLiteral` terms could satisfy `sh:in`/`sh:hasValue` interchangeably,
disappear into one value on an alternative path, and match each other's
incoming edges. A parsed alternative-path shape with `sh:maxCount 1`
incorrectly conformed when those two distinct values were present.

The three helpers now use `RDF.Term.sameTerm`, aligning membership,
deduplication, inverse paths, targets, `sh:equals`, `sh:disjoint` and the
node-expression intersection/removal consumers with one identity relation.
Language-tag case still folds; direction and numeric lexical spelling remain
distinct. SHACL's declarative `ValueSatisfies`/`FocusSatisfies` relations and
`termMem_iff` were updated together. Existing conformance equivalence and
soundness theorems compile against the corrected relation; those proofs still
share the underlying datatype, regex and path computations and do not establish
complete normative correctness of those dependencies.

```text
RDF.TermIdentity <--- SPARQL sameTerm / grouping / aggregate DISTINCT
       ^
       |
SHACL.Shapes: termMem / dedupTerms / subjectsOf
       |
       +-- Core membership and property-pair constraints
       +-- target and path value sets
       +-- node-expression intersection / removal

SHACL node-expression SPARQL arguments
       -> fresh variable bindings -> SPARQL Expr.eval
       -> original term result OR computed-value projection
```

The audit also found another literal-promotion copy in `SHACL.NodeExpr`.
Its term-to-AST adapter turned blank nodes into empty string literals, including
blank subjects inside triple terms, and treated boolean lexical `1` as false.
It now binds arguments to fresh indexed variables and uses the shared SPARQL
evaluator. The duplicate adapter and its `isBlank` workaround were removed.
Original term results bypass computed-decimal formatting, so `COALESCE` cannot
rewrite an existing decimal's lexical spelling. Numeric operators still obtain
values through SPARQL's conversion boundary.

### Regression evidence

The new [`SHACL/IdentityTests.lean`](../formal/lean4/L4Factoidal/SHACL/IdentityTests.lean)
contains **27 build-time guards**, including a parsed Turtle/SHACL regression,
XMLLiteral membership and inverse paths, distinct direction/numeric spellings,
and node-expression STR, sameTerm, COALESCE, type tests, triple accessors,
boolean handling and arithmetic. The distinguishing cases failed before the
implementation change; no upstream expected results were edited.

| Verification | Result |
| --- | --- |
| Untargeted `lake build`, including final harness changes | **871 jobs passed** |
| SHACL Core, full reports | **98/98** |
| SHACL-SPARQL, full reports | **22/22** |
| SHACL 1.2 node-expression corpus | **140 pass, 0 fail, 2 unsupported / 142**; unchanged from measured baseline |
| SHACL 1.2 rules corpus | **88/88** |
| Native fixture-error regressions | **3/3** |
| Reuse scanner regressions | **4/4** |

The two unsupported node-expression entries are `sht:Validate` cases which
that runner directs to `l4shacl`; they are not counted as node-expression
passes. These corpus measurements do not assert SHACL 1.2 Recommendation
status or complete SHACL conformance.

The fixture root remains the pinned data-shapes checkout
`/tmp/factoidal-okr-fixtures/data-shapes-08adb3776709a014bc3062ede793c36275b22446`.
Core and SPARQL use the commands/paths recorded in the previous section.
Run the other two executables from the repository root as follows; **the rules
runner takes a directory, while the node-expression runner takes a manifest**:

```sh
formal/lean4/.lake/build/bin/l4shacl-nodeexpr \
  /tmp/factoidal-okr-fixtures/data-shapes-08adb3776709a014bc3062ede793c36275b22446/shacl12-test-suite/tests/node-expr/manifest.ttl
formal/lean4/.lake/build/bin/l4shacl-rules \
  /tmp/factoidal-okr-fixtures/data-shapes-08adb3776709a014bc3062ede793c36275b22446/shacl12-test-suite/tests/rules
python3 tools/lean-shacl-harness-test.py
```

An incorrect rules-runner argument exposed a separate evidence-quality bug:
missing manifests produced an exit-zero total of zero tests. Rules and
node-expression runners now fail on missing, unreadable or empty leaf
manifests; missing nested includes are retained and reported instead of being
dropped. The three native regression tests first failed against the old
binaries, then passed against the rebuilt ones. They use temporary synthetic
entries to isolate discovery/errors, with no downloads or conformance claims.
The rules runner's successful-looking zero-test attempt is excluded from the
verification table.

Logs: `/tmp/factoidal-shacl-identity-{red,green,build-final,core,sparql}.log`,
`/tmp/factoidal-shacl-identity-nodeexpr-{before,final}.log`,
`/tmp/factoidal-shacl-identity-rules-final.log` and
`/tmp/factoidal-shacl-harness-red.log`. Updated audit output is
`/tmp/factoidal-shacl-identity-audit.json`: the direct imports of
`RDF.TermIdentity` now include both SHACL.Shapes and SPARQL.Expr.

### Remaining policy boundaries

The scanner finds one remaining runtime `eqb` mention in SHACL:
`Validation.termLe`. It combines less-than with engine term equality, so it
needs a value-comparison repair, not substitution of another identity helper.
[SHACL lessThanOrEquals](https://www.w3.org/TR/2017/REC-shacl-20170720/#LessThanOrEqualsConstraintComponent)
uses SPARQL's comparison operator and reports incomparable pairs as violations.
Different numeric spellings, cross-numeric types, dates/timezones and
noncomparable RDF terms must distinguish its replacement from term identity.
The numeric parser consolidation objective remains open.

Node expressions also retain historical special handling of seconds,
language-range matching and fixed identifier generators. The seconds fixture
expects lexical `00`; reviewing that adapter requires checking the value/term
comparison contract of the corpus as well as the function. These exceptions
are not erased by the shared argument bridge. ShEx neighbourhood lookup,
SPARQL joins/SELECT DISTINCT and storage still use legacy equality; graph
operations can merge XML literals before a validator sees them. This pass
corrects SHACL's local consumers and does not claim a global identity migration.


## Shared relational comparisons: SPARQL, SHACL and XSD (2026-10-22)

[SHACL range constraints](https://www.w3.org/TR/2017/REC-shacl-20170720/#value-range-components)
and [property-pair comparisons](https://www.w3.org/TR/2017/REC-shacl-20170720/#LessThanOrEqualsConstraintComponent)
explicitly use SPARQL relational operators. [SPARQL's operator table](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#OperatorMapping)
selects datatype operations; it does not authorize arbitrary lexical ordering
of every pair of RDF terms. The previous SHACL implementation nevertheless had
three different paths: numeric/date range checks, a lexical fallback for
property-pair `<`, and `< || Term.eqb` for `<=`. SPARQL had its own broad lexical
fallback. Merely replacing the last `eqb` with `sameTerm` would retain the wrong
contract.

[`Fn/Comparison.lean`](../formal/lean4/L4Factoidal/Fn/Comparison.lean) now owns
the shared relational adapter. Its `literalCompare`/`termCompare` entry points
return `Option Bool`: false is a comparison result, while none means an invalid
lexical form, unsupported operand pair, or unresolved calendar comparison.
SHACL reports both false and none as a violation. SPARQL preserves the error.

```text
SHACL min/max Inclusive/Exclusive --+
SHACL lessThan/lessThanOrEquals ----+--> Fn.Comparison
SPARQL <, <=, >, >= ---------------+       |
                                           +--> XSD lexicalFor .xsd10
                                           +--> Dec.cmp
                                           +--> IEEE754 conversion / fvalCmp
                                           +--> calendar parsing / dtCompare

Separate contracts still under review:
  SPARQL = / !=, arithmetic, ORDER BY, MIN/MAX
  RDF identity: sameTerm / grouping / aggregate DISTINCT
```

The adapter validates numeric operands at their source datatype, including
integer-derived bounds, then promotes integer/decimal, float and double values
at comparison time. It uses XSD's existing IEEE value model instead of SHACL's
scaled-number parser copy. Float values widen exactly when compared with doubles;
decimal/integer inputs round at the promoted floating type. Signed zeros compare
equal, infinities are ordered, and NaN relational tests return false. Invalid
numeric lexicals return an error, rather than receiving a fabricated value or
lexical comparison. Strings use codepoint ordering and booleans their value
ordering. IRIs, blank nodes, language-tagged strings, XML literals and unknown
datatypes have no relational mapping in this supported table.

Calendar comparisons reuse XSD 1.0 parsing and the existing exact-fraction
partial order. The first integration run was too restrictive for mixed timezone
presence and lost four dateTime cases; it also omitted the existing `xsd:date`
extension (`mf:XsdDateOperations`, `open-world/date-3`). Both were repaired before
final verification. The adapter now retains that date extension and uses
[XSD's timezone-window order](https://www.w3.org/TR/2004/REC-xmlschema-2-20041028/#dateTime-order):
some mixed pairs can be decided without assigning an implicit timezone. Pairs
whose possible order overlaps still return none. This supersedes the earlier
survey statements that SHACL rejects every mixed-timezone pair.

There is still no execution-context implicit timezone. Consequently this is
not the complete [F&O dateTime comparison contract](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#func-dateTime-less-than),
which can use such context. The IEEE conversion also inherits the documented
binary32-via-binary64 rounding profile in `XSD.IEEE754`. Neither limitation is
hidden by naming the adapter after its intended standards family.

### Proofs and verification

The new [`SHACL/ComparisonTests.lean`](../formal/lean4/L4Factoidal/SHACL/ComparisonTests.lean)
contains **37 guards** and **three universal agreement theorems**. They cover
numeric spelling/cross-type comparisons, float rounding, signed zero,
infinity/NaN, malformed lexicals, calendar offsets and ambiguity, unsupported
RDF types, strings/booleans, and parsed SHACL range/property-pair shapes.
Distinguishing guards failed against the old implementation. The theorems prove
that SHACL `<`, `<=` and `minInclusive` use the same result as SPARQL for arbitrary
inputs; they prove integration agreement, not independent correctness of XSD
parsing or IEEE conversion. Their axiom audits contain only Lean's standard
foundations. No new `sorry`, user axioms, `native_decide`, partial definitions
or FFI were added.

One old authored guard expected two strings to be incomparable in a range
check. It now expects their specified string comparison. Upstream corpus
expectations were unchanged.

| Final check | Result |
| --- | --- |
| Untargeted `lake build` | **874 jobs passed** |
| SPARQL 1.1 + 1.2 manifests | **885/885**, unchanged baseline |
| SPARQL 1.0 evaluation manifest | **215 pass / 67 fail**, unchanged baseline and failure names |
| SHACL Core full reports | **98/98** |
| SHACL-SPARQL full reports | **22/22** |
| SHACL node expressions | **140 pass / 2 unsupported**, no failures |
| SHACL rules | **88/88** |
| Fixture-error / reuse-scanner regressions | **3/3**, **4/4** |

The native fixture roots and commands are the same as the preceding two
sections. Baselines are `/tmp/factoidal-order-{wide,10}-before.log`; the final
build is `/tmp/factoidal-order-build-final.log`; native logs are
`/tmp/factoidal-order-{wide,10,shacl-core,shacl-sparql,nodeexpr,rules}-final.log`.
The initial intentionally failing guard run is `/tmp/factoidal-order-red.log`.
Intermediate `after` logs contain the subsequently repaired calendar regressions
and are not the final measurements. There are no new failures relative to the
pre-pass SPARQL manifests. The unchanged native totals are compatible with the
new guards finding behaviours absent from those fixture sets.

The reuse audit now tracks `Fn.Comparison` imports and its comparison entry
points; it reports **374 runtime modules and 55 cross-family name groups**.
Both SHACL.Validation and SPARQL.Expr import the new owner. SHACL runtime code
has no remaining `eqb` identifier mentions in that scan. The absence of those
mentions does not prove all equality policy is correct: transitive dependencies
still matter.

The next integration target is SPARQL numeric equality and arithmetic. They
still use the historical scaled representation, so IEEE rounding/NaN semantics
can differ between `=` and the repaired relational operations. Computed float
results also need to retain their numeric type through arithmetic. ORDER BY
and MIN/MAX remain on their separate ordering path. These are substantive
remaining gaps; the new shared adapter is an integration step, not a declaration
that numeric semantics are finished. Namespace/QName and regex follow-through
also remain in the earlier queue.


## Numeric equality and parser reuse (2026-10-22)

The next pass found observable duplication inside the SPARQL implementation:
`<` and `<=` used XSD floating values, but `=` used an exact scaled-decimal
interpretation of their lexical forms. Consequently a float rounding boundary
could compare equal under `<=` in both directions while `=` returned false.
This was an implementation mismatch with the common numeric promotion required
by [SPARQL's operand mapping](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#OperatorMapping).

`Fn.Comparison.numericCompare` now implements numeric equality and inequality
as well as relational tests. SPARQL's `numericValue?` adapter preserves the
original float/double type, parses integer-derived types with their bounds,
and supplies computed integers directly as XSD decimal values. Numeric equality
within RDF 1.2 triple-term comparison also uses this path. NaN is unequal to
itself; signed zeros compare equal; infinities, underflow and numeric promotion
use the same existing XSD value model as relational tests. These follow the
[F&O numeric comparison contract](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#func-numeric-equal)
within the inherited IEEE conversion profile described above.

```text
SHACL SPARQL constraints ---------> SPARQL expression evaluation
                                      |
SPARQL numeric = / != ----------------+--> numericEquality
SPARQL triple-term numeric objects --------> numericEquality
                                                |
                                                +--> Fn.Comparison.numericCompare
SHACL ranges / property pairs ------+                    |
SPARQL < / <= / > / >= -------------+--> Fn.Comparison ---+
                                                         +--> XSD lexical values
                                                         +--> Dec.cmp / fvalCmp

SPARQL scaled arithmetic / casts / ORDER BY
  parseIntString -------> XSD.parseIntegerLex
  parseToScaled --------> XSD.parseDecimalLex
  parseDoubleToScaled --> XSD.decimalOrScientific
  (shared lexical validation; remaining arithmetic/order policy is separate)
```

The three old lexical parsers are now thin adapters. This removes local digit
accumulation and decimal/exponent parsing, rejects `-`, `1.x`, `1.-2` and `1e-`,
and accepts valid leading-plus and leading-point forms. The old decimal parser
silently fabricated a zero fractional part on failure. Sharing validation fixes
that bug in arithmetic and casts as well as in comparison. Decimal normalization
now belongs to XSD; `Scaled` remains the representation of legacy operations.

There is a necessary consumer-specific boundary. Invalid numeric **values**
cannot be compared numerically, but identical ill-typed **RDF literals** can
still compare equal under [RDFterm-equal](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#func-RDFterm-equal).
An initial implementation rejected both and lost `open-eq-07`. The final
`numericEquality` adapter attempts numeric comparison first, then uses
`Literal.sameTerm` for identical raw literals if value lookup failed. Different
ill-typed literals remain an error. NaN produces a numeric answer before that
fallback, so its identity cannot incorrectly override numeric inequality.
Manually constructed invalid computed `.dec`/`.dbl` values remain errors.
This boundary is why the normative dependency should produce shared value
primitives plus explicit consumer policy, rather than one universal equality.

`Fn.ComparisonTheorems` proves decimal reflexivity and floating reflexivity with
a non-NaN premise. SPARQL's integer/plain-string agreement proofs are updated;
decimal reflexivity now assumes the XSD decimal parser succeeds, and double
reflexivity explicitly assumes a parsed non-NaN value. A separate theorem proves
the identical ill-typed literal fallback. Their audits use only Lean's standard
foundations. No new `sorry`, user axioms, `native_decide`, partial definitions or
FFI were introduced.

The new `SPARQL.NumericTests` guards cover rounding/type promotion, NaN/infinity,
signed zero, underflow, derived integer bounds, RDF fallback, malformed lexicals,
scientific notation and arithmetic error propagation. Distinguishing guards
were run against the old implementation first. Two initial expectations that
rejected identical ill-typed literals were corrected after checking the native
corpus and RDFterm-equal contract; they are not counted as old-code bugs.

### Remaining numeric reuse work

The audit now inventories both shared numeric operations and legacy numeric
helpers by source location. `SPARQL.Query` is the remaining runtime caller of
the old `SPARQL.numericCompare`; expression comparison no longer uses it.
That helper still supplies ORDER BY and MIN/MAX. The old comment claiming its
ordering was conformant has been replaced with its actual limitation.

The next concrete targets are:

- **Numeric classification and EBV.** `isNumericDatatype` still has a four-type
  whitelist, `fnIsNumeric` does not check lexical validity, and floating EBV
  inspects the pre-rounding mantissa. Reuse XSD numeric lookup for these, with
  tests for derived integer bounds and underflow. Keep the SPARQL 1.1/1.2
  malformed-EBV policy explicit.
- **Arithmetic and result types.** Scaled arithmetic still lacks IEEE special
  values/rounding and promotes float literals to `.dbl`. Sharing a parser does
  not fix that. Preserve float versus double in computed results before moving
  more F&O consumers onto the value operations.
- **Ordering and nonnumeric equality.** ORDER BY/MIN/MAX need their own total
  ordering policy over the shared values. DateTime equality, unknown-datatype
  equality errors and cross-category RDF equality still have separate gaps.
  Sorting, value equality and RDF identity must retain distinct contracts.

The XSD binary32-via-binary64 rounding limitation remains. XPath/F&O arithmetic
has not been migrated by this pass, and unchanged native suite totals are not
evidence that every numeric edge case is covered.

### Final verification

| Check | Result |
| --- | --- |
| Untargeted `lake build` | **876 jobs passed** |
| New numeric guards | **32 passed** |
| SPARQL 1.1 + 1.2 manifests | **885/885** |
| SPARQL 1.0 evaluation | **215 pass / 67 fail**, same failure names as baseline |
| SHACL Core / SPARQL | **98/98**, **22/22** |
| SHACL node expressions / rules | **140 pass / 2 unsupported**, **88/88** |
| Fixture-error / scanner regressions | **3/3**, **4/4** |

Fixtures and commands are the same as the preceding comparison section. The
baseline logs are `/tmp/factoidal-order-{wide,10}-final.log`; the final build is
`/tmp/factoidal-numeric-build-final.log`; native logs are
`/tmp/factoidal-numeric-{wide,10,shacl-core,shacl-sparql,nodeexpr,rules}-final.log`.
The initial guard run is `/tmp/factoidal-numeric-red.log`. Intermediate logs
without `final` include the subsequently fixed `open-eq-07` regression. Upstream
expected results were unchanged. There are no new native failure names.

The refreshed `/tmp/factoidal-numeric-audit.json` reports **374 runtime modules
and 55 cross-family helper-name groups**. The unchanged counts illustrate the
scanner's limits: the semantic duplication removed here had different helper
names. Its new numeric identifier inventory exposes the remaining callers;
it still records textual mentions, not name-resolved calls or semantic clones.


## Numeric type tests, EBV and Boolean casts (2026-10-22)

The follow-through found three more disagreements. `isNumeric` classified
datatype names without checking values and omitted integer-derived types.
Floating EBV inspected the lexical mantissa before IEEE conversion, so a value
that underflowed to zero remained truthy. Boolean casts used the scaled parser,
rejecting NaN/infinity and promoting a source float to double too early.

New [`Fn.Numeric`](../formal/lean4/L4Factoidal/Fn/Numeric.lean) owns numeric
datatype classification, XSD 1.0 lexical-value lookup and numeric-to-Boolean
conversion. `Fn.Comparison` retains compatibility aliases for its earlier
input helpers, with no copied implementation. SPARQL `numericValue?`, numeric
EBV, `isNumeric` and Boolean casts use that common input layer. This follows
[isNumeric's validity requirement](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#func-isNumeric)
and [F&O Boolean conversion](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting-to-boolean).

```text
SHACL node-expression SPARQL bridge --> SPARQL isNumeric / logical-not
SHACL-SPARQL constraints ------------> SPARQL expressions
                                        |
SPARQL numeric EBV / Boolean cast -------+--> Fn.Numeric
SPARQL isNumeric / numericValue? --------+       |
Fn.Comparison numeric inputs -----------+       +--> XSD lexicalFor .xsd10
                                                +--> parsed Dec / Fval
```

`isNumeric("127"^^xsd:byte)` now succeeds; out-of-range `128` and malformed
numeric lexicals do not. NaN and infinity are valid numeric values. Numeric EBV
and Boolean casting use the resulting value: `1e-50` is false as a float and
true as a double. NaN and either signed zero yield false; infinities yield true.
The SHACL node-expression bridge inherits the fixes without another conversion
table; three added guards exercise that actual bridge.

Boolean casts dispatch before generic literal promotion. Their numeric branch
retains the original datatype; the string branch applies XSD whitespace collapse
before Boolean lexical validation, as required by
[F&O string casting](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting-from-strings).
XML whitespace is accepted around `true`; internal spaces and nonbreaking
spaces are not. Language-tagged and unknown-datatype literals no longer become
booleans merely because their text says `true`. Boolean EBV also delegates its
lexical parsing to XSD rather than maintaining another lexical table.

The existing edition boundary is now explicit in source documentation.
[SPARQL 1.1 EBV](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#ebv)
maps malformed Boolean/numeric literals to false, whereas the
[11 October 2026 SPARQL 1.2 draft](https://www.w3.org/TR/2026/WD-sparql12-query-20261011/#ebv)
raises an error. The evaluator continues using the latter policy with the
existing XSD 1.0 numeric lexical profile. There is no complete, selectable
SPARQL-edition configuration yet. Passing both finite fixture collections does
not establish that one policy conforms to both specifications. This replaces
the earlier source comment suggesting those green suites justified that claim.

`SPARQL.NumericBooleanTheorems` proves cast/EBV agreement for every decimal and
double lexical input, agreement for numeric RDF literals with explicit
non-string/non-Boolean premises, and `isNumeric`'s use of shared validated
values. These are integration proofs, not independent correctness proofs of
XSD parsing or IEEE conversion. Their axiom audits contain only Lean's standard
foundations. `NumericBooleanTests` contains 40 guards; 17 distinguishing guards
failed before the implementation changed. No new `sorry`, user axioms,
`native_decide`, partial definitions or FFI were introduced.

Arithmetic, other casts, computed-float type retention and ORDER BY/MIN/MAX
remain on their existing paths. The numeric layer still inherits XSD's
binary32-via-binary64 rounding profile. XPath's separate numeric representation
has not been migrated by this pass.

Final checks: untargeted `lake build` **880 jobs**; SPARQL 1.1/1.2 **885/885**;
SPARQL 1.0 **215 pass / 67 fail**, with unchanged failure names; SHACL Core
**98/98**, SPARQL **22/22**, node expressions **140 pass / 2 unsupported**, and
rules **88/88**. Fixture-error regressions pass **3/3**; scanner regressions
pass **4/4**. No upstream expected results were changed.

The build log is `/tmp/factoidal-numeric-bool-build.log`; the final native logs
are `/tmp/factoidal-numeric-bool-{wide,10,core,shacl-sparql,nodeexpr,rules}.log`.
Comparison baselines are the preceding pass's `numeric-*-final.log` files;
fixture roots and commands remain the same. The red guard run is
`/tmp/factoidal-numeric-bool-red.log`. The refreshed audit at
`/tmp/factoidal-numeric-bool-audit.json` reports **375 runtime modules and 55
cross-family helper-name groups**, including direct imports of `Fn.Numeric`
from SPARQL.Expr and Fn.Comparison. These measurements establish this pass's
tested integration, not full standards conformance.


## Floating arithmetic and aggregate reuse (2026-10-22)

Binary arithmetic still promoted floats to doubles and operated on scaled
decimal spellings. It therefore missed rounding at the source/result type,
signed-zero rules and IEEE special values. The same problem occurred in a
separate SUM/AVG accumulator. Fixing only expression operators would leave
aggregates using different numeric semantics.

New [`Fn.Arithmetic`](../formal/lean4/L4Factoidal/Fn/Arithmetic.lean) implements
floating addition, subtraction, multiplication and division over XSD `Fval`
values. It converts finite operands to exact integer ratios and rounds the
result once to binary32 or binary64 through the existing `XSD.roundRational`.
Special-value rules handle NaN, infinity and signed zero before finite
calculation. There is no host floating-point arithmetic or new FFI in this
implementation. [F&O's binary numeric operators](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#func-numeric-add)
provide the semantic contract.

Operand promotion moved into `Fn.Numeric.floatingValue`; comparison retains a
compatibility alias. Thus arithmetic and comparison use the same parsed source
values and promotion rules. SPARQL's `evalArithmetic` validates operands before
promotion and emits a float literal for a float result, or a double result when
either operand is double. Derived integer types use XSD lexical bounds and
produce integer results where required. Integer/decimal division by zero remains
an error; floating division can return signed infinity or NaN.

```text
SPARQL + - * / -----------+
SUM (recursive addition) +--> evalArithmetic --> Fn.Arithmetic
AVG (SUM / count) -------+         |                 |
SHACL SPARQL builtins ---+         |                 +--> XSD.roundRational
                                  +--> Fn.Numeric <--+
Fn.Comparison -----------------------> Fn.Numeric
                                        |
                                        +--> XSD lexical values / promotion
```

The old `sumNumericAcc` and AVG's independent precision/type machinery were
removed. [SPARQL SUM and AVG](https://www.w3.org/TR/2013/REC-sparql11-query-20130321/#defn_aggSum)
now use the expression arithmetic operation: SUM folds from the right with
integer zero; AVG divides that sum by the count. A nonnumeric value reaches the
same error path instead of being silently skipped by the helper. Aggregate
expression-error filtering and DISTINCT retain their separate existing policy.

There are **39 SPARQL arithmetic/aggregate guards**, including actual bound
aggregate evaluation; **19 binary** and **eight aggregate** distinguishing cases
were measured red before each migration. An independent table adds **62 finite
oracle cases**, checking output bits against CPython double operations and
binary32 input/output conversion through `struct.pack/unpack`. This finite
comparison is not proof of every IEEE or double-rounding boundary. Existing XSD
lexical/rounding tests remain part of the default build.

Seven `Fn.ArithmeticTheorems` pin NaN propagation, zero/infinity rules and
float/mixed result types. Three `SPARQL.ArithmeticTheorems` prove integer-path
agreement and the SUM/AVG arithmetic recurrence. Their kernel audits contain
only Lean's standard foundations. These are special-value and integration
proofs, not a proof that the finite rounding algorithm implements all IEEE
requirements. No new `sorry`, user axioms, `native_decide`, partial definitions
or FFI were added.

The remaining boundaries matter. Decimal-only arithmetic still uses `Scaled`,
with the existing ten-place division policy (integer division uses sixteen).
AVG now inherits the ordinary division policy instead of a separate ten-place
implementation. Unary operators, ABS/ROUND/CEIL/FLOOR, other numeric casts,
ORDER BY/MIN/MAX and XPath's numeric model still need integration. Output uses
XSD's exact round-tripping floating decimal expansion, not shortest canonical
formatting. Input decimal-to-float promotion still inherits XSD's documented
binary64-then-binary32 profile; result arithmetic rounds directly to its format.

### Harness comparison and final evidence

The first native run fixed four mixed-datatype arithmetic cases in SPARQL 1.0,
but SUM/AVG each appeared to regress in the wider corpus. Their double results
were the correct IEEE values in longer exact decimal spellings. Inspection found
another scaled-decimal comparator in `Harness.Compare.numericLiteralEqual`.
That helper already intended same-datatype numeric **value** matching, but its
unrounded decimal comparison rejected the equivalent doubles.

The harness now uses the shared XSD/F&O comparison for this existing leniency.
Five new guards cover equivalent double spellings, adjacent double and float
values, datatype mismatches and malformed lexicals. The equivalent-spelling
guard was measured red first; adjacent values and differing result datatypes
remain rejected. No expected result file was edited. Because the harness shares
the XSD value layer, its green results are not an independent arithmetic oracle;
the 62 external bit-vector observations provide a separate finite check.

| Final check | Result |
| --- | --- |
| Untargeted `lake build` | **886 jobs passed** |
| SPARQL 1.1 + 1.2 | **885/885** |
| SPARQL 1.0 evaluation | **219 pass / 63 fail**, up from **215 / 67**, no new failure names |
| SHACL Core / SPARQL | **98/98**, **22/22** |
| SHACL node expressions / rules | **140 pass / 2 unsupported**, **88/88** |
| Fixture-error / reuse scanner regressions | **3/3**, **5/5** |

The four newly passing cases are the `+`, `-`, `*` and `/` mixed-number-datatype
tests. Final build: `/tmp/factoidal-arithmetic-build-final.log`; SPARQL logs:
`/tmp/factoidal-arithmetic-{wide,10}-final.log`; SHACL logs:
`/tmp/factoidal-arithmetic-{core,shacl-sparql,nodeexpr,rules}.log`. Baselines are
the preceding `numeric-bool-{wide,10}.log` files. Red phases are
`/tmp/factoidal-arithmetic-red.log`, `...-aggregate-red.log` and
`...-harness-red.log`. Intermediate SPARQL logs without `final` predate the
harness repair. Fixture roots and commands are unchanged from earlier sections.

The library-only reuse scan could not expose this harness duplication. New
`--include-harness` scanning covers it explicitly and has a fixture regression
that also verifies test-module exclusion. The ordinary scan reports **376
runtime modules / 55 name groups**; the expanded scan reports **430 modules /
60 name groups**. Reports are `/tmp/factoidal-arithmetic-audit.json` and
`/tmp/factoidal-arithmetic-harness-audit.json`. Imports and textual mentions
remain review evidence, not proof of actual invocation or semantic equivalence.


## Shared unary numerics and XPath rounding (2026-10-22)

This pass found semantic duplication that helper-name matching alone missed:
SPARQL's `lexFloor`/`lexCeil`/`lexRound` and XPath's `floorN`/`ceilingN`/`roundN`
implemented the same integral-rounding rules with different algorithms. XPath
handled negative fractions correctly; SPARQL lost their sign, rounded negative
ties away from zero, and sometimes manufactured zero from invalid lexical forms.
SPARQL unary plus also accepted nonnumeric operands, and its float operands
became doubles through the legacy literal-promotion path.

The normative connection is behavioral, not a claim that XPath 1.0 cites a later
specification. [XPath 1.0 §4.4](https://www.w3.org/TR/1999/REC-xpath-19991116/#section-Number-Functions)
and [F&O 2007 §6.4](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#func-round)
require nearest-integer ties toward positive infinity. F&O also specifies
primitive numeric result types and special floating values. SPARQL's unary
operators and numeric functions use these F&O operations. This supports sharing
an exact rounding primitive while retaining each consumer's value-model and
error policies.

### Implemented dependency map

Arrows below are implementation calls/adapters, not normative references:

```text
SHACL.NodeExpr.sparqlApply
           |
           v
      SPARQL.Expr
           | numericValue? --> Fn.Numeric --> XSD.Lexical / XSD values
           |
           | evalNumericUnary
           v
     Fn.NumericUnary ----------------> Fn.Arithmetic
           | decimal / floating          | magnitude, sign, result rounding
           |                             v
           |                         XSD.IEEE754
           v
       Fn.Rounding <---------------- XPath.Number.integralN
       exact integer ratios                  ^
       floor / ceiling / ties-up             |
                                        XPath.Eval
                                             ^
                                             |
                                     XSLT and XPath clients
```

`Fn.Rounding` has no lexical, datatype or special-value policy. Both adapters
supply exact numerators and positive denominators. `Fn.NumericUnary` handles
validated decimals and binary32/64 values, preserves NaN/infinities/signed zero,
and retains float versus double. SPARQL's six unary forms now delegate to it;
`numericResult` shares result projection with binary arithmetic. The five old
SPARQL helpers (`splitDecimal`, `allZeros`, `lexFloor`, `lexCeil`, `lexRound`)
were removed. XPath's three finite rounding implementations became adapters to
the same primitive. SHACL's existing bound-term bridge inherits the corrections.

Examples now checked include `ROUND(-1.5) = -1`, `FLOOR(-0.1) = -1`,
`CEIL(-0.1) = 0`, float result typing, negative floating zero, NaN and infinity,
scientific notation, derived-integer bounds, and type errors for malformed or
nonnumeric operands. The old authored guard expecting `ROUND(-1.5) = -2` was
corrected against F&O; no vendored expected result file was changed.

### Evidence and limits

Thirty of the first 34 expression guards failed against the old evaluator.
The final module has **39 expression guards**, with **5 additional SHACL bridge
guards**. There are **120 independent finite bit-result observations** (40
binary32/64 inputs × floor/ceiling/round), generated using CPython's exact
`Decimal.from_float` conversion and directed integral rounding. These include
half boundaries, source-type rounding, signed zero, subnormals and large finite
values; they are a finite corpus, not a universal IEEE proof.

Ten public kernel-checked theorems cover integral preservation, arbitrary
halfway values rounding upward, ceiling/floor duality, floating special values,
result types and agreement between the XPath and F&O **exact-decimal adapters**
for arbitrary mantissas/scales. Their audits use only Lean's standard foundations.
They do not identify the current XPath number model with IEEE doubles.

| Check | Result |
| --- | --- |
| Untargeted `lake build` | **893 jobs passed** |
| SPARQL 1.1 + 1.2 | **885/885** |
| SPARQL 1.0 evaluation | **221 pass / 61 fail**, up from **219 / 63**, no new failure names |
| SHACL Core / SPARQL | **98/98**, **22/22** |
| SHACL node expressions / rules | **140 pass / 2 unsupported**, **88/88** |
| Vendored XSLT subset | **84 pass / 3 fail / 1 refused**, matching the earlier recorded totals |
| Schematron fixture | **8/8**, no undecided cases |
| Fixture-error / scanner regressions | **3/3**, **5/5** |

The newly passing upstream tests are **Unary Minus with various datatype** and
**Unary Plus with various datatype**. The full-build log is
`/tmp/factoidal-unary-build-final.log`; native logs are
`/tmp/factoidal-unary-{wide,10,core,shacl-sparql,nodeexpr,rules,xslt,schematron}.log`.
SPARQL baselines are `/tmp/factoidal-arithmetic-{wide,10}-final.log`; the red
expression run is `/tmp/factoidal-unary-red.log`. The first full-build log
without `final` contains an oracle-test type error corrected before the final run.
The XSLT residual failures are `copy-3102`, `namespace-4801`, `node-1601`, with
`select-5901` refused for a missing source document; these are not counted as passes.

The expanded reuse scan (`--include-harness`) now inventories rounding and unary
numeric helpers and the two new shared modules: **432 runtime modules / 63
candidate name groups**, recorded in `/tmp/factoidal-unary-audit.json`. The name
filter broadened, so its group count is not directly comparable to the previous
60 as a measure of added or removed redundancy. Source mentions and imports are
review aids; the adapter theorem and executing tests provide stronger evidence
of actual reuse.

### Next reuse targets

The largest remaining numerical split is **ORDER BY / MIN / MAX and numeric
casts**: these still reach legacy scaled values and literal promotion. A next
pass should use typed XSD values while retaining SPARQL's distinct ordering,
error and unbound-value rules. Numeric comparison alone is not a complete term
ordering policy.

**XPath's value model** remains exact decimal plus special values, without
binary64 rounding or distinct signed zero. Sharing integral rounding narrows the
duplication but does not fix that representation gap. The source header now
states this limitation rather than suggesting tests justify the divergence.

**Date accessors** needed a narrower audit than first recorded here. Source
reinspection found SPARQL already using validated, edition-aware XSD values;
the remaining bypass was SHACL node expressions' `extractSecondsField` shortcut.
The following integration pass removes that bypass and tests fractional seconds,
invalid input and timezone policies. The earlier claim that SPARQL still
extracted its date fields lexically was inaccurate.

Inherited decimal-to-binary32 parsing/promotion rounding, bounded decimal
division precision, and shortest floating lexical formatting remain open.


## Removing SHACL builtin bypasses (2026-10-22)

Source reinspection corrected the preceding date-accessor assessment: SPARQL's
`dtValue` and component accessors already used the edition-aware XSD parser.
The actual duplicate was SHACL's `extractSecondsField`, which scanned characters
without validating the datatype or date, truncated fractional seconds and
returned zero for malformed input. A neighboring `langMatchesNe` duplicated an
existing shared basic language matcher but omitted case folding.

Both operations now use the ordinary bound-term SPARQL bridge:

```text
SHACL.NodeExpr.sparqlApply
      |
      +-- seconds --> SPARQL.Expr.seconds
      |                    |
      |                    v
      |              dtSeconds / dtValue --> XSD.parseDateTimeFor(.xsd10)
      |                    |
      |                    v
      |              exact decimal result --> XSD.canonicalSeconds
      |                                        (SHACL result spelling only)
      |
      +-- langMatches --> SPARQL function dispatch
                                |
                                +--> simpleLiteral? (argument types)
                                |
                                +--> Fn.String.langMatchesBasic
                                     (case-insensitive basic filtering)
```

This follows [SPARQL SECONDS](https://www.w3.org/TR/sparql11-query/#func-seconds)
and [LANGMATCHES](https://www.w3.org/TR/sparql11-query/#func-langMatches).
`SECONDS` preserves the exact fractional value and requires a valid dateTime;
`LANGMATCHES` takes simple string literals and uses basic language filtering.
SPARQL's previous `toString?` dispatch accepted other RDF term types; it now
uses a typed `simpleLiteral?` adapter. Its `fnLangMatches` name is a compatibility
alias for the existing shared matcher, rather than another implementation.

The SHACL fixture expects `"00"^^xsd:decimal` for zero seconds. That permitted
result spelling remains a projection policy, implemented with the existing XSD
seconds formatter **after** SPARQL validates and evaluates the input. It does not
reintroduce a date parser or drop fractions: `02.5` and `00.1234567890123456789`
now retain their full values. The harness still compares exact result terms;
no expected file or comparison policy was changed to make the tests pass.

Deleted four SHACL helpers: `afterChar`, `takeWhileLc`, `extractSecondsField`,
and `langMatchesNe`. Added **22 date-accessor guards** and **13 language-bridge
guards**, including collections that check both argument positions and both
SPARQL/SHACL callers. **12 date guards and 6 language guards failed first**.
Cases cover long fractions, timezone limits, malformed dates, XSD 1.0 year zero,
BCE rollover, missing timezone policy, wrong types/arity, case folding, wildcard
matching and basic-versus-extended language ranges. They are authored regression
evidence, not a claim of complete SHACL 1.2 conformance.

Verification: untargeted `lake build` **896 jobs passed**; SPARQL 1.1/1.2
**885/885**; SPARQL 1.0 **221 pass / 61 fail**, with identical failure records to
the unary baseline; SHACL Core **98/98**, SPARQL **22/22**, node expressions
**140 pass / 2 unsupported**, rules **88/88**. Fixture-error regressions **3/3**,
reuse scanner **5/5**. Build: `/tmp/factoidal-bridge-build.log`; native logs:
`/tmp/factoidal-bridge-{wide,10,core,shacl-sparql,nodeexpr,rules}.log`; red logs:
`/tmp/factoidal-seconds-red.log`, `/tmp/factoidal-language-red.log`.

The expanded audit now inventories the date and language bridge identifiers,
and records SPARQL's direct import of `Fn.String`. It remains **432 runtime
modules / 63 candidate name groups** (`/tmp/factoidal-bridge-audit.json`). The
unchanged count despite deleting incorrect helper bodies is another reason not
to use same-name collisions as a semantic-redundancy metric.

The next observed string boundary gap is `REGEX`/`REPLACE`: their pattern,
replacement and flag arguments still use broad `toString?` conversion. The new
simple-literal adapter provides a reuse point, but those callers have not been
migrated in this pass. Numeric casts, ordering/MIN/MAX and XPath binary64 value
integration also remain open.


## Shared regex preparation and replacement boundaries (2026-10-22)

`REGEX` and `REPLACE` now use `EvalResult.simpleLiteral?` for pattern, flags
and replacement arguments, rather than accepting anything `toString?` could
render. Text arguments still accept the supported string-literal kinds. This
implements the argument distinction in [SPARQL 1.1 REGEX/REPLACE](https://www.w3.org/TR/sparql11-query/#func-replace).
The existing SHACL bound-term bridge inherits these checks.

The audit also found that replacement bypassed `Regex.Profiles` altogether.
Shared `compileSearch` now handles the dialect and input-sensitive checks for
both operations; `replaceSparql` delegates through it before calling the engine.
Consequently unsupported escape or Unicode semantics propagate as errors from
both operations, instead of replacement silently using a different language.
This does not implement the missing Unicode/category behavior.

```text
SHACL node expressions --> SPARQL REGEX / REPLACE
                                  |
                     simpleLiteral? + stringLiteralInfo?
                                  |
                         Regex.Profiles
                         /            \
                  matchSparql     replaceSparql
                         \            /
                           compileSearch
                                  |
                            Regex.XPath
                         /               \
                     isMatch            replace
                                           |
                              quoteReplacement (q mode)

REPLACE result --> erStringPreserve(language, datatype, direction)
```

REPLACE now threads base direction through the existing result constructor, so
an `rdf:dirLangString` result retains its language and direction. The helper's
optional direction parameter leaves other callers' current policies unchanged;
this pass does not claim all string functions preserve direction correctly.

The shared engine's `q` mode previously quoted only the pattern. It now quotes
replacement template metacharacters too, so `$`, `$1` and backslashes remain
literal, and ignores `m/s/x` when `q` is present. These rules are specified by
[F&O 3.1 flags and replacement](https://www.w3.org/TR/xpath-functions-31/#func-replace).
The profile comment now distinguishes SPARQL 1.1's XPath 2.0 reference from the
[11 October 2026 SPARQL 1.2 Working Draft](https://www.w3.org/TR/sparql12-query/#func-regex),
which references F&O 3.1. Automatic `q` dispatch remains the current compatibility
policy; there is still no complete selectable edition configuration.

Added **30 authored guards**, including invalid-type collections covering every
non-text argument position, ordinary language tags, direction, pattern/template
errors, capture substitution, quote mode and actual SHACL calls. Eleven initial
boundary guards failed before repair; four further quote-mode guards exposed
the literal-replacement bug. Three kernel-checked laws prove that the quote
encoding is always a valid template, has no capture references, and expands to
the original codepoints for arbitrary input and capture spans. These prove the
encoding properties, not the correctness of the entire regex matcher.

Verification: untargeted `lake build` **898 jobs passed**; SPARQL 1.1/1.2
**885/885**; SPARQL 1.0 **221 pass / 61 fail**, unchanged failure records;
SHACL Core **98/98**, SPARQL **22/22**, node expressions **140 pass / 2 unsupported**,
rules **88/88**; vendored JSON Schema draft-07 **770/770**, no undetermined cases;
fixture-error regressions **3/3**, scanner **5/5**. Build log:
`/tmp/factoidal-regex-boundary-build.log`; native logs:
`/tmp/factoidal-regex-boundary-{wide,10,core,shacl-sparql,nodeexpr,rules,jsonschema}.log`.
Red runs: `/tmp/factoidal-regex-boundary-red.log`, `/tmp/factoidal-regex-quote-red.log`.
The expanded scan inventories preparation, replacement and metadata callers:
**432 runtime modules / 63 candidate name groups**, in
`/tmp/factoidal-regex-boundary-audit.json`.

### Engine gaps observed before the selection repair below

A separate follow-up probe demonstrates that the passing corpora miss important
replacement semantics. Replacing `^a` with `z` in `aba` currently returns `zbz`
instead of `zba`; replacing `a$` likewise returns `zbz` instead of `abz`.
Replacing `(a)|(ab)` in `ab` using `[$1][$2]` currently returns `[][ab]` instead
of the ordered-alternative result `[a][]b`. The engine's replacement regex drops
anchors, and its longest-match selection disagrees with the specified first
alternative rule. Evidence: `/tmp/factoidal-regex-followup.lean` and
`/tmp/factoidal-regex-followup.log`. These are observed failures, not passing
guards, and are the next implementation priority. Unicode support, other string
metadata callers and numeric casts/order remain separate open work.

## One replacement selection path, with derivative reuse (2026-10-22)

The anchor and alternative failures recorded above are now repaired. Replacing
`^a` and `a$` in `aba` returns `zba` and `abz` respectively; `(a)|(ab)` in `ab`
with `[$1][$2]` returns `[a][]b`. The engine now retains zero-width anchors and
greedy/reluctant quantifiers in its capturing syntax tree. A continuation-based
matcher chooses the first successful ordered alternative consistent with the
remaining pattern, and returns both the selected span and its captures.
Repeated groups retain their latest capture. Anchor checks use original input
codepoint positions, with LF-only multiline boundaries. These rules follow
[F&O regular expression syntax](https://www.w3.org/TR/xpath-functions-31/#regex-syntax)
and [fn:replace](https://www.w3.org/TR/xpath-functions-31/#func-replace).

The redundancy was internal as well as across specs: the engine selected a
longest span with derivatives, then independently tried to recover captures for
that endpoint. Removing `longestEnd` and `pickCaps` eliminates this disagreement.
The legacy string-returning `regexReplace` now delegates to the same public
compile/replace path, retaining its unchanged-input fallback on errors.

```text
SHACL node expressions --> SPARQL replaceCore --> Regex.Profiles.replaceSparql
                                                           |
legacy regexReplace ---------------------------------------+--> compile / replace
                                                                    |
                                                          capturing syntax tree
                                                           /                 \
                                               eraseAssertions               |
                                                      |                      |
                                             Exec.anchoredPrefix             |
                                                      |                      |
                                             Exec.acceptsNorm                |
                                                      |                      v
                                            possible start? -------------> cmatch
                                                               ordered span + captures
                                                                            |
                                                                     expandTemplate
```

The derivative engine remains useful: replacement derives an assertion-erased
prefix language from the same capturing tree and uses the existing matcher to
reject impossible starting positions before ordered search. It does not use
that language to select a winning span. A 128-character ambiguous repetition
checks successful short-circuiting; a second case checks rejection of a long
impossible prefix before a later valid match. This avoids those exponential
enumerations without claiming a general complexity bound or a proved connection
between the prefix filter and capturing semantics.

Added **43 authored guards**, including actual SHACL and legacy-adapter calls;
**20 of the initial 37 failed** before repair. An additional **200 static oracle
vectors** record CPython `re.sub` observations on a deliberately shared ASCII
subset (20 patterns by 10 inputs). Python's different newline-anchor behavior
is excluded from that corpus and covered by explicit F&O tests instead. Four
generic kernel-checked laws establish non-multiline anchor checks and ordered
alternative success/fallback; their only axiom dependency is `propext`. They do
not establish parser correctness, full matcher semantics or fuel adequacy.

The expanded reuse inventory remains **432 runtime modules / 63 candidate name
groups**; it now records `eraseAssertions` and `anchoredPrefix`, and reports no
remaining `longestEnd` or `pickCaps` mentions. Inventory:
`/tmp/factoidal-replace-selection-audit.json`. Same-name candidates are search
leads, not confirmed semantic clones.

Verification: untargeted `lake build` **901 jobs passed**; SPARQL 1.1/1.2
**885/885**; SPARQL 1.0 **221 pass / 61 fail**, with identical failure records;
SHACL Core **98/98**, SPARQL **22/22**, node expressions **140 pass / 2 unsupported**,
rules **88/88**; JSON Schema draft-07 **770/770**, no undetermined cases;
fixture-error regressions **3/3**, scanner **5/5**. Build log:
`/tmp/factoidal-replace-selection-build-final.log`; native logs:
`/tmp/factoidal-replace-selection-{wide,10,core,shacl-sparql,nodeexpr,rules,jsonschema}.log`.
Initial failing guards: `/tmp/factoidal-replace-selection-red.log`.
These finite corpora are regression evidence, not full conformance proofs.

Remaining work: `regexMatch` still exposes its legacy F* flag/error policy;
CSVW and ShEx consumers need explicit profile decisions before migration.
Unicode/category semantics and multi-digit capture references remain incomplete.
Ordered-search fuel adequacy, assertion-erasure soundness and worst-case runtime
remain unproved. Numeric casts, ordering/MIN/MAX, XPath binary64 values and other
string metadata callers remain separate reuse opportunities.

## ECMA whitespace reuse and the CSVW dependency mismatch (2026-10-22)

Tracing the remaining legacy consumers exposed a normative dependency error:
CSVW duration formats use ECMAScript, and other nonnumeric/nonboolean/nondate
formats use it too. The Lean duration branch instead calls legacy
`Regex.regexMatch`; other regex formats return `noFormat`. Corrected the map
above and the stale CSVW module comments, which had claimed duration regexes
were absent or specified by XPath. [CSVW §§6.4.5–6.4.6](https://www.w3.org/TR/tabular-data-model/#formats-for-durations)
also requires malformed regex formats to warn and be ignored. The existing
conversion path has only a lexical value and a Boolean validity flag, so a
proper migration needs warning/unsupported propagation through that path.
It has not been migrated in this pass.

Expanded the shared ECMA profile first: `Regex.Ecma.lower` translates `\s`,
`\S`, `\v` and unescaped dot into the existing parser's language. The whitespace
set includes all 25 ECMA whitespace/line-terminator characters; dot excludes
LF, CR, U+2028 and U+2029. Escaped dots/backslashes and class-local dots retain
their meanings. Class expansions protect their boundary endpoints against
adjacent source hyphens. This follows [ECMA-262 11th edition §§11.2–11.3 and
21.2.2](https://www.ecma-international.org/wp-content/uploads/ECMA-262_11th_edition_june_2020.pdf).
XSD and XPath whitespace remain separate. Flagged matching, astral UTF-16
semantics, Unicode escapes, lookaround and other unsupported syntax remain
outside this ECMA profile; no complete ECMA parser claim is made.

```text
JSON Schema pattern / patternProperties / additionalProperties
                             |
                  Regex.Profiles (.ecma2020)
                             |
                    Regex.Ecma.lower
                             |
                  shared parser + derivative matcher

CSVW duration ----> legacy regexMatch       [migration still required]
CSVW other regex formats ----> noFormat     [missing enforcement]
ShEx pattern ----> legacy regexMatch        [F&O 3.1 profile still required]
```

The ShEx edge is distinct: its [string-facet rules](https://shex.io/shex-semantics/#stringFacet)
reference F&O 3.1 and apply to literal lexical forms, IRIs and blank-node labels.
Reusing the execution machinery does not justify imposing ECMA whitespace on
that consumer. Its Boolean pattern API also needs a policy for unsupported
semantics before migration.

Added **24 authored guards**, including JSON Schema property applicability and
cross-dialect checks; **16 fail with the previous profile**. Added **504 static
Node v22.22.2 `RegExp.test` observations**, covering 14 patterns across all 25
whitespace characters and 11 boundary/non-whitespace characters. They include
negated classes and hyphens beside class escapes. These are finite independent
comparisons, not a proof of lowering or full regex correctness. No new axioms,
`sorry`, `native_decide`, partial definitions or FFI were added.

The audit now records the ECMA frontend and legacy consumer identifiers:
**433 runtime modules / 63 candidate name groups**, in
`/tmp/factoidal-ecma-audit.json`. The module count grew by the explicit dialect
frontend, while matching still reuses the same parser and derivative engine.

Verification: untargeted `lake build` **905 jobs passed**; JSON Schema draft-07
**770/770**, no undetermined cases; SPARQL 1.1/1.2 **885/885**; SPARQL 1.0
**221 pass / 61 fail**, identical failure records; scanner **5/5**. Logs:
`/tmp/factoidal-ecma-{build,jsonschema,wide,10}.log`. Focused regression evidence:
`/tmp/factoidal-ecma-red-valid.log` and `/tmp/factoidal-ecma-target.log`.

## CSVW regex migration with shared conversion diagnostics (2026-10-22)

The CSVW migration identified above is now implemented for the supported ECMA
subset. Duration and other regex-valued formats call `applyRegexFormat`, which
uses `Regex.Profiles.matchWith .ecma2020`. String, HTML/XML/JSON and other
nonnumeric/nonboolean/nondate format constraints are now applied. Duration
values additionally use `XSD.validLexicalFor .xsd11` with the actual subtype,
fixing acceptance of `P1Y` as a dayTimeDuration and `P1D` as a yearMonthDuration.
The legacy `regexMatch` call is removed from CSVW.

The integration follows [CSVW §§6.4.5–6.4.6](https://www.w3.org/TR/tabular-data-model/#formats-for-durations):
a nonmatching cell remains convertible as a string, while a malformed regex
format warns and is ignored. Definite delimiter/trailing-escape errors and
leading `*`, `+` or `?` are recognized by `Regex.Ecma.definitelyMalformed`.
Other parser refusals remain **unsupported**, rather than being assumed to be
invalid metadata. This deliberately leaves classification of other malformed
patterns incomplete. The profile is the declared ECMA-2020 subset; CSVW's
undated ECMAScript reference is not a mandate for that particular edition.

```text
CSVW duration / other regex formats --> applyRegexFormat
                                               |
                                     Regex.Profiles (.ecma2020)
                                               |
                                     shared ECMA frontend / engine

CSVW duration subtype ----------------> XSD.validLexicalFor (.xsd11)

format result + facets --> prepareLexical --> CellResult
                                               |
                                        tableRowInputs
                                         /          \
                                    RDF output    JSON output
                                         \          /
                              shared diagnostic collection
                                          |
                                  finishConversion
                         /                          \
                 completed output              no completed output
           warning / invalid cell allowed      unsupported semantics
```

`CSVW.Diagnostics` distinguishes `warning`, `invalidValue` and `unsupported`.
Cell diagnostics carry table URL, source row and column. Regex metadata warnings
are collected once per effective column, including empty/null columns; metadata
validation also checks these warnings at column, schema, table and group levels.
RDF and JSON reuse the same diagnostic collection and completion decision.
Both runners print warnings and count unsupported conversions separately from
passes, failures and missing-fixture skips. This is conversion coverage, not a
claim of complete CSVW validation of suppressed/unused data.

**API change:** `prepareLexical` returns `PreparedLexical` (value plus issues),
and `convert` / `convertJson` return `ConversionResult` (`value?` plus issues).
Callers must inspect the optional output and retained diagnostics. In-tree
callers have been migrated and compile. Two generic kernel-checked laws prove
that `finishConversion` withholds output on unsupported issues and preserves
it otherwise; their only axiom dependency is `propext`. These laws do not prove
the completeness of issue detection or the regex parser.

Added **39 authored guards**; **10 of the first 12 failed** before repair.
They cover regex matches/nonmatches, Unicode dialect differences, structured
string formats, duration subtypes, malformed/unsupported distinction, empty
columns and both output pipelines. A native regression test runs **both runners
against four temporary fixtures each**, checking warning output and the exact
three-pass/one-unsupported split. The upstream bad-format test153 (`+`) now
reports its warning; it previously passed while its format was silently ignored.

Verification: full untargeted `lake build` **909 jobs**; pinned CSVW RDF and JSON
manifests **270/270 each**, no failures/skips/unsupported cases, and no positive
metadata rejected by validation; JSON Schema **770/770**, no undetermined cases;
native diagnostic regression **1/1 (two runner subcases)**; scanner **5/5**.
Logs: `/tmp/factoidal-csvw-regex-{build,rdf,json,jsonschema}.log`; initial failures:
`/tmp/factoidal-csvw-regex-red.log`. Fixtures retain the pinned CSVW revision
`2bc84f937be11d313766ae0892c08c923a5a3799` recorded earlier.

The audit is now **434 runtime modules / 63 candidate name groups**, including
the new diagnostics module (`/tmp/factoidal-csvw-regex-audit.json`). Remaining
reuse targets include ShEx's F&O profile migration and `RIF.Builtins`' lexical
checks: RIF still imports CSVW helpers and performs local duration substring
checks instead of asking the shared XSD service about the actual subtype.
Full ECMA syntax/error classification, other CSVW malformed-format policies,
numeric casts/order and XPath binary64 integration remain open.

## RIF delegates lexical decisions to XSD (2026-10-22)

Removed `RIF.Builtins`' dependency on `CSVW.Formats`. Its `inLexicalSpace` now
delegates to `XSD.validLexicalFor .xsd11`, matching [RIF-DTB Second Edition's
datatype reference](https://www.w3.org/TR/rif-dtb/#Symbol_Spaces). The local
language/name/hex/duration checks and unconditional string-family acceptance
are gone. Base64 validation is now available. Primitive families use XSD's
derivation hierarchy, Boolean parsing uses `XSD.parseBooleanLex`, and decimal
normalization/comparison use the existing exact XSD helpers.

```text
RIF lexical checks ------> XSD.validLexicalFor (.xsd11)
RIF datatype families ---> XSD.Builtin.primitive
RIF Boolean values ------> XSD.parseBooleanLex
RIF numeric lexemes -----> XSD.decimalOrScientific / Dec.canonical / Dec.cmp

RIF --X--> CSVW.Formats   [dependency removed]
```

This rejects month-bearing `P1M` for dayTimeDuration while accepting `PT1M`,
rejects invalid language/name forms, and decides base64 lexical checks that
previously returned unknown. Existing year-zero, +INF, integer bounds and
dateTimeStamp timezone policies are pinned to XSD 1.1. Unknown type names remain
undecided. No XML whitespace preprocessing is added. Finite numeric lexemes are
canonicalized for the current arithmetic/comparison path; binary rounding,
general decimal arithmetic and value-aware casting remain separate work.

Added **33 guards**; **12 of the original 27 failed** before migration. Two
generic theorems establish agreement with the XSD adapter and propagation of
unknown type names; their axiom dependencies are only Lean's standard
`propext`, `Classical.choice` and `Quot.sound`. These prove adapter properties,
not correctness of the shared lexical parser or RIF value semantics.

Verification: untargeted `lake build` **911 jobs**; RIF Core now **25 pass /
2 fail / 12 undecided**, improved from **24 / 2 / 13**. The two failure records
are unchanged; one case remains unread and six import-rejection cases remain
unattempted. The isolated upstream `Builtins_Binary` case now passes with no
undecided result. SPARQL 1.1/1.2 **885/885**; scanner **5/5**. Logs:
`/tmp/factoidal-rif-xsd-{build,before,after,binary,wide}.log`; initial failures:
`/tmp/factoidal-rif-xsd-red.log`. Audit remains **434 runtime modules / 63
candidate name groups**, in `/tmp/factoidal-rif-xsd-audit.json`.

### Observed RIF value-guard gaps after lexical reuse

Probes in `/tmp/factoidal-rif-followup.lean` / `.log` still show:

- `is-literal-integer("1.0"^^xs:decimal)` returns `no`.
- `is-literal-dayTimeDuration("P0M1D"^^xs:duration)` returns `no`.
- `is-literal-not-string(<https://example.org/>)` returns `yes`.

The first two require value-space membership rather than testing the original
spelling against the target lexical grammar. The third incorrectly treats a
negative datatype guard as unrestricted Boolean negation: [RIF-DTB §§4.2–4.3](https://www.w3.org/TR/rif-dtb/#Guard_Predicates_for_Datatypes)
requires membership in some supported datatype's value space. These remain
confirmed implementation priorities, alongside incomplete casts and numeric
semantics; the lexical migration does not claim to resolve them.

## Shared value-space membership: RIF, RDF and OWL proofs (2026-10-22)

The three guard failures recorded above are now repaired. The lexical migration
exposed a second distinction: a datatype's lexical grammar does not decide
whether an already parsed value belongs to it. `XSD.ValueSpace` now owns that
question. RIF guards and RDF's modelled numeric datatype map both consume it;
OWL's two modelled containment proofs use its checked-source mapping laws.

```text
RIF positive/negative guards --+--> XSD.checkedLexicalValue (.xsd11)
                              |        |
                              |        v
                              +--> XSD.valueInBuiltin
                                       ^
RDF.valueInSpace --------------+--------+  via lexicalValueInBuiltin
  |
  +--> RDF.hasRangeClash --> RDFS/D entailment

OWL containment proofs ----------> XSD.ValueSpaceTheorems
                                    checked integer/int mappings
```

Examples now decided correctly include decimal `1.0` in the integer space,
`127.00` in byte, duration `P0M1D` in dayTimeDuration, and zero duration in both
duration subtypes. String membership checks actual whitespace/name/language
restrictions, so `"two  words"^^xs:string` is not a token value. DateTimeStamp
membership checks the parsed timezone. This follows the distinction between
[XSD lexical and value spaces](https://www.w3.org/TR/xmlschema11-2/#value-space).
Primitive tags remain distinct; this service performs no casts or numeric
promotion.

For RDF, this removes an inference error: a decimal `1.0` object constrained by
an integer range used to trigger `hasRangeClash`. The new tests establish that
it no longer does, while fractional `1.5` still clashes when both datatypes
are recognised. The supported RDF datatype map has not been enlarged.

RIF negative guards now apply only within the datatype domain. Lists return
`no` for both positive and negative guards. IRIs, local constants and
uninterpreted applications return `unknown`, because their datatype membership
cannot be inferred from their syntactic form alone. The latter is a conservative
implementation decision based on [RIF-BLD's interpretation of constants and
lists](https://www.w3.org/TR/rif-bld/#Semantic_Structures), alongside the
[negative-guard domain requirement](https://www.w3.org/TR/rif-dtb/#Negative_Guard_Predicates_for_Datatypes).
Invalid XSD source forms also return `unknown` before negation; two earlier
malformed-source tests were updated from `no` to reflect that boundary.
Empty-language PlainLiteral values use the same string restriction checks,
and string values satisfy PlainLiteral membership, matching the
[PlainLiteral value mapping](https://www.w3.org/TR/rdf-plain-literal/#Definition_of_the_rdf:PlainLiteral_Datatype).

The full build caught a related specification/proof defect: OWL's
`XsdValueSpaceSubset` quantified over every literal carrying the source datatype
IRI, without requiring an actual source value. Its premise now requires source
membership. The integer-to-decimal and int-to-integer proofs were restored using
shared mapping lemmas; malformed labelled constants no longer acquire values
through an unconditional containment claim. Other OWL datatype-map assumptions
remain assumptions.

Added **53 guards**, including the RDF range-clash integration cases and an
11-input RDF/RIF agreement check; **14 of the initial 20 guards failed** before
repair. Six new generic theorems cover decimal/duration membership, refused
source propagation, checked integer/int mappings and the RIF list-domain rule.
The two existing OWL containment theorems have the corrected premise. Axiom
audits use only `propext`, `Classical.choice` and `Quot.sound`; there are no new
user axioms or proof placeholders. These properties are not a proof of complete
XSD parsing, datatype membership or RIF entailment correctness.

Remaining boundaries are explicit: QName/NOTATION need namespace context;
list/universal XSD types and the provisional precisionDecimal representation
remain undecided by this service. RIF's language-tagged PlainLiteral and
XMLLiteral branches still assume valid constants; complete BCP 47 validation
and canonical XML lexical validation remain open. Existing support for XSD
names beyond the RIF core list is an implementation extension, not a claim that
every XSD built-in is a required RIF datatype.

The next probes confirm a separate identity/conversion cluster:
`literal-not-identical(1^^integer, 1.0^^decimal)` and the Boolean pair
`true`/`1` both still return `yes`; integer casting of decimal `1.0` and decimal
`1.5 + 2.5` still return no result. Evidence:
`/tmp/factoidal-value-guards-followup.lean` / `.log`. The identity repair should
reuse XSD value identity with RIF domain handling, preserving the distinction
from RDF term identity. The `RIF.Syntax` header's claim that the built-in compares
lexical/datatype pairs also needs correction with that repair. Numeric casts,
IEEE comparison and general decimal arithmetic remain open.

Verification: full untargeted `lake build` **916 jobs**; RDF rdf-mt **39/39**;
SPARQL 1.1/1.2 **885/885**, both with no failures/skips/unsupported results.
RIF Core remains **25 pass / 2 fail / 12 undecided**, with the exact same two
failure records; one unread and six unattempted import-rejection cases remain.
Scanner tests **5/5**; inventory **435 runtime modules / 63 candidate name
groups**. The new `XSD.ValueSpace` entry records direct RDF and RIF consumers;
counts remain discovery leads, not semantic clone counts. Logs:
`/tmp/factoidal-value-guards-{build,rif,rdf,sparql,owl,proofs}.log`,
`/tmp/factoidal-value-guards-red.log`, and
`/tmp/factoidal-value-guards-audit.json`.

## RIF value identity and XSD enumeration policy (2026-10-22)

RIF's `literal-not-identical` now compares decoded datatype values using the
shared `XSD.valIdentical`. The same `literalValue?` decoder serves datatype
guards and identity, removing another parallel interpretation of constants.
Integer `1` and decimal `1.0`, Boolean `true` and `1`, alternate hex case,
equivalent duration spellings and rounded float values now compare by value.
Primitive spaces stay distinct, as do positive/negative floating zero; NaN is
identical to itself. These choices follow [RIF-DTB §4.1.1](https://www.w3.org/TR/rif-dtb/#Comparison_for_Literals).

Empty-language PlainLiteral decodes to a string, while language-tagged values
compare text and lowercase language tags. Lists are outside the datatype domain
and make literal-not-identical false in either argument position. Unknown or
invalid source mappings remain undecided. XMLLiteral identity now returns
unknown instead of inferring distinct values from different spellings; canonical
XML identity is not yet established. As with the guards, complete language-tag
validation remains an explicit precondition/gap.

Reviewing the shared implementation exposed two more policy errors. Date/time
identity used timeline equality, erasing timezone offsets. It now compares the
seven properties, with decimal seconds normalized. XSD 1.1 explicitly separates
[equal instants from identical date/time values](https://www.w3.org/TR/xmlschema11-2/#dateTime).
The previous XSD test asserting identity for `12:00-05:00` and `17:00Z` was
corrected; a separate check retains their equality.

Enumeration needs a different relation: [XSD §4.3.5.4](https://www.w3.org/TR/xmlschema11-2/#rf-enumeration)
accepts values that are equal **or** identical. Atomic, list and union validation
now use `valEqualOrIdentical`, so equal instants with different offsets and both
floating zeros remain admissible, and NaN can enumerate itself. Both shared
relations compare list items recursively and handle singleton-list/atomic
correspondence. This fixes behaviour rather than merely renaming the old helper.

```text
RIF guard ------------+
                      +--> RIF.literalValue? --> XSD.checkedLexicalValue
RIF literal identity -+          |
                                 +--> XSD.valIdentical
                                         |
                                         +--> date/time properties + timezone

XSD atomic/list/union enumeration ------> XSD.valEqualOrIdentical
                                          identity OR datatype equality
RDF term identity ---------------------> RDF.sameTerm (separate operation)
```

Added **51 guards**, covering datatype identity, boundary decisions, atomic/list/
union enumeration and three rule-engine cases. A rule guarded by non-identity
no longer fires for integer `1` versus decimal `1.0`; it fires for `1` versus
`2.0`, and remains undecided for an invalid decimal source. Five generic laws
cover XSD delegation, both list-domain positions, timezone preservation and
date equality admitted by enumeration. They use only standard Lean foundations,
not new user axioms; they do not establish complete identity/parser correctness.
The misleading pair-comparison descriptions in RIF syntax/tests were corrected.

A separate gap remains in ordinary RIF equality and matching: `Engine.extend`,
`matchTm` and the `.equal` branch still use syntactic `GTerm` equality. The
literal-identity built-in repair does not claim to repair those paths or the
complete rule-model semantics. RDF-to-RIF conversion is also duplicated between
`Saturate` and the native harness; the former's empty-tag PlainLiteral reverse
mapping still needs review. These are concrete next integration targets alongside
value-aware casts, general decimal arithmetic and IEEE numeric comparison.

Follow-up probes in `/tmp/factoidal-rif-identity-followup.lean` / `.log` confirm
that ordinary equality and repeated-variable binding reject integer `1` versus
decimal `1.0`. They also show empty-tag PlainLiteral converting back to an RDF
`langString` with an empty tag, rather than the string value established by the
shared decoder. These observations narrow the next reuse/integration pass.

Verification: full untargeted `lake build` **919 jobs**; combined RDF rdf-mt and
SPARQL 1.1/1.2 manifests **924/924**, no failures/skips/unsupported cases. RIF
Core remains **25 pass / 2 fail / 12 undecided**, identical failure records,
one unread and six unattempted import-rejection cases. Scanner **5/5**;
inventory **435 runtime modules / 63 candidate groups**. The audit now tracks
identity and enumeration-policy identifiers separately. Logs:
`/tmp/factoidal-rif-identity-{build,target,proofs,rif,wide}.log`; inventory:
`/tmp/factoidal-rif-identity-audit.json`. These upstream suites do not amount to
full XSD validation-suite coverage; the new XSD cases are executable Lean guards.

## RIF matching and one RDF conversion boundary (2026-10-22)

`RIF.Matching.groundMatch` now supplies the common value-aware decision for
ordinary equality, ground-pattern matching and repeated-variable joins. It
uses the same decoded values as literal-identity built-ins. Equivalent integer/
decimal and Boolean spellings now join; lists and congruent function arguments
compare recursively. Distinct floating zeros and date/time offsets retain the
identity policy established in the previous pass.

This is an operational matcher for the current engine, without equality-producing
heads. A `no` result for different free IRI/local symbols means no match in that
model; it does **not** assert a general RIF unique-name assumption. Unknown
mappings produce an unresolved result, carried through `extend`, `matchTm` and
`.equal` to the existing blocked/undecided path. `extend` now returns an optional
substitution plus that flag. Equality can bind either side from a grounded term;
list/function patterns can bind internal variables. Two ungrounded equality sides
remain undecided. Unsupported equality/external-predicate heads now mark the
closure incomplete instead of being silently ignored. General equality-head
reasoning and a proof of engine adequacy remain open. The relevant specification
boundary is [RIF Core semantics and restrictions](https://www.w3.org/TR/rif-core/#RIF-Core_Semantics).

The native RIF runner and SPARQL-facing saturation path now import
`RIF.RdfMapping`, replacing the runner's separate term/triple conversion code.
`Saturate` re-exports its existing names. PlainLiteral reverse conversion uses
`literalValue?`, so `hello@` becomes an RDF string and nonempty tags are
lowercased. The conversion rules remain tied to the
[RIF/RDF compatibility mapping](https://www.w3.org/TR/rif-rdf-owl/#RDF_Compatibility).

```text
RIF.Engine: equality / joins / patterns
                |
                v
          RIF.Matching ------> RIF.literalValue? ------> XSD values / identity

Harness.RifRun ------+
                     +-------> RIF.RdfMapping --------> RIF.literalValue?
RIF.Saturate --------+                  |
                                       +--> RDF terms / frames / membership
```

Added **43 guards**; all **10 initial regression guards failed** before repair.
Coverage includes repeated-variable joins, ground equality, bindings in either
direction and inside lists, unknown propagation, rule conclusions, RDF frame
round trips and the saturation output for an empty-tag PlainLiteral. Three
generic kernel-checked laws establish matcher reflexivity, known-mismatch
conjunction handling and unresolved-result preservation. They use only standard
Lean foundations; this is not a proof of complete RIF matching semantics.

Verification: full untargeted `lake build` **925 jobs**; RDF/SPARQL manifests
**924/924**, no failures/skips/unsupported cases. RIF Core remains **25 pass /
2 fail / 12 undecided**, one unread and six unattempted import-rejection cases.
Scanner **5/5**; inventory **437 runtime modules / 63 candidate groups**.
The audit records both consumers of the new RDF mapping module. Logs:
`/tmp/factoidal-rif-matching-{build,target,proofs,rif,wide}.log`; initial failures:
`/tmp/factoidal-rif-matching-red.log`; inventory:
`/tmp/factoidal-rif-matching-audit.json`.

### Newly verified boundary/reporting defects

Historical findings from the matching pass; the following boundary pass repairs
these reporting and mapping defects. The fixture itself remains unchanged.

`RDF_Combination_Constant_Equivalence_4-import001.ttl` declares the relative
prefix `<www.w3.org/2001/XMLSchema#>`. The runner parses without a base, yielding
an invalid-IRI error for its datatype. `Harness.RifRun` currently discards Turtle
parse errors and subsequently reports a negative entailment result against the
missing import. The fixture remains unchanged; the recorded failure is not
explained by the identity implementation. Import errors need explicit reporting
and import/base resolution needs a separate review.

The shared RDF-to-RIF mapper also still drops RDF 1.2 direction: a directional
`"hello"@en--ltr` becomes ordinary `hello@en` PlainLiteral. It must either preserve
that extension through an explicit representation or report it unsupported;
sharing the old mapper does not repair the policy. Both observations are
executable probes in `/tmp/factoidal-rif-matching-followup.lean` / `.log`.
`Saturate.saturateGraph` also still drops blocked/capped closure flags, so the
SPARQL-facing result API needs the same completeness discipline as the native
RIF runner. Casts, arithmetic and broader RIF datatype support remain open.

## RIF import and completeness reuse (2026-10-22)

Two consumers of the same RIF engine had separate import-loading code and
different ways of losing errors. Native RIF silently discarded import parse
failures and loaded every adjacent Turtle file; SPARQL/RIF also replaced failed
imports with an empty graph. SPARQL then discarded the engine's blocked and
round-limit flags. A negative answer could therefore look successful even when
the rules or imports had not been fully evaluated.

`Harness.RifImport` now owns local fixture resolution and parsing for both
runners. Only declared imports are loaded; missing, unreadable and malformed
files produce diagnostics. The declared import URL supplies the parser's base.
Resolution remains a local fixture convention, with no network fetching: `.rdf`
locations prefer that file and can use a converted `.ttl` sibling; extensionless
locations try `.rdf`, `.ttl`, then the literal basename.

The native suite's bare conclusions inherit prefix names from imports by suite
convention. The shared loader now obtains Turtle bindings from the actual parser
state, including multiline/SPARQL-style declarations, relative namespace IRIs
and shadowing. RDF/XML uses `XML.scopeAtPath` and `XML.visibleBindings` at the
document root. This removes the separate line-based Turtle prefix scanner and
reuses the substantive XML Namespaces implementation across another boundary.
Root XML bindings and final Turtle bindings are fixture conveniences, not a
general definition of namespace scope for RIF imports.

```text
Harness.RifRun --------+
                      +--> Harness.RifImport --> Turtle parser + prefix state
Harness.Run (SPARQL) --+          |
                                 +--> RDF/XML parser
                                 +--> XML.NamespaceView --> XML.Namespaces

RDF graph --> RIF.RdfMapping --> RIF.Engine.closure
                 |                       |
         unsupported input         blocked / round limit
                 |                       |
                 +----> RIF.Saturate.Result <---- failed RDF output conversion
                                  |
                           completeGraph?
                                  |
                           SPARQL evaluation
```

`Saturate.saturateGraph` now returns a `Result`, retaining the partial graph and
four flags: blocked operations, exhausted rounds, unsupported RDF input and
unsupported RDF output. `completeGraph?` supplies a graph only when every flag
is false. All in-tree consumers were migrated, including the executable
`Unified.RifEmbed` comparison. `saturateWithProgram` returns `Option Result`;
`none` still means XML parsing failed. These are intentional public API changes.
The partial graph remains available for diagnostics, and should not be used to
answer queries. Completeness here is relative to the implemented engine and
mapping; it is not a proof of full RIF semantic adequacy.

The shared RDF mapper rejects direction-bearing literals instead of erasing
their direction. Graph checks also detect RDF triple terms, which this RIF
representation cannot encode. Failed conversions of derived frames, memberships
or subclass atoms prevent a complete result; positional RIF atoms intentionally
have no RDF projection and do not cause that failure. Native RIF reports an
unsupported input mapping as undecided. SPARQL reports an incomplete saturation
or unusable import as unsupported, before evaluating the query.

Added **21 build-time guards**, **three generic kernel-checked laws** and **eight
native regression tests** using temporary fixtures. The native tests include
seven RIF cases for declared imports, failure diagnostics, relative IRIs, prefix
bindings and ignored undeclared files; seven SPARQL/RIF tests cover empty inputs,
valid empty imports, missing/malformed imports, blocked rules, round exhaustion
and unrepresentable output. The laws establish direction rejection and the
result accessor's completeness gate, using only standard Lean foundations.
These checks are not a complete RIF conformance or engine-adequacy proof.

Verification: full untargeted `lake build` **929 jobs**; native regressions
**8/8**; RDF/SPARQL **924/924**, zero failures/skips/unsupported cases. RIF Core:
**25 pass / 1 fail / 13 undecided**, one unread and six unattempted
import-rejection cases. `RDF_Combination_Constant_Equivalence_4` moves from fail
to undecided: its relative datatype prefix now resolves against the import URL,
yielding an unsupported datatype rather than a silently discarded import. This
is a reporting correction, not a newly passing conformance case.
`EBusiness_Contract` remains the decided failure.

The scanner passes **5/5** and inventories **438 runtime modules / 63 candidate
groups**. It now records harness-to-harness imports, including both consumers of
`Harness.RifImport`; candidate groups remain leads for semantic review, not a
count of proven duplicates. Logs: `/tmp/factoidal-rif-boundary-{build,native,rif,wide}.log`;
inventory: `/tmp/factoidal-rif-boundary-audit.json`.

Next reuse targets remain RIF casts and numeric operations against shared
XSD/Fn machinery, followed by import-profile policy. Profile materialization was
preserved in this pass: native RIF leaves OWL profiles undecided; the SPARQL
harness retains its existing OWL RL approximation and RDF/RDFS handling. Those
policies are not interchangeable and still need explicit capability boundaries.
Full XMLLiteral identity, BCP47 validation and broader RIF semantics remain open.

## RIF numeric operations share XSD/F&O values (2026-10-22)

The next duplication audit found observable differences: RIF's `addDec`,
`subDec` and `mulDec` parsed integers despite their decimal names; signed
integer division/modulo used Lean's Euclidean operations; comparisons read
unrounded decimal spellings of IEEE values. `numeric-divide` and the standard
`numeric-mod` name were absent. Ten initial regression guards failed against
those implementations.

[RIF-DTB §4.5](https://www.w3.org/TR/rif-dtb/#Numeric_Functions_and_Predicates)
adapts numeric operations from F&O. The implementation now follows that reuse
boundary: `RIF.numericValue?` decodes through the existing checked XSD value
adapter; numeric predicates call `Fn.Comparison.numericCompare`; numeric
functions call `Fn.Arithmetic`. Shared promotion handles decimal, binary32 and
binary64 values. NaN, infinity and signed zero no longer fall through a decimal
lexical parser. Result serialization retains the primitive numeric type.

`Fn.Arithmetic` now also supplies decimal arithmetic, truncating integer division
and remainder. Decimal addition/subtraction/multiplication are exact; decimal
division accepts a fractional-place budget. RIF selects a magnitude-sensitive
budget providing at least 16 significant digits, truncating toward zero, so
very small decimal quotients are not rounded away merely by a fixed scale.
SPARQL's decimal path shares the arithmetic while retaining its existing
ten-fractional-place division policy and expression-layer lexical formatting;
its integer-only fast path is unchanged. Those precision/formatting policies
belong to the callers and are not conflated.

For integer division, decimal operands use an exact ratio; floating operands
divide at their promoted precision before truncation. Floating remainder uses
an exact truncating quotient and preserves the dividend's zero sign. These are
distinct F&O operations, not interchangeable uses of host `/` and `%`.
RIF accepts the standard `numeric-mod` name and retains `numeric-integer-mod`
as the historical native-suite alias. Unsupported operands and domain errors
still return no decided function result.

```text
RIF constants --> RIF.literalValue? --> XSD checked values
                        |
                  RIF.numericValue?
                        |
        +---------------+-------------------+
        v                                   v
Fn.Comparison.numericCompare          Fn.Arithmetic
        ^                              ^        ^
        |                              |        |
SPARQL / SHACL                    SPARQL      Fn.NumericUnary

caller policies: source edition, result type/spelling, decimal division precision
shared operations: promotion, IEEE rounding, comparison, decimal arithmetic
```

Added **49 RIF guards**, covering numeric predicates, arithmetic,
negative quotients/remainders, promotion, IEEE rounding, invalid/derived
datatypes, tiny decimal quotients and actual rule matching. **24 independent
CPython quotient/remainder vectors** compare integer results and IEEE bit
patterns in two additional guards. Four generic kernel-checked laws establish
comparison delegation, invalid-operand propagation and decimal zero-divisor
rejection; they use only standard Lean foundations. These do not constitute a
complete proof of arithmetic or RIF engine adequacy. Existing floating arithmetic
oracle tests and SPARQL expression tests remain part of the full build.

Remaining confirmed duplication: RIF casts still inspect only lexical spelling.
Probes of decimal `1.9` to integer and integer `2` to boolean return `none`,
despite available shared numeric value/conversion machinery. Evidence:
`/tmp/factoidal-rif-numeric-followup.lean` and `.log`. Cast source/target policy
is the next integration task. The remaining `EBusiness_Contract` fixture also
binds `xs:date` values and requires `is-literal-dateTime`; the probe correctly
rejects that guard. The fixture remains unchanged, and date arithmetic must not
be made to accept that type mismatch merely to improve the score.

Verification: full untargeted `lake build` **932 jobs**; RDF/SPARQL **924/924**;
native boundary regressions **8/8**. RIF Core improves to **26 pass / 1 fail /
12 undecided**, one unread and six unattempted import-rejection cases.
`Builtins_Numeric` is the newly passing case; the remaining decided failure is
`EBusiness_Contract`. Scanner **5/5**, inventory **438 runtime modules / 64
candidate groups**. The additional candidate is `numericResult`: RIF and SPARQL
intentionally adapt shared values to different output types. It is a useful
example of why same-name groups are review leads, not duplicate-implementation
counts. The inventory now records RIF as a consumer of both `Fn.Arithmetic` and
`Fn.Comparison`. Logs: `/tmp/factoidal-rif-numeric-{red,target,proofs,format,build,rif,wide,native}.log`;
audit: `/tmp/factoidal-rif-numeric-audit.json`.


## Shared value-aware casts (2026-10-22)

`Fn.Cast` now supplies conversions over checked XSD values for RIF and SPARQL's
four numeric constructors. The source datatype is decoded before conversion;
lexical recognition alone cannot implement decimal `1.9` to integer `1`, or
integer `2` to Boolean `true`. All ten initial RIF regression guards failed
before this change.

```text
RIF constants ----> RIF.literalValue? ------+
                                           |
SPARQL operands --> EvalResult.castValue? --+--> Fn.Cast.cast
                                                  |
                                   XSD.ValueSpace + Fn.Arithmetic
                                                  |
                                    target value/facet validation
                                                  |
                         RIF / SPARQL result spelling and error policy
```

The shared layer covers supported numeric/Boolean conversions, binary byte
retagging, duration projections and calendar projections. Numeric-to-integer
casts truncate toward zero and enforce the target subtype's bounds. Finite
binary-to-decimal conversion is exact. Source float precision is retained before
promotion. String sources apply the target whitespace rule before parsing;
invalid source values and unsupported conversions return `none`. RIF uses the
XSD 1.1 edition; SPARQL numeric constructors use XSD 1.0 with their retained
`+INF` string extension. SPARQL keeps a legacy floating spelling only when it
decodes to the same converted value.

The normative bridge is [RIF-DTB §4.4.1](https://www.w3.org/TR/rif-dtb/#Casting_to_XML_Schema_Datatypes)
and [F&O 2007 §17](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting).
QName/NOTATION require namespace context. List, universal and precisionDecimal
targets remain unsupported; time-to-dateTime needs dynamic context and is refused.
SPARQL's string and general calendar constructor paths have not migrated to this
module. Broader independent checks of subnormal narrowing and floating string
minimality remain necessary; the selected guards are not full cast conformance.

Added **54 RIF guards**, **19 SPARQL guards**, and **four generic laws** covering
successful target membership, unsupported targets and nonfinite decimal
conversion. The laws use only standard Lean foundations; they do not prove all
conversion clauses against the specification. No new user axioms, `sorry`,
`native_decide`, partial definitions or FFI were introduced.

Verification in the original working checkout: full untargeted `lake build`
**937 jobs**; RDF/SPARQL **924/924**, zero failures/skips/unsupported cases;
native RIF boundary regressions **8/8**. RIF remains **26 pass / 1 fail /
12 undecided**, one unread and six unattempted import-rejection cases.
`EBusiness_Contract` remains the decided failure. Scanner **5/5**; the inventory
has **439 runtime modules / 64 candidate groups**, and records both `Fn.Cast`
consumers. These inventory numbers include the separate hash-grouping work in
that checkout; the draft PR excludes it. Logs: `/tmp/factoidal-cast-build.log`,
`/tmp/factoidal-cast-target.log`, `/tmp/factoidal-cast-rif.log`,
`/tmp/factoidal-cast-wide.log`; inventory: `/tmp/factoidal-cast-audit.json`.


The isolated draft PR subsequently passed its full build (**932 jobs**),
RDF/SPARQL **924/924** and all four native/scanner Python regression scripts
(**17 tests**). Its inventory is **438 runtime modules / 64 candidate groups**,
excluding the independent hash-grouping module. RIF counts are unchanged. See
[the review record](20261022-standards-reuse-review.md#isolated-pr-validation)
for commands, exact scope and mainline integration limits.
