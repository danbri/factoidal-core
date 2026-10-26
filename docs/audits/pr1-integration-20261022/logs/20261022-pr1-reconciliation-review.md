# PR1 reconciliation review — 2026-10-22

Read-only review of the in-progress `integrate-pr1` reconciliation, based on
`87af61c9b7398ed1effa65744cbd3c84afe311be` and incoming PR1
`ed19f0905781008d12275c6fbbff257cb77f044a`. The integration agent owns edits,
builds and runtime probes. No build or product-file edit was performed by this
reviewer. Arithmetic and regex are assigned elsewhere.

## Findings sent to the integration agent

1. **Introduced XPath namespace-uri regression.** At review time,
   `XPath/Eval.lean:141–153` resolves only element/attribute kinds, but sends
   every kind except PI through the failed-resolution sentinel fallback.
   `evalCall` at lines 513–515 exposes that as `" unbound:"`. Main returned
   the empty namespace for other kinds. On `<r>text<!--c--></r>`, independent
   probes should expect `""` from `namespace-uri(/)`,
   `namespace-uri(/r/text())`, `namespace-uri(/r/comment())` and
   `namespace-uri(/r/namespace::xml)`. Reserve the unbound sentinel for failed
   element/attribute resolution and preserve empty namespace for other kinds.
   This is source-derived, not a claimed execution result in this review.
   [XPath 1.0 §4.1](https://www.w3.org/TR/1999/REC-xpath-19991116/#function-namespace-uri)
   specifies empty namespace URI for node kinds other than elements/attributes.

2. **Incoming RIF completeness contract omitted during reconciliation.**
   `Harness/RifRun.lean:65–100` retained main's local RDF mapping copies;
   the ordinary entailment path around lines 399–405 omitted PR1's
   `graphMappingSupported` refusal. Incoming PR1 imports/opens
   `RIF.RdfMapping`, while the library saturation adapter already uses that
   shared implementation. Restore the shared mapping and the ordinary RDF
   completeness guard, preserving main's separate OWL-Direct dispatch.
   Current import parsing uses RDF 1.1, so unsupported direction/triple-term
   input may already fail at the parser: no current-corpus false verdict is
   asserted. This is an omitted contract and duplication hazard.

3. **New input-proportional non-tail sibling traversal.**
   `XML/NamespaceView.lean:43–48` recursively obtains the remaining siblings
   and then constructs `first :: remaining`. This adds an unbounded call stack
   to namespace-adapted MathML, Schematron and SPARQL XML result parsing. It
   conflicts with the repository's input-loop rule. Replace it with a tail
   accumulator/reverse traversal or a proved compiled twin. A broad sibling
   stress input should also run on Wasm. No stack overflow was measured here.

## Preserved capabilities and bounded checks

- `XML/Document.lean`, `XML/Namespaces.lean` and `XML/Parser.lean` were compared
  byte-for-byte with base `87af61c` and were unchanged.
- XPath retains main's document identities and resolves names through the
  owning document; this review found no dropped document-ID declaration.
- Main RIF import-rejection handling, local override/stale-override accounting,
  RDF-only conclusions and OWL-Direct dispatch remain present.
- A declaration/match-arm comparison found no deleted main named built-in
  match arm in `RIF/Builtins.lean`; the temporal, string and list functions
  remain. This is inventory evidence, not a semantic equivalence proof.
- The date-vs-dateTime guard change was checked against the primary RIF-DTB
  specification rather than accepting main's old comment as authority.
  [RIF-DTB §2.3](https://www.w3.org/TR/rif-dtb/#Datatypes) delegates the XSD
  value spaces to XML Schema; keeping the old ad-hoc date/dateTime identity
  solely for a fixture would not follow from that comment.

## Preexisting limitation, not a PR1 regression

`XSLT/Transform.lean:671–674` adds `xmlns=""` only when the copied root is
unprefixed. A prefixed root can also carry unprefixed descendants: copying
`<p:x xmlns:p="urn:p"><y/></p:x>` beneath `<out xmlns="urn:out">` without an
empty-default declaration changes the namespace of `y` when serialized XML
is reparsed. Main already lacked that fixup. The integration agent was told
to classify this as a follow-up limit, rather than an introduced regression.

## Reviewed snapshot hashes

These files are being edited by the integration agent; hashes identify this
review's latest read, not a final commit or approval of a later revision.

- `formal/lean4/L4Factoidal/XML/NamespaceView.lean`: `0cfcc56b2c0510e103db3d0dcd1bba5e25689368f8c15092e7b23dd63ac692c5`
- `formal/lean4/L4Factoidal/XPath/Eval.lean`: `8f4c1cc59ca374ad61f68dee59b5c20420ce58689e3d6d3f2defa396ca9a66c8`
- `formal/lean4/Harness/RifRun.lean`: `aa0db8573ea73a5ba8da31fb5af8cc95ae3c460a92c90719bfc9924fdcba17ba`
- `formal/lean4/L4Factoidal/XSLT/Transform.lean`: `fa435e3c8e73edfaf055db2475c148aa87280c829b3f452471f6c4b325527806`
