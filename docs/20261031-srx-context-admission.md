# Checked SRX admission to the public XQuery context loader

`SPARQL.ResultsXmlRouting` adds `QueryResult.toSrxReport`. It serializes the
result once with the existing `toSrx`, invokes `XPath4.Doc.ofString` once, and
routes that cached outcome through `Dataflow.Stage.choose`. The cache includes
an equation binding the outcome to the exact serialized text. Refusal does not
remove, replace, or rewrite RDF lexical data.

The accepted constructor `.xml text doc proof` retains the exact emitted text,
the parsed XDM document, and a proof of `Doc.ofString text = .ok doc`. The
refused constructor `.diagnostic message` retains the loader's original error.
Public adapters can project this to `{kind:"xml",xml:text}` or
`{kind:"diagnostic",code:"XML_ADMISSION_REFUSED",message}`. The parser can
refuse reasons other than invalid characters, so the diagnostic code does not
claim that every refusal is a character error.

The production theorems are:

- `QueryResult.toSrxReport_exact`: an accepted production report emits the
  original `result.toSrx` text.
- `QueryResult.toSrxReport_accepted`: observing accepted text yields both its
  actual `Doc.ofString` acceptance witness and its identity with `result.toSrx`.
- `QueryResult.toSrxReport_refused`: the reported error is the actual loader
  failure on the original serialization.

These statements concern this parser boundary, not SRX schema validity, RDF
round trips, or acceptance by another XML implementation. `Doc.ofString` calls
`XML.parseXML` and `Doc.ofDocument`; it does **not** check namespace
well-formedness. In particular, the existing directional-literal serialization
uses an undeclared `its:dir` prefix and this context loader accepts it. A guard
records that limitation. XML parsing also normalizes line endings and attribute
values; no lexical preservation through parsing is claimed. The accepted text
itself remains unchanged.

## Validation

On 2026-10-31, Lean 4.33.1 compiled both new modules with twenty passing guards.
The guards cover ASK and empty SELECT, escaping and supplementary characters,
legal XML whitespace, forbidden C0 characters and U+FFFE/U+FFFF, variable-name
attribute content, and the namespace limitation above. All three production
proofs audit to the standard `propext`, `Classical.choice`, and `Quot.sound`
axioms only.

To avoid copying the large build cache, compilation used a private output
overlay `/private/tmp/srx-routing-overlay`, with read-only symlinks to existing
compiled dependencies in `factoidal-composition-proofs` and the current
`factoidal-routing` Conditional module. Both commands ran with the shared
`/private/tmp/depmap-qt4-lake.lock` held and explicit `formal/lean4` cwd:

```
LEAN_PATH=/private/tmp/srx-routing-overlay lean -o /private/tmp/srx-routing-overlay/L4Factoidal/SPARQL/ResultsXmlRouting.olean L4Factoidal/SPARQL/ResultsXmlRouting.lean
LEAN_PATH=/private/tmp/srx-routing-overlay lean -o /private/tmp/srx-routing-overlay/L4Factoidal/SPARQL/ResultsXmlRoutingTests.olean L4Factoidal/SPARQL/ResultsXmlRoutingTests.lean
```

This is focused source validation; the public dispatcher, npm decoding, and
compositor integration are separate changes. No package build, workflow
dispatch, fixture modification, or catalog exclusion was performed here.
