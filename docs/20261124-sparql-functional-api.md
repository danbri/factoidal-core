# Functional SPARQL API: initial step

The parser produces `SPARQL.Query` in `Expr.lean`, and the evaluator uses that
same AST. `FunctionalQuery.lean` adds pure transformations of its pattern and
solution modifiers, with identity, composition, and commutation theorems. It
compiles with the pinned Lean 4.33.1 toolchain. Arbitrary changes are not
validated or automatically semantics preserving.

The planned public representation should provide complete, versioned, lossless
structured data plus textual and programmatic s-expressions, all decoded to the
actual Lean AST. Parsing, printing, traversal, transformations, execution, and
validation belong in Lean; JS/WASM adapters should marshal the same values.
Input errors and resource limits must be explicit. Printing and parsing must not
perform SERVICE requests. Preserve comments and original source separately:
semantic AST round trips cannot promise lexical fidelity.

Existing `Query.toSse` is a diagnostic format, not a lossless codec: it omits
VALUES rows, aggregate details, and query fields. A general SPARQL printer does
not yet exist; the existing ASK/BGP round trip is restricted. Do not promote
this format to a public interchange format or claim complete round-trip support.
Include SPARQL versions, query and update, literal datatypes and languages,
datasets, grouping, ordering, limits, scope, EXISTS, SERVICE, subqueries and
paths. Add constructor coverage, `decode(encode(q)) = q` proofs where feasible,
parser/printer round-trip tests and native/WASM differential tests. Leana can
consume the resulting API rather than reimplementing RDF/SPARQL semantics.

## Corpus observation, 24 November 2026

`lake env lean --run Wikidata/MartinPoulterProbe.lean` processes the 579
harvested original queries with `parseSparql ... none .v11`: 0 accepted,
579 rejected, including 555 generic unresolved-prefix diagnostics, 1 explicit
unresolved prefix and 23 expected-lbrace errors. This is not a SPARQL
conformance score: WDQS supplies default prefixes and supports extensions.
The probe intentionally adds none; the diagnostics can be affected by those
missing prefixes. Add an explicit WDQS prefix environment and preserve authored
prefix precedence before analysing support; never count these results as an
assertion that the corpus is invalid. No query was executed on a data store.
