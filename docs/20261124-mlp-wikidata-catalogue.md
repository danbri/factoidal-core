# Martin Poulter’s Wikidata query catalogue

The catalogue covers 580 SPARQL queries from the pinned main user page and its
14 subpages. It preserves the earlier order and source text for records
`mlp-001` through `mlp-579`. The last record recovers the query under the
“Wikipedia articles about objects on the register” heading in the collections
subpage. Its template is misspelt `SPARFQL` in the source, so the earlier
`SPARQL`/ `SPARQL2` harvest missed it. All 580 are SELECT queries.

The catalogue stores the title, domain, section path, query form, feature tags
and provenance for every query. The domain follows the page hierarchy. The
query form and feature tags use lexical heuristics. Each record links its
Wikidata revision and history, and its character offset locates the unchanged
text in the captured wikitext. The catalogue carries the Wikidata page text’s
CC BY-SA 4.0 attribution to Martin Poulter and the Wikidata contributors.

- `original_query` preserves the exact extracted wikitext.
- `classic_query` expands the `{{!}}` wiki escape and replaces
  `[AUTO_LANGUAGE]` in `wikibase:language` parameters with an explicit language
  tag. The default is `en`. `classic_query_template` retains the language
  placeholder for an interactive language selection.
- `replacement_query` contains the output from the original Wikimedia Java
  rewriter with the explicit language. `replacement_query_template` uses the
  Java rewriter’s output for the input with the language placeholder retained.
- `lean_replacement_query` contains the output from Factoidal’s Lean rewriter
  with the explicit language. `lean_replacement_query_template` runs the same
  rewriter with the reserved tag in `lean_language_marker` for an interactive
  language selection.
- Each engine’s rewrite status, rule trace, errors and warnings are recorded
  separately. A missing replacement is JSON `null`; an unchanged status can
  still supply query text. Optional parse observations use Lean’s WDQS-prefix
  parser for the raw source, prepared classic text and Java output.

A lexical scan found no other query-shaped lines outside these templates.
The extraction covers the captured revision set and does not chase links or
render arbitrary MediaWiki templates. The workbench uses the first 100
historical records, which are an exact slice of the full catalogue.

Run from the repository root after compiling the Lean rewriter in
`formal/lean4` with `lake build L4Factoidal.Wikidata.Rewrite`.

```bash
python tools/wikidata/build_mlp_catalogue.py \
  --jar /path/to/sparql-rewriter.jar \
  --out mlp-all-queries.json \
  --first-100-out mlp-first-100.json \
  --with-lean
```

The generator uses the pinned repository snapshots and local engines, and does
not request or compare live endpoint results. It checks snapshot and Java
response hashes. The output records the source snapshot, JAR and Lean source
fingerprints so different runs can be identified.

## Lean rewrite coverage

The first Lean implementation follows the original engine's stage order. It
removes Blazegraph query hints and rewrites `wikibase:isSomeValue` before
parsing. After parsing it handles the known scholarly subgraph endpoint and
scalar label and description lookups in one outer label service. It emits
standalone SPARQL for a rewrite and validates it with Factoidal's standard
parser. Scoped labels, alias aggregation, and prebound output mappings still
require the corresponding upstream binding and candidate-subquery logic.
Named subqueries, geospatial rewrites, GAS, bd:slice, bd:sample and date/time
rewrites remain to be ported. The Lean comments link to the matching upstream
Java source pinned at `e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74`.

The entry point is `L4Factoidal.Wikidata.rewriteQuery`. The npm adapter
`wikidataRewrite(query, { language: "en-GB" })` requires an engine built with
the new dispatch operation. The default is `en`, and an explicit shell locale
such as `en_GB.UTF-8` normalises to `en-gb`. An unrecognised or empty locale
falls back to `en`. Tests evaluate an actual rewritten query on a small local
RDF graph to check language priority and entity-ID fallback.

| Local rewrite run | First 100 | Full 580 |
| --- | ---: | ---: |
| Wikimedia rewrote / unchanged | 81 / 16 | 434 / 106 |
| Factoidal rewrote / unchanged | 81 / 16 | 404 / 106 |
| Both tools supplied query text | 97 | 509 |

The Wikimedia run used the checked-in executable JAR through Java JSONL.
These counts track statuses and text availability. The workbench runs one
query or one pair on demand, with the original for Blazegraph and the selected
replacement for QLever. Future parity claims need result comparisons and the
upstream golden fixtures for each rule.


## Normalisation and source review

The generated queries differ as text. No pair of actual rewrites matched with
only comments and whitespace removed by the Lean lexer. Parsing both sides
with Jena 4.10, clearing the prefix map, serialising, and comparing tokens
gave 1/81 exact matches in the first 100 and 2/403 across the complete
catalogue. Consistently renaming only variables absent from the original query
raised these counts to 75/81 and 370/403. All 403 pairs parsed in Jena. The
unmatched pairs can differ in OPTIONAL or BIND order, guard placement, or
lookups generated. That diagnostic neither proves nor refutes equal results.

Four ordered corpus examples (MLP 007, 011, 019 and 027) were run as pairs
on QLever. They returned the same column sets and bags of bindings with
83, 134, 1,081 and 41 rows respectively. The requests excluded the appended
original-query comment and compared complete results without imposing row order.

The three first-100 original-source issues reuse SELECT aliases that are
already in scope. This includes SUM and SAMPLE self-aliases. The SPARQL 1.1
scope rule is at https://www.w3.org/TR/sparql11-query/#variableScope .
These are now rejected by the Lean rewriter's outer projection check. The
general Factoidal parser still accepts certain grouped aliases. The review
flags 18 original aliases and one unmatched closing brace across the full
catalogue. The other original Java parse failure is MLP 508. Jena accepts
that source with explicit prefixes, so it is a rewrite-tool scanner issue.

The offending patterns for MLP 060 and 093 appear in the 18 December 2017
revision (610448730), and MLP 026 in the 7 December 2020 revision
(1319372974). Twelve of the 16 unchanged first-100 queries are present
verbatim in the 2017 revision. They already used standard query constructs
there, subject to WDQS's convenience prefix environment. That observation
does not reconstruct the edits that first made them portable.

Reproduce normalisation with `tools/wikidata/compare_rewrite_text.py`. It uses
the same local Jena JAR, a Java compiler, and the Lean tokeniser.
