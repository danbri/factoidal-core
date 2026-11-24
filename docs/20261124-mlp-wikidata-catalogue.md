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
render arbitrary MediaWiki templates. The first 100 historical records are available as an exact slice
of the full catalogue. The workbench browses all 580 records.

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

## Compatibility audit, 24 November 2026

The audit covers the [WDQS Compare page][compare], the [Learn][learn] and
[Migrate][migrate] pages, the [Wikitech rewrite guide index][wikitech] and the
[QLever optimisation examples][optimisation]. The general backend comparison
also covers storage, scaling, updates, authentication, observability and query
planning. Those are endpoint or operational properties. Rewrite coverage is
measured separately.

| Topic | Wikimedia Java source at the pin | Factoidal Lean |
| --- | --- | --- |
| Query hints and `wikibase:isSomeValue` | Source edits before ARQ | Implemented. The checked-in fixtures for these groups match byte for byte. |
| Variable reuse | Rejects a reused alias at ARQ parsing unless an earlier rule has already removed it | Recovers outer SELECT aliases using the lexer and existing projection, graph-pattern and modifier parsers. Preserves public result names. Ambiguous nested references and BIND target reuse require further scope analysis. |
| Date and duration typing | Rewrites supported expression literals and date-derived comparisons. Some ambiguous or mixed cases are refused or left alone. | Rule remains to be ported. |
| Geospatial | Rules for around, box, distance, globe, latitude and longitude apply under documented constraints | Rules remain to be ported. |
| `bd:slice` and `bd:sample` | Portability rules for supported forms. Sampling can legitimately change the returned rows. | Rules remain to be ported. |
| GAS | Converts supported traversal to QLever Path Search. Blazegraph traversal includes tree/visited-set semantics with no general SPARQL 1.1 equivalent. | Rule remains to be ported. |
| Label service | Broad post-parse conversion. WDQS v2 also offers the service via its proxy. | Scalar, single outer service subset. Nested/multiple services, aggregation and prebound outputs remain gaps. |
| Named subqueries | Hoists supported legacy definitions to QLever's `WITH %name AS { … }` and `INCLUDE` dialect. The migration guide separately documents v2 proxy support. | No named-subquery conversion yet. |
| `wikibase:mwapi` and `wikibase:decodeURI` | Explicitly diagnosed. The migration guide describes an external Action API request or client-side decoding, respectively. | Diagnosed as unsupported proprietary constructs. |
| Prefixes and graph routing | Implicit WDQS namespaces with explicit overrides, and scholarly service endpoint conversion | Implemented for known scholarly service IRIs. The workbench serves main-graph endpoints by default. |
| Evaluation order and performance | Removal of hints and several documented rewrites. No general guarantee of equivalent planning or improved latency. | The timing harness compares the original on Blazegraph with either saved rewrite on QLever. It reports comparable ratios only when the result bags match in all trials. |

At the pin, the Java engine separates leading comments, extracts named
subqueries, pre-processes hints and `wikibase:isSomeValue`, then calls
`QueryFactory.create(..., Syntax.syntaxSPARQL_11)` with implicit WDQS
prefixes filled in. The fallback after an ARQ parse failure only blanks
comments. Parsed rules run on Jena syntax objects. The final text is reparsed,
serialised once more and given a comment containing the original query. See
[the pinned Java implementation][engine] and [the named-subquery guide][named].

The Lean output path uses Wikimedia's text-only layout by default and
reconstructs ARQ's layout for supported parsed patterns. For other parsed
patterns it retains the edited source layout. Exact output includes generated
variables, namespace declarations, whitespace and the full original-query
comment. Pure Lean runs the rewrite. Python and Java are differential test
tools. The alias recovery is intentionally broader than the pinned Java
utility. All 18 repaired catalogue outputs parsed in independent Jena ARQ.

The checked-in `dist/sparql-rewriter.jar` at the pin did not contain the
date-duration rule from the source. For this audit the Java sources were
compiled against the bundled dependency classes, then the rewriter package
and resources in the archive were replaced with the compiled source and
current resources. The date-duration tests returned five rewrites from this
source-built oracle. The bundled executable returned zero. Use a source-built
JAR for future fixture runs.

| Differential sample | Cases | Status matches | Byte matches among successful rewrites |
| --- | ---: | ---: | ---: |
| Pinned Wikimedia fixtures against the source-built oracle | 213 | 65 | 25 / 134 Wikimedia rewrites, 32 with text from both |
| Martin Poulter corpus, same prepared English input on both sides | 580 | 530 | 47 / 403 paired successful rewrites |

The corpus also has 106 unchanged cases with byte-identical text. Lean
generated 422 rewrites and 106 unchanged results. The catalogue's 18
legacy-alias cases account for 18 of those rewrites. MLP 533, with an
unmatched closing brace, still fails. These are executable checks on the
local native Lean path and its Wasm dispatch module, with browser-Wasm
release and parity validation pending.

Reproduce against the pinned upstream checkout and a JAR compiled from it:

```bash
python tools/wikidata/compare_rewriter_fixtures.py /path/to/upstream \
  --jar /path/to/source-built.jar --out /tmp/wdqs-fixtures.json
python tools/wikidata/build_mlp_catalogue.py --with-lean \
  --jar /path/to/source-built.jar --out /tmp/mlp-catalogue.json
python tools/wikidata/compare_rewrite_text.py /tmp/mlp-catalogue.json \
  --jar /path/to/source-built.jar --out /tmp/mlp-text-comparison.json
python tools/wikidata/compare_endpoint_timings.py /tmp/mlp-catalogue.json \
  mlp-007 mlp-011 mlp-019 mlp-027 --trials 2
```

A live endpoint probe accepted a `SAMPLE(?item) AS ?item` example on
Blazegraph and rejected it on WDQS v2. WDQS v2 accepted a simple unconverted
label-service query. A named-subquery probe returned HTTP 400 on v2, so
proxy support in the documentation still needs endpoint confirmation for
the exact syntax at release. Four cross-endpoint timing probes returned
equal row counts and unequal RDF terms in both trials. For MLP 007, for
example, Blazegraph returned the matching count as `xsd:integer` and QLever
as `xsd:int`. The script records end-to-end durations, including transfer,
cache and service conditions. It records strict RDF-term equality separately
from datatype-only equivalence and leaves comparisons with remaining result
differences without a speed ratio.

At the first audit, the workbench served the earlier precomputed snapshot.
Release requires supported fixture parity, documented intentional differences and unavailable rewrites, native/Wasm agreement, and
a workbench build from the same tested corpus and oracle.

[compare]: https://www.wikidata.org/w/index.php?title=Wikidata:SPARQL_query_service/WDQS_backend_update/Compare&oldid=2574073050
[learn]: https://www.wikidata.org/wiki/Wikidata:SPARQL_query_service/WDQS_backend_update/Learn
[migrate]: https://www.wikidata.org/w/index.php?title=Wikidata:SPARQL_query_service/WDQS_backend_update/Migrate&oldid=2574071602
[wikitech]: https://wikitech.wikimedia.org/wiki/Wikidata_Query_Service/Migration
[optimisation]: https://www.wikidata.org/wiki/Wikidata:SPARQL_query_service/query_optimization_v2
[named]: https://wikitech.wikimedia.org/wiki/Wikidata_Query_Service/Migration/Rewrite_of_Utility_Services_and_Functions#Named_subqueries
[engine]: https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/SparqlRewriteEngine.java

## Exact output and JSONL compatibility

The second audit compares the same prepared English input with the pinned,
source-built Java oracle. Lean's formatter reads the validated token stream
with Factoidal's clause parsers. This keeps source-order FILTERs, nested
groups, and property paths before evaluation lowering. It emits ARQ's
prefix, triple and expression layout, and validation reparses the output.
Label rewrites use the upstream's ordering of automatic outputs and anchor
after the last subsequent outer-group binder of a label entity. The port
also rewrites the supported Blazegraph `geof:distance` call shapes.

| Corpus | Byte-identical rewrites | Byte-identical unchanged queries | Java-only rewrite | Lean-only rewrite |
| --- | ---: | ---: | ---: | ---: |
| First 100 | 81 / 81 paired | 16 | 0 | 3 |
| All 580 | 410 / 410 paired | 106 | 24 | 19 |

There are 21 corpus queries with no result text on either side. Of the 24
Java-only rewrites, 23 use named subqueries and one uses a nested label
service. The 19 Lean-only cases include 18 legacy alias repairs and the
`$date` prefix-scanner case. The 213 upstream fixtures remain a wider test
of the migration tool. 73 statuses and 33 of 134 Java rewrites match
byte for byte in that set. Named subqueries, expanded label scopes, date
and duration, remaining geospatial functions and services, and the
utility and GAS services remain release gates.

Build the native transport with `lake build l4wikidata-rewriter` in
`formal/lean4`. The command accepts Wikimedia JSONL v1 requests on stdin
and returns their request IDs, query IDs, SHA-256, and versioned result
envelopes. It needs no JVM. For the HTTP adapter, set `REWRITER_BIN` to
the absolute binary path. Native responses for all 580 records matched
the Lean batch path with protocol version and query identity checked.
To run the fixture audit through the same binary, add
`--lean-bin formal/lean4/.lake/build/bin/l4wikidata-rewriter` to
`compare_rewriter_fixtures.py`. The wider fixture audit is the
behavioural replacement gate. This revision builds the Lean Wasm
dispatch module. Browser-Wasm execution remains a separate release check.

The updated workbench serves the audited snapshot and includes a
byte-identical filter. Generate the same comparison metadata by adding
`--annotate-catalogue` to `compare_rewrite_text.py`.
