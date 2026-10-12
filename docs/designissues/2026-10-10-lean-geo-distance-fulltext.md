# Lean engine: `geof:distance`, `geof:envelope` and `text:query`

**Date:** 2026-10-10.
**Issue:** https://github.com/danbri/factoidal/issues/727 (OKR batch 1, key
result 4.1: https://github.com/danbri/factoidal/issues/768).
**Decision that started it:** coordinator, 2026-10-10, in the thread of issue
727: "`text:query` will be implemented in the Lean engine, not removed."
**Status:** landed. Hub posts 20 and 21 pass on the Lean engine; their
expected-failure markers are removed.

The F\* engine had three functions that the Lean engine did not: the
GeoSPARQL non-topological functions `geof:distance` and `geof:envelope`, and
the jena-text property function `text:query`. This record gives the
semantics the Lean engine now implements, where each part is wired, the
check against the F\* engine, and the measured cost of `text:query`.

## 1. `geof:distance` and `geof:envelope`

Module: `formal/lean4/L4Factoidal/Geo/Functions.lean`. Both functions are
served by `Geo.extFns`, the SPARQL 1.1 §17.6 extension table, so they reach
every SPARQL surface: the reference evaluator, the backend runners, the
`l4factoidal` command line, the wasm `query` operations and the npm package
(`Wasm/Ops/ExtFns.lean` consults `Geo.extFns` before any host function).

### `geof:distance(g1, g2)` — the F\* two-argument form

* Both arguments must be `geo:wktLiteral` literals that parse, in the same
  reference system (`sameCrs`; a literal with no CRS IRI is CRS84), and both
  must be points. Anything else is the §17.6 error: the row is dropped in a
  `FILTER` and the variable is unbound in `BIND` or a `SELECT` expression.
* The answer is the F\* answer: the exact squared distance of the two points,
  then one floored integer square root (`geoSqrtApprox`) at 9 decimal digits
  more than the input scale, as an `xsd:double` literal whose lexical form is
  that exact decimal (`"2.89252253232364639"` for London to Manchester).

### `geof:distance(g1, g2, units)` — the GeoSPARQL 1.1 form

GeoSPARQL 1.1 gives the function a third argument, the unit of measure of the
answer, and computes the distance "in the spatial reference system of geom1".
The engine performs no coordinate transformation and computes the planar
distance in the coordinate units of that reference system. So it answers in
one unit only, the unit of the reference system's axes:

| reference system of `g1` | unit answered |
|---|---|
| none (CRS84), `OGC/1.3/CRS84`, `EPSG/0/4326` | degree (`uom:degree`, `EPSG/0/9102`) |
| `EPSG/0/3857`, `EPSG/0/27700` | metre (`uom:metre`, `EPSG/0/9001`) |
| any other | none: every unit is refused |

The unit argument is an IRI, or an `xsd:anyURI` literal holding one. For any
other unit, or a unit that is not an IRI, the answer is the §17.6 error. The
engine never returns a number in a unit other than the one asked for.

**Shortfall:** a geodesic distance in metres between two points of a
geographic reference system (CRS84) is not computed; the call is refused.
Issue: https://github.com/danbri/factoidal/issues/772. Expected-failure
case: `xfail: geof:distance in metres between two CRS84 points` in
`npm/factoidal/test/geo-fulltext.test.js`.

The F\* engine has no three-argument form: `eval_geof_call` in
`SPARQL11.Algebra.fst` refuses every three-argument call.

### `geof:envelope(g)`

The bounding box of `g` as a closed rectangular `POLYGON` (five points, the
first repeated last), exact, in the reference system of `g`, typed
`geo:wktLiteral`, so the result is a valid argument of another `geof:` call.
An empty geometry has no bounding box and gives the §17.6 error, as does a
non-WKT argument.

## 2. `text:query`

Modules: `formal/lean4/L4Factoidal/SPARQL/FullText.lean` (semantics, codec,
evaluation), `SPARQL/Parser.lean` (`pFulltextObject`), `SPARQL/Query.lean`
(`lowerBgp`, `QueryPattern.mentionsFulltext`), `SPARQL/StoreDataset.lean`
(the backend decline), `SPARQL/DatasetRestriction.lean` and
`Storage/ShardManifest.lean` (the persisted-store planner).

### Semantics (slice 1 of `2026-07-05-fulltext-sparql-design.md`, as in the F\* engine)

* **Vocabulary.** The predicate `http://jena.apache.org/text#query`.
* **Object grammar** (F\* `parse_fulltext_query_object`): a string `"term"`;
  `( field "term" )`; `( field "term" limit )`. `field` is an IRI, a prefixed
  name or `a`; a property path or a variable is refused. There is no
  `( "term" limit )` form. Any other object (`?s text:query ?o`) is a parse
  error. Only one object follows the predicate: no `,` list.
* **Tokens.** Lowercase ASCII letters, then split on every character that is
  not an ASCII letter or digit (`defaultTokenizer`). A non-ASCII character is a
  separator.
* **Match.** A literal matches when its tokens include every query token
  (AND). The test is on tokens: `"pane"` does not match `"panel"`. The query
  `""` has no tokens and matches every literal. Only a literal object can
  match; the lexical form is searched whatever the datatype or language tag
  (`"42"^^xsd:integer` matches `"42"`).
* **Candidates.** The triples of the active graph whose predicate is the
  field (every triple when there is no field), in graph order. `GRAPH`
  chooses the graph searched.
* **Limit.** The first `n` MATCHING TRIPLES are kept, and only then is the
  subject bound. So a constant subject outside the first `n` matches gives no
  row, as in the F\* engine (`list_take n matched`, then `try_bind_subject`).
* **Rows.** One row per matched triple; a subject with two matching literals
  gives two rows. No score, no ranking.

### Encoding (F\* design, kept)

The parser recognises the `text:query` predicate before any collection
desugaring, and encodes `(field, term, limit)` into ONE literal in the object
position, with the private datatype `http://jena.apache.org/text#query-args`
and the three parts separated by U+001F (`encodeFulltextLiteral`). The
pattern stays an ordinary triple pattern in its BGP.
`TriplePattern.fulltext?` recognises it: the `text:query` IRI as predicate
AND a decodable marker literal as object. A `text:query` predicate with any
other object is an ordinary triple pattern.

### Where it is evaluated

* **Reference evaluator** (`QueryPattern.lowerWith`, `.bgp` arm →
  `lowerBgp`). A BGP with no `text:query` pattern lowers to itself
  (`lowerBgp_of_no_fulltext`). Otherwise each `text:query` pattern is taken out
  of the BGP and joined back as
  `.modified (fun active _ => fulltextSolutions ftq s active) .empty`.
  The join gives the F\* answer because the F\* `eval_fulltext_tp_store` reads
  its candidates with an unbound subject: the candidate list, the match and the
  limit do not depend on the row, and only the subject binding does.
  `fulltextScan` reads the graph in one tail-recursive pass, stops at the
  limit and tokenises the query once; `fulltextScan_eq` proves it returns the
  specification list `fulltextCandidates` (filter by field and match, then
  take the limit), order included.
* **Backend evaluator.** `evalPatternBackend` and its fast paths (LIMIT
  push-down, streaming `COUNT(*)`, ASK) read a BGP as triple patterns matched
  against stored triples, and would read a `text:query` pattern as an ordinary
  triple and answer nothing. `runSelectQueryBackendDataset` and
  `runAskQueryBackendDataset` answer `none` for a query whose pattern holds a
  `text:query` pattern (`QueryPattern.mentionsFulltext`), and every caller
  then runs the reference evaluator (`Wasm/Ops/Query.lean`
  `queryParsedDatasetWith`, `SPARQL/StoreEndpoint.lean`, and
  `Harness/QuadQuery.lean`, which now falls back for this case instead of
  failing). The restriction theorems `runSelectQueryBackendDataset_restrict`
  and `runAskQueryBackendDataset_restrict` still hold (both sides are `none`).
  The F\* engine has this defect on the three fast paths:
  https://github.com/danbri/factoidal/issues/774.
* **Persisted store.** The shard planner drops entries by the constant
  predicates, constant terms and graph names of the pattern. A `text:query`
  pattern reads the literals of every triple in its field, which none of
  those bounds covers. `DatasetRestriction.plannerFragment` is `false` for a
  BGP that holds a `text:query` pattern (so the SBM7 collectors keep every
  entry), and `ShardManifest.nativeConstantPredicates?` (the IBK3 collector,
  which is not guarded by `plannerFragment`) answers `none` for it.
  So over a persisted store `text:query` is answered by a SCAN of the decoded
  dataset. `factoidal serve` keeps the decoded dataset in memory and takes the
  same path. The `LiteralGramIndex` sidecar is not used, and no wire format
  changed. The index is a 3-gram candidate filter for substring containment
  (`2026-10-10-literal-index-lgi3.md`); a query token of three or more
  characters is a contiguous substring of the folded lexical form, so the
  index can serve as a candidate filter for tokens of that length, with a
  superset theorem stated over `fulltextCandidates`. That is a separate piece
  of work with its own proof.

## 3. Check against the F\* engine

Fixtures: `tests/parity/geo-fulltext/` (two data files, 27 queries: 20
`text:query`, 7 geo). The runner compares the answers of the two command-line
engines on each query: SELECT as a multiset of rows, ASK as a boolean, a parse
error as a refusal by both. A difference fails the run unless the query is
listed as an expected divergence with its reason, and a listed query whose
answers agree also fails the run (stale entry).

```
tools/fetch-builds.sh --set native        # F*: release build-1b06a9c8bf03-linux-x86_64
(cd formal/lean4 && lake build l4factoidal)
python3 tests/parity/geo-fulltext/run-parity.py \
    --fstar bin/linux-x86_64/factoidal --lean formal/lean4/.lake/build/bin/l4factoidal
```

Result, 2026-10-10: **21 agree, 0 fail, 6 expected divergence (out of 27).**

| query | why the answers differ |
|---|---|
| `ft-04-field-limit` | `( rdfs:label "panel" 2 )`: the F\* engine keeps the LAST two matches in document order (its predicate index lists a predicate's triples newest first); the Lean engine keeps the FIRST two. Slice 1 makes no ranking claim; both answers are two matches. |
| `ft-13-ask` | F\* ASK ignores `text:query` (`false`): issue 774. |
| `ft-15-count` | F\* streaming `COUNT(*)` ignores `text:query` (`0`): issue 774. |
| `ft-19-modifier-limit` | F\* LIMIT push-down ignores `text:query` (no rows): issue 774. |
| `geo-03-distance-units` | F\* has no three-argument `geof:distance`. |
| `geo-07-distance-mixed-crs` | F\* `geo_crs_compatible` treats a literal with no CRS IRI as compatible with ANY stated CRS, so it gives a number for a CRS84 point and an EPSG:27700 point; the Lean `sameCrs` refuses the pair (the Lean topology predicates already did). |

The two-argument `geof:distance` on same-CRS literals (all pairs of 10
geometries, including polygons, a line, a multipoint and an empty point),
`geof:envelope` on every geometry kind, both functions nested in `sfWithin`,
and the argument errors all agree.

## 4. Measured cost of `text:query`

@COST@

## 5. Tests

* `#guard`s, positive and negative: `Geo/FunctionsTests.lean` (distance,
  units, envelope), `SPARQL/FullText.lean` (evaluation over a graph, the
  limit-before-subject order, pattern recognition), `Wasm/Ops/Query.lean`
  (through the query operation, so through the backend decline: SELECT, field,
  AND, join, `GRAPH ?g`, ASK, `COUNT(*)`, LIMIT, no match, parse refusals, the
  backend runner's `none`, and the geo functions), `Storage/ShardManifest.lean`
  (the planner refuses a `text:query` BGP). Sabotage checks: removing the unit
  test in `geofDistanceIn` fails two guards; removing the backend decline fails
  eleven guards in `Wasm/Ops/Query.lean`.
* Hub: `tests/hub/post20_test.mjs` and `tests/hub/post21_test.mjs` assert the
  six cases that were expected failures.
* npm: `npm/factoidal/test/geo-fulltext.test.js`, with the metres case as an
  expected failure naming issue 772.
