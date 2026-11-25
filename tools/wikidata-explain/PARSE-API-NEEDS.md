# What the query explainer needs from the Factoidal parse API

For the Codex work exposing SPARQL structure from factoidal. The
consumer is `explain/SPEC.md`: deterministic, rule-based explanations
of the 580 MLP Wikidata queries. Items are listed in priority order.
The test set is SPEC §8 (T1–T13).

## Must have

1. **The parsed query as lossless, versioned JSON, from JS and WASM.**
   It should be the `SPARQL.Query` AST itself, not `toSse`, since
   `toSse` drops VALUES rows and aggregate details. It needs a
   `schema_version` and the parser or engine version. It must be
   available from Node and from the browser bundle.

2. **The WDQS prefix environment**, as in `L4Factoidal.Wikidata.Parser`:
   the same 38 default prefixes, with authored PREFIX declarations
   taking precedence. Expanded IRIs, plus the prefixed name as written
   where there was one: we render `wdt:P31`, not the full IRI.

3. **Both inputs parseable.** The primary input is the Factoidal
   rewrite (`lean_replacement_query`), which is the query we explain.
   The secondary input is the original or classic query (WDQS dialect,
   label `SERVICE`, `[AUTO_LANGUAGE]`), needed for translation notes
   and provenance. Parse errors come back as structured diagnostics, not
   exceptions.

4. **Every node kind, with nothing summarised:**
   - **Patterns:** `bgp`, `join`, `leftJoin` with its condition,
     `filter`, `union`, `minus`, `graph`, `lateral`, `bind`, `values`
     with all rows, `service` and `serviceVar` with the silent flag
     and full inner pattern, `subSelect`, `propertyPath`, `empty`.
   - **Query:** `form`, `dataset`, `groupBy` (variables and
     `expr AS alias`), `having`, `orderBy` with asc/desc,
     `distinct`/`reduced`, `limit`/`offset`, `postValues`.
   - **Expressions:** the full tree, including
     `aggregate(fn, distinct, arg)`, so we can tell `COUNT(DISTINCT x)`
     from `COUNT(x)` and from `COUNT(*)`. `groupConcat` must carry its
     separator, and `existsPat`/`notExistsPat` their patterns.

5. **Property paths kept as paths.** We need `wdt:P31/wdt:P279*`
   reported as sequence(P31, zeroOrMore(P279)), not only after it has
   been rewritten into simpler patterns. If the parser does rewrite
   paths, give both the authored form and the rewritten form.
   Several rules depend on this, including subclass closure and
   row multiplication.

6. **Blank nodes as written are told apart from fresh variables.** We
   need to know that `?x wdt:P217 []` was written as `[]` (an anonymous
   "some value"), versus `_:b` or `[ wdt:P1 ?y ]`. Each should come
   back with a stable generated name.

7. **Source offsets on every node**, as character start and end in the
   input text. These attach Martin's inline comments to the nodes they
   annotate (216 queries have them), and let each explanation sentence
   point back at its source span.

8. **Comments and directives returned separately** with offsets: the
   `#title:` and `#defaultView:` lines and ordinary `#` comments.
   Parsing them out is fine, but they must not be lost.

## Very useful

9. **Variable scope facts per node:** the variables it binds, which of
   those are certainly bound and which only possibly bound, and the
   variables it uses. We'd compute these ourselves if necessary. But
   if Lean has them with proofs, they are exactly what the rules for
   variables trapped inside an exclusion, `MINUS` with no shared
   variables, and optional parts need.

10. **Rewrite provenance:** for the rewritten query, a map from each
    rewritten node back to the original node and its rule ID
    (e.g. the label-service rewrite → generated OPTIONAL and BIND
    nodes). This lets the explainer describe what the user wrote, not
    the rewriter's scaffolding such as the `?x__label_value` variables.

11. **A canonical query hash** (`query_sha256` over the normalised
    AST), so cached explanations go stale exactly when a query's
    meaning changes.

## Not needed

- Query plans, cardinality estimates, execution.
- A SPARQL printer, though a round trip would help testing.
- Anything that makes network calls during parsing (SERVICE must not
  be contacted).

## Acceptance check we'll run

- All 580 `classic_query` and `lean_replacement_query` strings parse,
  or return diagnostics. Compare with the 549 of 579 originals
  accepted in the 2026-11-24 baseline.
- For T1–T13, the JSON exposes every element that the targets in SPEC
  §8 mention.
