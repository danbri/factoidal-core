# Native complete query results

The native triple and quad query tools accept `--json` before `--query`.
SELECT writes every binding in SPARQL Results JSON; ASK writes a JSON boolean
result document. Physical read counters and parsed-query diagnostics move to
stderr. The default text output stays unchanged and prints at most ten rows.

```sh
formal/lean4/.lake/build/bin/l4block-id-v3-query COLLECTION --json --query \
  'SELECT ?subject ?name WHERE { ?subject <urn:name> ?name }'
formal/lean4/.lake/build/bin/l4block-quad-query COLLECTION --json --query \
  'SELECT ?graph ?subject WHERE { GRAPH ?graph { ?subject <urn:name> ?name } }'
python3 tools/blockengine-results-json-smoke.py
```

`--json` supports SELECT and ASK, not CONSTRUCT or DESCRIBE. Unsupported forms
fail with exit status 2 and no stdout result. Explicit SELECT variables stay
in `head.vars` when they are unbound or the answer is empty. SELECT star uses
the existing evaluator's first-seen bound-variable header policy; this change
does not add a static in-scope-variable analysis for empty SELECT-star answers.

The triple tool also supports `--json --repeat N --query ...`. Each iteration
writes one complete JSON document followed by a newline. The loop is total.
It still resolves CURRENT, reads the manifest and delta, admits requested
artifact ranges and evaluates the query again on each iteration. It is not
a pinned read snapshot or a shared authenticated-artifact cache.

## Serializer refinement

`SPARQL.ResultsJsonFast` reuses the existing term, row and variable writers.
It joins row objects with the standard library's accumulator-based
`String.intercalate`, rather than the specification's right-associated
`rowsJoined` recursion. `ResultsJson` remains unchanged.

`ResultsJsonFastTheorems` proves, for every `QueryResult`, exact string equality
and exact UTF-8 byte equality with `QueryResult.toSrj`. This includes row and
variable order, duplicates, unbound variables and RDF 1.2 term serialization.
The theorem is a refinement of the existing serializer, not a general parser
round-trip theorem, a W3C conformance certificate or a runtime complexity bound.

Fourteen build-time guards cover empty, singleton and large row lists,
duplicates, escaped and Unicode names and literals, typed and language-tagged
literals, direction, nested triple terms and boolean answers. The native smoke
checks complete bags beyond the old ten-row preview, exact sequence equality
against the forced general path for modifier-bearing joins, predicate counts,
grouping, subject lookup, unbound variables, delta overlays and named graphs.
The smoke's fixtures use known IRIs and strings; it is not a general blank-node
isomorphism or numeric-value comparison implementation.

Destination validation passes: the library and ten native targets build
together in 673 jobs; complete-result smoke checks pass for IBK3, IBK4 and
IBK5; all five retained disk smoke scripts pass; native crypto and range
checks pass 107 and 38 tests respectively, with no failures. The expected
pre-implementation native failures were exit status 2 for the absent
`--json` option in each query tool. The serializer's missing-module red
build precedes its fourteen green guards and equivalence proofs.

## Measurement boundaries

The existing binding-site and scale preview benchmarks validate cardinalities
and count scalars, not complete result bags. Their old samples do not become
full-answer validation because this option now exists. A full-output benchmark
must include serialization, stdout transfer and validation in its stated scope.
Keep these costs separate from preview-only query latency.

Physical counters currently omit CURRENT, manifest, Merkle sidecar and DLOG
reads, and work performed by a failed speculative access path. They are
committed-artifact range counters, not total filesystem-byte accounting.
Fresh-process, repeated fresh-admission and persistent-server timings are
different execution models and must not be reported as interchangeable.
