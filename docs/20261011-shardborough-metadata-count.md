# Metadata cardinalities — 2026-10-11

- The JSON record `20261011-shardborough-metadata-count.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261011-shardborough-metadata-count.json) and is not in this tree.

Read snapshots now answer eligible whole-graph and predicate-bucket COUNT(*)
queries from retained array sizes. The query no longer filters or constructs
triple lists to count them. This reuses the existing graph and ordered-subject
arrays; it adds no index, preparation pass or answer cache.

## Lean implementation and proof boundary

`SPARQL/MetadataCount.lean` reuses the existing streaming-count detector,
including its restrictions on distinct variables, aggregate selection,
GROUP BY, HAVING, VALUES, DISTINCT/REDUCED and ORDER BY. Constant subject or
object constraints and repeated variables keep the existing evaluator.
Missing predicates count as zero. The complete count row retains its alias
and `xsd:integer` datatype; OFFSET and LIMIT apply to that one-row result.
The entry point performs the same blank-node rewrite as the backend runner.

`MetadataCountTheorems.cardinality_eq` proves every successful metadata
lookup equals `backendCountExact`, under the admitted source index's
`Index.Wf` invariant. Predicate-array sizes equal original bucket lengths
by the ordered index's universal invariant. Well-formedness establishes
that every bucket member has the requested predicate. Whole-graph counting
uses the admitted graph array's size. Duplicates retain their multiplicity.

`countRows_eq_backend` lifts this to the complete existing SELECT backend
answer for every successfully detected query and environment.
`PreparedSnapshotTheorems.selectRows_eq_reference` proves the new wrapper,
including metadata counts, ordered slices and fallback, equals its retained
reference for every query/environment. Axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. These are executable Lean
refinements; they do not establish that every pre-existing aggregate rule
implements all SPARQL semantics.

Snapshot dataset clauses still use the reference evaluator before the
metadata path. Native regression checks also exposed a pre-existing fresh
IBK3 CLI bug: COUNT with an unavailable FROM graph returned the local
whole-graph count. The CLI's ordinary SELECT/ASK fallback now uses the
reference evaluator for dataset clauses, whose local-dataset policy gives
an empty graph in this case. Complete native answers pin both routes;
this IO wrapper correction has regression evidence, not a separate theorem
about the complete native storage pipeline.

The F* lineage is `formal/fstar/SPARQL11.Store.fst`:
`detect_streaming_count_star`, `count_star_solution`, and the physical count
inside `eval_select_backend_on_graph`. The new retained-array metadata path
and its universal refinements are Lean-first work. No F* verification result
is used as proof of this Lean optimization.

## Test-first validation

The focused target failed before its implementation existed. Nineteen guards
cover whole-graph/predicate sizes, duplicate triples, missing predicates,
bound-position rejection, aliases, count slicing, blank-node rewriting and
unsupported query shapes. Snapshot guards additionally check the public
wrapper and dataset-clause fallback against the reference evaluator.

The native regression suite compares full known answers with the fresh CLI.
It checks whole-graph and predicate counts across delta replay and CURRENT
activation: old snapshots retain counts 7/2, a new delta snapshot observes
8/3, and the next activated generation observes 1/0. Admission and corruption
rejection, error recovery and the existing exact SELECT/ASK checks also pass.
The failed pre-fix FROM trial is retained separately in the evidence report.

Validation:

```
cd formal/lean4
lake build L4Factoidal.SPARQL.MetadataCountTests L4Factoidal.SPARQL.MetadataCountTheorems
lake build L4Factoidal.SPARQL.PreparedSnapshotTests L4Factoidal.SPARQL.PreparedSnapshotTheorems
lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query l4block-quad-query l4w3c
```

The combined build passes 709 jobs. Native snapshot checks and IBK3/IBK4/IBK5
complete-JSON smokes pass. The W3C reference/evaluator run passes 631 tests,
with 0 failures, skips or unsupported cases. Its existing harness tolerances
remain separate from exact native answers and universal refinement proofs.

## Measurements

The same immutable generated 300,000-triple graph is used as in the
[ordered-subject report](20261011-shardborough-ordered-subject-access.md).
Archived/current snapshots alternate one warmup and five samples per query;
complete JSONL serialization and transfer are timed, with exact validation
outside timing. Both snapshots stay open. Opening is measured separately;
RSS after readiness is not peak memory. Builds, profilers and other database
benchmarks do not overlap timing windows; ordinary OS activity remains and
CPU observations are retained.

Paired medians, milliseconds:

| Query | Archived | Metadata count |
| --- | ---: | ---: |
| Predicate COUNT | 9.024625 | 0.074708 |
| Two-pattern join, 100,000 rows | 1,353.134333 | 1,349.510042 |
| Ordered OFFSET 3 LIMIT 7 | 0.082917 | 0.082625 |

Only count latency changes materially. Opening observations are 6.445 and
6.281 seconds, respectively; RSS after readiness is 192.516 and 192.484 MiB.
These are single startup/RSS observations, not medians or a memory speedup.
The eager ordered arrays still incur the preparation cost documented earlier.

Separate native competitor medians, milliseconds:

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| limit-zero | 0.069 | 0.721 | 0.048 | 1.707 |
| predicate-count | excluded | excluded | 0.043 | 1.158 |
| ask-present | 0.039 | 0.965 | excluded | excluded |
| ask-absent | 0.035 | 0.454 | excluded | excluded |
| object-index | 91.691 | 19.554 | 92.504 | 119.262 |
| subject-join | 1339.153 | 375.972 | 1351.674 | 3331.872 |
| object-subject-join | 134.059 | 39.478 | 135.471 | 245.231 |
| subject-triple-join | 1662.874 | 572.922 | 1658.794 | 5118.387 |
| limit-slice | 0.146 | 4.100 | 0.149 | 133.616 |

The eligible predicate count is faster than the configured Virtuoso run
in these transport-inclusive samples. QLever COUNT remains excluded because
its integer datatype differs. Broad joins still trail QLever; no broad-join
improvement follows from this count shortcut.

The known QLever COUNT datatype difference and Virtuoso ASK shape differences
remain exclusions, with raw documents retained. No coercion converts them
into exact successes. The synthetic graph, pinned configurations, single
client and different transports do not establish industry parity. Large
varied workloads, compact joins/terms, disk execution, concurrent queries,
update/recovery costs and peak memory remain required work.

[Evidence JSON](20261011-shardborough-metadata-count.json) retains raw samples,
full-answer checks, commands, binary/source/log hashes and the failed native
regression. Previous stage reports remain historical measurements.

The next [native string-order change](20261011-shardborough-native-string-order.md)
retains this count path and separately measures broad-join and preparation gains.
