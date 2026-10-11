# Ordered subject access — 2026-10-11

Shardborough read snapshots now prepare stable subject-ordered arrays for
each predicate. Eligible single-pattern SELECT queries extract their ordered
OFFSET/LIMIT interval before constructing bindings. This removes the full
matching and sorting work from the measured small ordered slice. It adds
preparation time and memory; neither cost is omitted from the report.

## Implementation and proof boundary

`formal/lean4/L4Factoidal/SPARQL/OrderedSubject.lean` builds ascending and
descending arrays from each original predicate bucket. Each direction is
sorted independently, preserving the previous stable sort's tie order and
duplicates. Reversing the ascending array would reverse tied rows and is not
used. The private index constructor retains a universal invariant: every
array equals the corresponding complete original bucket sorted by the
existing subject comparator. Missing predicates have empty arrays.

The plan detector admits a default-graph singleton BGP of the form
`?subject <predicate> ?object`, with different variable names, exactly one
ascending/descending subject-variable order key and a finite LIMIT.
Projection may be SELECT-star or a list of variables. OFFSET is supported.
Dataset clauses, repeated variables, expressions, extra sort keys, other
pattern positions, grouping/HAVING, DISTINCT/REDUCED and VALUES fall back to
the existing evaluator. This is a reusable predicate access path, not a cache
of query answers. It handles arbitrary RDF subjects and object terms.

`execute` uses bounded `Array.extract`, then builds and projects just the
selected bindings. Object-before-subject binding-list representation, hidden
synthetic variables, unbound projected names, row positions and multiplicity
all preserve the existing behavior.

`OrderedSubjectTheorems.lean` proves the chain:

- successful detection reconstructs the complete original query;
- every admitted predicate bucket has the named predicate under `Index.Wf`;
- singleton matching returns exactly the mapped bucket, in its original order;
- the query's subject-variable comparator equals the physical subject comparator
  for every environment and active graph;
- sorting commutes with that mapping, and projection commutes with slicing;
- the complete physical answer equals `runSelectQueryBackendDataset`.

`PreparedSnapshotTheorems.selectRows_eq_reference` then proves the optimized
snapshot row wrapper equals its retained reference for **every query and
environment**. Detection failure uses the reference path. The standard Lean
axiom audit lists only `propext`, `Classical.choice` and `Quot.sound`; there are
no new assumptions about sorted input and no custom axioms, `sorry` or
`native_decide`.

The snapshot holds these arrays alongside its existing hash index. Both are
prepared once from the admitted graph after delta replay. Existing frozen
generation/update semantics remain. Readiness now identifies the hash and
subject-order index builds separately; legacy `index-builds=1` remains the
hash-index count. These are control-flow counts, not allocation counters.
No query performs collection IO after readiness. Arrays are not persisted,
and fresh disk CLI execution does not use this snapshot-only access path.

The F* semantic responsibility remains in `formal/fstar/SPARQL11.Store.fst`'s
detectors and `eval_limit_single_tp`; that route rejects ORDER BY. This new
ordered access implementation and its refinements are Lean-first work. No
F* proof or executable result is presented as evidence for the Lean arrays.

## Test-first validation

The focused regression target was added before the implementation and failed
on the missing API. Its passing guards compare the new path with the ordinary
backend on duplicates, tied subjects, blank nodes, both directions, hidden
sort keys, missing predicates, zero/oversize limits, offsets past the end and
unbound projected variables. Twelve rejection guards pin the unsupported
shapes. A further matrix checks 120 direction/projection/offset/limit
combinations against the complete existing backend answer.

Validation commands:

```
cd formal/lean4
lake build L4Factoidal.SPARQL.OrderedSubjectTests
lake build L4Factoidal.SPARQL.OrderedSubjectTheorems L4Factoidal.SPARQL.PreparedSnapshotTheorems
lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query l4block-quad-query l4w3c
```

The combined build passes **705 jobs**. Expanded native snapshot tests check
stable descending ties and compare exact sliced answers with the fresh CLI.
Admission, delta/CURRENT isolation, corruption rejection and error recovery
also pass. Native IBK3/IBK4/IBK5 JSON smoke checks pass. Large native checks
verify complete 100,000-row ascending and descending finite-limit answers
and a large offset through the actual new single-pattern path, against the
independent generated oracle.

The W3C SPARQL 1.1 reference/evaluator run remains **631 pass, 0 fail, 0 skip,
0 unsupported**. Its existing harness tolerances do not certify all native
storage execution; the exact native checks and universal refinement proofs
are separate evidence.

## Measurements

The corpus is the same immutable, generated 300,000-triple default graph as
the [previous operator report](20261011-shardborough-exists-and-ordered-prefix.md).
`tools/blockengine-snapshot-pair-bench.py` alternates archived/current binaries
with one warmup and five measured samples. Opening and RSS after readiness
are recorded separately. Both snapshots stay open; timings include complete
JSONL serialization and transfer. Every answer is independently checked
outside timing. RSS is not peak memory.

Separate competitor reruns use one warmup and three alternating samples per
workload with the previously pinned QLever/Virtuoso configurations. They
retain the documented COUNT datatype and ASK-shape exclusions and the
JSONL/HTTP transport differences. There are no builds, profilers or other
database benchmarks during timing windows. Ordinary OS activity remains;
CPU observations are retained.

Paired query medians at 300,000 triples, in milliseconds:

| Query | Archived | Ordered index |
| --- | ---: | ---: |
| ASK present | 0.033625 | 0.034792 |
| Two-pattern join, 100,000 rows | 1,370.213666 | 1,342.157417 |
| Ordered OFFSET 3 LIMIT 7 | 320.981334 | 0.088625 |

Preparation was observed once per binary in this pair; these are not
startup medians. RSS is sampled immediately after readiness, not at peak:

| Preparation | Archived | Ordered index |
| --- | ---: | ---: |
| Opening, seconds | 1.778 | 6.241 |
| RSS after readiness, MiB | 182.234 | 192.562 |

The slice avoids the prior full-bucket matching/sorting cost. Broad join
latency remains roughly unchanged; no broad-join speedup is claimed.
The added indexes cost about 4.46 seconds of opening and 10.33 MiB of RSS in
this pair. They are built eagerly even if a session never uses this access path.

Separate native competitor medians, in milliseconds:

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| LIMIT zero | 0.040 | 0.671 | 0.053 | 1.548 |
| Predicate COUNT | excluded | excluded | 8.943 | 1.194 |
| ASK present | 0.033 | 0.980 | excluded | excluded |
| ASK absent | 0.034 | 0.506 | excluded | excluded |
| Object lookup, 10,000 rows | 92.110 | 19.372 | 91.760 | 119.332 |
| Two-pattern join, 100,000 rows | 1,341.731 | 376.969 | 1,342.345 | 3,475.592 |
| Object-driven join, 10,000 rows | 134.406 | 39.402 | 134.013 | 241.012 |
| Three-pattern join, 100,000 rows | 1,648.151 | 571.966 | 1,645.835 | 5,085.826 |
| Ordered OFFSET 3 LIMIT 7 | 0.147 | 3.540 | 0.141 | 138.567 |

This eligible slice is now faster than both configured competitors in these
transport-inclusive measurements. Other families still show substantial
gaps: broad joins trail QLever by about 2.9–3.6 times, and predicate COUNT
still trails Virtuoso. The synthetic corpus, pinned configurations and
single-client runs do not establish industry parity. Known excluded answer
shapes remain recorded differences, not exact-answer successes.

Raw samples, commands, opening/memory scope, binary/source hashes, exact
answer checks and conformance log hashes are in the
[evidence report](20261011-shardborough-ordered-subject-access.json).

## Remaining parity work

This change covers subject ordering of a complete predicate bucket. Other
sort keys, selective object constraints and ordered joins still need physical
plans with their own refinements. Broad joins still construct string-keyed
bindings, estimates still count materialized rows, and opening still decodes
the whole admitted graph into RAM. Compact term IDs, reusable cardinalities,
disk-backed execution, larger varied workloads, concurrency, updates/recovery
and peak-memory measurements remain part of the industry-parity goal.

The subsequent [metadata-count change](20261011-shardborough-metadata-count.md)
reuses these array sizes without another index. It has separate before/after
and competitor samples; this report retains the earlier binary and timings.
