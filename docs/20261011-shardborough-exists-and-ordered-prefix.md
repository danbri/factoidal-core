# Indexed ASK and ordered prefixes — 2026-10-11

- The JSON record `20261011-shardborough-exists-and-ordered-prefix.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261011-shardborough-exists-and-ordered-prefix.json) and is not in this tree.

Landing note (2026-10-11): in this tree ASK applies its solution modifiers (`formHasSolution`, https://github.com/danbri/factoidal/issues/699). The early-exit path therefore also requires no GROUP BY, HAVING, trailing VALUES, OFFSET or LIMIT (`askUsesModifiers`); other ASK shapes run `evalAskBackendReference`, and `evalAskBackend_eq_reference` proves the two agree on every input.

Shardborough now stops a singleton indexed ASK at its first full pattern match
and retains only the needed sort prefix for eligible finite SELECT slices.
Both changes have Lean refinement proofs. Industry performance parity remains
open: the measured ordered slice still scans all matches, and broad joins
retain substantial QLever gaps.

The follow-up [ordered-subject access report](20261011-shardborough-ordered-subject-access.md)
adds an indexed path for eligible single-pattern slices. This report retains
its original implementation and measurements; the follow-up records separate
query, preparation and memory measurements.

## Executable contracts

`SPARQL/IndexedExists.lean` uses the same candidate access choices as `igSearch`
but traverses hash buckets without first reversing them. `List.any` stops at
the first triple passing both the bound filter and `tpMatch`. The second test
is essential for repeated variables and invalid bindings. Object keys with
language tags, XML literal equality or embedded triples keep the broader
candidate path required by the existing matcher.

`indexedSingleTpExists_eq` proves exact equality to nonemptiness of
`evalSingleTpBackend` for every index, pattern and input binding. It does not
need an index-well-formedness premise because it refines the same physical
access paths; completeness against the admitted graph remains the index's
separate invariant. `evalBgpBackend_single` proves the singleton BGP identity.
`StoreDataset.evalAskBackend_eq_reference` then proves the optimized ASK
equals the retained full-row evaluator for every query, environment and
dataset backend. Empty answers still report named/default backend decode
failures. Other patterns and legacy post-VALUES requests use the reference
path. Blank-node rewriting still happens at the query entry point.

The fast path avoids complete bucket reversal, filtering and solution-list
allocation for successful indexed probes. It is not a constant-time guarantee
for all ASK shapes: absent/incompatible candidates may require scanning;
unbound and unsafe-object-only access still constructs `index.toGraph`.

`SPARQL/OrderedPrefix.lean` defines a bounded merge with exactly the same
branch and tie choices as `List.merge`. It proves that truncating each merge
input to the requested count preserves the output prefix. Recursive contiguous
splitting then proves

```
mergeSortPrefix rows le count = (rows.mergeSort le).take count
```

for every list, count and Boolean comparator. There are no totality or
transitivity assumptions, so incomparable SPARQL values preserve the current
runtime sort's behavior too. A separately proved tail-recursive merge is
installed through Lean's `csimp` mechanism to handle large finite limits.

`Query.finishSelectRows` states the existing final SELECT stages: order,
project, duplicate removal, slice. `finishSelectRowsPrefix_eq` proves equality
of its prefix implementation for every comparator option, row projection,
DISTINCT/REDUCED flag, offset, limit and input sequence. The compiler uses that
implementation through a function-equality `csimp` theorem. Finite slices
without duplicate removal request `offset + limit` rows. DISTINCT, REDUCED,
unlimited and unordered cases retain the reference route. Grouping/HAVING and
SELECT expressions run before these final stages; row freshness contexts are
not renumbered after truncation. Ordering can still use unprojected variables.

This reduces sorting work and intermediate rows; it is not ordered-index
access or LIMIT push-down into matching. Partitioning and matching still
visit the full input. No formal asymptotic complexity theorem is claimed.

The adversarial ASK tests also found that the parser rejected a trailing
VALUES clause. The [SPARQL grammar's Query production](https://www.w3.org/TR/sparql11-query/#rQuery)
permits it after ASK. The parser now joins that clause into the ASK pattern,
preserving UNDEF/schema and propagating malformed-data errors. This narrow
correction does not implement ASK solution modifiers; those remain a separate
conformance gap. Refinement to the previous evaluator alone is not a universal
SPARQL conformance proof.

## Tests and verification

Tests were added before implementation. The new operator targets initially
failed because their APIs did not exist; ASK VALUES tests also recorded four
actual acceptance/evaluation failures against the old parser. Retained logs
are hashed in the evidence report.

- Indexed matcher guards include a 48-pattern by four-binding matrix, repeated
  variables, empty indexes, invalid subjects/predicates and language-tag case.
- Prefix guards compare five comparators over twelve prefix sizes, including
  ties, always-true/false and a non-transitive comparator.
- Final SELECT guards compare 800 combinations of ordering, projection,
  duplicate flags, offsets and limits against the full-sort specification.
- Snapshot guards exercise blank-node ASK, VALUES, hidden sort keys,
  DISTINCT/REDUCED, grouping/HAVING and BNODE freshness across slices.
- Native regression checks compare complete answers on the snapshot and fresh
  disk routes, then test recovery, pinned-generation/delta behavior and
  admission rejection.
- Large native checks verify full 100,000-row finite ascending and descending
  results and an offset near the end against the independent generated oracle.

`lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query
l4block-quad-query l4w3c` passes **701 jobs**. Audited new proofs use only Lean's
standard `propext`, `Classical.choice` and `Quot.sound` axioms where needed;
there are no custom axioms, `sorry` or `native_decide`. Native IBK3/IBK4/IBK5
complete JSON checks pass. The pinned W3C SPARQL 1.1 run remains **631 pass,
0 fail, 0 skip, 0 unsupported**. That run uses the reference/evaluator route
and existing harness tolerances; the exact native checks are separate.

## Measurement method

`tools/blockengine-snapshot-pair-bench.py` holds the archived and updated native
snapshots open over the same immutable 300,000-triple generated fixture.
Opening is separate from timing. One warmup precedes five measured samples
per binary, with alternating request order. Every complete JSON answer is
checked against the independent oracle outside the timed interval. Times
include serialization and JSONL transfer. Both snapshots stay resident, so
this is an implementation comparison, not a peak-memory comparison.

The competitor driver separately repeats all nine workloads with one warmup
and three alternating samples against each native competitor. Configurations,
exact-answer exclusions, HTTP/JSONL transport differences and memory scope
remain as [documented previously](20261011-shardborough-projection-and-competitor-sessions.md).
QLever's COUNT datatype and the bare Virtuoso endpoint's ASK result shape are
retained as explicit differences and excluded from paired timings. No answer
coercion is introduced. There are no builds, profilers or other database
benchmarks during timing windows. Ordinary OS activity remains and before/after
CPU observations are retained.

All raw samples, binary/source/driver hashes, correctness results and W3C
log hashes are in the [evidence report](20261011-shardborough-exists-and-ordered-prefix.json).

## Results and next work

Local before/after medians at 300,000 triples, in milliseconds:

| Query | Archived | Updated |
| --- | ---: | ---: |
| ASK present | 21.600 | 0.042 |
| ASK absent | 0.046 | 0.033 |
| Two-pattern join, 100,000 rows | 1,350.699 | 1,371.179 |
| Ordered OFFSET 3 LIMIT 7 | 852.300 | 318.482 |

The present-ASK row-allocation cost is removed on this probe. The ordered
slice improves about 2.7 times. Broad join latency is roughly unchanged;
there is no broad-join speedup claim.

Updated native competitor medians at 300,000 triples, in milliseconds. Each
Shardborough column belongs to its separate alternating competitor run.

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| LIMIT zero | 0.059 | 0.718 | 0.040 | 1.657 |
| Predicate COUNT | excluded | excluded | 9.774 | 1.199 |
| ASK present | 0.038 | 0.951 | excluded | excluded |
| ASK absent | 0.034 | 0.463 | excluded | excluded |
| Object lookup, 10,000 rows | 93.543 | 19.617 | 93.380 | 117.940 |
| Two-pattern join, 100,000 rows | 1,374.811 | 375.915 | 1,373.342 | 3,409.711 |
| Object-driven join, 10,000 rows | 137.235 | 39.416 | 137.160 | 248.592 |
| Three-pattern join, 100,000 rows | 1,692.214 | 572.191 | 1,675.938 | 4,986.492 |
| Ordered OFFSET 3 LIMIT 7 | 321.248 | 3.613 | 319.414 | 136.599 |

The ordered-slice gap to QLever is still about 89 times; Virtuoso is about
2.3 times faster on that slice. Shardborough’s simple present-ASK is faster
in this transport-inclusive comparison. Full joins still trail QLever by
about 3.0–3.7 times. These synthetic, single-client results do not establish
industry parity, and excluded answer shapes are not exact-answer successes.

The next large slice improvement needs a proved ordered access path that can
avoid producing every candidate binding. Broad joins also need compact term
IDs, cardinality access without row construction and better physical join
execution. Larger, varied workloads, concurrency, updates/recovery and peak
memory measurements remain required before an industry-parity claim.
