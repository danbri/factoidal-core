# Native string ordering — 2026-10-11

Shardborough's query ordering now compares strings through Lean's native
string-order primitive. The prior comparator allocated two character lists
on every comparison. Removing those lists improves complete-result queries
and preparation of the subject-order indexes.

## Implementation and proof

`SPARQL/StringOrder.lean` defines `strCompareFast` using the standard strict
string order: return -1 when left is smaller, 1 when right is smaller, and
0 otherwise. Lean defines this order as lexicographic Unicode codepoint
order and implements its decision procedure natively.

The module proves by induction on character lists that the original
`listCharCompare` equals this three-way lexicographic decision. The theorem
`strCompareFast_eq` then proves equality with the existing `strCompare`
for **all strings**. `strCompare_csimp` installs the proved function equality
as a compiler simplification. The specification and prior proofs still use
the original definition. There is no change to collation, RDF term ranks,
SPARQL ordering semantics or sort stability.

`Query.lean` imports this module before defining term-ordering callers.
Inspection of generated `Query.c` confirms that those callers invoke
`strCompareFast`; generated `StringOrder.c` invokes `lean_string_dec_lt`
without character-list construction. This uses Lean's existing native
primitive and its normal compiler/runtime trust boundary; no new foreign
implementation or custom axiom is introduced. Expression functions already
compiled in `Expr.lean` retain their earlier comparator calls. This change
does not claim to replace every string comparison in the system.

Both audited theorems depend only on `propext`, `Classical.choice` and
`Quot.sound`. There are no `sorry`, custom axioms or `native_decide` proofs.
The F* lineage is `formal/fstar/SPARQL11.Algebra.fst`'s `String.compare` calls
in literal, subject, term and evaluated-result ordering. The refinement of
the Lean character-list comparator is new Lean work; F* verification is not
used as proof of this implementation.

## Test-first validation

The focused test target was added first and failed on the missing module.
Nineteen guards include 529 pair comparisons over 23 specimen strings,
self-equality and reversal, empty/equal/prefix strings, long common prefixes,
embedded NULs, composed/decomposed text, two-/three-/four-byte codepoints,
the surrogate-gap boundary and the largest Unicode scalar value.

`tools/blockengine-string-order-test.py` checks the compiled snapshot and
fresh disk CLI against independent complete expected JSON documents. Its
27-row fixture includes NULs, Unicode boundaries and equal object values.
Both ascending and descending multi-key ordering are checked through full
answers and five finite slice cases, including LIMIT zero and offsets past
the end. All 24 native-route answers pass. Existing snapshot admission,
corruption, delta/CURRENT isolation, exact counts, error recovery and result
checks also pass, as do IBK3/IBK4/IBK5 JSON smokes.

```
cd formal/lean4
lake build L4Factoidal.SPARQL.StringOrder L4Factoidal.SPARQL.StringOrderTests
lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query l4block-quad-query l4w3c
```

The combined build passes 712 jobs. The W3C reference/evaluator run remains
631 pass, 0 fail, 0 skip, 0 unsupported. Its harness tolerances remain separate
from exact native answers and the universal comparator refinement.

## Measurements

The same immutable generated 300,000-triple graph as the
[metadata-count stage](20261011-shardborough-metadata-count.md) is used.
`tools/blockengine-snapshot-pair-bench.py` alternates archived/current
snapshots with one warmup and five measured samples per workload. Complete
JSONL serialization and transfer are timed; every full answer is checked
outside timing. Both snapshots remain resident. Opening is measured
separately. No build, profiler or other database benchmark overlaps the
timing windows. Ordinary OS activity remains and CPU observations are kept.

Paired medians, milliseconds:

| Query | Archived | Native string order |
| --- | ---: | ---: |
| Predicate COUNT | 0.052083 | 0.045125 |
| Object lookup, 10,000 rows | 91.770750 | 30.696500 |
| Two-pattern join, 100,000 rows | 1,352.909209 | 610.001834 |
| Object-driven join, 10,000 rows | 136.753625 | 75.310084 |
| Three-pattern join, 100,000 rows | 1,686.630750 | 928.137708 |
| Ordered OFFSET 3 LIMIT 7 | 0.083416 | 0.085625 |

The measured two-pattern join is 2.22 times faster. Object lookup is 2.99
times faster; that query includes ORDER BY, so this does not establish a
faster physical object-index read. Tiny count/slice differences do not
establish further improvements to those operators.

Opening was observed once per binary: 6.550 versus 1.912 seconds. RSS after
readiness was 192.906 versus 192.344 MiB, not peak RSS. The indexes are still
built eagerly and held in RAM. Faster comparisons reduce their preparation
cost; neither a persisted ordered index nor a general startup scaling claim
follows from this single fixture.

Separate native competitor medians, milliseconds:

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| limit-zero | 0.041 | 0.571 | 0.052 | 1.520 |
| predicate-count | excluded | excluded | 0.056 | 1.195 |
| ask-present | 0.042 | 1.021 | excluded | excluded |
| ask-absent | 0.032 | 0.445 | excluded | excluded |
| object-index | 31.781 | 19.408 | 30.836 | 117.685 |
| subject-join | 613.512 | 375.522 | 603.409 | 3300.741 |
| object-subject-join | 74.873 | 39.440 | 73.676 | 240.774 |
| subject-triple-join | 927.527 | 581.005 | 922.210 | 4879.288 |
| limit-slice | 0.146 | 3.881 | 0.141 | 139.285 |

Broad joins now take about 1.6 times the configured QLever time on this
fixture; the object-driven join is about 1.9 times. This narrows the earlier
gap but does not close it. Shardborough is faster than the configured
Virtuoso run on each exactly compared SELECT family here.

Known QLever COUNT datatype and Virtuoso ASK shape differences remain
recorded exclusions. Exact answers are never obtained by coercing those
differences away. Transports differ (JSONL versus HTTP), configurations are
pinned rather than claimed optimal, and clients are sequential. The small
synthetic graph and these measurements do not establish industry parity.

Raw samples, complete-answer checks, source/binary/log hashes, generated-C
inspection and commands are in the
[evidence report](20261011-shardborough-native-string-order.json).

## Remaining work

Broad joins still build string-keyed association-list bindings and evaluate
and count candidate buckets repeatedly. Compact term/row representations and
physical join execution remain next execution targets. Larger varied graphs,
persisted execution, concurrent workloads, updates/recovery and peak resource
measurements remain necessary to establish the original parity goal.

The separate diagnostic profile subsequently identified JSON escaping as the
largest remaining sampled cost. The next
[streaming-escape change](20261011-shardborough-streaming-json-escape.md)
retains the comparator and records its own proof, tests and measurements.
