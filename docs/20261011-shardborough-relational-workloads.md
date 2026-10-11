# Varied query workloads and exact planner counts — 2026-10-11

The broader corpus found two defects that the earlier star-join fixture did
not expose: aggregates nested inside functions could become unbound, and
three-step chain joins repeatedly scanned large buckets during planning.
Both fixes are implemented in Lean. The original industry parity goal
remains open.

## Corpus and complete answers

`tools/blockengine-relational-corpus.py` constructs people, organisations,
cyclic links, names, optional aliases, alternative affiliations and integer
scores. Its independent answer oracle uses construction formulas, without
running a SPARQL evaluator. Five hand-checked small tests cover the oracle.
There are nine query families: two- and three-step chains, a dimension join,
a selective chain, OPTIONAL, UNION DISTINCT, grouped counts, numeric top-k
and VALUES with a chain. All queries specify deterministic result ordering.

This controlled synthetic corpus is not LUBM, BSBM or SP2Bench. It does not
represent a production dataset or all SPARQL features. Group counts use
`STR(COUNT(?subject))` in the query itself. The expected result is a string;
the comparison does not coerce differing numeric result datatypes.

The corpus has `5N + ceil(N/7) + ceil(N/11) + min(N,100)` triples. Native
preparation uses the existing Lean pack, activation and snapshot admission
executables. Preparation and correctness checks are outside query timings.
The comparator and local pair drivers now accept an explicit corpus and
workload selection. Their prior scale corpus remains the default. These
drivers explicitly bound collection hashing to 512 MiB and 1,024 entries,
configurable up to 4,096 entries, and response captures to 512 MiB by
default, configurable up to 2 GiB.
Each response still has a 64 MiB cap. Tests cover corpus selection, byte and
file limits, and symbolic-link rejection. The original collection helper's
64 MiB/128-entry defaults remain in force for its other callers.

## Correctness before measurement

The first QLever pilot at 5,334 triples failed on the complete grouped
answer. Shardborough returned each organisation with an unbound count.
`Query.rewriteAggregates` and `exprHasAggregate` did not traverse ordinary
string and other function arguments completely. The parser's optional
argument detection also called that incomplete runtime predicate.

Seventeen test-first guards cover nested STR, CONCAT, COALESCE, IF, unary
minus, optional arguments, implicit grouping, empty input and group counts.
Sixteen fail before the implementation change; the independent subquery
scope guard already passes. Runtime rewriting and aggregate detection now
traverse every expression constructor, argument list and optional argument.
EXISTS bodies keep their independent query scope. Native tests check nested
counts through both fresh disk queries and pinned snapshots.

`AggregateExpressionTheorems.lean` proves for all expressions that rewriting
removes aggregates in the current expression scope and runtime detection
agrees with the parser. A separate universal witness establishes the lexical
result of `STR(COUNT(*))` for every solution group. These are narrow contracts,
not a complete proof of SPARQL aggregate semantics. The existing aggregate
result conversion policy for blank nodes and triple terms is unchanged.

The F* lineage is `formal/fstar/SPARQL11.Algebra.fst`, `rewrite_aggregates`
and `expr_has_aggregate`. Their traversal is likewise incomplete. This is
a deliberate Lean extension, without a claim of a corresponding F* proof.
The failed pilot is retained with `measurement_valid=false`; none of its
partial timings establishes a performance result for the corrected program.
Corrected small pilots against both competitors match all nine full answers.

## Exact cached estimates

At 523,477 triples the original three-step chain query hits the native
120-second response cap. The failed report and shutdown diagnostics remain
retained. A separate profile of the smaller, validated chain finds the
planner's `chooseBestTpBackend` in 3,421 of 3,864 sampled worker stacks.
The planner repeatedly estimated an unbound predicate by reversing,
filtering and counting its entire bucket for each intermediate binding.
Profiled requests are excluded from latency measurements.

`OWL.RL.Index` now maintains a hash map of exact predicate-match counts.
Its proof field equates each cached count to the corresponding bucket's
filtered length, including duplicates. `empty` and `push` construct this
certificate. It applies even without a whole-graph well-formedness premise.
The proof is erased at runtime; insertion adds one count-map lookup/update
per triple. Persistence formats and the query planner's choices do not change.

`RDF.StoreCapabilities.igEstimateFast` uses the existing graph array size
for a completely unbound request and the new map for a predicate-only
request. All other bounds still search and count, including language-tag
and XML literal equality fallbacks. `igEstimateFast_eq` proves equality
with the original estimate for every index and bound; `igEstimate_csimp`
installs the proved compiler replacement. Generated C confirms the array
size/map lookup and the retained search fallback.

Ten test-first guards cover duplicates, empty indexes, missing predicates,
push, language-tag case and two complete 64-bound matrices. The old snapshot
used for paired performance measurements already contains the aggregate
correctness fix. Thus those timings isolate the count optimization.
The audited aggregate and estimate theorems use only `propext`,
`Classical.choice` and `Quot.sound`; no custom axiom, `sorry` or
`native_decide` is introduced.

The estimate's F* lineage is `RDF.Store.Capabilities.fst`'s `caps_of_indexed`
and its `SPARQL11.Algebra.fst:ig_estimate` calls. F* already special-cases
whole-graph cardinality; the certified predicate cache is a new Lean
implementation and refinement, not a ported F* theorem.

## Validation and results

The targeted guards/proofs pass. The initial combined native/library build
passes 716 jobs; the final build including pack and activation passes 739.
The W3C reference/evaluator suite passes 631 tests, with zero
failures, skips or unsupported entries; its existing comparison tolerances
remain. Separate native tests validate full JSON answers, admission failures,
snapshot isolation, nested aggregates, and Unicode/control-character sorting
and escaping. Complete IBK3/4/5 JSON smokes pass. Oracle/helper tests pass.

The local 5,334-triple pair uses one warmup and five alternating samples.
Three-step chain medians change from 26.055 to 2.919 ms; the selective chain
changes from 0.403 to 0.082 ms. Grouping stays about 4.27 ms, as expected
because its algorithm is unchanged. Every answer matches the complete
independent oracle. The failed larger trial is a capped failure, not an
exact before-time or a speedup ratio.

At 523,477 triples, both competitor trials use one warmup and three
alternating samples per query. All nine full answers match, without answer
exclusions or numeric coercion. Medians in milliseconds:

| Query | Shardborough paired with QLever | QLever | Shardborough paired with Virtuoso | Virtuoso |
|---|---:|---:|---:|---:|
| Two-step chain | 268.166 | 386.263 | 265.953 | 3,407.140 |
| Three-step chain | 361.081 | 396.836 | 360.717 | 3,396.565 |
| Dimension join | 247.218 | 390.376 | 244.439 | 3,381.610 |
| Selective chain | 4.895 | 9.504 | 4.384 | 25.589 |
| OPTIONAL alias, LIMIT 25 | 98.405 | 7.998 | 98.567 | 141.225 |
| UNION DISTINCT | 174.435 | 10.022 | 169.432 | 3.670 |
| Grouped string count | 819.628 | 2.822 | 793.894 | 5.308 |
| Numeric top-k | 51.507 | 1.750 | 51.591 | 7.412 |
| VALUES chain | 170.077 | 5.768 | 173.585 | 2.229 |

The broader results overturn any inference of general parity from the
earlier star joins. Grouping, duplicate removal and selective execution
remain large gaps. The QLever-paired snapshot opens in 3.04 seconds and
uses 311.8 MiB RSS after readiness; these are single opening observations,
not peak-memory or ingestion comparisons.

At 1,570,231 triples, QLever again matches all nine complete answers.
The same warmup/three-sample procedure gives these medians, milliseconds:

| Query | Shardborough | QLever |
|---|---:|---:|
| Two-step chain | 867.416 | 1,170.786 |
| Three-step chain | 1,171.153 | 1,206.241 |
| Dimension join | 825.922 | 1,188.978 |
| Selective chain | 14.500 | 21.947 |
| OPTIONAL alias, LIMIT 25 | 333.387 | 16.312 |
| UNION DISTINCT | 639.335 | 22.341 |
| Grouped string count | 5,767.229 | 4.412 |
| Numeric top-k | 161.611 | 2.943 |
| VALUES chain | 583.533 | 10.129 |

Snapshot opening is 9.07 seconds and RSS after readiness is 867.9 MiB,
again a single opening observation rather than peak resource usage. The
larger collection contains 1,467 files. Result captures total 762.7 MiB,
within the explicitly raised 2 GiB budget. The grouped count has only 100
output rows: its delay is execution, rather than full-result transfer volume.

The separate Virtuoso comparison also matches all nine complete answers
at 1,570,231 triples. Medians, milliseconds:

| Query | Shardborough | Virtuoso |
|---|---:|---:|
| Two-step chain | 868.750 | 10,471.248 |
| Three-step chain | 1,183.651 | 10,770.723 |
| Dimension join | 818.438 | 10,560.348 |
| Selective chain | 14.759 | 74.338 |
| OPTIONAL alias, LIMIT 25 | 332.267 | 409.867 |
| UNION DISTINCT | 638.792 | 5.968 |
| Grouped string count | 5,725.969 | 8.586 |
| Numeric top-k | 162.108 | 21.250 |
| VALUES chain | 582.188 | 2.224 |

The Virtuoso-paired snapshot opens in 9.11 seconds with 867.9 MiB RSS
after readiness; Virtuoso reports 788.4 MiB at that point. These observations
do not measure peak memory, query allocations or equivalent storage models.
Native preparation of the large corpus takes 59.74 seconds for packing and
26.38 seconds for activation in one observation, separately from queries.

A separate post-measurement grouping profile first validates the complete
100-row answer at 523,477 triples, then checks seven repeated byte-identical
responses. Group accumulation appears in 3,715 of 3,852 worker samples;
row-list append appears in 1,411. The current `addToGroups` scans/maps the
group list and repeatedly appends each row to its group. This identifies
the next work: stable hash grouping and efficient row accumulation, with
exact grouping-equality and row-order proofs. That work is proposed, not
implemented by this increment; profiled requests are not timing samples.

Raw evidence, hashes, configurations, samples and later larger results are
recorded in [the machine-readable record](20261011-shardborough-relational-workloads.json).
Queries run sequentially with full rendering and transfer timed; parsing,
validation and capture writes are outside timing. Shardborough uses JSONL
and the competitor uses HTTP. Opening and RSS after readiness are separate;
RSS is not peak memory. Builds, profiling and database benchmarks do not
overlap timing windows. Ordinary host activity remains recorded.

QLever is 0.6.0 with result caching disabled (`-c '0 B' -k 0`), a 1 GB
query memory limit and `-j 1`. That last setting limits concurrent queries;
operator parallelism retains its default. Virtuoso is 7.2.17 with the
retained configuration specifying one thread per query and 256 MB query
memory. This is not a normalized execution-resource or tuning comparison.
The larger corpus explicitly uses a 1 GB QLever loader budget, 4,096
collection entries and a 2 GiB capture budget. These bounds are recorded
per run; the smaller trials retain their earlier settings.

To reproduce preparation and the native pair after building the binaries:

```sh
python3 tools/blockengine-relational-corpus-test.py
python3 tools/blockengine-corpus-prepare.py --corpus relational --subjects 1000 \
  --output-dir /tmp/shardborough-relational-1000
python3 tools/blockengine-snapshot-pair-bench.py --corpus relational --subjects 1000 \
  --fixture-dir /tmp/shardborough-relational-1000 \
  --before ARCHIVED_SNAPSHOT --after formal/lean4/.lake/build/bin/l4block-snapshot-session \
  --samples 5 --output-dir /tmp/shardborough-relational-pair
```

The competitor driver takes `--corpus relational`, the same fixture size
and directory, explicit server/loader/library paths, samples and an empty
output directory. Exact executable commands and configurations are retained
in the machine-readable reports. For the 300,000-subject fixture, add
`--collection-max-files 4096 --capture-mib 2048` and, for QLever,
`--loader-memory '1 GB'`. Preparation uses the corresponding file bound.

Remaining work includes larger and standard datasets, grouping and selective
query plans, resource normalization, sustained concurrency, persisted ordered
access, updates and recovery. These results do not establish industry parity.
