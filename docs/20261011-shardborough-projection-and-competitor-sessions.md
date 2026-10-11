# Projection correction and native competitor sessions — 2026-10-11

- The JSON record `20261011-shardborough-competitor-sessions.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261011-shardborough-competitor-sessions.json) and is not in this tree.
- The JSON record `20261011-shardborough-projection-conformance.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261011-shardborough-projection-conformance.json) and is not in this tree.

Shardborough now reports statically projected variables even for empty
SELECT-star answers and variables unbound in every row. Native warm-session
measurements against QLever and Virtuoso also identify the next performance
work: ordered slicing, present-ASK, cardinality access and broad joins.
Industry parity remains unproved.

The subsequent [indexed-ASK and ordered-prefix work](20261011-shardborough-exists-and-ordered-prefix.md)
addresses two measured gaps below. This report retains its original binaries
and samples; the follow-up contains separate before/after and competitor runs.

## Projection correction

The previous reference evaluator and native tools obtained SELECT-star
headers from returned bindings. Thus `SELECT * WHERE { ?s ?p ?o } LIMIT 0`
returned `head.vars=[]`, and all-UNDEF VALUES columns disappeared. This
contradicts the [in-scope-variable rule](https://www.w3.org/TR/sparql11-query/#variableScope)
and the [projected-variable JSON header rule](https://www.w3.org/TR/sparql11-results-json/#select-encode).

`QueryPattern.inScopeVars` and `Query.projectedVars` in `SPARQL/Query.lean`
now determine headers from the query. The collector includes GRAPH and
SERVICE endpoint variables, BIND aliases, both sides of joins/OPTIONAL/UNION,
path endpoints and recursively projected subqueries. It excludes query blank
nodes, variables used only in FILTER/EXISTS and the right operand of MINUS.
Explicit projections keep their declared order. SELECT-star header order is
unspecified by the standard; this implementation keeps first query occurrence
and removes duplicates. Solution mappings and their evaluation are unchanged.

The parser already preserves trailing VALUES as a pattern with its declared
column names, even for empty or all-UNDEF data. The earlier snapshot note's
concern about losing this parsed schema was an incorrect inference from the
legacy `postValues` field. No parser or query-AST representation change was
needed. Direct AST users of that legacy field can contribute only names
actually carried by its bindings; declared VALUES schema belongs in the
`.values names rows` pattern.

The reference evaluator, read snapshots, IBK3 JSON CLI and IBK4/IBK5 JSON CLI
all use the same header function. This deliberately corrects the Lean behavior
inherited from the F* `collect_distinct_vars_in_order` route; F* execution is
unchanged. Row-observation helpers remain available for callers that need them.

`ProjectionTheorems.lean` proves that reference headers equal the declared
projection for every query, graph and environment; headers are independent
of graph/environment; explicit projection order is preserved; and SELECT-star
headers contain no duplicate names. The existing snapshot LIMIT-zero theorem
now preserves the corrected reference header. Kernel checks report only
`propext`, `Classical.choice` and `Quot.sound`.

Twenty new pure guards include regressions that failed against the old implementation, then passed.
They cover empty results, zero limits, never-bound OPTIONAL variables, MINUS,
FILTER/EXISTS scope, BIND errors, empty/all-UNDEF VALUES, GRAPH/SERVICE, paths,
blank nodes and nested projections. The native snapshot regression failed
on the actual old binary before the fix. Snapshot/IBK3 and quad JSON tests
now check complete empty/UNDEF answers. Two older guards that depended on
output-binding header order were updated to query order.

Validation passes:

- `lake build L4Factoidal l4block-snapshot-session l4block-id-v3-query l4block-quad-query l4w3c`
  completes 693 jobs, including guards and proofs.
- Native snapshot and IBK3/IBK4/IBK5 complete JSON smoke tests pass.
- The pinned W3C SPARQL 1.1 manifest rerun remains **631 pass, 0 fail, 0 skip,
  0 unsupported**. This is the reference/evaluator route; the harness's
  existing comparison tolerances do not replace the exact new header guards.

The [retained correctness report](20261011-shardborough-projection-conformance.json)
records native responses, rejections, binary/test hashes, W3C submodule and
runner hashes, log hashes and toolchain.

## Native comparison method

`tools/blockengine-competitor-session-bench.py` creates one isolated competitor
index/database, starts its native server and opens a Shardborough snapshot
over the identical generated Turtle corpus. Publication/activation already
exist and are not timed. Competitor loading, port readiness and native snapshot
opening are recorded separately; those phases are different lifecycle costs
and must not be compared as ingestion parity.

Each workload has one warmup per engine and three measured samples with
alternating execution order. Queries are sequential from one client.
Shardborough uses JSONL pipes; competitors use loopback HTTP with a fresh
connection per request. Both timings include complete serialization and body
transfer. JSON parsing, exact validation and capture-file writes are outside
timing. The OS cache is retained. There are no concurrent builds or other
database benchmarks in these windows; ordinary host processes remain present.
Before/after CPU observations are retained. These are transport-inclusive
observations, not transport-normalized operator timings.

QLever 0.6.0 uses the previously hash-checked official ARM64 native archive.
Its result cache is disabled with `-c '0 B' -k 0`; `-j 1` permits one
simultaneous query. Operator parallelism retains engine defaults. Query memory
is capped at 1 GB. Virtuoso 7.2.17 uses the previously hash-checked Homebrew
ARM64 bottle with the full configuration retained: 10,000 buffers, 6,000 dirty
buffers, 256 MB query memory, one thread per query and no periodic checkpoint.
These are pinned configurations, not claims of optimal tuning. All servers
and child environments are local scratch resources and are stopped by the tool.

Every paired timed answer equals the complete independent generated oracle,
including header order for explicit SELECT, row positions, multiplicities and
RDF term fields. Only documented response extensions are removed. Known
differences stay explicit and receive **no paired timings**:

- QLever's scalar COUNT uses `xsd:int` instead of the expected `xsd:integer`.
- This bare Virtuoso endpoint emits SELECT-shaped ASK results rather than
  JSON booleans. Its strict JSON Accept behavior also requires the explicit
  format parameter and `Accept: */*` retained in the tool.

The report separates `measurement_valid` from `all_answers_exact`; all four
measurement reports are valid, and all four have explicit answer differences.
Five negative helper tests verify that exclusions check whole documents and
do not accept wrong counts, extra rows/variables, wrong ASK values/datatypes,
or silently discard unknown extensions.

## Results

The generated default graph has type, unique name and modulo-ten group
triples for each subject. Both 3,000- and 300,000-triple fixtures were measured
against each competitor. Raw reports, all samples, commands, configurations,
hashes, memory scope and excluded cases are in the
[retained evidence](20261011-shardborough-competitor-sessions.json).

At 300,000 triples, median latencies are milliseconds. Shardborough has a
separate interleaved run against each competitor; its samples are not pooled.

| Query | Shardborough / QLever run | QLever | Shardborough / Virtuoso run | Virtuoso |
| --- | ---: | ---: | ---: | ---: |
| LIMIT zero | 0.053 | 0.669 | 0.039 | 1.640 |
| Predicate COUNT | excluded | excluded | 9.192 | 1.219 |
| ASK present | 21.944 | 1.059 | excluded | excluded |
| ASK absent | 0.039 | 0.574 | excluded | excluded |
| Object lookup, 10,000 rows | 91.177 | 19.667 | 91.595 | 117.421 |
| Two-pattern join, 100,000 rows | 1,348.828 | 376.484 | 1,354.384 | 3,511.133 |
| Object-driven join, 10,000 rows | 134.566 | 39.710 | 134.877 | 245.510 |
| Three-pattern join, 100,000 rows | 1,653.018 | 571.844 | 1,663.066 | 5,135.812 |
| Ordered OFFSET 3 LIMIT 7 | 847.626 | 3.700 | 850.462 | 131.577 |

QLever's broad join advantage is about 2.9–3.6 times here. Ordered slicing
has the largest gap, about 229 times, and present-ASK about 21 times. The
Virtuoso run also shows ordered-slice and COUNT gaps, despite slower full
result joins under this configuration. A faster result for one configured
engine/workload is not an industry-parity result.

RSS was sampled immediately after startup/loading, before measured queries.
At 300,000 triples it is about 182 MiB for Shardborough, 25 MiB for QLever and
595 MiB for Virtuoso. These are **not peak-memory comparisons**: Shardborough
has already materialised its whole graph, whereas demand-paged competitor
indexes may become resident during queries. No post-query or concurrent-client
peak-memory claim follows from these samples.

The first large Virtuoso attempt failed because `file_to_string` rejected the
20,200,000-byte fixture at its 10 MiB limit. No query times were collected.
The tool now uses the documented [bulk loader](https://docs.openlinksw.com/virtuoso/rdfperfloading/)
and checks `LOAD_LIST` completion/error state before timing. The failed trial
remains explicitly discarded in the evidence. The earlier small Virtuoso
trial used TTLP and retains its own driver hash and loading command.

```sh
python3 tools/blockengine-competitor-session-bench-test.py
python3 tools/blockengine-competitor-session-bench.py \
  --engine qlever --server /path/to/qlever-server --loader /path/to/qlever-index \
  --library-dir /path/to/scratch-dylibs \
  --fixture-dir /path/to/subjects-100000 --subjects 100000 --samples 3 \
  --output-dir /path/to/empty-results-directory
```

For Virtuoso, select `--engine virtuoso`, its native `virtuoso-t` and `isql`,
and the relevant OpenSSL library directory. The installed unixODBC `isql` is
not the Virtuoso client.

## Next work toward parity

The measurements make query operators the next priority. Ordered slicing
currently sorts a broad binding sequence before discarding almost all rows.
Present-ASK constructs every matching binding, and exact COUNT/estimates scan
candidate lists. Early-exit existence, retained cardinalities, bounded ordered
selection and ID-based joins need Lean contracts and failing regressions.

The goal also requires larger real graphs, feature-specific workloads,
representative tuning, ingestion, peak memory, disk-scale execution, concurrent
clients and standards-correct endpoint behavior. None is established by this
synthetic nine-query, single-client comparison.
