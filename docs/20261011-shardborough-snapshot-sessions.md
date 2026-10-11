# Shardborough native read snapshots — 2026-10-11

Shardborough now has a Lean-native session that admits one immutable IBK3
generation, replays its default-graph DLOG, materialises the merged graph and
builds an index once. Queries reuse that admitted value. This closes the
per-query admission gap identified in the [page-cache work](20261010-shardborough-page-caches.md).
It does not establish QLever/Virtuoso parity.

## Contract and use

```sh
(cd formal/lean4 && lake build L4Factoidal l4block-snapshot-session)
printf '%s\n' '"SELECT ?s WHERE { ?s ?p ?o } ORDER BY ?s LIMIT 10"' \
  '"ASK { ?s ?p ?o }"' |
  formal/lean4/.lake/build/bin/l4block-snapshot-session /path/to/collection
python3 tools/blockengine-snapshot-session-test.py --report /tmp/session-check.json
```

The first stdout line is a JSON readiness record. Each subsequent request is
one JSON **string** containing SPARQL, followed by a newline. JSON escaping
supports multiline queries and Unicode. Each response is one complete SPARQL
Results JSON document or an error object. Output is flushed after every line;
EOF closes the session. Invalid framing, parse errors and unsupported query
forms return errors without poisoning the next request. SELECT and ASK are
supported; graph-result and update requests require their separate interfaces.
`BASE` supplies expression IRI resolution, and the native edge captures a
single UTC timestamp per request for `NOW()`.

The session pins the resolved generation and a strictly replayed DLOG at open.
Later delta updates, CURRENT switches and file damage do not change its
answers. A newly opened session sees the newer state or rejects damaged
storage. Admission authenticates all committed artifacts before readiness;
there are no collection reads during query execution. Dataset clauses use
the existing reference evaluator and local dataset policy: this default-only
store does not fetch unavailable FROM graphs from the network.

The implementation holds the complete decoded graph and its in-memory
indexes. Readiness takes longer than opening one selective query, and memory
grows with the graph. There is no eviction, live refresh, HTTP endpoint,
parallel request scheduler or bounded-memory ID cursor execution in this
increment. These remain material parts of the database parity goal.

The readiness record's `admissions` and `index-builds` fields describe the
one-time construction in the native control flow; they are not allocation
profiler measurements. Its byte counters cover the existing artifact range
reads, not total disk IO or all control/sidecar reads.

## Lean implementation and assurance

- `SPARQL/PreparedSnapshot.lean` holds the graph, index and `Index.Wf` proof.
  SELECT/ASK reuse the indexed evaluator; dataset clauses use the reference
  evaluator. The caller can supply a request-specific query environment.
- `Harness/SnapshotSession.lean` owns admission, strict replay, JSONL framing,
  request clocks and IO. It uses the existing generation resolver and Merkle
  materializer rather than a second storage parser.
- `PreparedSnapshotTheorems.lean` proves that the prepared backend is the
  ordinary indexed backend and that every valid snapshot materialises its
  exact graph, preserving order and multiplicities. This is a boundary proof,
  not a new universal refinement of the entire backend query evaluator.

Measurements exposed a needless full candidate scan for `LIMIT 0`. The new
session returns the declared empty SELECT result before backend evaluation.
`selectPost_limit_zero`, `evalSelect_limit_zero` and `run_limit_zero` prove
agreement with the reference result for every admitted graph, SELECT form,
dataset clause, offset, ordering, grouping and post-VALUES input. All checked
proofs use only `propext`, `Classical.choice` and `Quot.sound`.

The initial implementation inherited a conformance gap: the reference evaluator built
`SELECT *` headers from returned rows, so empty answers had an empty header
and always-unbound variables could disappear. The
[SELECT projection rule](https://www.w3.org/TR/sparql11-query/#select)
instead selects in-scope variables, and the
[JSON header rule](https://www.w3.org/TR/sparql11-results-json/#select-encode)
requires the projected variables even when they are unbound. The initial zero-limit
proof preserved the old reference behavior; it did not certify that
header rule. The measurements use explicit SELECT variables and are unaffected.
The [projection and competitor follow-up](20261011-shardborough-projection-and-competitor-sessions.md)
corrects this in the Lean evaluator and native tools, with new failing-first
guards and revised zero-limit proofs. The parser already retains trailing
VALUES schema; the earlier concern about losing it was an incorrect inference
from the legacy AST field. The performance measurements above remain historical
measurements of their recorded binaries and explicit-projection workloads.

## Test-first evidence

The new guard suite and native test failed first with the implementation
absent. A later BASE-expression regression failed against the actual initial
implementation, then passed after query-base propagation. The LIMIT-zero
shortcut's proof obligation failed before adding that branch and now passes.

There are 23 pure guards covering exact projected answers, a non-functional
star join, OPTIONAL, MINUS, EXISTS/NOT EXISTS, VALUES, subqueries, aggregates,
language-tag equality, unavailable dataset clauses, BASE, NOW, zero limits
and unsupported forms. The native test compares complete known answers and
tests actual INSERT/DELETE replay, old/new sessions across CURRENT changes,
malformed DLOG, damaged committed bytes, unsafe pointers, unactivated direct
generations and continued reads after storage damage. Its
[retained report](20261011-shardborough-snapshot-session-correctness.json)
includes every response and rejection plus binary/test hashes.

`lake build L4Factoidal l4block-snapshot-session` passes all 627 build jobs,
including library guards and proof checks. The native session test, existing
complete-result smoke and repeat-driver negative tests also pass. The existing
[631-case SPARQL 1.1 run](20261011-shardborough-sparql-conformance.json) is a
reference-evaluator result, not conformance certification of this session.

## Measurements

`tools/blockengine-snapshot-session-bench.py` checks every complete ordered
answer against the independent generated oracle. Each query has one warmup
per mode and three measured samples, alternating mode order. Parsing answers,
validation and writing captured stdout files are outside timing. The full
JSON output and its transfer through the pipe are included. Fresh mode also
includes process startup, admission and exit; snapshot mode starts after
readiness. OS caches remain populated. No build or competing database
benchmark ran during these windows; ordinary host background processes were
present and before/after CPU snapshots are retained.

The corpus has three triples per subject: type, unique name and modulo-ten
group. It is a synthetic default graph, not a representative feature suite.
All nine workloads at all three sizes passed, including every warmup: 216
complete answer documents. Medians below are milliseconds.

| Triples | Query | Fresh admission | Open snapshot |
| ---: | --- | ---: | ---: |
| 3,000 | Two-pattern subject join | 52.053 | 9.793 |
| 3,000 | Three-pattern subject join | 62.340 | 12.457 |
| 3,000 | Object-driven subject join | 41.320 | 0.965 |
| 30,000 | Two-pattern subject join | 306.204 | 116.809 |
| 30,000 | Three-pattern subject join | 431.192 | 143.783 |
| 30,000 | Object-driven subject join | 158.613 | 11.048 |
| 300,000 | Two-pattern subject join | 6,014.164 | 1,343.800 |
| 300,000 | Three-pattern subject join | 9,013.532 | 1,664.289 |
| 300,000 | Object-driven subject join | 1,614.355 | 133.851 |

| Triples | Snapshot admission/indexing (ms) | RSS after readiness (MiB) |
| ---: | ---: | ---: |
| 3,000 | 37.940 | 22.656 |
| 30,000 | 162.252 | 35.516 |
| 300,000 | 1,780.510 | 181.688 |

RSS is one resident-memory sample after readiness, not peak RSS. Opening is
one measured event per size, not a median. These are separate execution and
freshness modes; the ratios do not mean a live database query became faster
without paying startup or memory costs.

The full workload measurements precede the LIMIT-zero shortcut and retain
that binary's hash. A separate five-sample targeted measurement of the final
binary at 300,000 triples passed all complete-answer checks: open-session
`LIMIT 0` median **0.059 ms**, versus **9.414 ms** in the earlier session
implementation. The unchanged fresh CLI measured **27.373 ms** in that later
window. This is a separately recorded follow-up, not an interleaved old/new
binary speedup trial.

The [machine-readable evidence](20261011-shardborough-snapshot-session-benchmark.json)
retains unchanged raw reports, per-sample timings, complete-output hashes,
fixture/collection/binary/driver hashes, host/toolchain, queries and memory
scope. The new LIMIT-zero result is kept separately from the earlier stage.

```sh
python3 tools/blockengine-snapshot-session-bench.py \
  --fixture-dir /path/to/subjects-100000 --subjects 100000 --samples 3 \
  --output-dir /path/to/empty-results-directory
```

## Remaining work toward parity

The [follow-up](20261011-shardborough-projection-and-competitor-sessions.md) now
records same-workload, transport-inclusive warm QLever/Virtuoso measurements.
Representative industry parity is still unproved. Native
QLever and Virtuoso correctness probes are available; their recorded COUNT
datatype and bare-endpoint ASK differences must remain explicit. The next
comparison needs pinned server settings, complete results, memory and startup
costs, and clearly separated core versus HTTP transport timings.

At 300,000 triples, broad joins still take over a second and ordered slicing
still processes a broad candidate set. Exact estimates scan candidates,
ASK evaluates complete matching sequences, and decoded RDF terms and binding
lists dominate the execution model. Useful next changes are retained
cardinality statistics, early-exit existential reads, ID-based joins and late
term decoding. Larger real graphs, feature-isolating queries, bounded-memory
storage/ingestion and concurrent-client behavior remain unmeasured.
