# Complete-answer native repeats — 2026-10-10

- The JSON record `20261010-shardborough-core-repeat.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261010-shardborough-core-repeat.json) and is not in this tree.

`tools/blockengine-core-repeat.py` measures the core triple query tool's
`--json --repeat N --query QUERY` mode. Every iteration emits one complete
SPARQL Results JSON document and is checked against a known generated fixture.
This amortizes process startup, but **every iteration performs fresh admission**:
it is not a pinned generation, persistent admitted session, shared decoded/chunk
cache, or streaming result cursor.

## Reproduce

Build the native pack, activation and triple-query tools first. Do not run this
benchmark alongside builds, competitor pulls/servers or other benchmarks.

```sh
python3 tools/blockengine-core-repeat-test.py
python3 tools/blockengine-core-repeat.py --subjects 10 --repeat 2 --samples 1
python3 tools/blockengine-core-repeat.py --subjects 1000 --repeat 20 --samples 3
```

The default output directory is a retained `factoidal-core-repeat-*` temporary
directory; `--output-dir` must be absent or empty. To reuse the previous scale
fixture without packing/activation, add
`--reuse-dir /private/tmp/factoidal-core-scale-98028a36/subjects-1000`.
Reuse requires the exact generated fixture bytes for the requested subject
count. Binary, fixture and collection hashes must remain unchanged during a run.

The driver caps subjects (10–10000, multiples of ten), repeats (1–1000), samples
(1–10), per-process/global time, and combined stdout/stderr bytes. Oversized
expected answers are refused before setup; actual output is streamed with hard
byte limits. Timeouts, nonzero exits and malformed/incomplete/wrong answers fail
visibly and leave a partial report plus bounded raw outputs. No build is run.

## Actual run

The tiny validation passed 36 complete documents on 10 subjects/30 triples.
The retained 1000-subject/3000-triple run checked **720 complete documents**:
nine workloads, 20 repetitions per process, one excluded warmup process and
three measured processes per workload. All checks passed. It ran at
22:45:12–22:45:22 UTC in an exclusive native measurement window, before the
root helper checks at 22:46 UTC. Host: macOS 15.6.1, ARM64; Lean 4.33.1.

| Workload | Median process ms (20 iterations) | Amortized ms/iteration |
|---|---:|---:|
| LIMIT 0 | 28.139 | 1.407 |
| Predicate COUNT | 51.803 | 2.590 |
| ASK present | 51.463 | 2.573 |
| ASK absent | 28.666 | 1.433 |
| Object selection | 114.135 | 5.707 |
| Subject/name join | 544.736 | 27.237 |
| Object-driven subject/name join | 317.944 | 15.897 |
| Subject/name/group join | 776.522 | 38.826 |
| Ordered OFFSET 3 LIMIT 7 | 272.200 | 13.610 |

Raw measured samples, excluded warmups, expected-result/raw-output hashes, native
counter histograms and provenance are retained in
[`20261010-shardborough-core-repeat.json`](20261010-shardborough-core-repeat.json).
The full local report is
`/private/tmp/factoidal-core-repeat-1000-20261010/report.json`; its stdout/stderr
files total 24,374,000 bytes. These temporary raw files are not committed and
may be removed by OS cleanup. The compact JSON identifies the measured binary
and dirty source increment over core base `98028a368d508fe45ff90b5d98210af855d15532`.

## What is checked and timed

Known fixture subjects are unique padded IRIs, with one plain string name,
one type and one of ten IRI groups each. SELECT workloads use deterministic
`ORDER BY ?subject` except the empty LIMIT 0 result. Every binding, variable,
term field, row position and duplicate is checked; COUNT and ASK are exact.
Only JSON object-key order is ignored. No blank-node matching, datatype
coercion or general RDF semantic comparison is implemented. Negative controls
cover late corruption beyond the old ten-row preview, missing/duplicate/
reordered rows, missing/extra documents, incorrect COUNT, numeric-vs-boolean
ASK, duplicate JSON keys, non-JSON constants, truncated lines, output budgets
and timeout refusal.

Process timing includes startup, repeated parsing/admission/authenticated
reads/evaluation, complete JSON serialization and bounded output capture.
Fixture setup, hashing and complete-answer validation are outside the query
stopwatch. The OS page cache is not evicted. Dividing a batch wall time by 20
is an amortized observation, **not** an individual-query latency distribution
or sustained persistent-session throughput. Native logical/fetched range
counters are retained, but omit control files, Merkle sidecars, DLOG and some
failed speculative reads; they are not total disk IO.

These small-fixture numbers establish a reproducible full-answer repeat
baseline, not a speedup, large-corpus scaling result, general streaming-query
proof, or QLever/Virtuoso comparison.
