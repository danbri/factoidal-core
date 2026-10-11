# Shardborough page selection, decoded caches and QLever probe

Date: 2026-10-10. Base: `98028a368d508fe45ff90b5d98210af855d15532`.
The worktree already contained serializer, Nat posting-selection and benchmark
changes. This increment preserves that work. QLever/Virtuoso performance
parity remains an active objective, not an achieved result.

## Lean implementation and proof

`Storage/SubjectRowIndexWireV2.pagesForArray` exposes the existing binary
directory search over an array. `pagesFor` keeps its previous list interface.
`Storage/SubjectPageSelection.candidatePages` converts a directory once per
batch and replaces page-reference `List.eraseDups` with a hash set. It still
deduplicates the complete `(ordinal, PageRef)` value and sorts the result by
ordinal. It does not collapse two inconsistent references merely because
their ordinal agrees.

`SubjectPageSelectionTheorems.candidatePages_eq_reference` proves exact
list equality with the old algorithm for **every** directory and requested
ID list. The result includes page identity and read order; the theorem needs
no sortedness premise. It does not prove that an unadmitted directory is a
complete index. Existing activation and corruption checks retain that duty.

`Storage/PageCache` provides artifact-local decoded pages keyed by page
number. `PageCacheTheorems.lookup_ofList` proves lookup equals the previous
first-match list lookup, including duplicate page keys and missing pages.
`term_ofList` proves exact optional term equality for every page list, page
width and term ID, including malformed widths and out-of-range offsets.
`lookup_insert` supplies the update contract for the incrementally decoded
TLI1 cache.

`Harness/IndexedBlockV3Materialize` uses these caches for TLI1 cache hits,
sparse PTD1 row reconstruction and TLI1/PTD1 term agreement. Each cache stays
inside one artifact read; it stores authenticated decoded pages. It does not
persist across queries or replace admission. Existing subject/predicate
checks, term-array bounds and Merkle reads remain in the execution path.

These are landed Lean implementations and landed **page/term lookup
refinements**. They are not a universal proof of the IO materializer or whole
SPARQL engine. No F* source changes are made. The semantic lineage is
`formal/fstar/SPARQL11.Algebra.fst`; the immediate executable storage
reference is the checked-out Lean materializer and SRI2 search. The changes
add no custom axioms, admissions, native-decide proofs or partial definitions.
The axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.

## Test-first validation

The two regression modules were written and invoked before their respective
implementation modules existed; both initially failed on the missing import.
The final 19 guards cover spanning postings, inclusive boundaries, duplicate
requests, read ordering, absent pages, inconsistent duplicate references,
first-occurrence cache values, cache overwrites, large Nat keys, zero page
widths and missing array cells. The full library imports tests and theorems.

Validation in this checkout:

```sh
cd formal/lean4
lake build L4Factoidal.Storage.SubjectPageSelectionTests L4Factoidal.Storage.SubjectPageSelectionTheorems
lake build L4Factoidal.Storage.PageCacheTests L4Factoidal.Storage.PageCacheTheorems
lake build L4Factoidal l4block-id-v3-query
cd ../..
python3 tools/blockengine-core-repeat-test.py
python3 tools/blockengine-results-json-smoke.py
tools/blockengine-ibk3-persistent-smoke.sh
tools/blockengine-ibk3-direct-select-smoke.sh
tools/blockengine-ibk3-compact-smoke.sh
```

All pass. JSON smokes cover IBK3, IBK4 and IBK5; lifecycle smokes cover
activation, selective reads, delta replay, compaction and refusal cases.
After initializing the pinned W3C submodule at
`35c503a6323db83c2e54ff404387210c20d57c18`, a fresh `l4w3c` run on
`sparql/sparql11/manifest-all.ttl` passes **631 of 631** tests, with zero
failures, skips or unsupported cases. This checks the reference/evaluator
route, not the native disk backend. The [validation record](20261011-shardborough-sparql-conformance.json)
pins the runner and log hashes.

Mutation controls also pass: restricting candidate selection to one page
fails four spanning/order guards; reversing cache insertion order fails three
first-occurrence guards. Restoring the implementations restores the passing
tests and full build. The final native binary hash agrees with the binary used
for the JSON/lifecycle and large-result checks.

The [large-result check](20261010-shardborough-page-cache-large-correctness.json)
validates every ordered binding of both 100,000-row joins after the decoded
cache change, on the 300,000-triple store. Its times are excluded because of
host contention.

## Batch page-selection measurement

The [retained reports](20261010-shardborough-page-selection-benchmark.json)
contain every sample, exact query and command, fixture/collection and binary
hashes, output hashes and physical counters. The baseline executable was
copied before the page-selection change and already includes the pre-existing
Nat posting-selection and JSON changes. The optimized executable adds only
batch page selection. The later decoded-page cache is a separate increment.

Host: macOS 15.6.1 ARM64, Lean 4.33.1. Each query/binary has one excluded
warmup and three measured fresh processes. Order alternates between binaries.
Timings include startup, admission, reads, evaluation, ORDER BY and full JSON
serialization/output. Fixture setup and complete-answer validation are outside
timing. OS caches are not evicted. Every sample equals the independently
generated complete ordered answer. Physical modes and range counters agree.

| Triples | Query | Before ms | Batch selection ms |
| ---: | --- | ---: | ---: |
| 3,000 | Subject join | 51.733 | 51.660 |
| 3,000 | Object-driven join | 40.902 | 40.735 |
| 3,000 | Three-pattern join | 62.118 | 61.998 |
| 30,000 | Subject join | 322.251 | 314.218 |
| 30,000 | Object-driven join | 160.166 | 161.018 |
| 30,000 | Three-pattern join | 453.166 | 450.711 |
| 300,000 | Subject join | 6,104.138 | 5,943.786 |
| 300,000 | Object-driven join | 1,742.365 | 1,744.718 |
| 300,000 | Three-pattern join | 10,257.405 | 9,597.107 |

The native effect is modest. No general throughput or memory improvement is
claimed. Range counters exclude some control, Merkle-sidecar, delta and failed
speculative reads; they are not total disk IO. An earlier exploratory scale
run overlapped small builds and is excluded from this comparison.

The decoded-page-cache timing trial is **discarded**: unrelated Lean work and
heavy Chrome CPU activity were observed, and the unchanged baseline warmup
rose to 35.815 seconds from approximately six seconds. The trial was stopped;
its incomplete report is retained. It establishes no cache speedup or slowdown.
No unrelated user process was stopped. New timings require a usable host window.

Reproduce a paired run after preserving the relevant baseline binary:

```sh
python3 tools/blockengine-page-selection-bench.py \
  --baseline /path/to/archived-query \
  --fixture-dir /path/to/subjects-100000 --subjects 100000 \
  --samples 3 --output-dir /path/to/fresh-results
```

Large stores, output documents and logs stay in local `.codex-runs/`, excluded
through `.git/info/exclude`. Retained JSON records their paths and hashes.

## Native QLever differential probe

The [official Homebrew formula](https://github.com/qlever-dev/homebrew-qlever/blob/main/Formula/qlever.rb)
provides QLever 0.6.0 ARM64. Its archive was downloaded into ignored scratch
storage and its published SHA-256 was checked:
`e496c08902a8e4a2262dfcea8106f00feaa6060cabdfcf55e4838639396022f3`.
The missing jemalloc dylib was extracted from a hash-checked Homebrew bottle
into the same scratch directory. No system package or configuration changed.
QLever reports version `v0.6.0`.

`tools/blockengine-qlever-smoke.py` builds an isolated QLever index from the
exact 1,000-subject / 3,000-triple Turtle fixture also stored by Shardborough.
It executes nine queries, captures complete answers and stops its own server.
It limits query memory to 1 GB and disables QLever result caching. Its listener
uses QLever's default address on a temporary port; requests use loopback. The
fixture contains generated data only. The probe is a correctness comparison,
not a latency benchmark. Process modes differ and the host was contended.

[The retained probe report](20261010-shardborough-qlever-correctness.json)
records commands and hashes. Shardborough matches all nine generated answers.
QLever matches eight after excluding only its top-level `meta` extension.
COUNT's numeric value is equal, but QLever emits `xsd:int` where the reference
and Shardborough emit `xsd:integer`. The tool reports that exact-term mismatch
separately and checks the complete alternate document; it does not silently
coerce types. See [QLever's compliance record](https://docs.qlever.dev/compliance/).

```sh
python3 tools/blockengine-qlever-smoke.py \
  --qlever-index /path/to/qlever-index --qlever-server /path/to/qlever-server \
  --library-dir /path/to/scratch-dylibs \
  --fixture-dir /path/to/subjects-1000 --subjects 1000 \
  --output-dir /path/to/fresh-qlever-probe
```

## Native Virtuoso differential probe (2026-10-11)

A hash-checked Homebrew ARM64 bottle of Virtuoso 7.2.17 was extracted into
ignored scratch storage. Its SHA-256 is
`34460ec8da9cdde5e97f8b6a22ffe3a012b5cbcac6b634311d334ae9dcc41028`;
the native server reports `7.2.17.3243-pthreads (440dbf41b3)`. The existing
OpenSSL 3 library is supplied to its child process through `DYLD_LIBRARY_PATH`.
No package was installed. SQL and HTTP listeners bind to loopback temporary
ports, and the probe stops its own process.

`tools/blockengine-virtuoso-smoke.py` loads the identical generated 3,000
triples with `TTLP` into `urn:shardborough:fixture`, then uses that graph as the
protocol default graph. This follows the documented
[Virtuoso default-graph parameter](https://docs.openlinksw.com/virtuoso/rdfdefaultgraph/).
The [retained report](20261011-shardborough-virtuoso-correctness.json) records
the complete configuration, commands, output hashes and answer differences.

All **seven SELECT answers match**, including COUNT's `xsd:integer` datatype.
The comparison explicitly removes optional `head.link` metadata and Virtuoso's
`results.distinct` / `results.ordered` extensions. ASK returns a SELECT-shaped
`__ASK_RETVAL` integer binding (`1` / `0`) in this minimal native setup, rather
than the standard JSON boolean document. Both cases remain explicit failures;
the tool exits nonzero. It does not coerce those bindings to booleans.

The same minimal endpoint returns 406 to a strict JSON Accept header. With
the documented `format=application/sparql-results+json` parameter and
`Accept: */*`, it returns JSON under `Content-Type: text/html`. The report
retains the actual header. These are observations of this bare configuration,
not claims about all Virtuoso deployments. Resolving its endpoint configuration
is still needed before a protocol-inclusive comparison.

```sh
python3 tools/blockengine-virtuoso-smoke.py \
  --virtuoso-server /path/to/virtuoso-t --virtuoso-isql /path/to/virtuoso-isql \
  --library-dir /path/to/openssl/lib \
  --fixture-dir /path/to/subjects-1000 --subjects 1000 \
  --output-dir /path/to/fresh-virtuoso-probe
```

Initial load syntax and strict-Accept failures remain in scratch logs and are
excluded from correctness totals. No competitor timing is claimed.

## Remaining parity work

No competitor timing is claimed. The next measurement needs
same-host pinned QLever and Virtuoso, complete answer checks, separate ingestion
and query phases, explicit cache/process modes, memory and per-query latency.
The fresh-admission CLI cannot represent a warm database server session.
The [2026-10-11 snapshot-session follow-up](20261011-shardborough-snapshot-sessions.md)
adds retained admission and indexing with explicit frozen-snapshot semantics,
and separately records its startup and memory costs. A concurrent HTTP
database server and representative competitor timings remain work.

The broader workload should include real graphs and SPARQL features beyond
these stars. [Sparqloscope](https://github.com/ad-freiburg/sparqloscope) provides
dataset-specific, feature-isolating queries and includes QLever/Virtuoso
comparisons. Persisted ID joins, late term materialization, retained admitted
state, planning/cardinality estimates and bounded-memory ingestion remain
performance work. Each new path needs a reference contract, failing regression,
Lean refinement where available, complete answers and attributable measurements.
