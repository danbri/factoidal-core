# SPARQL BGP index reuse

Date: 2026-10-10. Base commit: `3589fd33` in `factoidal-core`.

## Implementation

`SPARQL/Algebra.lean` previously built a graph hash index for each
triple pattern, even when later patterns used the same bound positions.
It also built an index when evaluating a single input solution.

`evalBgpIdx` now uses `evalBgpRowsCached`. Each BGP evaluation keeps
indexes keyed by the subject/predicate/object position mask. A repeated
mask reuses its index. A singleton uses an existing matching index or
scans the graph without building one. An empty intermediate result
ends evaluation. Indexes remain local to the active graph and BGP.

The original `evalBgpRowsIdx` remains available as a reference. The
benchmark also freezes the original implementation locally, so later
changes to that reference cannot silently change the measured baseline.

## Proof and tests

This is a landed Lean implementation with landed Lean theorems.
The F* lineage is `formal/fstar/SPARQL11.Algebra.fst`; this change
introduces no new F* implementation or theorem.

`SPARQL/IndexedEvalRefinement.lean` proves:

- `cachedTpIndex_correct`: a cache lookup returns the index of the
  same graph and mask, and insertion preserves cache validity.
- `evalBgpStepCached_correct`: every step preserves the complete
  ordered solution sequence and cache validity.
- `evalBgpRowsCached_eq`: evaluation from arbitrary seed rows and a
  valid cache equals the existing `evalBgpFrom` evaluator.
- `evalBgpIdx_eq_evalBgp`: the production entry point returns exactly
  the existing evaluator's list, including row order, duplicate
  multiplicity, and binding layout.

The axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. There is no new `sorry`, user axiom, `native_decide`,
external primitive, or partial definition. The refinement preserves
the current executable equality rules; it does not establish new
standards-conformance results.

`SPARQL/IndexedBgpTests.lean` has 38 build-time guards. The initial
regressions passed with the original production evaluator before the
switch. The expanded tests pass with the cache. They cover all eight
position masks, heterogeneous seed domains, duplicate rows, repeated
variables, empty/missing results, language-tag case, XMLLiteral
canonicalization, nested triple terms, and cache reuse/cardinality.
Disabling cache hits deliberately fails the three reuse guards at
lines 90, 91, and 101. Restoring lookup restores the passing build.

Validation:

```sh
cd formal/lean4
lake build L4Factoidal.SPARQL.IndexedBgpTests
lake build L4Factoidal.SPARQL.IndexedEvalRefinement
lake build L4Factoidal
lake -f Bench/lakefile.lean build l4sparql-index-bench
timeout 600 .lake/build/bin/l4sparql-index-bench all 100,1000,10000 5 8
timeout 600 .lake/build/bin/l4sparql-index-bench all 100000 3 8
```

The full library build passes (417 jobs). This checkout's W3C test
submodules are uninitialized; no W3C corpus run is claimed.

## Native measurements

Host: macOS 15.6.1 (24G90), arm64. Compiler: Lean 4.33.1, Lake native
build. The benchmark executable SHA-256 is
`708c0e1b80d5f7c16ff951f0e0f329ad3eb1921e35ad98df734dbf031c5bbf83`.

`Bench/SparqlIndexBench.lean` generates eight properties per subject.
The star reads all eight properties; the point query fixes one subject;
the missing query adds a ninth, absent predicate. Each case checks
complete list equality between the frozen baseline, cached evaluator,
and parsed full SELECT, as well as the expected row count. Parsing,
fixture construction, and correctness comparisons are outside the
timed regions. Timed work includes BGP index construction, probes, and
result materialization; the SELECT column also includes query
evaluation and result post-processing. It excludes serialization.

Timings use five runs through 80,000 triples and three runs at 800,000
triples, after one warmup per case, in the same process. `IO.lazyPure`
forces result evaluation and its length between
monotonic nanosecond clock reads. Compilation finished before the
recorded run. These are synthetic in-memory measurements, not disk,
HTTP, ingestion, or competitor measurements.

| Triples | Case | Legacy BGP ms | Cached BGP ms | Full SELECT ms | BGP speedup |
|---:|---|---:|---:|---:|---:|
| 800 | star | 1.863 | 0.528 | 0.518 | 3.53x |
| 800 | point | 1.517 | 0.074 | 0.070 | 20.49x |
| 800 | missing | 1.859 | 0.482 | 0.491 | 3.85x |
| 8,000 | star | 16.729 | 4.659 | 4.983 | 3.59x |
| 8,000 | point | 14.703 | 0.705 | 0.664 | 20.87x |
| 8,000 | missing | 18.791 | 4.874 | 4.969 | 3.86x |
| 80,000 | star | 335.945 | 85.398 | 87.847 | 3.93x |
| 80,000 | point | 312.797 | 10.629 | 9.863 | 29.43x |
| 80,000 | missing | 389.567 | 87.855 | 95.422 | 4.43x |
| 800,000 | star | 7,039.541 | 1,385.389 | 1,418.276 | 5.08x |
| 800,000 | point | 7,237.926 | 101.946 | 98.211 | 71.00x |
| 800,000 | missing | 7,850.482 | 1,427.728 | 1,445.546 | 5.50x |

Raw nanosecond medians are in `20261010-sparql-bgp-index-reuse.csv`.
The separate benchmark Lake configuration builds only the necessary
pure Lean imports. The main configuration's Ed25519 native dependency
is absent from this checkout; this benchmark does not use Ed25519.

## Remaining work toward database parity

QLever/Virtuoso performance parity remains unverified. This checkout
does not yet contain Shardborough's physical storage implementation.
The current implementation was located read-only at
`/Users/danbri/working/factoidal`, HEAD `0c331255b`, with unrelated local
changes. No changes were made there. Core is the selected new home.

The first coherent storage migration is the existing IBK3/PTD1 codec
and theorem dependency closure: 22 new Lean modules plus reconciliation
of `Storage/Bytes.lean`, `Storage/DeltaLog.lean`, and its tests. Native
query/pack/activation/compaction requires further dependencies and
targeted shared-API integration. Copying shared SPARQL files wholesale
would overwrite this improvement.

This cache still builds an index for each newly encountered mask and
does not persist between BGPs or queries. Production can retain up to
seven indexes, increasing peak memory for queries that encounter many
masks. Memory was not measured in this benchmark. Bucket probes still
reverse their candidate lists. Next performance evidence needs the
disk-backed routes, ingestion memory and throughput, representative
SPARQL workloads, and same-host QLever/Virtuoso comparison with result
validation and separate cold/warm measurements.
