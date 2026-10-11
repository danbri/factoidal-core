# Native IBK3 indexed-selection experiment — 2026-10-10

- The JSON record `20261010-shardborough-indexed-selection-benchmark.json` is in commit 906527b of danbri/factoidal-core (https://github.com/danbri/factoidal-core/blob/906527bae7a741780bb4bab8ccb0f8eb890c85ad/docs/20261010-shardborough-indexed-selection-benchmark.json) and is not in this tree.

One focused, proof-backed change removes quadratic Nat-list deduplication and
membership from SRI2 subject selection. On the same persisted synthetic
100,000-subject / 300,000-triple store, the measured 100,000-row two-way join falls
from **19.549 s to 4.897 s**: **3.992×** for this workload, not a general engine
scalability or competitor-parity claim.

The [retained measurement JSON](20261010-shardborough-indexed-selection-benchmark.json)
contains hashes, exact commands, sample times, expected cardinalities, read
counters, explicit exclusions and assurance boundaries. The host is macOS
15.6.1 ARM64, Lean `v4.33.1`.

## Controlled comparison

Each subject has one type, one unique name and one modulo-10 group. Both
binaries query the same activated store, generated and packed before timing:

```sparql
SELECT ?subject ?name WHERE {
  ?subject <urn:scale:type> ?type .
  ?subject <urn:scale:name> ?name
}
```

| Fresh process | Baseline ms | Optimized ms |
| --- | ---: | ---: |
| 1 | 19,548.911 | 4,897.184 |
| 2 | 20,406.935 | 4,893.838 |
| 3 | 19,363.814 | 5,065.959 |
| Median of all three | 19,548.911 | 4,897.184 |

Runs alternate baseline/optimized, have a 120-second cap, and retain every
sample. Startup, artifact admission and ten-row preview output are included;
fixture creation, pack/activation, profiling, validation and complete JSON
serialization are excluded. The OS page cache is not evicted. Team builds
and container workloads are paused; this is not a system-wide load guarantee.

All six runs return 100,000 rows, identical preview rows and identical counters:
20,643,925 logical-read bytes / 20,745,528 fetched bytes. These counters cover
selected successful artifact reads, not all filesystem IO. A separate new-binary
JSON run checks **all 100,000 typed bindings and their multiplicities** against
the generated fixture; the actual and expected canonical bag hashes agree.
The original binary predates `--json`, so native before/after validation itself
checks cardinality and preview equality, not complete baseline answer bags.

The baseline executable is preserved from source
`98028a368d508fe45ff90b5d98210af855d15532`. The optimized executable is a
**working tree on that HEAD**, identified by executable, source-file and focused
diff hashes in the JSON. It also includes the new JSON CLI/serializer; the timed
commands use preview mode and do not execute JSON serialization.

Additional `SubjectPageSelection` / `pagesForArray` edits and a query executable
rebuild are observed **after** these measurements. This report preserves the
measured Nat-only increment's hashes; it does not time or validate that later
working tree. Output-file mtimes place the last paired sample at 23:43:17,
the JSON validation at 23:43:49 and the excluded profile process at 23:44:37
local time; the additional source edits begin at 23:46:48.

## Why this change

A two-second native baseline sample finds 1,077 sampled stacks in Nat
`List.eraseDups` under `scanEntryForSubjectsV2`, another 110 in the second
subject deduplication, and 39 in list-based posting membership. These are
sample-slice observations, not whole-query CPU percentages.

`SubjectRowIndexWireV2.distinctIds` now uses a Nat hash set while preserving
first-occurrence order; `selectedPostings` builds a wanted-ID set and filters
the existing ordered page/posting lists. The materializer calls these helpers.
Kernel-checked `distinctIds_eq_eraseDups` and `selectedPostings_eq_filter`
prove exact list equality, including duplicate postings, rather than just set
equality. Six guards cover empty input, interleaved duplicates, large Nats and
page/row order. Deliberately reversing results first fails three order guards.
Both proofs depend only on `propext`, `Classical.choice` and `Quot.sound`;
there are no new admissions, custom axioms or partial definitions.

An excluded post-change two-second sample, taken from a three-repeat process,
instead observes general-finisher/index construction and row/paged-dictionary
materialization. Nat deduplication no longer dominates that slice. The first
sandboxed sampling attempt refuses inspection; an approved direct retry works.
No additional engine optimization is included, and the repeat-process memory
footprint is not compared with the baseline single-process sample.

## Exploratory scaling and exclusions

The earlier pack → activate → query experiment covers 1k/10k/100k **subjects**,
or 3k/30k/300k triples. Pack and activation each have one sample; queries use
a first sample plus three subsequent fresh processes. It checks exact generated
cardinalities and COUNT values, not complete bags. Possible small-module build
overlap makes this exploratory evidence, not the controlled speedup baseline.

| Subjects / triples | Pack ms | Activate ms | Two-way join ms | Selective join ms |
| --- | ---: | ---: | ---: | ---: |
| 1k / 3k | 135.260 | 83.042 | 47.206 | 39.683 |
| 10k / 30k | 1,157.599 | 611.394 | 979.011 | 164.584 |
| 100k / 300k | 11,230.973 | 6,072.036 | 19,330.435 | 2,153.609 |

The 100k exploratory full join excludes profiled sample index **1** as well as
first sample index **0**: its median uses only indices **2 and 3**, not three
runs. The original three-way driver query contains an extra closing brace;
those parse failures are discarded, not attributed to the engine. Corrected
three-way checks succeed at all three sizes, but are **single validation runs**
(275.559 / 1,652.896 / 37,018.476 ms), never three-run medians. The original
profile filename says `10k`; the actual workload is 100k subjects / 300k triples.

## Reproduction and validation

The measured version builds from `formal/lean4` with the exact command retained
in the JSON (library plus all ten native targets, **673 jobs, PASS**). Complete-result IBK3,
IBK4 and IBK5 smokes, five disk lifecycle smokes, 107 native crypto checks and
38 native range checks pass. Host IO, HACL/native crypto and native compilation
remain trusted boundaries; the equivalence proofs are not performance theorems.

Generate a fresh scale store with:

```sh
python3 tools/blockengine-core-scale.py --subjects 1000,10000,100000 --warm-runs 3 --timeout 120 --output-dir /private/tmp/factoidal-scale-new
```

Preserve the baseline executable before rebuilding, then compare an existing
activated collection without repacking:

```sh
python3 tools/blockengine-core-scale.py --subjects 100000 --warm-runs 3 --timeout 120 --baseline-query /path/to/preserved-query --existing-collection /private/tmp/factoidal-scale-new/subjects-100000/collection --output-dir /private/tmp/factoidal-selection-new
```

In comparison mode `--warm-runs 3` means three measured runs per executable,
with no excluded warmup. Raw local artifacts remain under
`/private/tmp/factoidal-core-scale-98028a36` and
`/private/tmp/factoidal-core-selection-comparison`; large result dumps are not
checked in. The corrected driver passes all seven query shapes on a 100-subject
native fixture; six invalid argument invocations also fail visibly.
