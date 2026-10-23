# Parallel block scans on SBM11

Date: 2026-10-12. Work issue: https://github.com/danbri/factoidal/issues/799
(stage 1). OKR: https://github.com/danbri/factoidal/issues/801 KR 1.2. Owner,
2026-10-12: "KR1.2 yes". Baseline: SBM11 (owner, 2026-10-12: "Consider smb11
our baseline for shardcore").

Stage 1b (2026-10-13, the streamed, counted and ORDER BY ... LIMIT paths of
one pattern): section "Stage 1b: streamed and aggregate paths" below.

## Stage 1: parallel block scans

### 1. Result

- `l4sbm11 query --threads N` cuts the selected blocks of each BGP scan into
  at most N consecutive chunks and scans each chunk in its own Lean task
  (`IO.asTask`, dedicated thread). N = 1 (the default) runs the single-thread
  code path unchanged (`Store.scanTable = none`).
- Answers are identical at 1, 2, 4 and 8 threads on every input tested
  (section 4). The byte counts that `--explain` prints are identical too.
- Speed on olympics: q07 at 4 threads is 0.79 of the 1-thread time; q10 is
  0.89. q01, q19 and q21 do not use the parallel path and do not change
  (section 5).
- Speed on the DBpedia slice (13.1 times olympics, section 5.1), 8 BGP join
  queries: 4 threads give 0.58 to 0.72 of the 1-thread time (d06 0.58, d05
  0.66, d07 0.62, d09 0.72). The issue's target (4 threads at most 0.4 of 1
  thread on q07, q19, q21, on the 10x dataset) is not met. q07, q19 and q21
  are olympics queries; the DBpedia slice has no queries with those names,
  and its scan queries (the streamed path) were not timed here.

### 2. Method

Code: `L4Factoidal/Storage/Sbm11/ParallelScan.lean` (the split),
`IdQuery.scanListM` (the loop of `scanFoldM` over a given list of blocks),
`IdQuery.scanTableOf` (used by `evalBgpM`), `Harness/Sbm11Query.lean`
(`scanTableParM`, `Session.view`, `Session.absorb`).

1. The parent reads the PRM1 entries of the permutation (this opens the
   permutation) and computes the selected blocks (`blocksFor`), in block
   order.
2. `chunksOf c` cuts that list into consecutive chunks of
   `c = ceil(blocks / N)` blocks.
3. Each chunk runs `scanListM` from an empty table in its own task, with the
   per-block function `scanBlockM` that the single-thread scan uses.
4. The parent waits for the tasks in chunk order and appends the chunk
   tables in that order (`Table.append`); it adds the statistics.

Chunk order: the chunks are consecutive and in block order, and the parent
appends them in chunk order, so the rows come out in block order, as in the
single-thread scan.

Shared state: each task gets a view of the session with its own byte and
lookup counters, its own dictionary state and a copy of the opened
permutations. The parent adds each view's counters after the task has
finished. Scan tasks call only `metas` and `prb`; dictionary lookups and the
output printer run in the parent. The verified chunk cache (only under
`--verify merkle`) is one cache shared by all tasks, behind a `Std.Mutex`:
a cache per task fetches and checks the same chunks again, so the byte counts
would grow. With one shared cache each chunk is fetched once, and the totals
equal the single-thread totals. Under `--verify none` (the default for an
activated generation) there is no cache and no lock.

Measured on olympics q07, `--explain`, 1 thread against 4 threads:
`none`: block bytes 1,141,223, range bytes 1,669,338, file bytes 1,751,517
both; `merkle`: 1,141,223, 5,832,103, 6,090,010 both.

Not parallel (single-thread, as before): scans with a delta overlay (stage 5:
the insert cursor runs across blocks); the streamed path (`pattern ...
streamed`, LIMIT and single-pattern output, which can stop early); the
counted and grouped paths; the joins themselves (merge and hash join run
after the scans). The scans that feed a merge join are parallel; the join is
not divided.

### 3. What is proved

`L4Factoidal/Storage/Sbm11/ParallelScan.lean`:

- `chunksOf_flatten`: the chunks of a list, concatenated, are the list.
- `mem_of_mem_chunksOf`: an element of a chunk is an element of the list.

`L4Factoidal/Storage/Sbm11/ParallelScanTheorems.lean`:

- `parallel_acc_eq` (list form): for an admitted permutation (the activation
  checks of L4e: `prmAdmitted`, every block `decodeBlockAt`), a scan with no
  overlay (`ox.on = false`), and a list `L` of block numbers inside the
  permutation, the scans of the chunks of `L`, run one by one from an empty
  accumulator and concatenated in chunk order, equal the scan of `L`. Both
  sides are `Except` values over lists of rows (`blockOut`). The proof uses
  `ScanFoldTheorems.forIn_blocks` (the loop of lemma L4e).
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.

No hypothesis states the conclusion. No `sorry`, `native_decide`, user
axiom or raised heartbeats.

### 4. What is tested only

- The production accumulator is `Table` (byte columns, `Table.append`), not a
  list. The step from `Table.append` to list concatenation is not proved.
- The theorem is over `Store Id`; the binary runs the same generic code in
  `IO` (as for L4e).
- Answer checks, `tests/sbm11/threads.sh` (exit 0): SPARQL JSON byte for byte
  and the answer fields of the stderr line, threads 2, 4, 8 against 1:
  - gate fixture: 36 queries x 4 thread counts, identical 36 (out of 36);
  - gate fixture packed with 2 rows per block (3 selected blocks per scan,
    so several chunks): identical 36 (out of 36);
  - olympics, `tests/qlvr/queries`: identical 21 (out of 21).
- The W3C census at several thread counts: `SBM11_THREADS=N
  tests/sbm11/census.sh`. Not run in this landing. Its generations are small
  (one block per permutation in most cases), so it does not exercise
  several chunks; the 2-row gate does.

WASM: the SBM11 query harness is native only (`Harness/Sbm11*`, file `pread`)
and is not in the `l4wasm` library, so the threaded path never runs in
wasm32. The wasm build does not use `-pthread` (`Wasm/build-wasm.sh`). How
Lean `Task` behaves in that runtime is not verified.

### 5. Measurements

`ROUNDS=8 tests/sbm11/bench-threads.sh /home/user/qlvr-work/sbm11/s3/wfull`
(olympics, 1,781,625 quads, `--verify none`), 2026-10-12. Round 1 discarded;
rounds 2 to 8 kept (7 per cell), interleaved by round, query and thread
count. Each process: `--repeat 10`; the warm figure is the median of its 10
runs; the table gives the median over the 7 processes, the range, and the
peak RSS (VmHWM, median). Machine: 4 vCPU VM. 1-minute load average before
each process: median 1.18 to 1.21, range 1.09 to 1.35 over the whole run.

| Query | path | 1 thread ms | 2 threads ms | 4 threads ms | 8 threads ms | 4/1 | RSS kB 1 / 4 / 8 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q01-count-all | counted from metadata | 0.22 | 0.21 | 0.22 | 0.22 | 1.00 | 15,388 / 15,420 / 15,448 |
| q07-join-three | BGP, 4 scans (parallel) | 32.55 (32.17 to 35.08) | 27.38 | 25.83 (21.60 to 34.09) | 38.54 | 0.79 | 27,612 / 57,460 / 86,504 |
| q10-orderby-limit-double | BGP, 1 scan (parallel) | 15.73 | 15.03 | 13.98 | 15.94 | 0.89 | 23,732 / 40,204 / 48,540 |
| q19-scan-bound-predicate-iri | streamed (not parallel) | 93.05 | 93.09 | 93.39 | 94.61 | 1.00 | 35,904 / 35,900 / 35,876 |
| q21-scan-bound-predicate-lang | streamed (not parallel) | 172.33 | 162.17 | 168.64 | 163.47 | 0.98 | 27,680 / 27,684 / 27,788 |

Findings:

- q07: 4 threads give 0.79 of the 1-thread time; the 4-thread range (21.60 to
  34.09 ms) overlaps the 1-thread range (32.17 to 35.08 ms) at its top.
  8 threads are slower than 1 (1.18) on 4 vCPU. Peak RSS grows with the
  thread count (27.6 MB to 86.5 MB): each chunk table is held until the
  parent appends it.
- q10: 0.89 at 4 threads, inside the noise of the 1-thread range (13.77 to
  19.04 ms).
- q19 and q21: no change. They take the streamed path, which stage 1 does not
  divide. The issue names them as targets, so the streamed path needs its own
  division (an ordered merge of chunk streams that can stop early) before the
  target can be measured.
- q01: no block is read (counted from PRM1 metadata).

### 5.1 DBpedia slice (2026-10-12, evening)

`ROUNDS=8 VERIFY=none bash tests/sbm11/bench-threads.sh
/home/user/bench-data/sbm11/dbpedia <8 queries>` on the DBpedia slice
generation of https://github.com/danbri/factoidal/issues/798 (23,269,559
quads, packed by commit 408898bd), with `l4sbm11` built from commit
659dcd5a. `VERIFY` is a new option of the script (it passes `--verify none`;
the generation is not activated, so the binary default is `merkle`). Queries:
every BGP join of `tools/bench/three-engines/queries/dbpedia` (d05, d06 star
joins; d07, d08 path joins; d09 join and GROUP BY; d12, d14 join and FILTER;
d15 join and ORDER BY LIMIT). Round 1 discarded; rounds 2 to 8 kept (7 per
cell), interleaved by round, query and thread count; `--repeat 10` per
process. 1-minute load average before each process: median 1.20, range 0.46
to 1.98 over the kept rounds. Answers at 1, 4 and 8 threads were checked
before the timing: equal multisets for all 8 queries (row counts as in the
three-engine record, for example d05 1,130, d08 688).

| Query | 1 thread ms (range) | 2 threads ms | 4 threads ms (range) | 8 threads ms | 4/1 | 8/1 | RSS kB 1 / 4 / 8 | load before |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| d05-star-three | 331.30 (300.57 to 362.37) | 259.04 | 219.54 (197.56 to 223.25) | 206.35 | 0.66 | 0.62 | 92,744 / 244,972 / 260,624 | 0.46 to 1.98 |
| d06-star-film | 36.01 (34.77 to 38.42) | 26.48 | 21.00 (20.20 to 21.68) | 22.43 | 0.58 | 0.62 | 29,168 / 59,304 / 89,588 | 0.74 to 1.98 |
| d07-path-two-hops | 77.81 (71.06 to 82.25) | 56.03 | 48.26 (43.86 to 56.72) | 53.09 | 0.62 | 0.68 | 37,944 / 90,056 / 136,328 | 0.74 to 1.98 |
| d08-path-three-hops | 88.05 (71.78 to 101.28) | 70.72 | 59.20 (53.08 to 76.09) | 59.48 | 0.67 | 0.68 | 43,688 / 103,240 / 155,236 | 0.74 to 1.90 |
| d09-group-birthplace | 43.62 (36.52 to 47.05) | 37.42 | 31.37 (29.80 to 36.67) | 32.56 | 0.72 | 0.75 | 27,120 / 47,912 / 55,896 | 0.76 to 1.91 |
| d12-filter-numeric | 27.48 (24.65 to 40.53) | 21.43 | 16.62 (14.16 to 19.85) | 25.18 | 0.60 | 0.92 | 29,224 / 57,612 / 85,492 | 0.76 to 1.91 |
| d14-filter-date | 49.78 (48.74 to 54.35) | 37.59 | 32.01 (30.45 to 34.22) | 41.08 | 0.64 | 0.83 | 39,312 / 68,604 / 86,984 | 0.86 to 1.91 |
| d15-orderby-limit | 25.55 (21.43 to 27.81) | 20.59 | 16.41 (13.81 to 17.18) | 17.50 | 0.64 | 0.68 | 25,156 / 60,564 / 91,408 | 0.86 to 1.91 |

Findings:

- 4 threads give 0.58 to 0.72 of the 1-thread time on all 8 queries. On
  every query the 4-thread range is below the 1-thread range (no overlap).
  On olympics the same build gave 0.79 (q07) and 0.89 (q10): the larger
  scans divide better.
- 8 threads on 4 vCPU are not faster than 4 threads (0.62 to 0.92).
- Peak RSS grows with the thread count (d05: 92.7 MB at 1 thread, 245 MB at
  4, 261 MB at 8), as on olympics (section 5).
- The 1-thread times are lower than the SBM11 warm times of the
  three-engine record (d05 331 against 575 ms there, section 7.3). That
  record used the binary of commit 408898bd and `--repeat 5`; this table
  uses commit 659dcd5a and `--repeat 10`. The cause of the difference was
  not isolated. Compare thread counts only within this table.

Raw CSV: `/home/user/bench-data/results/sbm11-threads-dbpedia.csv` (not in
the repository).

### 6. What is open

- The streamed path (q19, q21), the counted and grouped paths: single-thread.
- Scans with a delta overlay: single-thread.
- Merge joins are not divided by key range.
- The `Table.append` step to the list form: not proved (tested).
- Lean `Task` in the wasm32 runtime: not verified (the threaded path is
  native only).
- Peak RSS grows with the thread count; chunk tables could be appended as
  tasks finish in order to keep fewer of them live.
- The 10x dataset (DBpedia slice, https://github.com/danbri/factoidal/issues/798):
  BGP joins measured (section 5.1); the streamed scans (d10, d13, d16, d17)
  and the 4/1 target of 0.4 are open.
- The W3C census at 2, 4, 8 threads: not run.
- Stage 2 (PushIR): not started.

### 7. Gates

All on this landing's tree, 2026-10-12, exit codes read:

| Gate | Result |
| --- | --- |
| `lake build` (nice -n 10) | exit 0, 0 errors, 1,603 jobs |
| `tests/sbm11/run.sh` | exit 0: 149 pass, 0 fail (out of 149) |
| `tests/sbm11/threads.sh` | exit 0: section 4 |
| `tests/qlvr/run.sh` | exit 0: 39 pass, 0 fail (out of 39) |
| `tests/prim/run.sh` | exit 0: wasm32 21,581 pass, 0 fail (out of 21,581) |
| `Wasm/native-smoke.sh` | exit 0: 350 pass, 0 fail, 0 xfail (out of 350) |
| `tests/known-defects/run.sh` | exit 0: 13 XFAIL, 0 XPASS, 0 probe errors (out of 13) |
| `tests/stack/run.sh --canary` (512 KB) | exit 0: 59 pass, 0 fail (out of 59) |
| `python3 tools/lean-tail-recursion-audit.py --gate` | exit 0 |

The stack canary and native-smoke need `lake` on `PATH`; without it the
canary control is not compiled and the canary is not scored (exit 1).

## Stage 1b: streamed and aggregate paths

Date: 2026-10-13. Work issue: https://github.com/danbri/factoidal/issues/799
(stage 1b). Commits on branch `work799`:
`3dec4885` (the divided paths and tests), `eb0b17b1` (the merge theorems),
`4188d9f2` (task copies, range count), `fa572e9c` (task page cache bound),
and this record.

### 1b.1 Result

- `l4sbm11 query --threads N` now also divides the three single-pattern
  paths that stage 1 left on one thread: the streamed path (one pattern, no
  ORDER BY, no DISTINCT, no aggregate), the counted path (COUNT and GROUP BY
  over one pattern) and ORDER BY ... LIMIT over one pattern (no DISTINCT).
  `--threads 1` runs the single-thread code.
- Answers are identical at 1, 2, 4 and 8 threads on every input tested
  (section 1b.5): the SPARQL JSON byte for byte, and the byte counts of the
  stderr line when no dictionary page cache is emptied.
- 4 threads against 1 thread, warm medians (section 1b.6): DBpedia slice
  d13 0.31, d16 0.33, d10 0.57, d17 0.96; olympics q21 0.42, q19 0.65, q07
  0.77. The issue's target (4 threads at most 0.4 of 1 thread on the 10x
  dataset) is met by d13 and d16. It is not met by d10 (0.57; 0.37 at 8
  threads), d17 (3 ms at every thread count), q19 and q21 (olympics, not the
  10x dataset). Section 1b.7 names the remaining costs.

### 1b.2 Method

Code: `IdQuery.lean` section "Divided single-pattern paths" (`Par`,
`rangeCount`, `divide?`, `streamPartM`, `emitPieceM`, `countPartM`,
`Groups.merge`, `topPartM`, `orderPermM`, `ScanSpec.fresh`,
`FKind.fresh`), `Harness/Sbm11Query.lean` (`parFold`, `Session.par`,
`Session.view`, `Session.local`, `Session.sharedPage`, `Session.prefetch`,
`taskPages`, `cacheTaskPage`).

1. **Ranges.** The parent reads the PRM1 entries and the selected blocks, as
   stage 1. `rangeCount threads minRows est` gives the number of ranges: at
   most `threads`, and at most `est / minRows` (`est` the rows of the
   selected blocks, `minRows` 8,192 by default, `SBM11_MIN_RANGE_ROWS`);
   fewer than 2 runs the single-thread code. A streamed range holds at most
   16 blocks, so a large streamed scan has more ranges than threads. A scan
   with a delta overlay stays on one thread (as stage 1).
2. **Tasks.** `parFold` starts one pool task per range, at most `threads`
   at once, and folds the range results in range order as they finish; the
   next task starts when one result is folded, so at most `threads` results
   wait in memory. Each task has its own view of the session (counters,
   permutation copies; stage 1) and makes its own copies of the spec, the
   FILTER conjuncts and the overlay context (`ScanSpec.fresh`,
   `FKind.fresh`, equal to the originals: `fresh_eq`).
3. **Streamed path.** Each range applies the FILTERs to each block's rows
   and renders at most OFFSET + LIMIT of its rows, each as a comma and its
   binding object, in pieces of at most 512 rows with the end offset of each
   row. The parent steps over the pieces in order: it skips what is left of
   OFFSET, emits up to what is left of LIMIT, and drops the comma before the
   first row emitted (`emitPieceM`, the step of the single-thread loop). The path is
   divided only when OFFSET + LIMIT is above the estimate. Then the
   single-thread scan never reaches LIMIT before its last block, so both
   read the same blocks. A LIMIT at or below the estimate stays on one
   thread: a divided scan would read blocks that the single scan does not
   read (it stops early), and the byte counts would differ.
4. **Counted path.** Each range builds its group map (`countStepM` over its
   blocks, from no groups). The parent adds each range's groups to its map
   in range order (`Groups.merge`: the range's keys in their order, with their
   counts), so the keys come out in order of first appearance, as in one
   pass. The group table, ORDER BY and the rendering run in the parent.
5. **ORDER BY ... LIMIT k.** Each range scans its blocks into a table,
   applies the FILTERs, and keeps the first OFFSET + LIMIT rows in the ORDER
   BY order (`orderPermM`, the code `finishM` uses: `topK` or the stable
   sort). The parent appends the range tables in range order and runs
   `finishM` on the union, which orders it again and takes the window. The
   scan is the scan `evalBgpM` makes for one pattern, and the parent reads
   the PRM1 entries `evalBgpM` reads for its estimate, so the files read are
   the same.
6. **Dictionary in the tasks.** Rendering, string FILTERs and ORDER BY keys
   read dictionary pages in the tasks. A task has its own page cache (made in
   the task, at most `SBM11_TASK_PAGES` pages, default 1,024). On a miss it
   goes to `taskPages`, a tree map shared by the tasks under `dictLock`: a
   page there is taken; a page being loaded by another task is waited for (a
   promise in the map); else the task marks it as loading, loads it outside
   the lock (under `--verify merkle` inside the lock, where the chunk caches
   are shared) and publishes it. Before a block's rows are rendered,
   `Session.prefetch` takes all the pages they need with two rounds of the
   lock. A task keeps copies of the pages it takes. `taskPages` holds at most
   `SBM11_PAGES` entries and is emptied when full, as the session's cache.
   After the tasks, the session reads `taskPages` on a miss in its own
   cache, so the pages the tasks loaded are not loaded again.

Byte counts. With `SBM11_PAGES=1000000` no cache is emptied, every page is
loaded once at every thread count, and every byte count of the stderr line
is identical (tests/sbm11/threads.sh runs so). With the default limit of
2,048 pages, a query that touches more pages (olympics q19 and q21 touch
about 2,100) empties the cache and loads pages again; how many depends on
the order in which the tasks touch them, so the dictionary bytes differ
between thread counts (q21, one run: 4,967,124 file bytes at 1 thread,
4,611,770 at 4 threads). The block bytes are identical in every case.

### 1b.3 What is proved

`L4Factoidal/Storage/Sbm11/ParallelMergeTheorems.lean`. The statements are
list lemmas over the rows of the blocks (`R b`: the rows block `b` gives
after the FILTERs, in row order), the ranges `ParallelScan.chunksOf c L`:

- `stream_divided_eq_single`: each range keeps the first `cap` of its rows;
  with `off + lim ≤ cap`, the parent's step over the ranges in order
  (`winStep`) keeps the rows the single-thread step over the blocks keeps.
  Parts: `window_fold` (the step over any partition keeps rows
  `[off, off + lim)` of the concatenation), `window_cap`, `capFold` (a
  range's loop with its cap keeps the first `cap` rows).
- `count_divided_eq_single`: the range counts add up to the count of the
  concatenation.
- `groups_divided_eq_single`: a group map (`GM`: keys in order of first
  appearance, a count per key; the parts of `Groups` that `groupTable`
  reads), built per range from the pairs of its blocks and merged in range
  order (`GM.merge`, the model of `Groups.merge`), equals the map of one
  pass. Core lemma: `merge_addAll`.
- `topK_divided_eq_single`: with `le` a total preorder (transitive, total)
  and the stable merge sort of the Lean core library (`List.mergeSort`),
  the first `k` rows of the concatenation of each range's first `k` rows
  equal the first `k` rows of all rows. Parts: `mergeSort_append` (the sort
  of a concatenation is the merge of the sorts), `take_merge_congr` (the
  first `k` rows of a merge read only the first `k` rows of each input).

`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` for three;
`propext`, `Quot.sound` for `count_divided_eq_single`. No hypothesis states
a conclusion: the hypotheses are `off + lim ≤ cap` and the transitivity and
totality of `le`. Also `ScanSpec.fresh_eq` and `FKind.fresh_eq` in
`IdQuery.lean`: the task copies equal the originals.

Finding: `ParallelScanTheorems.lean` (stage 1, `parallel_acc_eq`) was not
imported by any build root, so `lake build` never checked it; its olean was
absent. `L4Factoidal.lean` now imports it and `ParallelMergeTheorems.lean`.
A walk of the imports from the roots of `lakefile.lean` finds two more
modules that no root reaches: `L4Factoidal.OWL.ComprehensionTheorems` and
`L4Factoidal.RDF.GraphPatterns` (not changed here).

### 1b.4 What is tested only

- That the code computes the list functions: the rendered `ByteArray`
  pieces and their row ends, the `Std.HashMap` of `Groups` against `GM`,
  `Qlvr.Query.topK` and `sortPermByKey` against `List.mergeSort`, and that
  the order keys of a range (ranks over the range's values) compare as the
  keys over the union do.
- The `IO` instance, the tasks, the shared page cache and the promises.
- That the single-thread scan never stops early when OFFSET + LIMIT is above
  the estimate (the rows of a scan are at most the rows of its selected
  blocks); the byte counts of the tests check it.

### 1b.5 Answer checks

`tests/sbm11/threads.sh`, exit 0, final code (commit `fa572e9c`): SPARQL JSON
byte for byte and every field of the stderr answer line (with
`SBM11_PAGES=1000000`), threads 2, 4 and 8 against 1:

- gate fixture, `tests/sbm11/gate/*.rq` and the 19 stage 1b queries
  `tests/sbm11/threads/*.rq` (OFFSET and LIMIT across ranges, LIMIT below,
  equal to and above the estimate, FILTERs decided in the tasks, GROUP BY on
  constant and non-constant columns, COUNT(?x), the graph variable, ORDER BY
  with ties, OFFSET, two keys, literals, LIMIT above the rows): identical 82
  (out of 82);
- the same packed with 2 rows per block, `SBM11_MIN_RANGE_ROWS=0`: identical
  82 (out of 82); coverage at 4 threads: the divided streamed path ran for 16
  queries, the counted path for 7, ORDER BY ... LIMIT for 5;
- olympics q01 to q21: identical 21 (out of 21); q19 and q21 with the
  default page limit, SPARQL JSON and block bytes: identical 2 (out of 2);
- DBpedia slice d01 to d17 (`--verify none`): identical 17 (out of 17); and
  each of the 68 answers (17 queries × 4 thread counts) equal to the
  Virtuoso answer of the three-engine record
  (`/home/user/bench-data/answers/dbpedia/*.virtuoso.json`, the
  normalisation of `tools/bench/three-engines/bench.py`): equal 68, different
  0.

### 1b.6 Measurements

`ROUNDS=8 REPEAT=7 tests/sbm11/bench-threads.sh` (with `VERIFY=none` for
DBpedia), binary of commit `fa572e9c`, 2026-10-13 04:56 to 04:58 UTC. Round
1 discarded; rounds 2 to 8 kept (7 per cell), interleaved by round, query and
thread count; each process runs the query 7 times and its warm figure is the
median of its runs; the table gives the median over the 7 processes and the
range. Machine: 4 vCPU (`nproc` 4); 8 threads run more tasks than CPUs. The
1-minute load average before each process: 1.06 to 1.77 (no other gate run
was active). Raw CSV: `/home/user/bench-data/results/sbm11-threads-1b-*.csv`
(not in the repository).

DBpedia slice (23,269,559 quads, the 10x dataset of
https://github.com/danbri/factoidal/issues/798):

| Query | path | 1 thread ms (range) | 2 threads ms | 4 threads ms (range) | 8 threads ms | 4/1 | 8/1 | RSS kB 1 / 4 / 8 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| d10-group-predicates | counted, GROUP BY ?p | 33.08 (23.37 to 37.89) | 20.96 | 18.83 (13.80 to 24.66) | 12.36 | 0.57 | 0.37 | 23,888 / 38,764 / 42,336 |
| d13-filter-strstarts | streamed, STRSTARTS | 347.90 (312.88 to 388.90) | 194.76 | 107.53 (98.81 to 118.36) | 92.51 | 0.31 | 0.27 | 19,740 / 34,396 / 34,300 |
| d16-orderby-limit-scan | ORDER BY ... LIMIT 10 | 61.25 (46.06 to 77.29) | 29.45 | 20.49 (18.99 to 23.29) | 16.63 | 0.33 | 0.27 | 38,352 / 50,832 / 34,604 |
| d17-count-all | counted, COUNT(*) | 3.15 (2.77 to 3.48) | 2.87 | 3.00 (2.63 to 3.79) | 2.98 | 0.96 | 0.95 | 19,952 / 28,340 / 28,352 |

Olympics (1,781,625 quads), default dictionary page limit:

| Query | path | 1 thread ms (range) | 2 threads ms | 4 threads ms (range) | 8 threads ms | 4/1 | 8/1 | RSS kB 1 / 4 / 8 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q19-scan-bound-predicate-iri | streamed | 96.57 (92.77 to 108.29) | 76.46 | 62.72 (54.45 to 64.66) | 58.24 | 0.65 | 0.60 | 36,388 / 122,768 / 122,980 |
| q21-scan-bound-predicate-lang | streamed | 173.77 (153.27 to 183.84) | 123.30 | 72.80 (63.44 to 75.94) | 75.31 | 0.42 | 0.43 | 28,176 / 126,708 / 102,200 |
| q07-join-three | BGP (stage 1; scans with candidates not divided) | 15.74 (10.75 to 19.56) | 11.66 | 12.12 (11.62 to 13.72) | 11.75 | 0.77 | 0.75 | 22,140 / 26,328 / 26,332 |

Olympics q19 and q21 with `SBM11_PAGES=1000000` (no page cache emptied):

| Query | 1 thread ms (range) | 2 threads ms | 4 threads ms (range) | 8 threads ms | 4/1 | 8/1 | RSS kB 1 / 4 / 8 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q19-scan-bound-predicate-iri | 36.45 (27.75 to 52.54) | 29.81 | 24.04 (19.14 to 52.11) | 25.35 | 0.66 | 0.70 | 54,764 / 127,376 / 114,476 |
| q21-scan-bound-predicate-lang | 102.71 (86.43 to 181.33) | 74.98 | 49.98 (41.30 to 66.56) | 40.32 | 0.49 | 0.39 | 38,412 / 136,824 / 114,448 |

Findings:

- d13 and d16 meet the target at 4 threads (0.31, 0.33). d13 reads 823
  blocks and tests a STRSTARTS rank range per row; d16 reads 80 blocks and
  keeps 10 rows per range.
- d10 is 0.57 at 4 threads and 0.37 at 8: its work is in the 137 blocks
  (of 5,941 selected) where the predicate changes inside the block, and
  `countChunk` builds a key list per row there (an allocation per row:
  about two fifths of its single-thread profile). Ranges of equal block counts do not
  hold equal numbers of those blocks. Four ranges per thread (tried, not
  kept): 0.59 at 4 threads and d17 1.07.
- d17 reads 1 block of 5,941 (every other block is constant over the
  counted columns). It takes 3 ms at every thread count; the ranges save the
  per-block planning and spend the same on the tasks.
- q19 and q21 render every row (39,768 and 137,026 rows). At the default
  page limit, the single-thread runs load about 2,100 dictionary pages again
  on every run (q19: 97 ms against 36 ms with no limit). Without the limit
  q21 is 0.49 at 4 threads and 0.39 at 8. The remaining costs at 4 threads
  are in section 1b.7.
- q07: stage 1 measured 32.6 ms at 1 thread; with sideways information
  passing (https://github.com/danbri/factoidal/issues/809) its join scans
  take candidates, and a scan with candidates is not divided. Its first scan
  (8,192 estimated rows) is not divided; its second (16,384) is divided into
  2 ranges.
- Peak RSS grows with the thread count, most for the streamed path (q19: 36
  MB at 1 thread, 123 MB at 4). Section 1b.7.

### 1b.7 What failed on the way, and the costs that remain

Each item names the measurement; the rules are in `skills/lean4-performance`
section "Values that two threads can reach".

1. **A shared hash map is copied on every insert.** The first version gave
   the tasks the session's `Std.HashMap` page cache as a second level. A
   value two threads can reach is marked multi-threaded and is never updated
   in place (`lean_is_exclusive` is false for it): every insert copied the
   bucket array. q21 at 4 threads: 335 ms against 158 ms at 1 thread (load
   average 7: the gate suite of another checkout was running);
   `lean_copy_expand_array` and `lean_mark_mt` led the profile. Repair: the
   task makes its own cache; the shared level is a `Std.TreeMap`.
2. **Contended reference counts on the shared spec.** Every task read the
   parent's `ScanSpec` in every block; the reference counts of a shared value
   are atomic operations on lines all tasks use. d17: 7.9 ms at 4 threads
   against 3.7 ms at 1, CPU time about 2.8 ms more per task. The same for the
   dictionary header that `keySlice` read through `g.dictHdr`, and for pages
   that several tasks render with. Repair: `ScanSpec.fresh`, `FKind.fresh`,
   a term count field, `copyPage`. d17 then 2.9 ms, d10 26.5 to 11.8 ms, d13
   344 to 114 ms (single runs). Stage 1's scan tasks use the copies too.
3. **One lock round per page.** Loading each page under `dictLock` made q19
   slower at 4 threads than at 1 (the scheduler took a fifth of the profile).
   Repair: loads outside the lock with a promise per page, and a prefetch of
   all the pages of a block in two lock rounds.
4. **Whole-block render buffers.** A task's buffer for a block (about 500 KB
   for q21) was freed by the parent; memory a task allocates and another
   thread frees is not reused at once, and fresh memory comes in 2 MB huge
   pages that the kernel clears (`clear_page_erms`, a third of q19's profile
   at 4 threads). Repair: pieces of 512 rows. Remaining: at 4 threads q21
   still has about 550 page faults per run against 17 at 1 thread.
5. **A range per block for small scans.** q07 at 4 threads was slower than
   at 1 thread with one range per block (12.2 against 9.9 ms). Repair:
   `rangeCount` (ranges of at least 8,192 estimated rows).
6. **Stage 1's empty table.** The parent's empty table had the capacity of
   the whole scan, and each task's first append copied it at that capacity.
   Repair: each task makes its own empty table sized to its blocks.

Remaining costs at 4 threads, not removed here:

- Atomic reference counts on the PRM1 entries (`metas`, read in every block;
  the entries of different ranges are different objects, so these are not
  contended).
- The page faults and peak RSS of item 4: each worker thread has its own
  heap. RSS: q19 36 MB at 1 thread, 123 MB at 4; q21 28 MB and 127 MB.
- The dictionary page limit (2,048 pages): q19 and q21 load their pages
  again on every run at every thread count.
- d10: the per-row key list of `countChunk` and the uneven spread of the
  blocks that need it.
- Scans with candidates (sideways information passing) are not divided.

### 1b.8 What is open

- The `Table`, `ByteArray` and `Std.HashMap` steps to the list lemmas
  (tested, not proved), as for stage 1.
- LIMIT at or below the estimate: one thread (section 1b.2, item 3).
- Scans with candidates and merge joins: one thread.
- The peak RSS of the divided streamed path (section 1b.7).
- Lean `Task` in wasm32: not verified; the threaded path is native only.
- Stage 2 (PushIR): not started.

### 1b.9 Gates

All on this landing's tree (commit `fa572e9c` plus this record),
2026-10-13, exit codes read:

| Gate | Result |
| --- | --- |
| `lake build` (whole package) | exit 0, 0 errors, 1,635 jobs |
| `python3 tools/lean-tail-recursion-audit.py --gate` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 186 pass, 0 fail (out of 186); oracle 21 (out of 21) |
| `tests/sbm11/threads.sh` | exit 0: section 1b.5 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query (out of 609 eligible) |
| the same with `SBM11_MIN_RANGE_ROWS=0` | exit 0: 605 matched, 0 differed; 4 refused at query (out of 609) |
| `tests/qlvr/run.sh` | exit 0: 39 pass, 0 fail (out of 39) |
| `tests/prim/run.sh` | exit 0: native 21,581 pass, 0 fail (out of 21,581); wasm32 21,581 pass, 0 fail (out of 21,581) |
| `Wasm/native-smoke.sh` | exit 0: 351 pass, 0 fail, 0 xfail (out of 351) |
| `tests/known-defects/run.sh` | exit 0: 14 XFAIL, 0 XPASS, 0 probe errors (out of 14) |
| `tests/stack/run.sh --canary` (512 KB, `STACK_FIXTURES` in this worktree's scratch directory) | exit 0: 71 pass, 0 fail (out of 71) |
| `#print axioms` on every new theorem and on `ScanSpec.fresh_eq`, `FKind.fresh_eq` | `propext`, `Classical.choice`, `Quot.sound` or a subset |
| `sorry`, `native_decide`, `axiom`, a bare `import Std`, `maxHeartbeats` in the Lean diff since `488eb1bc` | none (the one added import is `Std.Data.TreeMap`, in `Harness/Sbm11Query.lean`) |

Census rows: "matched the reference engine" is row agreement over the same
input, not conformance.

Test environment of this worktree: the `third_party/testing/w3c` entry was a
plain directory (not a symlink into the main checkout, so hazard 40 did not
apply) and was initialised with `git submodule update --init --depth 1`;
`tools/fetch-builds.sh --set native` and `--set web` installed the release
of source commit `e3c3aa013871` (the F\* binaries for `known-defects`);
`L4FACTOIDAL_BIN` named this worktree's Lean build.

## Stage 1c: OKR batch 3 KR 1.2 (2026-10-22)

Issue https://github.com/danbri/factoidal/issues/799, key result in
https://github.com/danbri/factoidal/issues/875. Target: 4-thread over
1-thread ratio at most 0.4 for DBpedia d10 and d17 and olympics q21, q19, q07;
peak RSS at 4 threads at most 2 times the 1-thread RSS.

Method: `tests/sbm11/bench-threads.sh`, 6 rounds (round 1 dropped), 7 runs per
process, median of medians. Machine: 4 vCPU, shared with another agent's
builds and audits; the 1-minute load average was 1.6 to 5.5 during the runs.
Ratios of runs under that load are not reliable to better than about 0.1.
Profiles: `/usr/lib/linux-tools-6.8.0-146/perf record -e cpu-clock
--call-graph dwarf` and `-e page-faults -c 1`.

| Query | 1 thread before / after (ms) | 4 threads before / after (ms) | 4/1 before | 4/1 after | RSS MB 1 / 4 threads after |
| --- | ---: | ---: | ---: | ---: | ---: |
| d10 | 32.4 / 10.6 | 16.8 / 6.7 | 0.52 | 0.63 | 26 / 49 |
| d17 | 0.37 / 0.39 | 0.41 / 0.39 | 1.11 | 1.01 | 22 / 22 |
| q21 | 209.8 / 114.2 | 81.5 / 42.3 | 0.39 | 0.37 | 43 / 104 |
| q19 | 109.5 / 37.4 | 69.1 / 26.1 | 0.63 | 0.70 | 59 / 108 |
| q07 | 10.4 / 6.5 | 7.5 / 6.5 | 0.72 | 0.99 | 26 / 39 |

d17 is not a scan query any more: commit `ddcd9e54` answers it from the PRM1
entries (0.4 ms at every thread count, no block read), so its ratio is not
a measure of the scan. q21 meets 0.4. The other ratios got worse because the
1-thread time fell more than the 4-thread time: absolute times fell by 2.5
to 3.5 times at 4 threads for d10, q19 and q21, and q07 at 1 thread by 1.6
times (part of that is the upstream commit `885ec1d1`). q19 and q21 RSS
ratios: 1.84 and 2.44, not within 2.

What landed:

1. `countChunk` (d10): the end of a run of equal keys is found with one word
   read per row (`runEnd`, `Codec.Zstd.word64U`); the key list is built once
   per run. `countChunkRef` is the first version. d10 at 1 thread 32.4 to
   10.8 ms. Tested, not proved: `l4scanfold-test` compares the two on 108
   generated chunks (`tests/sbm11/run.sh` part (x)).
2. Frame decoders with `Prim.Bytes.pushU64LE`: `FrameWords.decodeWordsF`,
   `decodeWordsRangeF`, proved equal to the spec decoders
   (`decodeWordsF_eq`, `decodeWordsRangeF_eq`); `colAll_slice` and
   `colRange_slice` rewrite with them. `put64` was eight `lean_byte_array_push`
   calls (18 percent of d10). The extern cannot run in the build-time
   interpreter, so the two scan `#guard`s of `ScanFoldTests` became the
   compiled program `l4scanfold-test`.
3. Divided streamed path: each 512-row piece buffer is sized from the bytes
   per row of the previous piece. The 64 bytes per row reserved before made
   a piece copy itself to larger buffers; those copies were 43 percent of the
   698 page faults of q21 at 4 threads. q21 RSS at 4 threads 150 to 104 MB.
4. Dictionary page cache: default 8,192 pages (was 2,048; q19 needs between
   4,096 and 8,192), a full cache drops one sixteenth instead of everything,
   256 pages per task (was 1,024). q19 at 1 thread 100 to 37 ms. The
   comparison "before" at the old default includes that thrash, so the ratios
   of q19 and q21 moved against the target because the 1-thread time fell.
5. Scans with candidates are divided into block ranges
   (`scanSipTableParM`, `scanListSipM`, `Store.scanSipTable`), with
   `ParallelSipTheorems.parallel_sip_acc_eq` (list form, no hypothesis states
   the conclusion; the `Table` and `IO` steps are tested by
   `tests/sbm11/threads.sh`). Tasks use the pool (no `.dedicated`): q07 at
   4 threads 5.9 to 5.2 ms in single runs. It gave no measured gain over the
   undivided scan under the machine load (q07 ratio 0.99, 8 threads 0.83).

Remaining costs (profiles above):

- Per-query parallel overhead of CPU time: at 4 threads CPU time is 1.4 to
  1.5 times the 1-thread CPU time for q07 (2.8 s against 1.9 s for 300 runs)
  and 1.3 to 1.5 for d10. The sources seen: first-touch faults of 2 MB huge
  pages in each worker's mimalloc heap (`clear_page_erms`, 15 percent of d10
  at 4 threads against 3 percent at 1; 27 faults per run, 1 `madvise` purge
  per run; with `MIMALLOC_PURGE_DELAY=-1` the faults fall from 2,973 to 468
  per 100 runs), and atomic reference counts of shared values. Lean's
  semantics do not need them; the allocator setting is a process option, not
  a Lean program change, and was not made.
- d10 and q07 are 6 ms queries; with 1-thread times of 10.6 and 6.5 ms and
  task start and merge costs of the order of 0.3 ms per task, a ratio of 0.4
  needs a persistent worker heap (the faults above) that this work did not
  build.
- Peak RSS of divided streamed scans: the rows of all ranges are held until
  the parent writes them (q21: 137,026 rows, about 23 MB), plus the shared
  page level and per-thread heaps (`MIMALLOC_ARENA_EAGER_COMMIT=0` halves RSS
  of d10 at 4 threads). The 2 times limit is not met for q19 or q21.
- Gates for the rebased tree: `lake build` exit 0; `tests/sbm11/threads.sh`
  exit 0 (all answers identical, including the new default-limit and
  2,048-page sections); `tests/sbm11/run.sh` and
  `SBM11_THREADS=4 tests/sbm11/census.sh` were run on the tree of the first
  commit and of the page-cache and piece commits before the rebase (3,112
  pass, 0 fail, 29 expected-fail; 605 executed, 605 matched, 0 differed) and
  not again after it; the three `tools/lean-*.py --gate` audits exit 0.

## Stage 1d: peak RSS of the divided streamed path (2026-10-22)

Issue https://github.com/danbri/factoidal/issues/799, key result in
https://github.com/danbri/factoidal/issues/875: peak RSS at 4 threads at most
2 times the RSS at 1 thread.

Cause. The streamed path (`IdQuery.streamPartM`) cut the scan into ranges of
at most 16 blocks. olympics q21 selects 34 blocks, so the ranges were 4 of 9
blocks: as many ranges as tasks. `Harness/Sbm11Query.parFold` already folds
the results in range order and starts the next task when one is folded, but
with 4 ranges and a window of 4 tasks every range was running or finished
before the first was written, so all 137,026 rows (about 23 MB rendered) were
held at once.

Repair (`IdQuery.streamRangeBlocks` = 1). A range of the streamed path is one
block. There are then more ranges than tasks, and `parFold` holds at most
`threads` running or finished ranges (the parent writes range k and frees it
before the task for range k + threads starts). The order of the answer does
not change: `parFold` folds in range order. Values tried (q21 at 4 threads,
single runs, 7 repeats): 2 blocks 69 MB, 1 block 63 MB, 4 blocks 83 MB, 16
blocks 105 MB.

Theorems (`ParallelMergeTheorems`; `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound` or a subset; no hypothesis states a
conclusion):

- `stream_divided_eq_single` (stage 1b) holds for every range size `c`.
- `stream_one_block_ranges_eq_single`: its instance `c = 1`.
- `stream_incremental_eq`: stepping over the ranges one prefix at a time, in
  range order, equals stepping over all of them.

Tested, not proved (as in stage 1b): that `parFold` frees each range before
the next starts, and the `Table`/`ByteArray` steps: `tests/sbm11/threads.sh`.

Measurement. `tests/sbm11/bench-threads.sh`, olympics, `--verify none`, 6
rounds (round 1 dropped), 7 runs per process, median over rounds of the
warm median; RSS is the largest VmHWM. Machine shared with other work.

| Query | threads | before ms | after ms | before RSS MB | after RSS MB |
| --- | ---: | ---: | ---: | ---: | ---: |
| q19 | 1 | 44.9 | 42.1 | 58 | 58 |
| q19 | 4 | 28.6 | 24.7 | 108 | 93 |
| q21 | 1 | 107.5 | 129.6 | 42 | 42 |
| q21 | 4 | 57.9 | 51.6 | 107 | 67 |

RSS ratio 4 to 1 thread: q19 1.86 to 1.60, q21 2.55 to 1.60. Both within 2.
The 1-thread binary is the same code before and after (the change applies to
divided scans only); the q21 1-thread time differences (107.5 and 129.6 ms)
are machine noise, and the 4-thread times did not get worse.


Gates (exit codes read): `lake build` exit 0 (1,869 jobs);
`tests/sbm11/threads.sh` exit 0 (all answers identical, 1, 2, 4, 8 threads);
`tests/sbm11/run.sh` exit 0 (3,112 pass, 0 fail, 29 expected-fail, out of
3,141); `SBM11_THREADS=4 tests/sbm11/census.sh` exit 0 (605 executed, 605
matched the reference engine, 0 differed); `tools/lean-tail-recursion-audit.py
--gate`, `tools/lean-unbuilt-modules.py --gate`,
`tools/lean-registry-audit.py --gate`, `tools/lean-csimp-reach.py --gate` exit
0; `tools/lean-hygiene-audit.py` (no `--gate` option) clean; no `sorry` added.

## Stage 1e: range workers and the remaining costs (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/799, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. Owner constraint, 2026-10-22,
verbatim: "Yes lets come back to allocator later". No allocator option or
environment variable was set or changed. Commits on branch
`batch3/kr12-speed`: `5fdf2a9e`, `71ad4e92`, `f3022eae`, `a2cdf15d` and this
record.

### 1e.1 Result

4 threads against 1 thread, before (`origin/main` `271fbcae`) and after
(this branch), the 1b.6 method: `tests/sbm11/bench-threads.sh` with
`ROUNDS=8 REPEAT=7 THREADS="1 4"` (DBpedia with `VERIFY=none`), round 1
dropped, median over 7 processes of each process's warm median; RSS is the
largest VmHWM. Machine: 4 vCPU (`nproc` 4), kernel 6.18.44-fc-v153 (the
container restarted during this work and the kernel changed; both columns
were measured on the new kernel, one after the other, 2026-10-23 04:20 to
04:33 UTC); load average 1.3 to 1.4. Raw CSV:
`.claude-runs/kr12-final-{before,after}-{oly,dbp}.csv` (not in the
repository).

| Query | 1 thread ms before / after | 4 threads ms before / after | 4/1 before | 4/1 after | RSS MB 1 / 4 threads after | RSS 4/1 after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q21 | 100.3 / 95.3 | 46.9 / 31.7 | 0.47 | 0.33 | 52 / 92 | 1.76 |
| q19 | 33.2 / 34.4 | 24.4 / 19.6 | 0.73 | 0.57 | 70 / 116 | 1.65 |
| d10 | 10.2 / 9.9 | 6.5 / 5.6 | 0.64 | 0.56 | 26 / 50 | 1.92 |
| q07 | 5.05 / 4.95 | 5.39 / 5.58 | 1.07 | 1.13 | 38 / 57 | 1.51 |
| d17 | 0.33 / 0.32 | 0.34 / 0.32 | 1.02 | 1.02 | 22 / 22 | 1.00 |

q21 meets 0.4. q19, d10, q07 and d17 do not. The RSS limit (at most 2 times
1 thread) holds for all five. The 1-thread code is the same before and after
except the page-limit reads (1e.2 item 2); the 1-thread differences are run
to run variation. Single processes vary by up to 2 times between their
fastest and median runs at 4 threads (q19: medians 13.8 to 22.4 ms over four
processes of 7 runs), so a ratio is not reliable to better than about 0.05.

Answers: `tests/sbm11/threads.sh` exit 0 after each commit (gate fixture 140
and 140 identical, olympics 21 and 2 and 2, DBpedia 19; DBpedia against the
three-engine record: equal 76, different 0).

### 1e.2 Method

1. **Range workers** (`Harness/Sbm11Query.parFold`). Before: one pool task
   per block range, each with a new view of the session and an empty page
   cache. The streamed path has ranges of one block (stage 1d), so q19 made
   about 70 tasks per query, and each filled a new cache from `taskPages`.
   After: at most `threads` worker tasks per fold. A worker takes the next
   range from a shared counter (ranges are taken in range order), keeps its
   view and page cache for all its ranges, and puts the result in the range's
   slot; the parent folds the slots in range order and takes each result out
   of its slot (a resolved `IO.Promise` keeps its value while the promise is
   reachable: with results in promises, q21 at 4 threads held all its rows,
   121 MB peak RSS against 81 MB). A bounded fold (the streamed path) gives
   range `k` a permit only after range `k - 2 × threads` is folded
   (`parWindowFactor` 2; 1 per thread: q19 19.0 ms and q21 37.0 ms against
   15.2 and 28.9 ms, single processes of 21 runs). The counted and ORDER BY
   ... LIMIT paths (small results) give every range a permit at once
   (`IdQuery.Par.fold`'s `bounded` argument).
2. **Page limits read once.** `SBM11_PAGES` and `SBM11_TASK_PAGES` were read
   from the environment on every page insert (`getenv`: 1.3 percent of q19
   at 4 threads). They are read at `openSession` (`Session.pageLimit`,
   `Session.taskPageLimit`).
3. **Shared pages without `dictLock`.** `Session.sharedPage` reads a ready
   page from `taskPages` with `IO.Ref.get` (a persistent tree map: the get
   gives the map as it was at one moment) and takes the lock only for a page
   that is missing or being loaded. `perf record -e sched:sched_switch`: 82
   percent of the context switches of q19 at 4 threads were waits for
   `dictLock` in this function before; most remaining switches are in the
   loads under `--verify merkle`, which still run under the lock.
4. **A page is copied on its second use.** A worker's first use of a page
   reads the shared page and keeps no copy (`Session.onceSeen`, a set the
   worker makes); the second use copies it into the worker's cache.
   Reading every page shared (no copy): q19 at 4 threads 26 ms against 18
   ms (reference counts on pages that all workers read).
5. **New strings in the task copies.** `s ++ ""` compiles to `s` (checked
   with `lean -c`, Lean 4.33.1), so `ScanSpec.fresh`, `FKind.fresh` and
   `countPartM` kept the shared variable-name strings that every task reads
   in every block. `IdQuery.freshStr` (`String.ofList s.toList`,
   `@[noinline]`) makes a new object. d10 at 4 threads: the reference counts
   of the group variable names were 5 percent of the profile (0.5 percent at
   1 thread); after, they are not in the profile. The skill
   `lean4-performance` said `++ ""` makes a copy from 2026-10-13; corrected
   in the same landing.

### 1e.3 What is proved and what is tested only

- `IdQuery.freshStr_eq` (`freshStr s = s`) and `IdQuery.map_freshStr`; with
  them `ScanSpec.fresh_eq` and `FKind.fresh_eq` stay proved. `#print
  axioms`: `propext`, `Classical.choice`, `Quot.sound`.
- The merge theorems of stages 1b and 1d hold for the ranges of any size and
  are unchanged: the workers fold the same ranges in the same order.
- Tested only: that `parFold` folds every range once in range order, frees
  each result, and finishes its workers after a failure;
  `tests/sbm11/threads.sh` (1, 2, 4 and 8 threads, byte-identical answers and
  stderr byte counts with `SBM11_PAGES=1000000`), `tests/sbm11/run.sh` and the
  census at 4 threads.

### 1e.4 Tried and not kept

- A page cache per worker slot kept for the life of the session (a
  `Std.TreeMap`, because a cache that two threads reach over its life is MT
  and a hash map that is MT is copied on every insert): q19 at 4 threads 18 to
  22 ms, q21 38 to 48 ms (a tree look-up per id).
- Larger worker caches (`SBM11_TASK_PAGES` 1,024 to 8,192): no faster, peak
  RSS of q19 at 4 threads 150 to 157 MB.
- 4 and 64 counted ranges per thread for d10 (to spread its 137 read blocks
  over more ranges): no change in time (5.5 to 6.5 ms at 4 threads either
  way).

### 1e.5 What remains (https://github.com/danbri/factoidal/issues/961)

- q07 (5 ms): at 4 threads the parent thread has 36 percent of the CPU
  samples (about 2.8 ms per run): the plan, the two scans below the range
  minimum, the merge and hash joins, the ORDER BY keys and the rendering. The
  divided scans with candidates are 48 percent of the 1-thread time. 0.4
  needs the joins and the ORDER BY keys divided.
- d17: answered from the PRM1 entries (commit `ddcd9e54`); there is no scan
  to divide. A decision for the owner: drop it from KR 1.2 or replace it.
- d10 and q19: `clear_page_erms` (first touch of fresh memory in the worker
  heaps) is the largest cost that 1 thread does not have (q19: +877 samples
  of 14,359 at 4 threads; d10: +459 of 12,212). It is allocator behaviour,
  left for the deferred allocator work.
- d10 and q19: at 4 threads CPU time is 1.37 and 1.47 times the 1-thread CPU
  time, and the workers are busy about half the wall time.
- No timing harness compares these ratios with a target, so there is no
  expected-failure row.

### 1e.6 Gates

On commit `a2cdf15d` (exit codes read):

| Gate | Result |
| --- | --- |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `tests/sbm11/threads.sh` | exit 0: all answers identical (1e.1) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `tools/land-gates.sh` | exit 0: `lake build`, `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, wasm, native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), npm 588 pass, 0 fail, 2 skipped, hub 479 pass, 0 fail, engine-compare 7 pass, 0 fail, the LWS, Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

Census rows: "matched the reference engine" is row agreement over the same
input, not conformance.

## Stage 1f: q07 serial work after the scans (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961 (item 1), key result KR
1.2 of https://github.com/danbri/factoidal/issues/875. Owner constraint,
2026-10-22, verbatim: "Yes lets come back to allocator later". No allocator
option or environment variable was set or changed. Branch
`batch3/kr12-q07`.

### 1f.1 Result

The 1b.6 method: `tests/sbm11/bench-threads.sh`, `ROUNDS=8 REPEAT=7
THREADS="1 4"` (DBpedia with `VERIFY=none`), round 1 dropped, median over 7
processes of each process's warm median; RSS is the largest VmHWM. Before:
`origin/main` `09b25507`; after: this branch. The two binaries ran one after
the other, 2026-10-23 05:51 to 05:52 UTC, load average 1.0 to 1.3. Raw CSV:
`.claude-runs/q07/final-{before,after}-{oly,dbp}.csv` (not in the
repository).

| Query | 1 thread ms before / after | 4 threads ms before / after | 4/1 before | 4/1 after | RSS MB 1 / 4 threads after | RSS 4/1 after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q07 | 6.05 / 5.01 | 6.56 / 3.78 | 1.09 | 0.75 | 26 / 39 | 1.47 |
| q21 | 95.94 / 94.76 | 36.40 / 36.40 | 0.38 | 0.38 | 42 / 75 | 1.77 |
| q19 | 37.28 / 34.03 | 20.13 / 22.75 | 0.54 | 0.67 | 58 / 105 | 1.79 |
| d10 | 11.19 / 10.14 | 6.66 / 6.35 | 0.60 | 0.63 | 26 / 51 | 1.92 |
| d17 | 0.35 / 0.31 | 0.37 / 0.33 | 1.06 | 1.07 | 22 / 22 | 1.01 |

q07 does not meet 0.4. The RSS limit (at most 2 times 1 thread) holds for
all five. The q19 4-thread difference is run-to-run variation: interleaved
(8 rounds, 7 runs, the same two binaries, 05:52 UTC) q19 was 18.98 ms before
and 18.76 ms after at 4 threads, 34.69 and 33.26 ms at 1 thread. The q19,
q21, d10 and d17 code paths changed only by the constant-id memo (1f.2
item 3). Other A/B runs of q07 (interleaved, 8 to 10 rounds): 4/1 0.68 to
0.71 after, 0.95 to 1.06 before.

### 1f.2 Method

The q07 time was split by timestamps around the store calls (a temporary
trace, not committed; medians of 41 runs in one process, microseconds):

| Phase | 1 thread | 4 threads before | 4 threads after |
| --- | ---: | ---: | ---: |
| constants (6 dictionary look-ups) and estimates | 477 | 507 | 60 |
| scan of pattern 1 (8,192 estimated rows) | 161 | 166 | 170 |
| scan of pattern 0 (16,384 estimated rows) | 220 | 370 | 215 |
| merge join (6,248 by 13,369 rows) and candidates | 450 | 467 | 451 |
| scan with candidates, pattern 2 (66 blocks) | 1,708 | 1,190 | 806 to 853 |
| merge join and candidates | 125 | 151 | 140 to 155 |
| scan with candidates, pattern 3 (34 blocks) | 1,147 | 780 | 609 to 647 |
| hash join, ORDER BY keys and sort, rendering | 1,090 | 1,146 | 1,117 to 1,135 |

What landed:

1. **The calling thread scans the first block range**
   (`scanTableParM`, `scanSipTableParM`). Before, the parent started one
   task per range and waited. A task waits for a sleeping pool worker: on
   this VM a woken thread runs 50 to 120 microseconds later (a C
   condition-variable test: median 79, p90 126), and `perf sched record`
   showed only 2 pool worker threads in a 4-thread q07 process (the runtime
   starts a worker only when a task is queued and no worker counts as idle).
   q07 at 4 threads 4.25 to 3.68 ms.
2. **BGP scans need `2 × minRows` estimated rows per range** (16,384 by
   default). The scan of pattern 0 in 2 ranges took 0.37 to 0.47 ms against
   0.24 to 0.28 ms in one.
3. **Constant ids are kept for the session** (`Session.idMemo`, dictionary
   hits only, at most 65,536 entries). Each look-up is a binary search over
   GDX1 entries and GDV1 pages, about 14 positioned reads; 0.43 ms of q07
   at every thread count.
4. **The merge join in left row ranges** (`ParallelJoin`,
   `IdQuery.mergeJoinParM`), for at least 32,768 input rows per range (every
   join of 2 rows or more when `Par.minRows` is 0, the gate fixtures). Each
   range starts at the binary-search lower bound of its first left value in
   the right column; the ranges' index pairs are appended in order and the
   output gathered once. q07's join (19,617 rows) is not divided: in 4 ranges
   it took 0.47 to 0.52 ms against 0.45 ms. With `--sip off` q07 joins
   13,369 and 269,625 rows: 4 threads 16.8 ms before, 13.5 to 15.5 ms with
   the divided join.

### 1f.3 What is proved and what is tested only

- Proved (`ParallelJoinTheorems`, `#print axioms`: `propext`,
  `Classical.choice`, `Quot.sound`; no hypothesis states a conclusion):
  `mergeJoinRanges_rangeChunks`: the join computed in the ranges of
  `rangeChunks` is `Qlvr.mergeJoin`, for join columns in non-decreasing
  order (the precondition of `MergeTheorems.mergeGo_spec`). With
  `lowerBound_spec`, `rangePairs_spec`, `chain_flatten`, `ranges_chain`.
  `mapPar_eq`: the task map is `List.map` (`Task.spawn fn` is `⟨fn ()⟩` in
  the logic). So `mergeJoinParM` equals `mergeJoin` by proof, not by test.
- Tested only: the caller-runs change and the scan threshold
  (`tests/sbm11/threads.sh`, byte-identical answers at 1, 2, 4 and 8
  threads; the gate fixtures divide every join); the memo
  (`tests/sbm11/run.sh`, the census).

### 1f.4 Tried and not kept

- **ORDER BY values read by range workers** (`Par.fold`, a view and a page
  cache per worker): q07's ORDER BY (291 values) 0.5 ms slower at 4 threads.
- **ORDER BY sort in aligned power-of-two blocks** sorted by tasks, then the
  merge passes from the block width (equal to `mergeSortBy` by `#guard`s): an
  ORDER BY of the 137,026 olympics labels took 930 ms at 4 threads against
  648 ms. The tasks' closures make the shared values MT, so every
  comparison takes and drops references atomically.
- **The merge join with the columns passed as closures**: `mergeGo` was
  specialised for the closure parameter, every row read was `lean_apply_1`
  with a boxed `UInt64`; 2.5 ms in 4 ranges against 0.45 ms. Repaired
  before landing (`rangePairsOf` passes lambdas over local byte arrays).
- **All pool workers started at open** (N tasks that wait until all N run):
  no time gained, peak RSS above 2 times the 1-thread RSS (q07 2.30, d10
  2.33): each running worker has its own heap.
- **More block ranges per scan with candidates** (8 instead of 4): no change
  beyond run-to-run variation.
- **A cached file descriptor per path** for `l4_block_pread` (a diagnostic
  build): the constant look-ups 0.25 ms faster, the scans unchanged. Not
  needed after the memo.

### 1f.5 What remains

q07 at 4 threads is about 3.7 ms; 0.4 needs about 2.0 ms. The serial part
alone is about 2.1 ms: the two small scans (0.39 ms), the merge join
(0.45 ms; dividing it costs more than it saves at this size), the second
join (0.15 ms), and the tail (1.12 ms: hash join, ORDER BY values by
`termOf` and the `sparqlOrderValue` sort, rendering of 313 rows). Each of
these is under 0.5 ms single-threaded, below the cost of a task that waits
for a sleeping worker. The two scans with candidates reach 2.0 and 1.8
times their 1-thread speed with 4 ranges, not 4: the wake-up of the 3
workers, and unequal work per range (blocks skipped by candidates).
Reaching 0.4 needs workers that do not sleep between the phases of a query
(a per-session worker pool) and the tail divided on such workers. That is a
design change, tracked in https://github.com/danbri/factoidal/issues/961.

### 1f.6 Gates

On commit `a0c92771` (exit codes read):

| Gate | Result |
| --- | --- |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `tools/land-gates.sh` | exit 0: `lake build`, `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, wasm, native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), npm 588 pass, 0 fail, 2 skipped, hub 479 pass, 0 fail, engine-compare 7 pass, 0 fail, the LWS, Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

## Stage 1g: a per-session worker pool (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961 (item 1), key result KR
1.2 of https://github.com/danbri/factoidal/issues/875. Owner constraint,
2026-10-22, verbatim: "Yes lets come back to allocator later". No allocator
option or environment variable was set or changed. Branch
`batch3/kr12-pool`.

### 1g.1 Result

q07 does not meet 0.4. Its 4-thread over 1-thread ratio went from 0.74 to
0.66 (the 1b.6 method) and from 0.76 to 0.62 with 21 runs per process. The
RSS limit holds for q07, q19, q21 and d17. d10 is at the limit before and
after (below).

Method: the 1b.6 method with the two binaries interleaved (before:
`origin/main` `4cb598ae`; after: this branch), 8 rounds, round 1 dropped, 7
processes per cell, `--repeat 7` (a second run with `--repeat 21`), median
over processes of each process's warm median; RSS is the largest VmHWM.
DBpedia with `--verify none`. 2026-10-23 07:20 to 07:40 UTC, load average 1.6
to 2.3 (the 4-thread runs themselves; no other job ran). Raw CSV:
`.claude-runs/pool/ab-r7.csv`, `ab-r21.csv` (not in the repository).

| Query | 1 thread ms before / after | 4 threads ms before / after | 4/1 before | 4/1 after | RSS MB 1 / 4 threads after | RSS 4/1 after |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q07 | 5.05 / 5.30 | 3.75 / 3.50 | 0.74 | 0.66 | 26 / 38 | 1.45 |
| q21 | 109.57 / 90.86 | 35.73 / 36.87 | 0.33 | 0.41 | 42 / 74 | 1.76 |
| q19 | 32.70 / 32.46 | 20.61 / 16.50 | 0.63 | 0.51 | 58 / 102 | 1.76 |
| d10 | 10.38 / 13.87 | 7.67 / 6.67 | 0.74 | 0.48 | 26 / 48 | 1.84 |
| d17 | 0.34 / 0.39 | 0.34 / 0.36 | 1.02 | 0.92 | 22 / 28 | 1.28 |

With `--repeat 21` (same method otherwise):

| Query | 4/1 before | 4/1 after | 4 threads ms before / after | RSS 4/1 after |
| --- | ---: | ---: | ---: | ---: |
| q07 | 0.76 | 0.62 | 4.06 / 3.34 | 1.45 |
| q21 | 0.38 | 0.37 | 34.29 / 33.84 | 1.72 |
| q19 | 0.57 | 0.53 | 18.52 / 18.27 | 1.79 |
| d10 | 0.67 | 0.66 | 6.89 / 6.50 | 2.07 |
| d17 | 1.26 | 1.06 | 0.39 / 0.31 | 1.28 |

The q21 and d10 1-thread differences in the first table (109.6 against 90.9
ms, 10.4 against 13.9 ms) are run-to-run variation: those paths have the same
code at 1 thread, and the second table has 91.0 / 92.3 and 10.3 / 9.9 ms.
No 1-thread time and no 4-thread time of q19, q21, d10 or d17 got slower
beyond that variation. d10 peak RSS, 10 processes each, 21 runs: 1 thread
26.4 to 29.0 MB; 4 threads before 48.4 to 57.2 MB (median 55.1), after 44.9
to 55.5 MB (median 53.7). The ratio of the largest values is 2.1 before and
1.9 after; the limit of 2 is met by the medians, not by every process, and
this work did not change that.

One process of q07 with 61 runs (`SBM11_PHASES=1`, the phase medians in
milliseconds; "before" is `4cb598ae` with the same marks added):

| Phase | 1 thread before | 1 thread after | 4 threads before | 4 threads after |
| --- | ---: | ---: | ---: | ---: |
| constants | 0.036 | 0.033 | 0.036 | 0.073 |
| scan of pattern 1 | 0.208 | 0.182 | 0.216 | 0.152 |
| scan of pattern 0 | 0.251 | 0.215 | 0.243 | 0.131 |
| merge join | 0.444 | 0.407 | 0.429 | 0.188 |
| scan with candidates, pattern 2 | 1.906 | 1.796 | 0.950 | 0.729 |
| merge join | 0.031 | 0.030 | 0.041 | 0.040 |
| scan with candidates, pattern 3 | 1.357 | 1.257 | 0.760 | 0.579 |
| hash join | 0.051 | 0.048 | 0.062 | 0.070 |
| ORDER BY keys and sort | 0.845 | 0.668 | 0.879 | 0.737 |
| rendering | 0.280 | 0.234 | 0.251 | 0.260 |
| whole query | 5.41 | 4.92 | 4.02 | 3.05 |

### 1g.2 The pool alone: start latency

`l4pool-bench 2000 200 3` (`Harness/WorkerPoolBench.lean`): 2,000 rounds;
in each the caller works 200 microseconds, then starts 3 jobs that read the
clock, and waits for them.

| Runner | job start p50 / p90 (us) | all results p50 / p90 (us) |
| --- | ---: | ---: |
| `IO.asTask` (Lean task pool) | 59 / 87 | 74 / 119 |
| worker pool, poll 1 ms | 5 / 9 | 8 / 12 |
| worker pool, poll 0 (block at once) | 124 / 219 | 167 / 266 |

The pool reduces the start latency by a factor of about 10, so the work went
on to divide phases on it.

### 1g.3 Design

`Harness/WorkerPool.lean`. `l4sbm11 query --threads N` starts N - 1 threads
when N is above 1 and at most the hardware threads
(`System.Platform.Internal.getHardwareConcurrency`); the calling thread is
the N-th. They stop when the command ends.

- Threads: `IO.asTask ... Task.Priority.dedicated`, one thread per worker,
  outside the Lean pool's worker limit, and no other task queued on it.
- Channel: a `Cell` per worker (mailbox) and per job (result): an `IO.Ref`
  that its one reader polls with `swap` (an atomic exchange) for at most 1 ms,
  then a promise it blocks on. A writer resolves the promise only when the
  reader has published one.
- Not chosen: `IO.Promise` as the channel (start p50 24 us: `resolve` and
  `wait` take the task manager's lock that every thread shares);
  `Std.Channel` (not measured: it is built on a mutex and condition
  variables, so a blocked receiver has the same kernel wake-up, and it has
  no bounded poll);
  `Task.spawn` (the Lean pool, 1f).
- `wake` at the start of a query with two or more triple patterns makes
  blocked workers poll again, so the first divided phase finds them awake.
- At 8 threads on 4 vCPUs no pool is started (7 polling workers made the
  scans with candidates 3 to 5 times slower); the divided paths then use
  `IO.asTask` as before.

What runs on the pool: the ranges of `scanTableParM`, `scanSipTableParM`
and the workers of `parFold` (`Session.spawnAt`); the ranges of the merge
join (`IdQuery.Par.mapList`, `poolMap`), divided from 4,096 input rows per
range (`poolJoinRows`; 32,768 without the pool); BGP scans divided from
4,096 estimated rows per range (`poolScanRows`; 16,384 without).

Not on the pool: ORDER BY keys and rendering (1g.6). In their place, a
1-thread change: `IdQuery.OrderRead` makes `isNumericOperand`,
`numericValue?` and `orderView` once per distinct value, and
`SPARQL.sparqlOrderViewed` compares two readings; `sparqlOrder` made them for
both operands on every comparison. q07's sort and ranks: 0.33 to 0.14 ms at
every thread count.

`IdQuery.Store.mark` (no effect on answers) and `SBM11_PHASES`: the phase
table above.

### 1g.4 What is proved and what is tested only

- Proved (`WorkerPoolTheorems`, `SPARQL/Query.lean`; `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound`; no hypothesis states a
  conclusion): `mergeJoinParM_eq` (the divided merge join is `mergeJoin`,
  given the runner's contract `mapList f xs = pure (xs.map f)` and join
  columns in non-decreasing order); `sparqlOrder_eq_viewed`,
  `OrderRead.cmp_of`, `orderRanks_map` (the ORDER BY ranks from the readings
  are the ranks the former code computed).
- Tested only: that the pool's `mapList` meets that contract, that the pool
  runs every job once and returns its result, the scan thresholds:
  `tests/sbm11/threads.sh` (byte-identical answers at 1, 2, 4 and 8 threads;
  8 threads uses no pool), `tests/sbm11/run.sh`, the census at 4 threads.

### 1g.5 Gates

On commit `a7c1e0f0` and the commits before it (exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 (1,994 jobs) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `lean-tail-recursion-audit.py --gate`, `lean-unbuilt-modules.py --gate` | exit 0, exit 0 (941 modules reached) |
| `tools/land-gates.sh` | LAND_GATES_RESULT |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

### 1g.6 Tried and not kept

- **ORDER BY readings and rendering in 4 parts on the pool**, each part on a
  view of the session (`Session.view`, `Session.local`). Each part took 2 to
  4 times as long per item as the same part on the calling thread with its
  own page cache; the same part on the calling thread through a view was as
  slow (page copies on second use, references to shared pages). With no
  page copies in those views, rendering 0.25 to 0.19 ms; the parent's sort
  of values the workers returned (MT) took 0.48 ms against 0.14 ms. Each
  part sorting its own values and the parent merging the runs: sort and
  ranks 0.12 ms, but the parts no faster. A/B over 6 processes of 41 runs:
  median 3.29 ms with the divided steps, 2.99 ms without. Removed.
- **Scans with candidates in 3 ranges per thread taken from a shared
  counter** (to balance ranges whose blocks are skipped by candidates):
  no change beyond run-to-run variation (0.69 to 0.83 and 0.55 to 0.67 ms).
- **A mailbox written with `IO.Ref.modify`** while the worker polled it with
  `swap`: job start p90 1,020 us (the whole poll time). Written with `swap`
  then `set`: p90 9 us.
- **A shutdown that only resolved a published promise**: a worker between
  its last poll and its wait had published none, and the process hung.
  Shutdown writes a value.
- **Waking the workers at the start of every query**: d17 (one pattern, 0.3
  ms) 0.37 ms at 4 threads against 0.29 ms.

### 1g.7 What remains

q07 at 4 threads is about 3.0 to 3.5 ms; 0.4 needs about 2.0 ms. The parts
of the work that the pool divides do not reach 4 times their 1-thread speed:

- The two scans with candidates (3.05 ms at 1 thread) take 1.3 ms at 4
  threads: each range does its blocks 1.3 to 1.7 times slower per block than
  1 thread does (27 to 44 us against 26 us per block, single runs). A C test
  of 4 threads on this VM (integer work, and random reads of 32 MB) runs at
  1.0 and 1.17 times the 1-thread time, so the machine is not the cause.
  The cause is not measured. Candidates: the PRM1 entries array that every
  range reads (shared, so reference counts are atomic), and the fresh memory
  of each worker's heap (1e), which is in the allocator work the owner
  deferred.
- The ORDER BY keys (0.67 ms, 291 values read through the dictionary) and
  the rendering (0.23 ms) stay on one thread (1g.6).
- The constants phase is 0.07 ms at 4 threads against 0.03 ms: the wake of
  the workers (`IO.Promise.resolve` for blocked workers).

Next step for 0.4: find the per-block cost of a range at 4 threads with a
per-thread profile (`perf record` with the binary unchanged since the
record), then give a worker unshared copies of what it reads per block; and
the allocator work.
Issue https://github.com/danbri/factoidal/issues/961 stays open.
