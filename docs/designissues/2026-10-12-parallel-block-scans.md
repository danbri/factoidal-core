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

On commit `dc320096` (exit codes read; the answer gates on `54208643`, which has the same Lean code apart from the wake rule of `26ce3f94`; `threads.sh` was run again on `dc320096`):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 (1,994 jobs) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `lean-tail-recursion-audit.py --gate`, `lean-unbuilt-modules.py --gate` | exit 0, exit 0 (941 modules reached) |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): `lake build`, unbuilt-modules, tail-recursion, wasm, native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), npm, hub, engine-compare, the LWS, Solid and authorization suites, lint |
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

## Stage 1h: where the 4-thread time goes (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. Owner constraint, 2026-10-22,
verbatim: "Yes lets come back to allocator later". No allocator option or
environment variable was set or changed. Branch `batch3/kr12-perthread`. The
question from stage 1g: why does each range of a scan with candidates do its
blocks 1.3 to 1.7 times slower at 4 threads than 1 thread does?

### 1h.1 Result

No engine code changed. The three code changes that this stage tried did not
meet the gates of KR 1.2 (1h.4). The measurements:

- Atomic reference counts are a small part of the extra time. Olympics q07 at
  4 threads: 0.19 ms of CPU per run (of 13.2 ms over all threads, 6.2 ms of
  it pool polling). The parts that code can remove without allocator work
  are not large enough to measure through the run-to-run variation.
- The scans with candidates of q07 lose time in four places: no range is
  switched out by the scheduler (0 of 800 ranges); a range run on a pool
  worker takes 15 to 25 percent longer than the same range on the calling
  thread, also when it is the only range that runs (stage 1g measured 1.3 to
  1.7 times from single runs; the medians of 100 runs per mode give 1.15 to
  1.25); the four ranges hold
  unequal work (the largest is 1.20 and 1.12 times the mean); and the
  waits at the start and end of the phase are 10 to 40 microseconds.
- The cause of the slower worker ranges is not found. It is not contention
  between workers, not the shared reference counts of the session's
  counters and permutation handles (copies made by the worker: no change),
  not the polling of the other workers (polling off: no change), and not the
  vCPU (the four vCPUs run one thread at the same speed). This VM has no
  hardware counters, so cache misses cannot be counted. The data a worker
  reads and writes per block is in its own heap (the block buffer from
  `pread`, the output columns), which is allocator behaviour.
- Olympics q19 at 4 threads spends 2.7 times the CPU time of 1 thread
  (79.9 against 29.1 ms per run). Most of the extra is that each query copies
  the dictionary pages again into new per-worker caches: the copies, the
  evictions of a full cache, fresh memory in the worker heaps and the frees
  of objects another thread made. A page cache per pool worker that lives as
  long as the pool removes 40 percent of that CPU time and 20 percent of the
  4-thread time, but its peak RSS is above 2 times the 1-thread RSS (1h.4).

KR 1.2 now (binary of `origin/main` `cbd7c72a`, which this stage does not
change), and the page cache of 1h.4 item 3 beside it for the record. The
1b.6 method with the two binaries interleaved: 8 rounds, round 1 dropped, 7
processes per cell, median over processes of each process's warm median; RSS
is the largest VmHWM. DBpedia with `--verify none`. 2026-10-23 08:22 to 08:40
UTC; load average 0.7 to 1.0 before the runs. Raw CSV:
`.claude-runs/perthread/ab-r7.csv`, `ab-r21.csv` (not in the repository).

| Query | `--repeat 7`: 1 / 4 threads ms | 4/1 | `--repeat 21`: 1 / 4 threads ms | 4/1 | RSS MB 1 / 4 threads (largest) | RSS 4/1 | target met |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 5.83 / 3.44 | 0.59 | 5.32 / 3.38 | 0.64 | 26 / 38 | 1.45 | no |
| q19 | 37.38 / 19.77 | 0.53 | 35.03 / 18.68 | 0.53 | 58 / 101 to 105 | 1.73 to 1.80 | no |
| q21 | 103.03 / 37.72 | 0.37 | 95.62 / 35.96 | 0.38 | 42 / 74 to 76 | 1.75 to 1.79 | yes |
| d10 | 10.39 / 7.26 | 0.70 | 10.70 / 7.27 | 0.68 | 26 to 28 / 50 to 51 | 1.83 to 1.90 | no |
| d17 | 0.35 / 0.36 | 1.02 | 0.31 / 0.31 | 0.99 | 22 / 28 to 29 | 1.28 | no |

The page cache per pool worker (not kept), same runs:

| Query | 4/1 `--repeat 7` | 4/1 `--repeat 21` | RSS 4/1 (largest) |
| --- | ---: | ---: | ---: |
| q07 | 0.60 | 0.78 | 1.45 |
| q19 | 0.44 | 0.39 | 2.02 to 2.03 |
| q21 | 0.42 | 0.40 | 1.94 |
| d10 | 0.70 | 0.59 | 1.92 to 2.01 |
| d17 | 1.21 | 0.86 | 1.28 |

The d10 1-thread time (10.4 to 10.7 ms) is the same as in stage 1g's second
table (10.3 / 9.9 ms); its 4-thread time is 7.3 ms here against 6.5 to 6.7
ms there, run-to-run variation of the VM (single processes of q19 at 4
threads took 14 to 33 ms in this stage).

### 1h.2 Method

- `perf`: `/usr/lib/linux-tools/6.8.0-146-generic/perf` (`/usr/bin/perf`
  asks for a package of the running kernel 6.18.44-fc-v153). Software
  events only: `perf stat -e cache-misses,instructions` gives "not
  supported" on this VM.
- Cost split: `perf record -e cpu-clock -F 1999 --call-graph dwarf,8192`
  of `l4sbm11 query --repeat N` and of `--repeat 1` (open, first run, exit)
  at 1 and 4 threads; `tools/perf-cost-split.py` (new) subtracts the second
  from the first and puts each sample in a class by its stack. The figures
  are CPU milliseconds per warm run, summed over all threads. The class
  "atomic RC / MT refs" counts `lean_dec_ref_cold`, which also frees
  single-threaded objects, so it is an upper bound.
- Range timing (temporary marks, not committed): the start and end time and
  the thread id (`IO.getTID`) of each range of `scanSipTableParM`, with
  `perf record -k CLOCK_MONOTONIC -e sched:sched_switch` for the times a
  thread was switched out. Three modes in one process (61 to 101 runs): the
  ranges one after another on the calling thread, one after another on the
  pool workers (each awaited before the next), and in parallel as shipped.
- MT state: a temporary `@[extern c inline "lean_is_mt(#2)"]` probe printed
  which session fields are marked multi-threaded after a run at 4 threads:
  `taskPages` and `idMemo` (shared with the task views, as designed); the
  session's own `pages` is not.

### 1h.3 Cost split

CPU milliseconds per warm run, all threads. q07: 300 warm runs; q19: 60;
d10: 200 (DBpedia, `--verify none`). Binary of `origin/main` `cbd7c72a`.

| Class | q07 1 / 4 threads | q19 1 / 4 threads | d10 1 / 4 threads |
| --- | ---: | ---: | ---: |
| compute (Lean code) | 4.80 / 5.32 | 28.74 / 56.37 | 8.46 / 9.89 |
| allocator | 0.40 / 0.87 | 5.53 / 12.21 | 2.48 / 2.80 |
| atomic RC / MT refs (upper bound) | 0.06 / 0.24 | 0.69 / 5.64 | 0.35 / 1.02 |
| page faults, zeroing | 0.07 / 0.09 | (1) / 1.69 | 0.04 / 0.62 |
| kernel: read, open | 0.29 / 0.49 | 0.03 / 0.77 | 0.48 / 0.68 |
| kernel: wake, sleep | 0.00 / 0.05 | 0.01 / 0.60 | 0.00 / 0.20 |
| pool polling | 0 / 6.16 | 0 / 2.58 | 0 / 3.26 |
| total | 5.62 / 13.22 | 29.12 / 79.87 | 11.81 / 18.47 |

(1) The first run of q19 at 1 thread clears more fresh pages than 60 warm
runs together, so the subtraction is negative (-5.9 ms); the 4-thread warm
runs clear about 7.6 ms more per run than the 1-thread warm runs.

The extra time at 4 threads that is not polling, in the classes the stage 1g
record asked for:

| Query | atomic RC (upper bound) | page faults, zeroing | allocator | compute (same code, more CPU: includes cache misses) | kernel |
| --- | ---: | ---: | ---: | ---: | ---: |
| q07 (+1.44 ms) | 0.19 (13 %) | 0.01 (1 %) | 0.47 (33 %) | 0.52 (36 %) | 0.25 (17 %) |
| q19 (+48.2 ms) | 4.95 (10 %) | 7.57 (16 %) | 6.69 (14 %) | 27.63 (57 %) | 1.33 (3 %) |
| d10 (+3.39 ms) | 0.67 (20 %) | 0.58 (17 %) | 0.32 (9 %) | 1.43 (42 %) | 0.39 (12 %) |

Where the classes come from (callers in the profiles):

- q07: the allocator extra is the frees at the end of each pool job of
  objects the calling thread made (`mi_free_block_delayed_mt`,
  `mi_free_generic_mt` under `workerLoop`) and the hash join. The compute
  extra is the divided merge join (its own symbol at 4 threads) and the
  decode loops `Sip.deltaGatherGoY` and `Sip.deltaFindGoY`: 0 to 9 percent
  more samples at 4 threads in two profiles (dwarf, 150 runs: 3,128 against
  3,099 samples in `scanBlockSipM`; flat, 401 runs: +8.8 and +7.9 percent).
  The kernel extra is `open` of the PRB1 file for each block (`d_lookup`,
  `init_file`).
- q19: `copyPage` (`memcpy`, its fresh memory and the reference counts of
  the shared page it copies), `insertPageBounded` (filters of a full worker
  cache), `onceSeen`, `sharedPage` (`taskPages.get` on a shared reference),
  `prefetch`, and the JSON escaping loop `escLoop` (2,420 against 1,857
  samples: the same work reading pages that another thread wrote).
- d10: `clear_page_erms` under `decodeWordsRangeF` (fresh output columns in
  the worker heaps), `lean_dec_ref_cold` under the block functions
  (`cutCol`, `frameSpan`, `blockChunk`), task posting (`lean_mark_mt`).

q07, the scans with candidates (microseconds, medians of 100 runs in one
process at 4 threads, ranges in range order; four processes gave the same
pattern, one of them with every mode 20 percent slower):

| Mode | pattern 2: ranges 0 to 3 | sum | pattern 3: ranges 0 to 3 | sum |
| --- | --- | ---: | --- | ---: |
| one after another, calling thread | 546 525 400 368 | 1,840 | 337 340 338 228 | 1,242 |
| one after another, pool workers | 599 586 564 424 | 2,173 | 395 418 452 280 | 1,545 |
| in parallel (as shipped) | 584 559 476 502 | 2,122 | 370 377 402 342 | 1,491 |

`sched_switch` over 101 runs: no range was switched out (800 ranges, 0
switches between start and end). With pool polling off (`spinNs` 0, the
workers block at once) the pattern is the same.

### 1h.4 Tried and not kept

1. **Counters and permutation handles made by the worker**
   (`Session.forWorker`: new counter refs, `LoadedPerm` copies with new path
   strings, made in the job and added to the view at its end). The session
   view's refs were made by the calling thread next to the result cell that
   it polls, so false sharing was a candidate. q07 ranges on the pool
   workers, sum of the four ranges of pattern 2 (4 processes of 101 runs):
   2,173 to 2,356 us without, 2,266 to 2,446 us with. No gain.
2. **PRM1 entries copied per range** (`freshMeta` of each entry of the
   range, in the job, positions renumbered). DBpedia d10 at 4 threads, CPU
   per warm run: 18.47 against 18.03 ms; the reference-count class 1.02
   against 0.99 ms. The decrements in `cutCol` and `frameSpan` stayed: they
   are frees, not shared entries. Not kept (no measured gain).
3. **A page cache per pool worker for the life of the pool**
   (`Harness.WorkerPool.start` with a value that each pool thread makes and
   gives to its jobs, a dictionary page cache that only that thread reaches;
   bounded folds take ranges in a fixed order, worker `j` ranges `j, j + n,
   ...`, so a worker meets the same pages in the next query; a page is
   copied into it on its second use in a fold). Olympics, 14 rounds (13
   kept) of `--repeat 7`, 2,048 pages per worker:

   | Query | 4 threads ms main / cache | peak RSS MB at 4 threads, median and largest, main / cache | RSS 4/1 largest main / cache |
   | --- | ---: | ---: | ---: |
   | q19 | 21.08 / 16.79 | 97 and 100 / 109 and 119 | 1.72 / 2.03 |
   | q21 | 42.41 / 41.67 | 72 and 74 / 82 and 83 | 1.76 / 1.95 |

   CPU per warm q19 run at 4 threads: 79.9 ms main, 48.4 ms with the cache
   (no `onceSeen`), 64.5 ms with 1,024 pages. 1,536 pages: q19 17.66 ms,
   RSS 4/1 2.12. 512 and 768 pages: no gain for q19, q21 45 ms. Ranges taken
   from the shared counter with the cache: q19 RSS 4/1 2.09 to 2.57. Three
   workers only (no fourth on the Lean task pool): q19 RSS 1.90 but q21 46
   to 49 ms. Not kept: the RSS limit of KR 1.2 (at most 2). The copies live in
   the worker heaps; with the allocator work (less fresh memory per worker)
   this is the first change to try again.

### 1h.5 What remains

- q19 (0.53) and d10 (0.68 to 0.70): the per-query page copies of the
  worker caches (q19), fresh memory in the worker heaps (q19, d10: `clear_page_erms`
  under the render buffers and decoded columns) and frees across threads.
  The page cache per pool worker meets 0.4 for q19 (0.39 to 0.44) but its
  peak RSS is 2.02 to 2.03 times the 1-thread RSS. Both need the allocator
  work (less fresh memory per worker heap, frees returned at once), which the
  owner deferred.
- q07 (0.59 to 0.64): the slower worker ranges (1h.1; cause not measured,
  candidate: the worker heap's memory, allocator work), the unequal ranges,
  and the serial ORDER BY keys and rendering (stage 1g).
- d17 (0.3 ms, no scan): the owner decision of
  https://github.com/danbri/factoidal/issues/961 item 2 is still open.
- `open` of the PRB1 file for each block read (`l4_block_pread`): kernel
  path lookups that grow at 4 threads (q07 +0.2 ms CPU per run). A cached
  descriptor was tried in stage 1f for the constants only.

Issue https://github.com/danbri/factoidal/issues/961 stays open.

### 1h.6 Gates

On commit `c55bb893` (the Lean code of `origin/main` `cbd7c72a`; exit codes
read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 (1,994 jobs) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `lean-tail-recursion-audit.py --gate`, `lean-unbuilt-modules.py --gate` | exit 0, exit 0 (941 modules reached) |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), wasm, npm, hub, engine-compare, the LWS, Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | no Lean diff |

The answers of `threads.sh` were also identical with the code of 1h.4 items
2 and 3 in place (run before they were taken out).

## Stage 1i: the allocator (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. Owner, 2026-10-23, verbatim:
"Start now" (the allocator work) and "Remove it" (d17 leaves KR 1.2). Rule
from the same decision: a change to the default allocator settings is shown
to the owner with its measurements before it lands. Branch
`batch3/kr12-alloc`.

### 1i.1 Result

KR 1.2 is not met. With what landed on `main` (2 block ranges per thread on
the counted path, 1i.4) and the default allocator settings, `--repeat 21`:
q07 0.71, q19 0.51, q21 0.39, d10 0.54; peak RSS 4/1 (largest) at most
1.96 in that run, but 2.10 for d10 in the run of 1i.5 (medians 1.88 to 1.96).

- No allocator setting makes a 4-thread run faster beyond the run-to-run
  variation (1i.3).
- `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` (no transparent huge pages) makes peak
  RSS smaller at 4 threads (`--repeat 7`, largest, `main`): d10 51 to 23 MB,
  q07 38 to 20 MB, q19 101 to 82 MB, q21 72 to 55 MB. Peak RSS 4/1 then is 1.1 to 1.7. The 1-thread time
  does not change beyond the variation.
- With that setting, the page cache per pool worker (stage 1h.4 item 3, 2,048
  pages) keeps peak RSS 4/1 below 2 (q19 1.86 to 1.92). q19 at 4 threads:
  17.1 and 16.5 ms against 19.3 and 18.5 ms without the cache. Its 4/1 ratio
  is 0.46 to 0.47: the q19 1-thread time varies between processes (1i.2).
  The setting is a default allocator setting: it is on a branch for the
  owner's decision (1i.5), not on `main`.
- q07 (0.64 at best) and d10 (0.53 at best) do not reach 0.4 with any
  setting or code change of this stage.

### 1i.2 Method

The 1b.6 method with variants interleaved (`.claude-runs/alloc/ab.sh`, not
in the repository): in each round, for each query and thread count, one
process per variant, the variant order turned by one each round; round 1
dropped; median over processes of each process's warm median; peak RSS is
the largest VmHWM of the cell. Olympics generation of stage 1h; DBpedia with
`--verify none`. 12 rounds (11 kept) with `--repeat 7` (2026-10-23 10:10 to
10:13 UTC) and with `--repeat 21` (10:13 to 10:21 UTC). The settings
screen: 6 rounds (5 kept), `--repeat 7`. Raw CSV: `.claude-runs/alloc/`
(`s1.csv` screen, `s3r7.csv`, `s3r21.csv`).

Run-to-run variation: the warm median of a 1-thread process varies by up to
1.5 times between processes of one binary and one setting (d10, 41 runs per
process: 9.1 to 14.6 ms; q19 7 runs: 30 to 52 ms). It is the same with the
process pinned to each of the four vCPUs (`taskset`) and with address
randomisation off (`setarch -R`), so it is the VM, not the code. A 4/1 ratio
of one variant therefore moves by about 0.05 to 0.1 between two runs of the
method; compare 4-thread times, and ratios only when the difference is
larger than that.

### 1i.3 The allocator in this toolchain, and its settings

Lean 4.33.1 (`leanprover/lean4:v4.33.1`). `include/lean/config.h` defines
`LEAN_MIMALLOC`, so `lean.h` allocates small objects with `mi_malloc_small`
(`lean_alloc_small_object`), other objects with `mi_malloc`
(`lean_alloc_object`, `src/runtime/object.cpp`) and frees with `mi_free` /
`mi_free_size`. Lean's own small-object allocator is not in this build (the
`#ifndef LEAN_MIMALLOC` paths use `malloc`, and they are not compiled).
mimalloc is v2.2.3 (`CMakeLists.txt`: `FetchContent`, `GIT_TAG v2.2.3`),
linked statically in `libleanrt.a`, with secure level 0 (`LEAN_MI_SECURE`).
It does not replace `malloc`: the Lean objects and the FFI buffers
(`lean_alloc_sarray` in `ffi/block_pread.c`) use it, the C library's own
calls do not. Each thread has its own mimalloc heap; an object freed by a
thread that did not allocate it goes to the thread-free list of its page and
the owning thread takes it back later (`_mi_free_delayed_block`,
`mi_free_generic_mt` in the stage 1h profiles).

Knobs:

- Compile time: `USE_MIMALLOC`, `LEAN_MI_SECURE`. Both need a rebuilt
  toolchain; not tried.
- Run time: the `MIMALLOC_*` environment variables, read when the process
  starts. Checked with `MIMALLOC_VERBOSE=1`, which prints the version and
  every option. Defaults in this build: `purge_delay` 10 ms, `purge_decommits`
  1, `eager_commit` 1, `eager_commit_delay` 1, `arena_eager_commit` 2,
  `arena_reserve` 1 GiB, `allow_large_os_pages` 2 (mimalloc calls
  `madvise(MADV_HUGEPAGE)` on the memory it maps; this VM has transparent huge
  pages set to `madvise`, so the kernel then gives 2 MB pages and clears each
  on first touch), `abandoned_reclaim_on_free` 0, `target_segments_per_thread`
  0, `generic_collect` 10000.
- In the process: `mi_option_set`, `mi_collect`, `mi_heap_*` are in
  `libleanrt.a` but Lean has no binding; a call needs an FFI function. The
  kernel call `prctl(PR_SET_THP_DISABLE)` has the same effect as
  `allow_large_os_pages=0` here (tested with a preloaded constructor: d10
  peak RSS 19.0 and 22.7 MB at 1 and 4 threads, against 18.6 and 22.8 MB with
  the variable) and also holds on a machine where huge pages are `always`.
- Not a knob here: `LEAN_NUM_THREADS` (the pool threads are
  `Task.Priority.dedicated`).

Screen of the settings (`--repeat 7`, 5 rounds kept; 4-thread ms, and RSS
MB at 4 threads, largest):

| Setting | q07 | q19 | q21 | d10 |
| --- | ---: | ---: | ---: | ---: |
| default | 4.54, 38 | 19.98, 102 | 35.60, 72 | 7.47, 48 |
| `PURGE_DELAY=-1` (never return memory) | 4.28, 38 | 19.56, 104 | 37.52, 79 | 6.86, 51 |
| `PURGE_DELAY=100` | 4.04, 39 | 19.91, 101 | 36.66, 75 | 7.62, 51 |
| `PURGE_DECOMMITS=0` (`MADV_FREE`) | 4.16, 38 | 20.17, 100 | 38.98, 75 | 9.06, 47 |
| `EAGER_COMMIT_DELAY=0` | 4.22, 38 | 19.94, 98 | 36.78, 73 | 7.87, 48 |
| `ALLOW_LARGE_OS_PAGES=0` | 3.95, 20 | 19.94, 84 | 38.60, 55 | 6.47, 22 |

No setting changes the 4-thread time beyond the variation. Only
`ALLOW_LARGE_OS_PAGES=0` changes peak RSS.

The interleaved runs (ms at 1 / 4 threads, 4/1, peak RSS MB at 1 / 4
threads largest and their ratio). `main`: `origin/main` `fc74f2a1`; `cand`:
`main` with 1i.4; `cand+pc`: `cand` with the page cache per pool worker of
stage 1h.4 item 3 at 2,048 pages; `lp0`: `MIMALLOC_ALLOW_LARGE_OS_PAGES=0`;
`pd-1`: `MIMALLOC_PURGE_DELAY=-1`.

`--repeat 21`:

| Variant | q07 | q19 | q21 | d10 |
| --- | --- | --- | --- | --- |
| main | 5.14 / 3.78, 0.74; 26 / 39, 1.47 | 37.19 / 18.19, 0.49; 58 / 105, 1.79 | 97.92 / 38.85, 0.40; 42 / 74, 1.76 | 10.26 / 7.26, 0.71; 26 / 54, 2.05 |
| cand (landed) | 5.09 / 3.63, 0.71; 26 / 38, 1.45 | 36.92 / 18.66, 0.51; 58 / 103, 1.77 | 100.67 / 38.87, 0.39; 42 / 74, 1.75 | 11.80 / 6.32, 0.54; 26 / 52, 1.96 |
| main, lp0 | 5.02 / 3.76, 0.75; 18 / 20, 1.09 | 34.91 / 18.56, 0.53; 52 / 88, 1.69 | 111.43 / 37.56, 0.34; 35 / 60, 1.70 | 10.20 / 7.08, 0.69; 19 / 24, 1.25 |
| cand, lp0 | 5.08 / 3.74, 0.74; 18 / 20, 1.09 | 42.64 / 18.47, 0.43; 52 / 85, 1.63 | 98.77 / 39.19, 0.40; 36 / 57, 1.60 | 10.32 / 6.16, 0.60; 19 / 23, 1.22 |
| cand+pc | 5.13 / 3.29, 0.64; 26 / 39, 1.46 | 35.42 / 15.84, 0.45; 58 / 117, 2.01 | 104.39 / 41.80, 0.40; 42 / 82, 1.94 | 10.16 / 6.55, 0.64; 26 / 54, 2.07 |
| cand+pc, lp0 | 5.44 / 3.45, 0.64; 18 / 20, 1.07 | 35.60 / 16.52, 0.46; 52 / 100, 1.92 | 110.55 / 43.88, 0.40; 36 / 65, 1.81 | 10.26 / 6.12, 0.60; 19 / 24, 1.26 |
| cand+pc, lp0, pd-1 | 5.14 / 3.58, 0.70; 18 / 20, 1.08 | 37.69 / 16.64, 0.44; 52 / 100, 1.92 | 98.00 / 39.72, 0.41; 36 / 66, 1.85 | 11.43 / 6.08, 0.53; 19 / 23, 1.23 |

`--repeat 7`:

| Variant | q07 | q19 | q21 | d10 |
| --- | --- | --- | --- | --- |
| main | 5.11 / 3.91, 0.77; 26 / 38, 1.45 | 37.80 / 20.60, 0.55; 58 / 101, 1.73 | 116.30 / 39.42, 0.34; 42 / 72, 1.71 | 10.77 / 7.13, 0.66; 26 / 51, 1.93 |
| cand (landed) | 5.57 / 3.90, 0.70; 26 / 38, 1.46 | 39.50 / 20.47, 0.52; 58 / 101, 1.73 | 114.93 / 39.79, 0.35; 42 / 74, 1.76 | 10.19 / 6.83, 0.67; 26 / 50, 1.92 |
| main, lp0 | 5.32 / 3.77, 0.71; 18 / 20, 1.13 | 46.67 / 19.98, 0.43; 52 / 82, 1.58 | 98.40 / 40.43, 0.41; 36 / 55, 1.54 | 10.26 / 7.20, 0.70; 18 / 23, 1.23 |
| cand, lp0 | 5.27 / 3.78, 0.72; 18 / 20, 1.12 | 44.60 / 19.25, 0.43; 52 / 83, 1.59 | 107.74 / 38.70, 0.36; 36 / 57, 1.59 | 11.72 / 7.03, 0.60; 18 / 22, 1.20 |
| cand+pc | 5.72 / 3.79, 0.66; 26 / 39, 1.46 | 43.53 / 17.38, 0.40; 58 / 117, 2.00 | 104.80 / 41.73, 0.40; 42 / 82, 1.95 | 10.54 / 6.27, 0.59; 26 / 49, 1.85 |
| cand+pc, lp0 | 5.37 / 3.52, 0.66; 18 / 20, 1.11 | 36.61 / 17.08, 0.47; 52 / 97, 1.86 | 113.75 / 40.74, 0.36; 36 / 62, 1.76 | 10.30 / 6.15, 0.60; 19 / 22, 1.20 |
| cand+pc, lp0, pd-1 | 5.66 / 4.22, 0.75; 18 / 20, 1.11 | 40.16 / 17.34, 0.43; 52 / 97, 1.86 | 103.77 / 39.83, 0.38; 36 / 65, 1.82 | 13.37 / 6.56, 0.49; 18 / 22, 1.19 |

Findings:

- Transparent huge pages cost memory, not time, here: without them each
  thread's heap grows in 4 KB pages, so peak RSS at 4 threads falls by 17 to
  31 MB and the 4-thread times stay within the variation.
- The page cache per pool worker makes q19 at 4 threads 2 to 3 ms faster
  (15.8 to 17.4 ms against 18.2 to 20.6 ms) in every setting. Without huge
  pages its peak RSS 4/1 is 1.86 to 1.92; with them, 2.00 to 2.01.
- Memory never returned (`PURGE_DELAY=-1`) gives no measured gain: the
  pages that the stage 1h profiles show cleared (`clear_page_erms`) are first
  touches of new heap memory, not memory given back and taken again.

### 1i.4 What landed: 2 block ranges per thread on the counted path

`IdQuery.Par.countPerThread` (default 2): `divide?` cuts the selected blocks
of the counted path (GROUP BY with COUNT over one pattern) into
2 × threads ranges, and the pool workers take them from the shared counter
of `parFold`. d10's costly blocks (the 137 of 5,941 in which the predicate
changes) are not spread evenly over 4 equal ranges; with 8 ranges a worker
that ends a cheap range takes another. DBpedia d10 at 4 threads, 21 runs per
process, 5 processes per value (`.claude-runs/alloc/cr.csv`):

| Ranges per thread | 1 | 2 | 4 | 8 | 16 | 32 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| d10 4 threads ms | 7.65 | 6.18 | 6.15 | 6.51 | 6.63 | 7.27 |

In the interleaved runs: 7.26 to 6.32 ms (`--repeat 21`) and 7.13 to 6.83 ms
(`--repeat 7`); peak RSS unchanged.

Proved: no new theorem is needed. `ParallelScanTheorems.parallel_acc_eq` is
stated for every chunk width `c` of `ParallelScan.chunksOf`, so it covers the
smaller ranges. Tested: `tests/sbm11/threads.sh` and the census at 4 threads
(1i.6).

### 1i.5 For the owner: one default allocator setting

The setting: transparent huge pages off in the `l4sbm11` process, either
`MIMALLOC_ALLOW_LARGE_OS_PAGES=0` in its environment or
`prctl(PR_SET_THP_DISABLE, 1)` at the start of its `main` (same measured
effect; the `prctl` form also holds where the kernel's huge-page mode is
`always`). Branch `batch3/kr12-thp` has the `prctl` form and the page cache
per pool worker (2,048 pages) on top of `main`.

What it gives (`--repeat 21`, 1i.3): peak RSS at 4 threads 17 to 31 MB
smaller for the 4 queries; with the page cache, q19 at 4 threads 18.66 to
16.52 ms with peak RSS 4/1 1.92 (2.01 with huge pages). What it does not
give: KR 1.2. q19 4/1 stays 0.46 to 0.47, q07 0.64, d10 0.60.

The branch itself (`496d790a`: `prctl` called first in `l4sbm11`'s `main`,
`L4_THP=on` keeps huge pages), against `main` (`15256876`), interleaved, 10
rounds (9 kept), `--repeat 21`; 4-thread ms, 4/1, peak RSS 4/1 (largest):

| Query | `main` | branch | branch with `L4_THP=on` |
| --- | --- | --- | --- |
| q07 | 3.50, 0.56, 1.47 | 3.32, 0.63, 1.06 | 3.64, 0.74, 1.46 |
| q19 | 18.24, 0.53, 1.80 | 15.98, 0.47, 1.85 | 16.57, 0.48, 2.04 |
| q21 | 34.80, 0.36, 1.78 | 39.33, 0.42, 1.74 | 38.41, 0.40, 2.05 |
| d10 | 6.10, 0.58, 2.10 | 6.31, 0.64, 1.19 | 5.74, 0.58, 2.07 |

Called in `main`, `prctl` takes away less memory than the variable (q07 25
against 20 MB, d10 28 against 22 MB at 4 threads): the runtime has touched
some memory before `main` runs. The d10 peak RSS 4/1 of `main` is at the
limit with huge pages (2.05 to 2.10 as the largest value in two runs; the
medians are 1.88 to 1.96): the limit of 2 holds for d10 only as a median
until a setting of this kind lands. Raw CSV: `.claude-runs/alloc/s4.csv`.

### 1i.6 Gates

On commit `15256876` (the Lean code of this landing; exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 (1,994 jobs) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `lean-tail-recursion-audit.py --gate`, `lean-unbuilt-modules.py --gate` | exit 0, exit 0 (941 modules reached) |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), wasm, npm, hub, engine-compare, the LWS, Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

### 1i.7 What remains

- q07 (0.71): the serial phases are slower at 4 threads than at 1 (ORDER BY
  keys 0.90 against 0.68 ms, rendering 0.34 against 0.26 ms, constants 0.08
  against 0.03 ms; `SBM11_PHASES=1`, 61 runs), and the two scans with
  candidates reach 1.9 times their 1-thread speed (1.67 against 3.13 ms).
  0.4 needs about 2.0 ms at 4 threads; the serial phases alone take 1.6 ms.
- d10 (0.54): rendering of the groups is serial (1.07 ms at 4 threads), and
  the 4-thread CPU time is 1.6 times the 1-thread CPU time (stage 1h.3).
- q19 (0.51): the page copies of the per-query worker caches; the page cache
  per pool worker removes part of them and needs the setting of 1i.5 to stay
  within the RSS limit.
- The method: the 1-thread time varies by up to 1.5 times between processes
  on this VM (1i.2). A 4/1 target of 0.4 is near the variation for q19 and
  q21.

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1j: huge pages off on `main`, and the work after the scans (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. Owner, 2026-10-23, answer
"Land it" to: "Land branch batch3/kr12-thp (prctl THP off at start of main,
L4_THP=on keeps huge pages, plus the 2,048-page worker cache) on main?".

### 1j.1 Result

KR 1.2 is met for q21 only. Peak RSS 4/1 is at most 1.82 for the four
queries. Final interleaved run, binary of `main` after part A (`15da4cc4`)
against this stage (`8b6f63b0`), 16 rounds (15 kept), `--repeat 21`,
2026-10-23 14:55 to 14:58 UTC:

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | target met |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 5.25 / 3.69 | 0.70 | 5.49 / 3.63 | 0.66 | 1.06 / 1.13 | no |
| q19 | 37.16 / 15.93 | 0.43 | 38.93 / 16.61 | 0.43 | 1.84 / 1.82 | no |
| q21 | 100.98 / 40.80 | 0.40 | 100.34 / 38.63 | 0.38 | 1.75 / 1.69 | yes |
| d10 | 10.54 / 6.38 | 0.61 | 10.48 / 4.71 | 0.45 | 1.22 / 1.25 | no |

A run of 11 rounds just before (10 kept) gave 4/1 of q07 0.63, q19 0.35,
q21 0.36, d10 0.48 for this stage, with 1-thread times of `main` up to 1.3
times those of this run (1i.2). Raw CSV: `.claude-runs/kr12j/F.csv`,
`F2.csv` (not in the repository).

A version of this stage with two more changes reached q19 0.38, q21 0.35 and
d10 0.41 to 0.44 (variant `E`, 1j.4 items 3 and 4), but it read some
dictionary pages and blocks twice, so the counters of
`tests/sbm11/threads.sh` differed from one thread (1j.5). Those two changes
are off or repaired in what landed; q19 at 4 threads, interleaved, 12
rounds: `E` 14.02 ms, landed 15.41 ms, landed with
`SBM11_STREAM_JOBS=4` 14.57 ms.

### 1j.2 Part A: branch `batch3/kr12-thp` on `main`

Merge `c2ee8e35` (no conflict) and the CLAUDE.md decision `15da4cc4`.
The 1b.6 method, one binary, 10 rounds (9 kept), `--repeat 21`:

| Query | 1 / 4 threads ms | 4/1 | peak RSS MB 1 thread / 4 threads (largest) | RSS 4/1 |
| --- | ---: | ---: | ---: | ---: |
| q07 | 5.24 / 3.74 | 0.71 | 23 / 25 | 1.06 |
| q19 | 34.96 / 15.81 | 0.45 | 57 / 105 | 1.86 |
| q21 | 99.70 / 38.42 | 0.39 | 40 / 72 | 1.79 |
| d10 | 10.65 / 5.70 | 0.54 | 24 / 28 | 1.18 |

Gates on `15da4cc4`: `lake build`, `tests/sbm11/run.sh`, `threads.sh`,
`SBM11_THREADS=4 census.sh`, the unbuilt-modules and tail-recursion gates
exit 0; `tools/land-gates.sh` exit 1 twice, each
time on one row of `tests/lws/scaling.mjs` ("storage files: peak RSS of a
start grows <= 16 MiB from s to 4s", growth 40.6 MiB). The merge changes
only `l4sbm11` harness files, which that test does not run; alone the test
failed once in four runs. Issue:
https://github.com/danbri/factoidal/issues/962.

### 1j.3 Measurements before the changes

`SBM11_PHASES=1`, 61 runs, binary of part A:

| Phase (ms) | q07 1 / 4 threads | d10 1 / 4 threads |
| --- | ---: | ---: |
| constants | 0.033 / 0.076 | 0.028 / 0.026 |
| scans and joins | 3.98 / 2.28 | 8.86 / 4.68 (the counted scan and the group table) |
| finish (ORDER BY keys) | 0.672 / 0.690 | 0.003 / 0.003 |
| render | 0.263 / 0.264 | 1.115 / 1.118 |

- d10 render: 665 groups, 1.7 microseconds per row. The dwarf profile puts
  most of it under `appendIdJsonM` for the count column: an inline integer
  went through `termOf`, `jsonOfTerm` and `Json.toString`
  (`escapeStringFast`, `lean_string_push`, `toStringFieldsAcc`).
- q07 finish: `orderReadOfM` 0.33 ms (`termOf` of 291 labels: list
  conversions and UTF-8 checks of the key decoder), `sortReads` 0.1 ms.
- q19 at 4 threads (`tools/perf-cost-split.py`, 60 warm runs): 47.8 ms of
  CPU per run against 39.2 at 1 thread (2.7 ms of it pool polling). The
  extra CPU is no longer the main cost (stage 1h: 79.9 against 29.1). The
  10 ranges of one block each went to 4 workers, and the fourth worker was a
  task of the Lean pool with a new page cache for each fold.
- d10 counted scan at 4 threads (`SBM11_RANGE_TRACE=1`, new: each job's
  start and duration): the 8 jobs keep the 4 workers busy 2.7 to 3.0 ms each
  (balanced), the fold takes 3.3 to 3.9 ms; the jobs together take 10.7 ms
  of CPU against about 8.2 ms for the same scan on one thread.

### 1j.4 What changed

1. **Inline literals printed from the id** (`IdQuery.appendIdJsonM`). An
   inline integer or boolean id gives its literal through `ofInlineCode?`
   (the term `termOf` gives) and the key printer's literal form
   (`Qlvr.Query.litBytes`). Tested, not proved: `tests/sbm11/run.sh`
   compares the output with `--reference-render` byte for byte. d10 render
   at 1 thread: 1.115 to 0.54 ms.
2. **The finished table rendered on the pool** (`IdQuery.renderJobs`,
   `Par.renderRows`, `SBM11_RENDER_ROWS`): at most two ranges per thread of
   at least 160 rows each, rendered by `renderRowsEndsM` and written in range
   order by `emitPieceM` (the text of `renderRowsM`). d10 at 4 threads,
   render phase: 0.55 to 0.71 ms on one thread, 0.43 to 0.49 ms divided (3
   processes each). A worker renders a row in about 1.2 microseconds against
   0.8 on the calling thread (dictionary pages from the shared map). With
   128 rows per range q07 (313 rows, 2 ranges) was slower (render 0.48
   against 0.25 ms), so 160 keeps q07 on the calling thread:

   | `SBM11_RENDER_ROWS` | d10 4 threads ms | q07 4 threads ms |
   | --- | ---: | ---: |
   | 0 (calling thread) | 5.74 | 3.81 |
   | 128 | 5.13 | 4.07 |
   | 160 | 4.65 | 3.43 |
   | 320 | 5.36 | 3.62 |

   (9 rounds, 8 kept, `--repeat 41`; q07 at 0 and 160 runs the same code,
   so 0.4 ms is the variation of this run.)
3. **Windows of a block range, off by default** (`IdQuery.StreamJob`,
   `streamJobs`, `Par.streamPerThread`, `SBM11_STREAM_JOBS=4` turns it on):
   with fewer than 4 jobs per thread, each range of the streamed path is cut
   into windows of about equal estimated rows; each job scans the range and
   renders its window; one job per range gives the scan statistics. Proved:
   `ParallelMergeTheorems.windows_concat` and `windows_range` (the windows'
   rows in order are the range's rows). Tested, not proved: that
   `streamPartM` keeps the window and that `streamJobs` chains the windows
   from 0 to `cap`. q19 at 4 threads, interleaved: 14.04 ms with windows,
   14.91 ms without; q21 38.73 against 37.63 ms (variation). Not on by
   default: each job reads the blocks of its range again, so the block bytes
   of `tests/sbm11/threads.sh` are not those of one thread (q19 at 4 threads:
   159,754 against 79,877), for a gain near the variation.
4. **The calling thread is the last worker of `parFold`** (`parentAt`;
   `SBM11_PARENT_TASK=1` gives the former task of the Lean pool). It runs
   its jobs between the folds of the results, with the session's own store
   and page cache, and takes a range only when its permit is given, so it
   never waits for itself. With a pool, the calling thread loads dictionary
   pages through `taskPages` as the workers do (`Session.pageKeys`), so no
   page is read twice (the range bytes of `threads.sh` equal those of one
   thread). Interleaved, 9 rounds (8 kept), `--repeat 21`, before that page
   change and with windows on:

   | Query | Lean pool task: 4 threads ms, RSS 4/1 | calling thread: 4 threads ms, RSS 4/1 |
   | --- | ---: | ---: |
   | q19 | 16.41, 1.77 | 13.11, 1.61 |
   | q21 | 40.12, 1.74 | 37.58, 1.57 |
   | d10 | 4.58, 1.23 | 4.54, 1.23 |

5. Phase marks `divide`, `countfold`, `groups` on the counted path, and
   `SBM11_RANGE_TRACE` and `SBM11_POOL_SIZE` (experiments only).

### 1j.5 A defect found and repaired before the landing

The first version of item 4 asked whether range `k` was ready with
`IO.Ref.get` on its result slot. For a ref that another thread writes,
`lean_st_ref_get` takes the value out and puts it back with two atomic
exchanges, and a write between them is lost (two `xchg` in its disassembly,
Lean 4.33.1). About one fold in 4,000 lost a range's result: the run failed
with "block range 1: its worker stopped", and the process hung at exit,
because the error left `main` with the pool running and the runtime waits
for its dedicated threads. Found by the 1b.6 method, which logged a
`FAIL Csj0 d10-group-predicates 4`; `gdb` of a hung process showed the main
thread in `lean_finalize_task_manager` and the three pool workers in
`Cell.take?`. Repairs: the ready test reads the range's promise
(`IO.hasFinished`); a failed run stops the pool before the error leaves
`main`. After the repair: 600 processes of d10 at 4 threads (21 runs each),
no failure; before it, 4 in about 400. Rule added to skill
`lean4-performance` (section "Values that two threads can reach").

`tests/sbm11/threads.sh` found two more differences before the landing,
both in the counters, not the answers: the windows read blocks twice (item
3, now off by default), and the calling thread read dictionary pages from
the file that a worker had read too (DBpedia d05, d08 and d11: range bytes
6,470,002 against 6,456,166 at one thread; repaired in item 4).

### 1j.6 Tried and not kept

- A pool of 4 workers for 4 threads (`SBM11_POOL_SIZE=4`, the calling
  thread folding only): q19 14.40 ms, but d10 7.28 and q07 5.14 ms against
  5.05 and 4.08 (a polling fourth worker takes a vCPU from the calling
  thread's serial phases).

### 1j.7 Gates

On commit `8b6f63b0` (the Lean code of this landing; exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 (1,994 jobs) |
| `tests/sbm11/threads.sh` | exit 0: gate 140 and gate2 140 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `tests/sbm11/run.sh` | exit 0: 3,131 pass, 0 fail, 28 expected-fail (out of 3,159) |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 executed, 605 matched the reference engine, 0 differed; 4 refused at query |
| `lean-tail-recursion-audit.py --gate`, `lean-unbuilt-modules.py --gate` | exit 0 (one allow-list line: `ParallelMergeTheorems.winsOf`, specification only), exit 0 (941 modules reached) |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), wasm, npm, hub, engine-compare, the LWS (scaling 21 pass, 0 fail, out of 21), Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |
| d10 at 4 threads, 600 processes of 21 runs (binary with the 1j.5 repair, before the page change of 1j.4 item 4); q19 at 4 threads, 250 processes of 21 runs (`8b6f63b0`) | no failure, no hang |

After `origin/main` moved by 53 commits (`200c4e64`), the merge `48be0759`
(no conflict): `lake build` exit 0 (2,042 jobs); `threads.sh` exit 0 (gate
347 and gate2 347 identical, olympics 21, 2 and 2, DBpedia 19, record equal
76, different 0); census at 4 threads exit 0 (605 matched); unbuilt-modules
exit 0 (985 modules reached); `tools/land-gates.sh` exit 1 only on its tail-recursion step (native-smoke 377 pass, 0 fail, 4 xfail, out of 381; cli-smoke 151 pass, 0 fail, 5 xfail, out of 156; npm, hub, engine-compare, the LWS (scaling 21 pass, 0 fail, out of 21), Solid and authorization suites, host-purity-lint 40 pass, 0 fail, out of 40).
`tests/sbm11/run.sh` exit 1 (3,346 pass, 5 fail, 28 expected-fail, out of
3,379) and the tail-recursion gate exit 1 (15 declarations): the same 5
failures and the same 15 declarations on a build of `200c4e64` alone, which
this stage does not change; issue
https://github.com/danbri/factoidal/issues/964.

### 1j.8 What remains

- q07 (0.66): the serial work after the scans at 4 threads is about 1.6 ms
  (constants 0.08, ORDER BY keys 0.69, rendering 0.26, joins 0.37,
  first scan 0.18); 0.4 needs about 2.0 ms in all. The ORDER BY keys spend
  0.33 ms in `termOf` of the labels (key decoding to a `Term`: list
  conversions and UTF-8 checks) and 0.1 ms in the sort; rendering 313 rows
  on the pool was slower than on the calling thread (1j.4 item 2). Next
  steps: order readings from the key bytes for string and language-tagged
  keys (with a proof against `orderValue`), and the 15 to 25 percent slower
  worker ranges of stage 1h.
- q19 (0.43): 10 ranges of one block on 4 workers (3, 3, 2 and 2 ranges),
  and the dictionary pages that the calling thread now takes through
  `taskPages` (peak RSS at 4 threads 103 MB against 91 MB with its own cache
  only). The windows of item 3 give about 0.8 ms but read each block twice;
  turning them on needs a decision on the block-bytes rule of
  `threads.sh`.
- d10 (0.45): the counted scan's jobs take 1.3 times the CPU of one thread
  (10.7 against 8.2 ms; stage 1h: compute and frees across threads), plus
  serial work of about 0.9 ms at 4 threads (`divide` 0.2 to 0.3 ms reading
  5,941 PRM1 entries, the group table 0.21 ms, rendering on the pool 0.42 to
  0.47 ms with workers 1.5 times slower per row than the calling thread).
- The 1-thread time of one process still varies by up to 1.5 times on this
  VM (1i.2): two runs of the method on one pair of binaries gave q19 0.35 and
  0.43.

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1k: the calling thread's work on the counted path, and the label keys (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. No allocator setting changed;
the block-bytes rule of `tests/sbm11/threads.sh` and `SBM11_STREAM_JOBS` are
not changed (owner question pending).

### 1k.1 Result

KR 1.2 is met for d10, q19 and q21; it is not met for q07. Final interleaved
run, binary of `main` `67c29a44` against this stage (`91f3fa3c`), 16 rounds
(15 kept), `--repeat 21`, 2026-10-23 19:29 to 19:31 UTC, after all gates had
ended (raw CSV `.claude-runs/kr12k/final.csv`, not in the repository):

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | target met |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 4.76 / 2.86 | 0.60 | 4.75 / 2.87 | 0.60 | 1.11 / 1.14 | no |
| q19 | 34.33 / 11.17 | 0.33 | 34.26 / 11.94 | 0.35 | 1.82 / 1.81 | yes |
| q21 | 91.08 / 31.03 | 0.34 | 92.40 / 31.32 | 0.34 | 1.67 / 1.68 | yes |
| d10 | 9.04 / 4.37 | 0.48 | 9.05 / 3.20 | 0.35 | 1.18 / 1.14 | yes |

d10 at 4 threads: 15 of 15 processes of this stage at or below 4.27 ms, 14
of 15 of `main` at or above 3.55 ms. q19 4-thread times of single processes
range from 9.6 to 16.2 ms for both binaries (1i.2); its difference here is
inside that range (a separate run of 13 rounds gave 11.16 for this stage and
12.11 for `main`). The 1-thread times did not get slower.

### 1k.2 Measurements before the changes

`tools/perf-cost-split.py` (stage 1h method), DBpedia d10, `--repeat 61`
against `--repeat 1`, 1 against 4 threads, binary of `main`: CPU per warm
run 8.76 ms at 1 thread, 15.07 ms at 4; of the difference, pool polling
3.60 ms, compute 1.23 ms, atomic reference counts 0.95 ms (`cutCol`,
`blockChunk`, `frameSpan`, `frameStarts`, `keyRange`: the shared PRM1
entries). The calling thread, per run (profile of that thread at 4,999 Hz):
`divide` 0.2 to 0.25 ms in `List.range`, `chunksOf` (`take`, `drop`,
`length`) and `selRows`; about 0.25 ms of `lean_dec_ref_cold` after the fold
(the position lists, MT because the jobs held them, freed one cell at a time
with atomic operations); `Groups.merge` and `groupTable` hashing every key
two or three times. `SBM11_RANGE_TRACE=1`: 8 jobs of 0.8 to 1.7 ms, 9.6 to
9.8 ms of CPU together against 7.3 to 8.4 ms for the scan on one thread.

Olympics q07, `finish` (ORDER BY keys) 0.65 to 0.69 ms at 1 and 4 threads:
`orderReadOfM` 64 percent of it, nearly all `Session.termOf` of 291
language-tagged labels; in `termOf`, `decodeLang?` on the list of the key
(UTF-8 checks over lists 27 percent, the list of the key 13 percent,
`splitLast` 9 percent, `tagAdmitted` 8 percent) and the dictionary page
access 27 percent.

### 1k.3 What changed

1. **Ranges as bounds** (`ParallelScan.rangeChunks`, `rangeBounds`,
   `boundsList`; `divide?`, `scanTableParM`, `scanSipTableParM`). The ranges
   of `List.range n` are built from `List.range'` segments, and a job gets
   `(lo, hi)` and makes its own list. Proved: `rangeChunks_eq`
   (`rangeChunks c n = chunksOf c (List.range n)`) and `rangeBounds_map`,
   so `parallel_acc_eq` and the merge theorems still describe the ranges.
   d10 at 4 threads: `divide` 0.19-0.26 to 0.03 ms; the interval after the
   fold (`groups` mark) 0.10-0.13 to 0.002 ms.
2. **Groups with a count array** (`IdQuery.Groups`: `index`, `keys`,
   `cnts`; `countOf`): an addition to a known key hashes it once; `merge`
   and `groupTable` read the counts from the array. Tested
   (`Harness/ScanFoldTest.lean`, `threads.sh`, census), as the former map was.
3. **Groups returned as numbers** (`FlatGroups`, `Groups.toFlat`,
   `mergeFlat`): a job returns the key words and the counts as two `Array
   Nat`; the calling thread adds them. Proved: `mergeFlat_toFlat` (equal to
   `Groups.merge` for keys of `w` words with a count each). d10 at 4
   threads, group table: 0.20-0.23 to 0.06-0.07 ms (1 thread: 0.13-0.15 to
   0.05-0.08 ms with item 4).
4. **Word count ids** (`countId` as `countIdBase + n.toUInt64`,
   `countId_eq` against the former `Nat` form `countIdSpec`; `countLimit`
   `@[noinline]`). The `Nat` form built a number above `2 ^ 63` and read
   `2 ^ 55` from decimal text (`lean_cstr_to_nat`) for every group.
5. **Borrowed PRM1 entries** (`(b : @& BlockMeta)` in the 21 per-block
   functions of the scan): atomic reference counts on d10 at 4 threads 1.07
   to 0.52 ms CPU per run.
6. **Language-tagged literal keys decoded from the byte range**
   (`TermKeyFast.decodeLangSlice`, `lastZeroGo`): the last `0x00` is found in
   the array and the two parts go to `String.fromUTF8?`. Proved:
   `lastZeroGo_spec`, `decodeLangSlice_eq`; `decodeKeySlice?_eq` holds for
   every key. q07 `finish`: 0.65 to 0.37-0.44 ms at 1 thread, 0.65 to 0.50
   ms at 4 threads.

Phases, `SBM11_PHASES=1`, 61 runs per process, 2 processes per cell (ms):

| Phase | d10 `main` 1 / 4 threads | d10 this stage 1 / 4 threads | q07 `main` 1 / 4 | q07 this stage 1 / 4 |
| --- | ---: | ---: | ---: | ---: |
| divide | - / 0.19-0.20 | - / 0.03 | | |
| count fold (4 threads) or scan (1 thread) | 7.3-8.4 / 2.80-2.91 | 6.8-10.4 / 2.59-2.74 | | |
| after the fold (`groups` mark) | - / 0.11 | - / 0.002 | | |
| group table (`bgp+filters` mark) | 0.13-0.15 / 0.20-0.22 | 0.05-0.08 / 0.06-0.07 | | |
| finish (ORDER BY keys) | | | 0.65 / 0.64-0.65 | 0.37-0.44 / 0.50-0.51 |
| render | 0.47-0.52 / 0.27-0.30 | 0.46-0.70 / 0.27-0.30 | 0.25 / 0.25-0.26 | 0.20-0.24 / 0.28-0.30 |

### 1k.4 Tried and not kept

- Ranges of equal estimated work on the counted path (`chunksByWeight`, a
  block whose output columns are constant over it weighing 1, another 1 per
  16 rows): d10 at 4 threads 5.26 ms against 4.10 ms with ranges of equal
  block counts (9 rounds). The trace showed balanced jobs; the loss was not
  explained and the code was removed.
- A copy of the PRM1 entries per job on the counted path (`rangeMetas`, as
  the BGP scans do): atomic counts 0.31 ms CPU lower, allocator 0.62 ms
  higher, no change in wall time. Item 5 removed the counts without the copy.
- A shorter poll before a pool worker blocks (`SBM11_SPIN_NS` 100,000 and
  20,000 against 1,000,000): no change in the serial phases larger than the
  variation between processes.

### 1k.5 Gates

On commit `91f3fa3c` (the Lean code of this stage; exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 3,354 pass, 0 fail, 28 expected-fail (out of 3,382) |
| `tests/sbm11/threads.sh` | exit 0: gate 347 and gate2 347 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 matched the reference engine |
| `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, `lean-csimp-reach.py --gate` | exit 0 (985 modules reached), exit 0, exit 0 |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), the LWS (scaling 21 pass, 0 fail, out of 21), Solid and authorization suites, host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

### 1k.6 What remains

- q07 (0.60): at 4 threads about 1.4 ms is on the calling thread after or
  between the scans: ORDER BY keys 0.50 ms (of which dictionary page access
  for 291 labels and the sort of their readings about 0.15 ms each; at 4
  threads the labels are read through the shared page map, 0.07 to 0.13 ms
  slower than at 1 thread), rendering 0.28 ms, joins about 0.3 ms, constants
  0.06 to 0.08 ms (0.03 ms at 1 thread). The two scans with candidates reach
  2.1 and 1.8 times their 1-thread speed. 0.40 needs about 1.9 ms at 4
  threads in all; the serial work alone at its 1-thread speed is about 1.2
  ms, so the target needs the ORDER BY keys or the rendering on the pool, or
  ORDER BY on the key bytes. Key byte order is the SPARQL order for
  `rdf:langString` labels only when no lexical form holds `0x00` (the key is
  lexical form, `0x00`, tag) and when UTF-8 byte order is the code point
  order of `strCompare`; neither is proved yet.
- d10 (0.35): the 8 jobs of the count fold take 1.2 to 1.3 times the CPU of
  the scan on one thread; the time after the fold is now about 0.4 ms
  (group table 0.06 ms, rendering 0.27 to 0.30 ms on the pool).
- The 1-thread time of one process still varies by up to 1.5 times on this
  VM (1i.2); d10 single processes at 1 thread: 7.7 to 13.9 ms.

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1l: ORDER BY on dictionary keys (2026-10-23)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. No allocator setting changed;
the block-bytes rule of `tests/sbm11/threads.sh` and `SBM11_STREAM_JOBS` are
not changed.

### 1l.1 Result

KR 1.2 is met for d10, q19 and q21; it is not met for q07 (0.53). Final
interleaved run, binary of `main` `e4edbc2e` against this stage (`39543aa6`),
16 rounds (15 kept), `--repeat 21`, 2026-10-23 21:44 to 21:47 UTC, after all
gates had ended (raw CSV `.claude-runs/kr12l/final.csv`, not in the
repository):

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | target met |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 4.68 / 2.74 | 0.58 | 4.34 / 2.31 | 0.53 | 1.14 / 1.13 | no |
| q19 | 33.05 / 11.35 | 0.34 | 34.38 / 11.68 | 0.34 | 1.81 / 1.81 | yes |
| q21 | 89.64 / 32.33 | 0.36 | 93.36 / 28.48 | 0.31 | 1.67 / 1.68 | yes |
| d10 | 9.30 / 3.30 | 0.36 | 8.98 / 3.15 | 0.35 | 1.16 / 1.16 | yes |

The change runs only for ORDER BY; q19, q21 and d10 have none, so their
differences are the variation between processes of this VM (1i.2; q21 at 1
thread 89.6 against 93.4 ms runs the same code). q07 is faster at 1 thread
too (4.68 to 4.34 ms), so the ratio moves less than the 4-thread time.

### 1l.2 Measurements before the change

`SBM11_PHASES=1`, 61 runs, binary of `main`: q07 `finish` (ORDER BY keys)
0.459 ms at 1 thread and 0.515 ms at 4 threads (291 distinct labels: decode
to `Term`, `OrderRead.of`, comparison sort). Other phases at 4 threads:
constants 0.07, first scan 0.15, scan0 0.15, join0 0.19, scan2 0.68, scan3
0.57, joins 0.10, render 0.28 ms.

### 1l.3 What changed

`IdQuery.orderKeysByKeysM?`: when every id of an ORDER BY column is unbound,
a blank node or an IRI (tags 1 and 2), or a dictionary literal (tag 3) whose
key is in group 3 (`rdf:langString`, exactly one `0x00` in the key body, so
no `0x00` in the lexical form) or group 4 (`xsd:string`) of
`OrderKey.keyGroup?`, the sort key of a row is 0 (unbound), the id (groups 1
to 3) or the id plus `2^60` (group 4). The key bytes are read in place
(`Store.keySlice`, `OrderKey.keyGroupSlice?`, a loop); no term is decoded
and the sort is on `UInt64`. Any other id gives `none` and the former path.
q07 `finish`: 0.46 to 0.18 ms at 1 thread, 0.52 to 0.21 ms at 4 threads.

Proved (`Storage/Sbm11/OrderKeyTheorems.lean`, axioms `propext`,
`Classical.choice`, `Quot.sound`):

- `char_cmp` (from 16 lemmas `cmpIJ`, one per pair of UTF-8 lengths):
  unsigned byte order of `String.utf8EncodeChar a ++ s` and
  `String.utf8EncodeChar b ++ t` is the code point order of `a` and `b`, and
  for `a = b` the order of `s` and `t`.
- `bytes_str`: `bytesCmp (bytesOfString a) (bytesOfString b) = strCompare a b`.
- `bytes_sep`: with no `0x00` in `a` and `b`, the byte order of `a 0x00 X`
  and `b 0x00 Y` is `strCompare a b`, then the order of `X` and `Y`.
- `orderValue_keyOrder`: for terms `t₁`, `t₂` with `termKey? tᵢ = some kᵢ`
  and `keyGroup? kᵢ = some gᵢ`, `sparqlOrderValue (orderValue t₁)
  (orderValue t₂)` is `-1` if `g₁ < g₂`, `1` if `g₂ < g₁`, else
  `bytesCmp k₁ k₂`. No premise states an order. `orderValue_error_term`,
  `orderValue_term_error`: an unbound variable comes first.
- `keyGroupSlice?_eq`: the in-place check is `keyGroup?` of the key bytes.

Not proved here: that the ids of one tag are in key byte order. That is the
dictionary invariant (`DictTheorems.decodeDict_sorted`, ranks of the sorted
dictionary) that the IRI and blank-node path `orderKeysByIds?` already uses.
Tested: `tests/sbm11/run.sh` part (z), `tests/sbm11/orderkeys/`: 8 queries at
1 and 4 threads compared with `l4factoidal` row by row in order
(`compare_answers.py ordered`): unbound values after OPTIONAL (ASC and DESC),
a blank node, IRIs, `xsd:string` and `rdf:langString` literals with 1- to
4-byte UTF-8 characters, empty lexical forms, tags that differ only after a
prefix, LIMIT, a lexical form with U+0000 and typed literals (the last two
take the former path). 16 pass, 0 fail (out of 16).

### 1l.4 Tried and not kept

- The finished table rendered on the pool for q07 (313 rows):
  `SBM11_RENDER_ROWS` 0, 40, 80 and 160 at 4 threads gave render 0.26, 0.26,
  0.37 and 0.26 ms. Measurement does not support a lower threshold.

### 1l.5 Gates

On commit `39543aa6` (exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 3,379 pass, 0 fail, 28 expected-fail (out of 3,407); part (z) 16 pass, 0 fail (out of 16) |
| `tests/sbm11/threads.sh` | exit 0: olympics and DBpedia answers identical at 1, 2, 4, 8 threads; DBpedia against the three-engine record: equal 76, different 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 matched the reference engine |
| `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, `lean-csimp-reach.py --gate` | exit 0 (998 modules reached), exit 0, exit 0 |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), LWS scaling 21 pass, 0 fail (out of 21), host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none (`decide +kernel` for two datatype IRI tests) |

After `origin/main` moved (`f0a7e5c3`), the merge (no conflict): `lake
build` exit 0; `tests/sbm11/run.sh` exit 0 (3,379 pass, 0 fail, 28
expected-fail, out of 3,407; part (z) 16 pass, 0 fail, out of 16);
`threads.sh` exit 0; census at 4 threads exit 0 (605 matched);
unbuilt-modules exit 0 (1,005 modules reached); csimp-reach exit 0;
tail-recursion exit 1 and `tools/land-gates.sh` exit 1 on that step only
(native-smoke 377 pass, 0 fail, 4 xfail, out of 381; cli-smoke 151 pass, 0
fail, 5 xfail, out of 156): three declarations that `f0a7e5c3` added
(`Column.ndigits`, `PackStream.Cut.run`, `PackStream.Pages.run`), not in this
stage's files; issue https://github.com/danbri/factoidal/issues/978.

### 1l.6 What remains

- q07 (0.53): at 4 threads about 2.3 ms; the target needs about 1.75 ms.
  Phases at 4 threads: constants 0.04, first scan 0.13, scan0 0.13, join0
  0.21, scan2 0.69, scan3 0.52, joins 0.10, ORDER BY keys 0.21, render 0.27
  ms. The two scans with candidates reach 2.5 and 2.4 times their 1-thread
  speed; the serial work (first scans, join0, ORDER BY keys, render) is about
  0.9 ms. ORDER BY keys still read 313 dictionary keys (page access); render
  on the pool is slower for 313 rows (1l.4).
- The 1-thread time of one process still varies by up to 1.5 times on this
  VM (1i.2).

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1m: q07, where the 4-thread time goes after stage 1l (2026-10-24)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. No allocator setting changed;
the block-bytes rule of `tests/sbm11/threads.sh` and `SBM11_STREAM_JOBS` are
not changed. Branch `batch3/kr12-q07c`.

### 1m.1 Result

KR 1.2 is met for d10, q19 and q21; it is not met for q07 (0.53). One change
landed: the block ranges of a scan with candidates are cut at equal estimated
work (1m.3). Its effect on q07 at 4 threads is 2.33 to 2.24 ms, which is
inside the variation between processes. Final interleaved run, binary of
`main` `7909fa00` against this stage (`6d7ca45c`), 16 rounds (15 kept),
`--repeat 21`, 2026-10-24 00:45 to 00:49 UTC, after all gates had ended (raw
CSV `.claude-runs/kr12m/final.csv`, not in the repository):

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | target met |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 4.42 / 2.33 | 0.53 | 4.24 / 2.24 | 0.53 | 1.14 / 1.14 | no |
| q19 | 32.21 / 10.42 | 0.32 | 32.95 / 10.43 | 0.32 | 1.83 / 1.83 | yes |
| q21 | 87.80 / 25.88 | 0.29 | 87.50 / 26.70 | 0.31 | 1.70 / 1.69 | yes |
| d10 | 8.79 / 3.08 | 0.35 | 8.61 / 2.95 | 0.34 | 1.15 / 1.15 | yes |

The change runs only in scans with candidates; q19, q21 and d10 have none at
the scale measured, so their differences are the variation between
processes (q21 at 4 threads: 25.0 to 34.9 ms for single processes of either
binary).

### 1m.2 Measurements

`SBM11_PHASES=1`, 101 runs per process, 5 to 10 processes per cell, binary of
`main`, q07 at 1 and at 4 threads (ms, median over processes):

| Phase | 1 thread | 4 threads |
| --- | ---: | ---: |
| constants | 0.03 | 0.04 |
| first scan (2 blocks, 8,192 rows) | 0.16 | 0.12 |
| scan0 (4 blocks) | 0.20 | 0.12 |
| join0 (merge join, 6,248 and 13,369 rows) | 0.38 | 0.18 |
| scan2 (with candidates: 312, 66 blocks, 50 read) | 1.65 | 0.62 to 0.72 |
| scan3 (with candidates: 290, 34 blocks, 33 read) | 1.18 | 0.51 to 0.57 |
| joins 2 and 3 | 0.07 | 0.07 |
| ORDER BY keys | 0.17 | 0.19 |
| render | 0.23 | 0.25 |
| total | 4.14 | 2.24 |

The target 0.40 needs about 1.66 ms at 4 threads. If the two scans with
candidates took a quarter of their 1-thread time (0.71 ms together), q07 at 4
threads would be about 1.81 ms: the serial phases alone (about 1.0 ms at 4
threads) keep the ratio above 0.4.

Why the scans with candidates do not reach 4 times (temporary time marks in
`scanSipTableParM`, not committed):

- Per-range setup and the end of the phase are small: from the entry of
  `scanSipTableParM` to the last task started 11 to 15 microseconds, from the
  last range to the end 11 to 20 microseconds.
- A block costs more at 4 threads: timed one by one (each block a job of a
  shared counter, 61 runs), a block that is read takes 30 to 54 microseconds,
  and the blocks of one scan sum to 1.87 ms at 4 threads against 1.65 ms for
  the whole scan at 1 thread (scan2). Over both scans the time per block is
  about 25 percent higher at 4 threads, on the calling thread and on the pool
  workers alike. Four separate 1-thread processes run at the same time take
  1.60 to 1.83 ms each for scan2 (alone: 1.66 to 1.79 ms), so the cost is in
  the process, not in the machine. Its cause is not found (as in stage 1h).
  CPU per warm run (`perf record -F 4999`, 500 runs): the two candidate loops
  `Sip.deltaGatherGoY` and `Sip.deltaFindGoY` 2.51 ms at 1 thread and 2.68 ms
  at 4 threads; `lean_dec_ref_cold` 0.03 and 0.22 ms; `ScanSpec.fresh` with
  the copy of the candidates (an `Array UInt64` of boxed words) 0.11 ms at 4
  threads.
- The ranges were unequal: with equal block counts the largest of the four
  ranges held 1.12 to 1.20 times the mean of the join-key values tested,
  because a block that the candidates rule out costs 1 microsecond. 1m.3
  removes this.
- The time of one range varies by up to 3 times between runs for the same
  blocks (scan0: 52 to 149 microseconds for one block), and the phase waits
  for the slowest of four.

### 1m.3 What changed

`scanSipTableParM` cuts the selected blocks at the points where the rows of
the blocks that will be read reach `j / n` of their total
(`ParallelScan.weightCuts`; a block weighs its rows when `selects`, `sipRange`
and `Sip.mayHold` let it through, else 0), as bounds of consecutive positions
(`ParallelScan.cutBounds`). Phases at 4 threads, 10 processes per variant
interleaved: scan2 0.722 to 0.695 ms, scan3 0.568 to 0.548 ms.

Proved (`ParallelScan.lean`, `ParallelSipTheorems.lean`; axioms `propext`,
`Classical.choice`, `Quot.sound`):

- `cutBounds_flatten`: for any list of cut points, the ranges concatenate to
  `List.range n`.
- `parallel_sip_acc_eq_parts`: the parallel scan with candidates over any
  partition of the block list (ranges whose concatenation is the list) equals
  the single scan; `parallel_sip_acc_eq_cut` for the ranges of `cutBounds`.
  The hypotheses are those of `parallel_sip_acc_eq`; none states the
  conclusion.

### 1m.4 Tried and not kept

Each measured with the variants interleaved, phases at 4 threads unless
stated:

- Each block of a scan with candidates as a job of a shared counter
  (`IO.Ref.modifyGet`), the parent placing the block tables in order: ranges
  equal, but each thread spent 50 to 100 microseconds more outside the block
  scans; scan2 0.623 to 0.685 ms. Granules of 2 and 3 weighted ranges per
  thread: no change larger than the variation.
- The ranges through `parFold` (dynamic, 1 to 4 ranges per thread): scan2
  0.63 to 0.73 to 0.83 ms.
- The calling thread's range with its own view and copies, as the tasks do:
  scan2 0.655 to 0.718 ms.
- A pause instruction after each empty poll of a pool cell (1, 4 or 16
  times): no change. Shorter polls (`SBM11_SPIN_NS` 20,000 and 200,000):
  slower (total 2.34 to 3.35 and 2.59 ms).
- The rendering built on the pool from key slices that the calling thread
  read first: reading the 626 keys took 0.12 ms and building the text on 4
  threads 0.16 ms, against 0.27 ms for the rendering on one thread; the next
  run's first phases were also slower (constants 0.04 to 0.08 ms: the shared
  pages are then multi-threaded objects).

### 1m.5 For the owner: one open file per permutation

`l4_block_pread` opens, stats and closes the file for every read. An
experiment that kept one open file per thread (`L4_FDCACHE`, not committed):
phases at 1 thread scan2 1.79 to 1.56 ms, total 4.44 to 3.90 ms (5
processes); at 4 threads total 2.34 to 2.17 ms (10 processes). In the final
interleaved run the difference was smaller: q07 4.24 / 2.24 against
4.26 / 2.17 ms, q19 32.95 / 10.43 against 31.88 / 10.30 ms. The change is
faster at both thread counts, and it makes the 4/1 ratio of KR 1.2 worse when
the 1-thread time gains more. A version to land keeps the descriptor in the
session's permutation handle and closes it with the session.

### 1m.6 Gates

On commit `6d7ca45c` (exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 3,379 pass, 0 fail, 28 expected-fail (out of 3,407) |
| `tests/sbm11/threads.sh` | first run exit 1: `gate ids-path-star-nested` at 4 threads exit 124 (the 600-second limit); second run exit 0: gate and gate2 347 identical, olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record: equal 76, different 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 matched the reference engine |
| `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, `lean-csimp-reach.py --gate` | exit 0 (1,027 modules reached), exit 0, exit 0 |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381), cli-smoke 151 pass, 0 fail, 5 xfail (out of 156), LWS scaling 21 pass, 0 fail (out of 21), host-purity-lint 40 pass, 0 fail (out of 40) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

After `origin/main` moved (`eea5bb40`), the merge (`055c0c2e`, no conflict):
`lake build` exit 0; `tests/sbm11/run.sh` exit 0 (3,379 pass, 0 fail, 28
expected-fail, out of 3,407); `threads.sh` exit 0 (all answers identical,
DBpedia equal 76, different 0); census at 4 threads exit 0 (605 matched);
unbuilt-modules exit 0 (1,043 modules reached); tail-recursion exit 0;
csimp-reach exit 0; `tools/land-gates.sh` exit 0 (native-smoke 377 pass, 0
fail, 4 xfail, out of 381; cli-smoke 151 pass, 0 fail, 5 xfail, out of 156).

The hang: `ids-path-star-nested` is a property path (`ex:a (ex:knows*)* ?o`)
with no scan with candidates, so it does not run the code of this stage. It
did not occur again in 1,350 runs (both binaries, 4 and 8 threads, with a
second query running beside it). It is recorded in
https://github.com/danbri/factoidal/issues/961.

### 1m.7 What remains

- q07 (0.53): about 1.0 ms of serial work at 4 threads (first scans and join
  0.42, ORDER BY keys and rendering 0.44, joins and constants 0.11), and the
  scans with candidates at about 25 percent more time per block than at 1
  thread, cause not found (1m.2).
- The rare hang of 1m.6.

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1n: the worker pool hang, and open files per generation file (2026-10-24)

Issue https://github.com/danbri/factoidal/issues/981 (the hang) and
https://github.com/danbri/factoidal/issues/961 (KR 1.2 of
https://github.com/danbri/factoidal/issues/875). No allocator setting changed.
Branch `fix/issue-981`.

### 1n.1 The hang of stage 1m: cause and repair

Cause: a lost write of the worker pool's stop flag. Each worker read the flag
with `IO.Ref.get`, and `Pool.shutdown` wrote it with `IO.Ref.set`. In the
Lean 4.33.1 runtime (disassembly of `lean_st_ref_get`, `_take`, `_set`,
`_swap`), `get` exchanges the value for null, spins while it finds null, and
puts the value back with a second exchange; a `set` between the two is lost
(`get` frees the new value and keeps the old). A worker that read the flag
while `shutdown` wrote it kept `false`, took the empty mailbox that
`shutdown` posted, blocked on its promise, and `shutdown` waited for its
thread for good. Every `l4sbm11 query` with a pool runs `shutdown` once, so
the query does not matter: `ids-path-star-nested` uses no divided scan.

Evidence:

| Test | Before the repair | After |
| --- | --- | --- |
| `l4pool-bench stress 50000 200 3` (start 3 workers, wake, 0 to 200 us of work, every second cycle one job per worker, stop), 300-second limit | 3 of 5 processes hung (one after more than 10,000 cycles) | 10 of 10 ended (500,000 cycles) |
| gdb of a hung `l4pool-bench`: main thread in `Pool.shutdown` (`IO.wait` of a worker task), one worker in `Cell.take?` (`IO.wait` of its promise) inside `workerLoop` | seen | - |
| `tests/sbm11/pool-stress.sh`, 20,000 processes of `ids-path-star-nested` at 4 threads; 20,000 of 67 queries (`ids-path-*`, `threads/*`) at 2, 4 and 8 threads; 20,000 at 4 and 2 threads beside 4 CPU-bound processes; 10-second limit each | 0 hangs, 0 failures (60,000 processes) | 0 hangs, 0 failures: 20,000 processes at 4 and 2 threads beside 4 CPU-bound processes, and the 500 of `threads.sh` |

The query processes did not reproduce the hang: the window is two
exchanges wide, and in a query process `shutdown` meets a worker at its
flag read only when the worker has just started or just finished a job.
`l4pool-bench stress` puts that moment in every cycle.

Repair (commit `ec07138e`):

- `Pool.shutdown` writes the flag with `modify fun _ => true`. `get`,
  `take`, `modify` and `modifyGet` all spin while the ref holds null, so
  they exclude each other; `set` and `swap` do not. Rule: a ref that two
  threads reach uses only `set`/`swap` or only `get`/`modify`/`modifyGet`
  (skill `lean4-performance`, which said "use `swap`, `modify` or
  `modifyGet`" since stage 1j; that was wrong when the other thread uses
  `set` or `swap`).
- The same mix in `parFold` (workers `get`, the calling thread `set` of the
  stop flag after a failure: a lost write there only lets workers run more
  ranges) and in `Session.gdxBytes` (a lost write only reads GDX1 again):
  both now write with `modify`.
- The review of `Harness/WorkerPool.lean` found no other mix: the cells use
  `set` and `swap` only, and the wake-up order (reader: publish the promise,
  read the value again; writer: write the value, take the promise) is
  correct when both are single exchanges. `parFold`'s result slots are
  written before their promise is resolved and taken after it is waited
  for. One more defect on an error path: a `parFold` worker whose setup
  failed took no range, and in fixed order the calling thread waited for
  its ranges for good; it now resolves each range it takes with the error.
- Test: `tests/sbm11/pool-stress.sh` (20,000 `l4pool-bench stress` cycles
  with a 120-second limit, then 500 query processes with a 10-second limit;
  a hung process gets its gdb stacks), run at the end of
  `tests/sbm11/threads.sh`.

### 1n.2 One open file per generation file: tried, not kept

Coordinator decision for this stage: the change of stage 1m.5 (one open file
in place of `open`, `fstat` and `close` per read) lands if it is faster at
both 1 and 4 threads, even if the 4/1 ratio gets worse. It was not faster at
4 threads, so it did not land. Code: branch `fix/issue-961-fd` (`d084e5d3`
one shared descriptor, `6b56213d` one descriptor per thread).

What was built (`d084e5d3`): `l4_block_file_open` and `l4_block_file_pread`
(an external object that holds the descriptor and the length read at open;
its finalizer closes the descriptor), `Harness.PosixRangeIO.ReadSrc` (a path
and an optional open file), and the query session's PRB1, PRM1, GDV1 and
GDX1 opened once. Answers of q07, q19 and q21 at 1 and 4 threads were
byte-identical; q07 at 1 thread made 19 `openat` calls in place of 1,338.

Interleaved, binary of `main` (`ec07138e`) against each variant, 16 rounds
(15 kept), `--repeat 21`, the 1b.6 method (raw CSV
`.claude-runs/p2/final.csv` and `tl.final.csv`, not in the repository):

| Query | `main` 1 / 4 threads ms | one shared descriptor 1 / 4 threads ms | `main` (second run) 1 / 4 | one descriptor per thread 1 / 4 |
| --- | ---: | ---: | ---: | ---: |
| q07 | 4.33 / 2.38 | 4.30 / 2.64 | 4.31 / 2.34 | 4.27 / 2.43 |
| q19 | 32.54 / 10.20 | 32.58 / 10.42 | 33.01 / 10.58 | 32.60 / 10.54 |
| q21 | 89.44 / 25.84 | 89.03 / 28.28 | 90.03 / 26.29 | 87.70 / 26.44 |
| d10 | 8.61 / 3.20 | 8.49 / 3.19 | 8.52 / 3.27 | 8.45 / 3.25 |

Peak RSS 4/1 did not change (q07 1.14, q19 1.82, q21 1.68, d10 1.22).

Why the gain of stage 1m.5 does not appear:

- A warm run reads few blocks. `strace -c` of q07 at 1 thread: 1,327
  `pread64` for `--repeat 1`, 3,107 for `--repeat 21`, so about 89 reads per
  warm run after the first; the block and page caches hold the rest. At
  about 1 microsecond per `openat`, the open per read costs about 0.1 ms of
  4.3 ms, which is inside the variation between processes. The stage 1m.5
  figures (4.44 to 3.90 ms) came from 5 processes of the phase method; its
  own final interleaved run gave 4.24 against 4.26 ms.
- One descriptor shared by 4 threads was slower at 4 threads in every query
  except d10 (q21 25.84 to 28.28 ms, slower in 12 of 16 rounds;
  q07 2.38 to 2.64 ms). A likely cause, not measured: in a process with more than
  one thread, each `pread` takes and drops a reference on the shared `struct
  file` (`fdget`), and 4 threads then write one cache line. With one
  descriptor per thread (a thread-local table of 16 entries in C, keyed by
  the object's number) the loss goes, and no gain is left.

What would change this: a cold query (the first run of a process reads all
1,327 ranges), or a store whose blocks do not fit the caches. Neither is a
KR 1.2 measurement.

## Stage 1o: the serial steps of q07 (2026-10-24)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. No allocator setting changed;
the block-bytes rule of `tests/sbm11/threads.sh` and `SBM11_STREAM_JOBS` are
not changed. Branch `batch3/kr12-q07d`.

### 1o.1 Result

KR 1.2 is met for d10, q19 and q21; it is not met for q07 (0.47 against
0.40). q07 at 4 threads went from 2.83 to 2.18 ms in the final run (2.33 to
2.67 ms on `main` and 1.96 to 2.21 ms on this stage over four interleaved
runs of the session). Final interleaved run: binary of `main` `c7700ee2`
against this stage (`b7d45ff4`), 24 rounds (23 kept), `--repeat 21`, the
1b.6 method, 2026-10-24 06:37 to 06:41 UTC, after all gates had ended (raw
CSV `.claude-runs/q07d/final4.csv`, not in the repository):

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | target met |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 4.40 / 2.83 | 0.64 | 4.62 / 2.18 | 0.47 | 1.14 / 1.22 | no |
| q19 | 34.55 / 12.01 | 0.35 | 34.65 / 11.76 | 0.34 | 1.81 / 1.81 | yes |
| q21 | 91.24 / 31.39 | 0.34 | 92.41 / 32.88 | 0.36 | 1.68 / 1.66 | yes |
| d10 | 8.68 / 3.25 | 0.38 | 8.83 / 3.33 | 0.38 | 1.20 / 1.21 | yes |

The 1-thread time of q07 in this run (4.62 against 4.40 ms) is the variation
between processes: three other interleaved runs gave 4.39 / 4.44, 4.34 /
4.45 and 4.39 / 4.46 ms, and the phase method (8 processes of 101 runs,
interleaved) gives 4.47 ms for `main` and 4.40 ms for this stage. No change
of this stage runs on the 1-thread path of q07 (the hint is not computed
without a pool, and the rendering loops are the ones of `main`).

### 1o.2 What changed

1. **The rows are rendered beside the ORDER BY sort.** With a worker pool, an
   ORDER BY result without DISTINCT, OFFSET or LIMIT of at least 64 rows
   (`Par.sortedRows`, `SBM11_SORTED_RENDER_ROWS`) is rendered in row ranges
   by pool workers (`Par.renderStart`, `renderPartM`: range `j` on worker
   `j`, one buffer per row) while the calling thread computes the order
   (`orderPermM`); the rows are then written in that order
   (`assembleRows`). A worker copies a shared dictionary page into its own
   cache on first use (`Session.copyFirst`): with the scans' rule (copy on
   second use in one job) every query read the pages again from the shared
   `taskPages`, and a worker took 2 to 4 times as long per row as the
   calling thread. A job decodes query-local ids with the query's vocabulary
   (`Store.withLocal`); the first version did not, and the gate query
   `ids-values-orderby` failed at 2 threads ("not a dictionary id",
   `tests/sbm11/threads.sh`). The stage 1j divided rendering had the same
   defect, never reached by a test; it now takes the vocabulary too.
   Phases at 4 threads: ORDER BY and render 0.47 to 0.21 ms (the render
   phase is the wait for the workers and the assembly, 0.03 ms).
2. **The next scan starts early.** Before its first scan, `evalBgpM` gives
   `Par.scanHint` the scan the join loop will most likely make next
   (`nextScanHint?`: the choice of `bgpStepM` from the estimates, no hint when
   the scan would take candidates with the first scan's estimate as its left
   rows). The native driver starts it on the last pool workers
   (`startScanTablePar`), and the store's `scanTable` takes its table when
   the spec is the same (`scanTableOrStarted`). It starts only under
   `verify none`, with no delta overlay and the PRM1 range of the key in the
   permutation's cache, so a scan that is not taken reads no PRM1 entry,
   fills no shared cache and adds no counter. q07 at 4 threads: first scan
   and scan0 0.24 to 0.18 ms.
3. **The range jobs are functions.** The jobs of `scanTableParM` and
   `scanSipTableParM` were `do` blocks in the caller's loop whose first lines
   made the job's own copies (`ScanSpec.fresh`, `OvCtx.fresh`, the copy of
   the candidates, `rangeMetas`). The generated C called those copies in the
   caller's loop, before the closure of the job was made: the compiler moves
   a pure `let` out of a closure body. So the calling thread made every
   task's copies before it scanned its own range (tasks started 9 to 18
   microseconds apart), and the copies were shared objects with atomic
   reference counts. The jobs are now `@[noinline]` functions
   (`scanRangeJob`, `sipRangeJob`).
4. **The candidates go to a job as words.** `scanSipTableParM` packs the
   candidates into one buffer (`packWords`, 312 words: 39 cache lines) and
   each job unpacks its own array (`unpackWords`). The first `unpackWords`
   used `Array.ofFn` and took 50 to 220 microseconds for 312 words; the
   `push` loop takes 4 to 6.

Proved (axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorry`):

- `RenderPermTheorems.sortedRender_eq`: for ranges that cover the rows of a
  well-formed table in order and an index array `perm` of its rows, when
  every range job succeeds, `assembleRows` of the jobs' rows equals
  `renderRowsM` of `t.reorder perm` (the serial path's bytes). The proof goes
  through `appendIdJsonM_eq` and `rowIntoM_eq` (each byte writer appends to
  its buffer). `rowRanges_cover`: the ranges of `sortedRenderJobs` cover the
  rows in order.
- `RenderPermTheorems.unpackWords_packWords`: a job's candidates are the
  caller's.
- `BgpTableTheorems.hintScanM_id`: the hint is `pure ()` in `Id`;
  `evalBgpM_modelS_par` holds with the hint in `evalBgpM`.
- The table of a scan started early is the table of `scanTableParM` for
  other range bounds (`ParallelScanTheorems.parallel_acc_eq`).

### 1o.3 Measurements

`SBM11_PHASES=1`, 101 runs per process, median over 10 processes per cell
interleaved (8 at 1 thread), binaries of 1o.1 (ms):

| Phase | 1 thread, main | 1 thread, this stage | 4 threads, main | 4 threads, this stage |
| --- | ---: | ---: | ---: | ---: |
| constants | 0.04 | 0.04 | 0.04 | 0.04 |
| first scan | 0.19 | 0.17 | 0.14 | 0.15 (posts the early scan) |
| scan0 | 0.22 | 0.22 | 0.14 | 0.04 (the early scan's wait) |
| join0 | 0.41 | 0.40 | 0.19 | 0.19 |
| scan2 (with candidates) | 1.74 | 1.78 | 0.74 | 0.71 |
| join2 | 0.03 | 0.03 | 0.04 | 0.03 |
| scan3 (with candidates) | 1.25 | 1.25 | 0.59 | 0.56 |
| join3 | 0.05 | 0.05 | 0.07 | 0.05 |
| ORDER BY | 0.18 | 0.18 | 0.21 | 0.22 (keys 0.12, sort 0.09; rows rendered meanwhile) |
| render | 0.25 | 0.24 | 0.27 | 0.03 (wait and assembly) |
| total | 4.47 | 4.40 | 2.51 | 2.08 |

### 1o.4 Tried and not kept

- The stage 1j divided rendering for q07 (`SBM11_RENDER_ROWS` 80 and 40):
  render 0.37 and 0.27 ms against 0.26 ms on the calling thread.
- Three weighted block ranges per thread, assigned round robin, for the
  scans with candidates (the range of blocks 31 to 48 of scan2 took 670 to
  690 microseconds in every run against 400 to 550 for the others): the phase
  medians did not change (scan2 0.718 to 0.695, scan3 0.553 to 0.573 ms).
- Diagnosis only, not a setting: `MIMALLOC_PURGE_DELAY=-1` in the
  environment changed no phase.

### 1o.5 The time per block at 4 threads

The scans with candidates still take about 23 percent more thread time at 4
threads than the whole scan at 1 thread (scan2: ranges of 458, 688, 526 and
406 microseconds against 1.65 ms). Checked:

- Not shared cores: a C loop pinned to CPU 0 ran 41 ms alone and 41 to 42 ms
  with a loop on each other CPU (no SMT siblings in this VM).
- Clock: 4 such loops at once, 41 to 44 ms each (at most 5 percent).
- CPU per run (`perf record -F 4999 --call-graph dwarf`, 201 runs): the loops
  `Sip.deltaGatherGoY` and `Sip.deltaFindGoY` 2.62 ms at 1 thread and 2.89
  ms at 4 threads; the rest of `scanBlockSipM` 0.55 and 0.81 ms.
- `open`, `fstat`, `pread` of 10,000 bytes and `close` (as `l4_block_pread`
  does): 3.2 microseconds per read in 1 thread, 4.2 in each of 4 threads;
  with an open descriptor 1.4 in both. About 22 reads per thread per scan, so
  about 20 microseconds per range.
- The copies made by the caller (item 3 of 1o.2): fixed; scan2 and scan3 at
  4 threads 0.72 and 0.57 ms to 0.64 and 0.50 ms with item 4.

The cause of the remaining 10 percent in the loops is not found.

### 1o.6 Gates

On commit `b7d45ff4` (the merge of `origin/main` `c7700ee2` and the stage;
exit codes read):

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 3,394 pass, 0 fail, 28 expected-fail (out of 3,422) |
| `tests/sbm11/threads.sh` | exit 0: gate and gate2 347 identical at 1, 2, 4 and 8 threads (gate sections with `SBM11_SORTED_RENDER_ROWS=1`), olympics 21, 2 and 2, DBpedia 19; DBpedia against the three-engine record equal 76, different 0; pool-stress 500 processes, hangs 0, failures 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 matched the reference engine |
| `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, `lean-csimp-reach.py --gate` | exit 0 (1,049 modules reached), exit 0, exit 0 |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381); cli-smoke 151 pass, 0 fail, 5 xfail (out of 156) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

The first gate run on the merge failed the tail-recursion gate: two
declarations merged from `main` (`SPARQL.scopeFromGraphs`,
`PhaseETests.chainOf.go`) had no entry, and `RenderPermTheorems.catB` was a
recursive definition. `catB` is now a `foldr`; the two entries are in
`tools/lean-tail-recursion-allow.txt` with their reasons.

A version that wrote `renderRowsM` through `rowIntoM` made olympics q21 at 1
thread about 3 percent slower (medians of 6 processes: 97.7 against 92.7 ms
with the inline loops); the inline loops are kept, and `forIn_cols` and
`rowLoop_eq` prove them equal to the `rowIntoM` form.

### 1o.7 What remains

- q07 at 0.47: the remaining time at 4 threads is in the scans with
  candidates (0.71 + 0.56 ms against 1.78 + 1.25 at 1 thread: about 25
  percent more thread time per block, 1o.5), the ORDER BY keys and sort on
  the calling thread (0.22 ms), the merge join (0.19 ms) and the first scan
  (0.15 ms). The target needs about 1.76 ms.
- Not tried: the ORDER BY keys of each row range read by the rendering
  workers (the keys of `orderKeysByKeysM?` are row-local; about 0.07 ms by
  estimate), and a cost model for the weighted cuts of a scan with
  candidates (the weight of a block did not predict its time).

Issue https://github.com/danbri/factoidal/issues/961 stays open.

## Stage 1p: q07, the time per block at 4 threads (2026-10-24)

Issue https://github.com/danbri/factoidal/issues/961, key result KR 1.2 of
https://github.com/danbri/factoidal/issues/875. No allocator setting changed;
the block-bytes rule of `tests/sbm11/threads.sh` and `SBM11_STREAM_JOBS` are
not changed. Branch `batch3/kr12-q07e`.

### 1p.1 Result

KR 1.2 is not met for q07: 0.50 on this stage and 0.50 on `main` in the
final run. The stage found the cause of the "25 percent more thread time per
block at 4 threads" of stage 1o.5 (1p.2: there is no slowdown of the decode;
the figure was the variation between processes) and landed one measured
change, a larger range for the calling thread in a divided merge join
(1p.4). That change saves about 0.03 ms of the 4-thread time (in-process
A/B), which the interleaved runs cannot resolve: in this session the 4-thread
time of one process of q07 varied from 1.8 to 2.6 ms, and 1-thread runs from
4.1 to 7.3 ms.

Final interleaved run: binary of `main` `51dc6db6` (its Lean code is that of
`6f5b9640`) against this stage (`59e211aa`), 32 rounds (31 kept),
`--repeat 21`, the 1b.6 method, 2026-10-24 09:21 to 09:27 UTC, after all
gates had ended (raw CSV `.claude-runs/q07e/final4.csv`, not in the
repository):

| Query | `main` 1 / 4 threads ms | 4/1 | this stage 1 / 4 threads ms | 4/1 | peak RSS 4/1 (largest), main / this stage | rounds this stage faster, 1 / 4 threads | target met |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| q07 | 4.52 / 2.24 | 0.50 | 4.47 / 2.24 | 0.50 | 1.21 / 1.22 | 17 / 20 of 31 | no |
| q19 | 35.27 / 12.67 | 0.36 | 35.85 / 13.48 | 0.38 | 1.80 / 1.80 | 16 / 14 of 31 | yes |
| q21 | 95.69 / 34.99 | 0.37 | 96.23 / 34.66 | 0.36 | 1.68 / 1.67 | 16 / 15 of 31 | yes |
| d10 | 8.74 / 3.47 | 0.40 | 8.86 / 3.48 | 0.39 | 1.22 / 1.21 | 11 / 13 of 31 | yes |

No change of this stage runs on the paths of q19, q21 and d10 (they make no
divided merge join), so their differences are variation between processes
and binaries. Three earlier interleaved runs of the same hour, with the
merge sort change of 1p.5 still in, gave for q07 4/1 0.47, 0.46 and 0.51
against 0.53, 0.52 and 0.53 for `main`, and in the third run `main` missed
the target for d10 and q21 too (0.41 and 0.41): in this period the machine
was slower than in stage 1o (q21 at 1 thread 94 to 97 ms against 91.2).

### 1p.2 The time per block at 4 threads: measured cause

Stage 1o.5 reported that a block of a scan with candidates takes about 25
percent more thread time at 4 threads than at 1 thread, cause not found. The
measurements of this stage (diagnostic code, not committed; olympics q07,
binary of `main` `9fb75e4d` or of this stage):

| Test | 1 thread | 4 threads |
| --- | ---: | ---: |
| Decode of the blocks of a range on bytes read once by the thread (`sipChunk`, 200 passes), thread time summed over the ranges, median of 20 runs in 10 processes per mode: scan2 / scan3 | 1,541.5 / 1,055.5 microseconds | 1,541.5 / 1,056 microseconds |
| The same with a read (`open`, `fstat`, `pread`, `close`) before each block: scan2 / scan3 | 1,746.5 / 1,154.5 | 1,801.5 / 1,261 |
| A range scanned twice in the same job, first and second pass (scan2, 4 ranges, 2 runs) | - | 390 / 395, 442 / 475, 435 / 481, 495 / 524 microseconds |
| Sum of the four range times of the real scan (scan2) against the 1-thread scan less its candidate step | 1.75 to 1.80 ms | 1.757 and 1.793 ms |
| TLB shootdowns per process of 201 runs; hypervisor steal per 401 runs; CPU migrations per 401 runs | 10 to 11; 3 to 5 jiffies; 0 | 28 to 34; 3 to 4 jiffies; 5 |
| 1-thread q07 pinned to each CPU in turn (`taskset`), 3 rounds | no CPU slower in every round (4.33 to 5.19 ms, the order changes) | - |

Findings:

- The decode loops (`Sip.deltaFindGoY`, `Sip.deltaGatherGoY`) do not slow
  down at 4 threads when each thread decodes bytes it holds: the summed
  thread time is the 1-thread time. So the cause is not the clock, memory
  bandwidth, shared caches, atomic reference counts in the loops or false
  sharing.
- A read per block costs about 4 microseconds at 1 thread (3 percent of
  scan2) and more at 4 threads (scan3: +9 percent). In the profile of 4
  threads the extra kernel time is in `do_dentry_open`, `init_file`,
  `_raw_spin_lock` and `lockref_get_not_dead`: the `open` and `close` of each
  read on one dentry from 4 threads (about 0.05 ms of CPU per run). Stage 1n
  measured one descriptor per thread: no gain at 4 threads in the query time.
- In the real scan the four range times add up to the 1-thread scan time.
  The "25 percent more per block" of stage 1o came from comparing processes:
  whole processes of q07 at 4 threads are 20 to 35 percent slower in every
  phase, the serial ones too (constants 0.035 against 0.045 ms, join2 0.027
  against 0.043 ms), and over time the machine changes speed (1-thread
  medians 4.3 to 4.9 ms in one hour). `perf` of separate 1- and 4-thread
  processes (loops +11 percent at 4 threads) has the same defect.
- What does cost more at 4 threads is data that another core made. The
  merge join of the first two scans (6,248 and 13,369 rows) in 4 equal
  ranges: the calling thread's range took 0.065 ms and the calling thread then
  waited 0.085 to 0.150 ms for the worker ranges (in-process measurement, 6
  processes). The calling thread made both tables (it appended the range
  tables of the scans), so their bytes are in its cache; a worker reads them
  at about half the speed per row.

What the scans with candidates lose at 4 threads, then, is (sub-phase marks,
median of 5 processes of 101 runs, a fast process): the candidate step on
the calling thread (0.04 ms before scan2, 0.08 ms before scan3; the same at
1 thread), the block weights and cut points (about 0.015 ms), the job starts
(0.006 ms), the slowest range against the mean of the four (about 0.05 ms in
scan2; the calling thread's range, which also holds the first block of the
key range, 40 to 80 microseconds as it decodes the key column), and the wait
and append of the range tables (0.012 to 0.017 ms).

### 1p.3 Measurement method: variants in one process

The differences sought here (0.01 to 0.05 ms) are smaller than the variation
between processes at 4 threads (whole processes 20 to 35 percent apart).
Interleaved processes misled twice in this stage: a binary that differed from
`main` only in `packWords` measured scan2 0.771 ms against 0.626 ms (8
processes each), and it was 4 percent slower at 1 thread in every phase,
which the change cannot cause. Method used for the decisions of 1p.4 and
1p.5: one binary in which a setting is read per run, the runs of one process
alternate between the variants, and the median of each variant is compared
inside each process, over 6 to 8 processes. It cannot measure an effect that
stays in a process once it happened (an object marked multi-threaded stays
so), and it is no substitute for the final interleaved run of the 1b.6 method.

### 1p.4 What changed

1. **The calling thread takes a larger range of a divided merge join.**
   `IdQuery.mergeJoinParM` cuts the left rows with `ParallelJoin.rangesShare`:
   the first range (the calling thread's) is `joinShare / 10` of an equal
   share, the others equal (`Par.joinShare`, `SBM11_JOIN_SHARE`, default 14).
   In-process A/B, 6 processes of 401 runs, the calling thread's range plus
   its wait for the workers (ms): share 10: 0.152 to 0.173; 12: 0.127 to
   0.154; 13: 0.124 to 0.151; 14: 0.124 to 0.143; 15: 0.124 to 0.144.
   Proved: `ParallelJoinTheorems.rangesShare_chain` (the ranges cover the
   left rows in order) and `mergeJoinRanges_rangeChunksShare`;
   `WorkerPoolTheorems.mergeJoinParM_eq` holds with the new ranges.
2. **`packWords` writes each word with one store** (`FrameWords.put64F`;
   `RenderPermTheorems.packWords_eq_put64`, `rfl`).
3. `l4sbm11 query` with `SBM11_PHASES` adds an `end` mark after the last
   phase (0.002 to 0.003 ms in every process measured).

### 1p.5 Tried and not kept

- **A smaller range for the calling thread in the scans with candidates**
  (`callerCuts`, 9/10 and 8/10 of an equal share, cut at the nearest prefix
  sum): in-process A/B of 10, 9 and 8 over 6 processes, no variant faster in
  every process (query medians within 0.08 ms of each other, in no order).
- **The merge sort specialised** (`@[specialize]` on `Qlvr.mergeSortBy` and
  its loops): `IdQuery.sipDistinct` sorts the join-key words of a scan with
  candidates through a closure call with boxed arguments per comparison
  (`UInt64.decLe` as a closure, read from the generated C). With the change
  the candidate step before scan3 took 0.081 ms against 0.089 ms before (one
  sample of 5 processes each, not an A/B) and scan3 at 1 thread 1.232
  against 1.250 ms (8 processes each). In the interleaved runs of the four
  queries q07 at 1 thread was 4.91 against 4.67 ms for `main` (69 rounds,
  slower in 42), which the phase method (4.31 against 4.36 ms) did not show.
  Its gain is not measured, so it was removed before the landing (commit
  `31452828`).
- **Block weights from the value range** (stage 1o.7 asked for a cost
  model): with bytes held, a block costs about 11 microseconds plus about 6
  nanoseconds per row up to the last row found, and the row is estimated
  from the block's join-column range `[vlo, vhi]` and the largest candidate
  in it. The estimate correlates 0.94 and 0.96 with the block times (the
  blocks have 4,096 rows but one; a first model from the count of
  candidates in the range: -0.09 and 0.55), and on held bytes it gives the cut points
  of the measured times. In the query, in-process A/B over 8 processes, it
  was slower in 6 (by 23 to 57 microseconds) and faster in 2 (12 and 16).
  The block times in the query include the read and other cores' data, which
  the model does not see.
- **The ORDER BY keys read by the rendering workers** (estimated -0.07 ms in
  1o.7): not built. In-process A/B of the rendering beside the sort against
  the rendering after it: the calling thread's keys and sort take 0.207 to
  0.221 ms both ways, so the workers do not slow it. The workers' rendering
  takes 0.38 ms of CPU for 313 rows in 3 ranges (0.28 ms at 1 thread), about
  0.13 ms each, and ends before the sort does. Keys made by the workers help
  only if they reach the calling thread before the rendering ends (a second
  result per job); then the gain is the calling thread's key time, 0.11 to
  0.12 ms, less the wait for the first keys. Not done in this stage.
- **The merge join on the pool from fewer rows** (step 3 of the brief): the
  joins after the scans with candidates are 312 by 312 rows (0.027 to 0.031
  ms, merge join) and a hash join of 313 rows (0.045 to 0.05 ms). At half
  the speed per row on a worker (1p.2), four ranges save at most about 0.01
  ms of the merge join, less three job starts (about 0.006 ms). Not tried.

### 1p.6 Gates

On commit `59e211aa` (the merge of `origin/main` `6f5b9640` and the stage;
exit codes read). The same gates passed on `441e4357`, the stage with the
merge sort change, merged with `origin/main` `51dc6db6`.

| Gate | Result |
| --- | --- |
| `lake build` | exit 0 |
| `tests/sbm11/run.sh` | exit 0: 3,394 pass, 0 fail, 28 expected-fail (out of 3,422), part (z) included |
| `tests/sbm11/threads.sh` | exit 0: gate2 347 identical, olympics 21, 2 and 2, DBpedia 19 identical at 1, 2, 4 and 8 threads; DBpedia against the three-engine record equal 76, different 0; pool-stress 20,000 start-stop cycles ended, 500 processes, hangs 0, failures 0 |
| `SBM11_THREADS=4 tests/sbm11/census.sh` | exit 0: 605 matched the reference engine |
| `lean-unbuilt-modules.py --gate`, `lean-tail-recursion-audit.py --gate`, `lean-csimp-reach.py --gate` | exit 0 (1,052 modules reached), exit 0, exit 0 |
| `tools/land-gates.sh` | exit 0 (LAND GATES PASSED): native-smoke 377 pass, 0 fail, 4 xfail (out of 381); cli-smoke 151 pass, 0 fail, 5 xfail (out of 156) |
| `sorry`, `native_decide`, `axiom`, `maxHeartbeats` in the Lean diff | none |

### 1p.7 What remains

- q07 at 0.50 in this period (0.47 in stage 1o). At 4 threads, in a fast
  process (sub-phase marks, ms): constants 0.04; hint and estimates 0.03;
  first scan 0.10 on the calling thread and 0.01 wait; scan0 wait and append
  0.045; merge join 0.12 to 0.14 and its output 0.017; the candidate step
  before scan2 0.04 and before scan3 0.08 (the same at 1 thread: the copy
  of the join column, the sort and the check that every value is a
  candidate, `sipCands`); block weights and cut points about 0.015 per scan;
  slowest range against the mean of four about 0.05 per scan; wait and append
  of the range tables 0.012 to 0.017 per scan; joins 2 and 3 0.03 and 0.05;
  ORDER BY keys and sort on the calling thread 0.21 (0.18 at 1 thread);
  rendering wait and assembly 0.035. The target needs about 1.8 ms.
- The per-block cost at 4 threads is not a cause any more: decode costs the
  same thread time; what costs more is the read path per block (`open` and
  `close` from 4 threads) and data that another core made (a worker reads
  the calling thread's tables at about half speed).
- Candidates for a later stage, each with its measured size: the ORDER BY
  keys sent back by the rendering workers before they render (at most the
  calling thread's 0.11 to 0.12 ms of keys, less the wait); the candidate
  step `sipCands` (0.04 and 0.08 ms on the calling thread at every thread
  count: the binary search of `allMemGo` for each row, 0.06 ms of CPU per
  run at 1 thread); a range of a scan with candidates read from bytes that
  the calling thread does not touch first.
- The measurement method: at 4 threads the variation between processes
  (20 to 35 percent) is larger than every remaining step. 1p.3 describes
  the in-process A/B that this stage used.

Issue https://github.com/danbri/factoidal/issues/961 stays open.
