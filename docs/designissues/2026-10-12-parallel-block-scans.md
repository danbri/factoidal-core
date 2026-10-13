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
