# Parallel block scans on SBM11

Date: 2026-10-12. Work issue: https://github.com/danbri/factoidal/issues/799
(stage 1). OKR: https://github.com/danbri/factoidal/issues/801 KR 1.2. Owner,
2026-10-12: "KR1.2 yes". Baseline: SBM11 (owner, 2026-10-12: "Consider smb11
our baseline for shardcore").

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
