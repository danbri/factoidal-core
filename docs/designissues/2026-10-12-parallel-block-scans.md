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
  (section 5). The 10x dataset was not measured: it is not in place.
  The issue's target (4 threads at most 0.4 of 1 thread on q07, q19, q21, on
  the 10x dataset) is not met on olympics and is not measured on the 10x
  dataset.

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
  not measured; not in place on 2026-10-12.
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
