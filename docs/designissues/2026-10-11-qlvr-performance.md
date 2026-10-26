# Factoidal/qlvr performance: the Lean implementation against the design

Tracking: https://github.com/danbri/factoidal/issues/778. Format record:
[2026-10-11-qlever-index-format.md](2026-10-11-qlever-index-format.md). Skill:
[`qlvr`](../../skills/qlvr/SKILL.md).

Owner, 2026-10-11, verbatim: "I am interested to see if we can create Lean
that approximates qlever perf avainst native qlever data, so we can work out
why our own efforts are too slow: how much is lean vs approach."

This record measures `l4qlvr` (the Lean QLever reader) against the QLever
server on QLever's own index, separates the cost of the Lean implementation
from the cost of the design, and lists the speed work that the measurements
caused. Each number names the command that produced it.

## Result

- After the changes below, on the warm path, `l4qlvr` answers the four-pattern
  join `q07` in 75 ms against QLever's 19 ms of computation. With libzstd in
  place of the Lean zstd decoder it answers in 23 ms. In `q07`, the Lean zstd
  decoder is 52 of the 75 ms.
- The same algorithm in Lean and in C (the `q07` kernel): Lean is 9 to 16
  times slower than C when the Ids are read and written as bytes of a
  `ByteArray`. Lean is 2.5 to 2.9 times slower than C when each Id is one
  machine word (`FloatArray`, `Array UInt64`). The difference is the access
  to an 8-byte Id in a `ByteArray`. Lean 4.33 has no unboxed 64-bit load or
  store for a `ByteArray`, so each Id costs eight byte accesses, each with
  `Nat` index arithmetic.
- For `q07`, the design difference to QLever is at most 4 ms: with libzstd
  the Lean reader takes 23 ms, QLever 19 to 21 ms. The rest of the gap is
  the Lean implementation.
- Before the changes, most of the time went to costs that were not in the
  design: one process per query (setup 10 to 96 ms), `Nat` shifts that go
  through GMP, one allocation per zstd match, a test per row where the rows
  are one sorted range, a hash-map update per row for `COUNT(*)`, a closure
  call per comparison in ORDER BY, and a JSON tree per output term.

## Method and machine

- Machine: linux x86_64, 4 vCPU Intel Xeon at 2.10 GHz, 15 GB RAM, Ubuntu
  24.04. Lean 4.33.1 (its bundled clang compiles the Lean C). The C kernel:
  gcc 13.3.0 `-O2`. libzstd 1.5.5 (`libzstd.so.1` of the distribution).
  Another agent session used the same machine during part of the runs; the
  tables give medians and repeated runs disagree by up to 15 percent.
- Instance: the olympics dataset, 1,781,625 triples, QLever image at commit
  ceace86 (`tests/qlvr/instance.json`); server on port 7019,
  `MEMORY_FOR_QUERIES = 2G`; the result cache is cleared before every QLever
  run.
- QLever compute: the server's `time.computeResult` for
  `application/qlever-results+json` with `send=0` (no rows exported).
  QLever HTTP: `curl` total time for `application/sparql-results+json`.
- Lean process: wall clock of one `l4qlvr query` process (start, vocabulary
  load, trailers, side index, execution, output).
- Lean warm: `l4qlvr query --repeat N` (new) loads the session once and runs
  the query N times in one process; the median execution time is reported.
  `l4qlvr serve INDEXDIR` (new) reads one query per line of standard input.
- Phase shares: `perf record --call-graph=dwarf` (perf 6.8.12) of
  `l4qlvr query --repeat 20`; the inclusive share of each phase's root
  function. Script used: per query,
  `perf record -F 4999 --call-graph=dwarf,16384 -- l4qlvr query INDEXDIR --file Q.rq --repeat 20`,
  then `perf report --children --sort symbol`.
- Commands: `tests/qlvr/bench-warm.sh` (all 21 queries), `tests/qlvr/kernel.sh`
  (the kernel), `l4qlvr zstd-diff INDEXDIR` (the codec),
  `tests/qlvr/bench.sh` (process times of stage 4).

## The fair comparison: start-up cost

QLever is a running server. `l4qlvr query` starts a process per query and
loads 16 MB of vocabulary files, six permutation trailers and the side-index
header (with an XXH64 of the 4.35 MB offsets file). For the queries that read
almost nothing (`q13`, `q14`, `q15`, `q18`), the process takes 17 to 22 ms
and the execution 0.1 to 0.3 ms (`tests/qlvr/bench-warm.sh`, 2026-10-11).
The `setup` value that `l4qlvr query` prints was 10 to 40 ms over five runs
of `q14`. `l4qlvr serve` loaded the session in 76 ms in one run after other
processes had used the CPU. All comparisons below use the warm figures.

QLever's own split: for `q07`, `computeResult` was 27 ms and `total` 28 ms
in one run; for the queries with large results (`q19` to `q21`), computation
takes 1 to 5 ms and the HTTP answer 188 to 696 ms, because QLever computes
lazily and the rows are serialised during export.

## Per query: before and after

The stage 4 binary (commit 9e82a507) against this commit. Process: median
of 7 runs; warm: `--repeat 20`, median; QLever compute: median of 7, cache
cleared before each:

| Query | QLever compute ms | Lean before, process ms | Lean before, warm ms | Lean after, process ms | Lean after, warm ms | Lean after, warm, libzstd ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q01 count all | 26 | 95 | 62.6 | 19 | 0.0 | 0.0 |
| q04 subject lookup | 3 | 38 | 15.9 | 26 | 7.6 | 1.4 |
| q07 join of four patterns | 19 | 294 | 184.4 | 97 | 74.8 | 22.9 |
| q10 ORDER BY DESC, LIMIT 10 | 22 | 444 | 394.2 | 46 | 25.5 | 10.6 |
| q16 STRSTARTS | 33 | 223 | 201.0 | 144 | 120.1 | 105.4 |
| q21 137,026 rows out | 3 | 906 | 883.9 | 256 | 222.1 | 205.7 |

"Lean before, warm" is the stage 4 engine with the new warm harness (the only
engine change in that binary is the `PermSrc` interface, which does not
change the work).

All 21 queries after the changes (`tests/qlvr/bench-warm.sh`, RUNS=3,
REPEAT=10; decode: the Lean or libzstd decoder time in one warm run):

| Query | Rows | QLever compute ms | QLever HTTP ms | Lean process ms | Lean warm ms | Lean warm libzstd ms | decode ms (Lean / libzstd) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q01-count-all | 1 | 22 | 17 | 20 | 0.0 | 0.0 | 0.0 / 0.0 |
| q02-predicate-counts | 16 | 34 | 34 | 20 | 1.2 | 3.2 | 1.0 / 2.9 |
| q03-scan-bound-predicate-int | 51 | 0 | 2 | 17 | 0.2 | 0.3 | 0.1 / 0.1 |
| q04-subject-lookup | 5 | 3 | 5 | 33 | 7.3 | 1.0 | 7.4 / 0.9 |
| q05-object-bound-type | 51 | 1 | 2 | 71 | 2.3 | 0.7 | 2.1 / 0.5 |
| q06-join-two | 52 | 2 | 4 | 24 | 0.7 | 0.4 | 0.1 / 0.1 |
| q07-join-three | 313 | 21 | 19 | 112 | 80.1 | 22.7 | 65.9 / 10.3 |
| q08-filter-lang-literal | 1 | 1 | 3 | 60 | 42.7 | 34.5 | 19.6 / 3.3 |
| q09-bgp-lang-literal | 1 | 1 | 2 | 24 | 4.4 | 0.9 | 4.2 / 0.7 |
| q10-orderby-limit-double | 10 | 28 | 24 | 46 | 24.2 | 9.6 | 16.8 / 2.5 |
| q11-filter-numeric | 34 | 1 | 3 | 73 | 53.4 | 37.4 | 25.4 / 5.8 |
| q12-group-medals | 3 | 2 | 4 | 35 | 6.3 | 3.7 | 3.0 / 0.5 |
| q13-subclass-of | 10 | 0 | 2 | 20 | 0.3 | 0.3 | 0.1 / 0.1 |
| q14-typed-int-object | 2 | 0 | 2 | 19 | 0.1 | 0.1 | 0.1 / 0.1 |
| q15-integer-object-matches-int | 2 | 0 | 2 | 21 | 0.1 | 0.1 | 0.1 / 0.1 |
| q16-strstarts | 5 | 34 | 35 | 208 | 115.6 | 101.9 | 19.2 / 3.1 |
| q17-noc-team-join | 1 | 3 | 4 | 29 | 5.3 | 1.1 | 5.8 / 0.8 |
| q18-games-by-year-limit | 5 | 0 | 2 | 18 | 0.2 | 0.1 | 0.1 / 0.1 |
| q19-scan-bound-predicate-iri | 39,768 | 2 | 200 | 125 | 87.7 | 77.3 | 5.7 / 1.1 |
| q20-scan-bound-predicate-double | 100,666 | 2 | 397 | 199 | 171.2 | 163.6 | 16.2 / 2.9 |
| q21-scan-bound-predicate-lang | 137,026 | 3 | 696 | 325 | 235.0 | 201.2 | 23.2 / 3.1 |

The same table before the changes (stage 4 engine, warm harness): `q07`
195.4 ms warm (163 ms decode), `q10` 443.6, `q16` 215.3, `q19` 317.1, `q20`
680.6, `q21` 903.6, `q01` 64.5, `q02` 167.7, `q11` 91.5, `q08` 75.8.

Every output after the changes is byte-identical to the stage 4 output on all
21 queries (a `cmp` of `l4qlvr query` stdout, old binary against new), and
`tests/qlvr/queries.sh` gives 21 pass, 0 fail, 0 refused (out of 21).

## Where the time goes: phases

Inclusive share of the warm run (`--repeat 20`, Lean decoder), from
`perf report --children`:

| Query | Phase | Before | After |
| --- | --- | ---: | ---: |
| q07 | zstd decode (`Zstd.decompress`) | 84 % | 81 % |
| q07 | joins (`mergeJoin` + `hashJoin`) | 9 % | 13 % |
| q07 | appending scan blocks (`Table.append`) | 1.8 % | 1.2 % |
| q07 | rendering SPARQL JSON | 1.2 % | below 0.5 % |
| q07 | `pread` | 0.6 % | 1.1 % |
| q10 | ORDER BY (`mergeSortBy` with a closure comparator, before; `orderPerm`, after) | about 50 % | 29 % |
| q10 | zstd decode | 10 % | 65 % |
| q16 | FILTER STRSTARTS (word decode and test) | 68 % | 78 % |
| q16 | zstd decode | 26 % | 17 % |
| q01 | COUNT, one hash-map update per row (`countGroups`) | 93 % | below 0.5 % |
| q04 | zstd decode | 88 % | 60 % |

(After the changes `q01` executes in 0.05 ms; its profile is the session
load. `q04` executes in 7 ms; a quarter or more of its profile is the session load.)

Lean runtime costs, as a share of self time (same profiles; allocation
includes `malloc`, `free`, mimalloc and the kernel clearing new pages):

| Query | Allocation and page clearing | `Nat` through GMP | `ByteArray.push`, `copySlice`, memmove | Closure calls and boxing |
| --- | ---: | ---: | ---: | ---: |
| q07 before / after | 34.8 % / 11.4 % | 12.0 % / 3.2 % | 9.5 % / 14.5 % | 0.1 % / 0 % |
| q10 before / after | 31.8 % / 27.4 % | 1.2 % / 2.2 % | 1.5 % / 9.6 % | 21.3 % / 0 % |
| q16 before / after | 35.4 % / 28.8 % | 3.5 % / 0.6 % | 18.1 % / 10.3 % | 1.3 % / 1.8 % |
| q04 before / after | 39.2 % / 48.0 % | 10.7 % / 3.1 % | 7.7 % / 8.4 % | 0.2 % / 0 % |

## The codec: Lean zstd against libzstd

`l4qlvr zstd-diff INDEXDIR` (new) decodes each of the 1,860 column frames
(22,232,169 bytes in, 499,663,936 bytes out) with the Lean decoder and with
libzstd in the same process, compares the outputs byte for byte and times
each decoder. Result: 1,860 pass, 0 fail (out of 1,860).

| Decoder | Time | Output rate |
| --- | ---: | ---: |
| Lean, stage 4 | 4,007 ms | 124 MB/s |
| Lean, + `UInt64` shift for the offset code, byte-wise copy of matches of up to 32 bytes, output reserved from the frame size | 2,324 ms | 214 MB/s |
| Lean, + one bounds test per `word64` | 2,283 ms | 218 MB/s |
| Lean, + bit position, states and repeat offsets of the sequence loop as `UInt64` | 1,768 to 2,001 ms | 249 to 282 MB/s |
| libzstd 1.5.5 | 309 to 336 ms | 1,486 to 1,612 MB/s |

The Lean decoder is 5.5 to 6.5 times slower than libzstd on these frames.
Its profile after the changes (`perf record` of `zstd-diff`, which also
runs libzstd; self time): `seqLoop` 29 %, byte-wise match copy (`pushCopy`
15 % and `lean_byte_array_push` 8 %), Huffman literals 5 %, `copySlice` 4 %.
Before the `UInt64` change, the annotated `seqLoop` had no single slow
instruction: most of its instructions boxed, unboxed and tested `Nat`
values.

Codec effect per query (warm, Lean decoder against libzstd): `q07` 80.1
against 22.7 ms, `q04` 7.3 against 1.0, `q10` 24.2 against 9.6, `q11` 53.4
against 37.4, `q16` 115.6 against 101.9 (`tests/qlvr/bench-warm.sh`).

The libzstd path is `ffi/qlvr_zstd.c`: `l4_zstd_decompress` loads
`libzstd.so.1` with `dlopen` at the first call, so the build needs no zstd
headers and a host without libzstd still builds; `l4qlvr query --libzstd`
uses it, the default is the Lean decoder. `tests/qlvr/run.sh` part (j) runs
`zstd-diff` (not scored when libzstd cannot be loaded).

## The kernel: the same algorithm in Lean and in C

`tests/qlvr/kernel.sh` dumps the decoded input of the hot part of `q07`
(`l4qlvr kernel-dump`: 31,250 rows of the POS blocks for `wso:medal` Gold,
269,625 rows of the PSO blocks for `wso:athlete`) and runs: keep the A rows
with (col0, col1) = (medal, Gold), keep the B rows with col0 = athlete,
merge join on `?i`. Output 13,369 rows; every implementation gives the same
checksum. Median of 30 runs, three script runs:

| Implementation | Representation | Median ms (three runs) | Times C |
| --- | --- | ---: | ---: |
| Lean, stage 4 code (`selectRows` + `mergeJoin` of stage 4) | `ByteArray` columns, `word64` with a test per byte, `Side.put64` | 36.6, 37.4 | 16 |
| Lean, stage 4 `selectRows` + new `mergeJoin` (`current`) | as above | 32.4 to 34.9 | 14 to 15 |
| Lean `bytes-push` | `ByteArray`, one bounds test per Id, 8 `push` per Id | 23.8 to 25.8 | 10 to 11 |
| Lean `bytes-set` | `ByteArray`, writes by `set!` into a buffer of known size | 20.7 to 22.4 | 9.0 to 9.6 |
| Lean `floats` | `FloatArray`, one 8-byte slot per Id (`Float.ofBits`/`toBits`) | 5.7 to 6.7 | 2.5 to 2.9 |
| Lean `native` | `Array UInt64` (each element a boxed object) | 6.1 to 6.8 | 2.7 to 2.9 |
| C `-O2` | `uint64_t` arrays | 2.05 to 2.38 | 1 |
| Lean `production` (range by binary search, then `mergeJoin`) | `ByteArray` | 9.0 to 9.2 | 3.9 (against C range) |
| C `-O2`, range | `uint64_t` arrays | 2.34 to 2.38 | 1 |

What this shows:

- For the same algorithm, the Lean cost is in the Id access. `bytes-set`
  and `floats` run the same loop structure; the first reads each Id as 8
  bytes with `Nat` index arithmetic (each `+` tests for a big number, each
  index is boxed and unboxed) and is 3.4 to 3.9 times slower than the
  second, which reads one 8-byte slot. `lean_byte_array_push` is an
  out-of-line call in Lean 4.33 (`lean.h` line 1195), so 8 pushes per Id are
  8 calls.
- With one machine word per Id, Lean is within 3 times of C. The remainder
  is the out-of-line `Float.ofBits`/`toBits` and `FloatArray.push`
  (`lean.h` lines 1260, 3175-3176), and for `Array UInt64` one allocation
  per element.
- The production code changed the algorithm (range search, gather by runs)
  and moved Lean from 16 times to 3.9 times C. In C the range search saves
  nothing measurable (2.3 ms both ways), so this change removed Lean cost,
  not design cost.

## The remainder against QLever, with causes

After the codec is replaced by libzstd, `q07` takes 22.9 ms in Lean and 19
to 21 ms in QLever: the Lean implementation of the join and scan (3.9 times
C in the kernel) is the visible remainder. Design differences that QLever's
source shows, at commit ceace86, and where they act:

| QLever design | Source | Effect here |
| --- | --- | --- |
| Columns decompressed into a block buffer it allocated (`ZstdWrapper::decompressToBuffer`, `decompressBlock`) | `src/util/CompressionUsingZstd/ZstdWrapper.h:105-110`, `src/index/CompressedRelationReader.cpp:752-761` | Lean allocates a new `ByteArray` per frame; with libzstd, `q07` still spends 10 ms in the decode step for 8.7 MB, about 850 MB/s against libzstd's 1,500 MB/s in `zstd-diff`. Allocation and page clearing are 11 % of the `q07` profile. |
| Galloping join when one side is 1,000 times larger | `src/engine/JoinImpl.cpp:349-362`, `src/global/Constants.h:40` | Not used in `q07` (ratio 20); the Lean reader has only merge and hash joins. |
| Distinct col0 values and counts from block metadata when a block holds one value | `src/index/CompressedRelationReader.cpp:618`, `:684-697` | The Lean reader now counts `COUNT(*)` from block row counts and groups by runs (`q01` 0.05 ms, `q02` 1.2 ms against QLever 22 and 34 ms). |
| STRSTARTS gives a prefilter on block metadata from the vocabulary's prefix range | `src/engine/sparqlExpressions/StringExpressions.cpp:245-275`, `src/engine/sparqlExpressions/PrefilterExpressionIndex.cpp:488-529` | The Lean reader decodes every label (two FSST passes) and tests it: `q16` 116 ms against 34 ms. Not separated into Lean and design cost: there is no C FSST measurement here. |
| Lazy computation: rows are produced during export | `computeResult` against the HTTP time above | For `q19` to `q21` QLever computes in 1 to 5 ms and answers over HTTP in 188 to 696 ms; the Lean reader writes the whole SPARQL JSON in 88 to 235 ms warm. |
| Result cache | cleared in every measurement here | none |

## Speed work done, each with its measured effect

All changes keep the output byte-identical (above) and the pure Lean
decoder the default.

1. Warm session (`Harness/Qlvr.lean`): `query --repeat N`, `serve`. Removes
   17 to 22 ms of process and load time per query (table above).
2. zstd (`L4Factoidal/Codec/Zstd.lean`): the offset-code shift in `UInt64`
   (the `Nat` shift called `lean_nat_shiftl` and GMP: GMP and `lean_nat_*`
   were 12 % of the stage 4 warm `q07` profile); matches of up to 32 bytes copied byte-wise into the
   unique output (`pushCopy`), longer ones as before; the output reserved
   from the expected size; the sequence loop's position, states and repeat
   offsets in `UInt64`. 124 to 249-282 MB/s.
3. Scans (`L4Factoidal/Qlvr/Bgp.lean`): in a block that is not full, the
   rows with the key prefix are one range, found by two binary searches
   (`keyRange`) and copied with `extract`, in place of a test per row; scan
   columns reserved from the metadata estimate.
4. Joins: pairs of row indices, then each output column gathered with one
   `copySlice` per run of consecutive rows (`gather`); a hash join on one
   shared variable keys a `UInt64` instead of a `List UInt64`.
5. COUNT and GROUP BY (`Query.countGroups`): no group variable adds the
   block's row count; one group variable counts runs (binary search when the
   table is sorted by it). `q01` 62.6 to 0.0 ms, `q02` 167.7 to 1.2 ms.
6. ORDER BY (`Query.orderPerm`): a `UInt64` sort key per row when the column
   has one datatype tag (and no NaN), a stable sort per key from the last
   condition to the first, and with LIMIT (no DISTINCT) a single pass that
   keeps the first OFFSET + LIMIT rows (`topK`); otherwise the reference
   comparison. `q10` 394.2 to 25.5 ms.
7. FILTER string functions (`Query.strTestBytes`): the test on the word's
   bytes, no `String` per row.
8. FSST: symbols appended by up to 8 pushes in place of one `copySlice`
   call per symbol.
9. SPARQL JSON (`Query.renderBytes`): written as bytes, escaped in runs,
   without a `Term` or `Json` value per term. `renderLoop` stays as the
   reference: `l4qlvr query --reference-render`, and `tests/qlvr/run.sh`
   part (i) checks that both give byte-identical output on the 21 queries.
   `q21` 883.9 to 222.1 ms (with items 2, 3 and 8).

## Follow-up: the Lean-to-C record (2026-10-12)

[2026-10-12-lean-to-c-performance.md](2026-10-12-lean-to-c-performance.md)
measures C compiler options (O2, `-march=native`, LTO, PGO) on the same
binary, audits the generated C of the kernel and zstd loops, and shows that
`USize` indices with `ByteArray.uget` compile to one 8-byte load: the kernel
goes from 31.4 ms (`bytes-set`) to 11.3 ms in pure Lean and to 5.8 ms with
one inline-C store (C 4.3 to 8.8 ms in the same rounds, at a higher machine
load than the tables above). The decoder's bit reader and short-match copy
now use the same idiom (`word64U`, `pushCopyU`, with equality theorems).

## What did not work or was not done

- One bounds test per `word64` in place of one per byte: 214 to 218 MB/s,
  inside the noise. The cost is the `Nat` arithmetic, not the tests.
- `ByteArray` with `set!` into a buffer of known size, in place of `push`:
  about 13 percent faster in the kernel (`bytes-set` 20.7 to 22.4 ms against
  `bytes-push` 23.8 to 25.8 ms);
  not used in the zstd decoder, because the frame checks use the output size.
- A `FloatArray` column representation would remove most of the kernel's
  Lean cost (2.5 to 2.9 times C), but the Lean zstd decoder writes bytes and
  converting costs one `word64` per Id; it was not adopted.
- QLever's STRSTARTS prefilter and galloping join are not implemented.
- The vocabulary is still read whole at session start (16 MB).

## What this means for Shardborough

- The process-per-query harness hid the engine: setup was 17 to 110 ms of
  every query. A Shardborough latency figure needs the warm path (a session
  that keeps the collection open) next to the process figure, and the
  disk-resident path, as the 2026-10-11 rule in `CLAUDE.md` requires.
- A pure Lean block codec costs 5.5 to 6.5 times libzstd. A storage
  format whose blocks need a general-purpose decoder per access pays that
  factor on every query; formats that a query can use without decoding
  (fixed-width Ids, a range found by binary search) avoid it, as `keyRange`
  does here.
- Ids stored as 8 bytes in a `ByteArray` and read with `Nat` indices cost
  about 3.5 times more than one machine word per Id in Lean, and 9 to 16
  times C. Shardborough's hot loops should use a word-per-Id representation
  or extend the trusted host boundary with a load primitive; either choice
  needs its own measurement and its own record.
- Most of the stage 4 gap was in avoidable per-row work (a test, a hash-map
  update, a closure call or an allocation per row). The same audit applies
  to the Shardborough query path before any change to its storage design.

## Commands

```
cd formal/lean4 && lake build l4qlvr
.lake/build/bin/l4qlvr zstd-diff /home/user/qlvr-work/instance
.lake/build/bin/l4qlvr query /home/user/qlvr-work/instance --file ../../tests/qlvr/queries/q07-join-three.rq --repeat 20 [--libzstd]
.lake/build/bin/l4qlvr serve /home/user/qlvr-work/instance < queries.txt
tests/qlvr/bench-warm.sh          # from the repository root; needs the server on port 7019
tests/qlvr/kernel.sh              # Lean kernel implementations and the C reference
tests/qlvr/run.sh                 # parts (i) render and (j) zstd-diff added
```
