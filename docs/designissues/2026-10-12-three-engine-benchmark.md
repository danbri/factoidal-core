# SBM11, Virtuoso 7.2 and QLever on olympics and a 23 M triple DBpedia slice

Date: 2026-10-12. Status: record (measurement). Work issue (OKR batch 2,
KR 1.1): https://github.com/danbri/factoidal/issues/798. Owner, 2026-10-12:
"bench yes", after the question "Are we becoming comparable to virtuoso and
qlever yet?"; and "Consider smb11 our baseline for shardcore." Script:
`tools/bench/three-engines/run.sh`. How to rerun: skill `perf-benchmarking`,
section "SBM11 against Virtuoso and QLever".

## 1. Result

- Answer check: DBpedia slice 17 of 17 queries equal on SBM11 and Virtuoso.
  Olympics 19 of 21 equal on SBM11, Virtuoso and the QLever oracle; 2 differ
  and are not timed (section 5). No difference is an SBM11 defect.
- On-disk size: SBM11 is 3.1 times smaller than Virtuoso on the DBpedia
  slice (567.7 MB against 1,746.9 MB) and 3.8 times smaller on olympics.
- Load: the SBM11 pack is 6.6 times slower than the Virtuoso bulk load on the
  DBpedia slice (1,334 s against 203 s). 60 % of the pack (799 s) is phase 2,
  the merge of the term runs, which grows about with the square of the number
  of distinct terms (section 8, item 1). After the repair of section 8 item 1 the pack
  took 288 s (phase 2 26 s).
- Warm queries (SBM11 execution in one process against one Virtuoso HTTP
  request): SBM11 is faster on scans and aggregates over large ranges
  (DBpedia d10, d13, d16, d17: 5.9 to 14 times faster than Virtuoso with its
  default threads) and on selective lookups. Virtuoso is faster on every join:
  3.6 to 26 times on d05 to d09, d12, d14, d15. OPTIONAL (d11) runs in the
  SBM11 reference fallback: 48.7 s and 849 MB, against 19 ms in Virtuoso.
- Process and cold times of SBM11 on the DBpedia slice are 41 to 582 ms for
  queries whose warm time is under 1 ms: each process reads the PRM1 block
  metadata whole (section 8, item 3).
- QLever (image-extracted binaries, ceace86; section 11): on olympics, index
  4.7 s, 285 MB peak RSS, 38.5 MB on disk; answers 19 of 21 equal to SBM11,
  Virtuoso and the oracle (q15 and q20: the two causes of section 5); warm
  median 1.8 to 591 ms. On the DBpedia slice (section 11.8): index 56.5 s,
  2,069 MB peak RSS, 872.5 MB on disk; answers 17 of 17 equal to SBM11 and
  Virtuoso; warm median 1.9 to 248 ms. QLever is faster than SBM11 warm on
  every join (6.4 to 13 times on d05 to d09) and on d11 to d17; SBM11 is
  faster on the lookups d01 to d04 and on d10.
- 2026-10-13, sideways information passing on the SBM11 id path (section
  11.9, https://github.com/danbri/factoidal/issues/809): SBM11 warm d05 365
  to 76 ms, d07 77 to 8.8 ms, d11 19.3 to 8.4 ms, peak RSS lower or equal
  (d05 83 to 27 MB); faster than QLever warm on d06, d07, d09 and d11,
  slower on d05 (76 against 43 ms), d08, d12, d14 and d15.

## 2. Engines

| Engine | Version | Configuration |
| --- | --- | --- |
| SBM11 | `l4sbm11` and `l4sbm11-pack` built from commit 408898bd (Lean `v4.33.1`) | `--verify none` and `--verify merkle`; query path single-threaded; packer 4 workers (default) |
| Virtuoso Open Source | 7.2.5.3229 (Ubuntu package `virtuoso-opensource-7` 7.2.5.1+dfsg1-0.8build1), native | ini written by `bench.py`: 340,000 buffers (about 2.8 GB), `MaxDirtyBuffers` 250,000, no result-row cap, no execution-time cap; thread configurations `1t` (`ThreadsPerQuery` 1, `AsyncQueueMaxThreads` 1) and `default` (4 and 10, the package values) |
| QLever | image-extracted (Docker Hub adfreiburg/qlever, ceace86): `qlever-index` and `qlever-server` from `/home/user/qlever-image/rootfs/qlever` (image digest `b2087ec9...`) | olympics and DBpedia slice measured 2026-10-12 (section 11); server result cache off; the source build was stopped by the owner |

Virtuoso loads with `ld_dir`, one `rdf_loader_run()` and `checkpoint`, into a
named graph; every query is sent with `default-graph-uri` set to that graph,
so Virtuoso's system graphs are not in the default graph. With a cap on
execution time, Virtuoso returns a partial answer with an `X-SQL-State`
header; the cap is off, and `bench.py` counts any such header as a failure
(none occurred).

## 3. Machine

Firecracker VM, kernel 6.18.44-fc. CPU: Intel Xeon @ 2.80 GHz, 4 vCPU. RAM:
16,479,424 kB, no swap. Disk: virtio block device `vda`, 256 GB (the guest
reports it as rotational; the physical medium is not known). The machine is
shared with one other agent; the 1-minute load average is in every table.

## 4. Datasets

| Dataset | Source | Licence | Triples | sha256 of the N-Triples file |
| --- | --- | --- | ---: | --- |
| olympics | https://github.com/wallscope/olympics-rdf at commit 54483d5 (skill `qlvr`) | as the qlvr record | 1,781,625 | `44e15095a3a9beefe09c512882a08d9b7aa82bba5e48fa22bfbfb361dde01ce0` |
| DBpedia 2016-10 slice | https://downloads.dbpedia.org/2016-10/core-i18n/en/mappingbased_objects_en.ttl.bz2 (sha256 `a5811aa5...c9953`) and `mappingbased_literals_en.ttl.bz2` (sha256 `0d0d6b55...d518`) | CC BY-SA 3.0 and GFDL (DBpedia 2016-10 release) | 23,269,560 lines, 23,269,559 distinct triples (13.1 times olympics) | `94025f74d5c4643ce05984524e5583c59a057b8110544ec9a7c55fbd21de85e1` |

Slice rule (`tools/bench/three-engines/slice.py`): every statement of
`mappingbased_objects_en` (18,746,174), and the statements of
`mappingbased_literals_en` with predicate `foaf:name`, `dbo:birthDate`,
`dbo:deathDate` or `dbo:populationTotal` (4,523,386); a statement with an IRI
that is not an N-Triples IRIREF is dropped (0 dropped). The file is 3.12 GB.

## 5. Queries and answer check

Olympics: the 21 qlvr oracle queries (`tests/qlvr/queries`, copied to
`tools/bench/three-engines/queries/olympics`). DBpedia slice: 17 queries in
`tools/bench/three-engines/queries/dbpedia`:

| Query | Shape |
| --- | --- |
| d01, d02, d03, d04 | selective lookup: subject; object; predicate and object; language-tagged literal object |
| d05, d06 | star join (three patterns on one subject) |
| d07, d08 | path join, two and three hops |
| d09, d10 | aggregate with GROUP BY (after a join; over every triple) |
| d11 | OPTIONAL |
| d12, d13, d14 | FILTER on a numeric literal, STRSTARTS, an `xsd:date` |
| d15, d16 | ORDER BY with LIMIT (after a join; over a whole predicate) |
| d17 | COUNT(*) over every triple |

Comparison (`bench.py`, `term_key`): each answer is a multiset of solutions.
IRIs by value; blank nodes all equal (no blank nodes occur in the answers);
language-tagged literals by lexical form and lower-cased tag; numeric literals
(the integer types, decimal, double, float) by value printed with 12
significant digits (QLever and Virtuoso do not keep the input datatype or
lexical form of numbers); `xsd:string` and simple literals by lexical form;
other literals by lexical form and datatype. SBM11 `--verify none` and
`--verify merkle` gave byte-identical answers on all 38 queries.

| Dataset | Equal | Different (not timed) |
| --- | ---: | --- |
| olympics | 19 of 21 | q15, q20 |
| DBpedia slice | 17 of 17 | none |

Causes of the two differences:

- **q15** `?g dbp:year 1936`: SBM11 0 rows, Virtuoso 2, QLever 2. The data
  says `"1936"^^xsd:int`; the query constant is `"1936"^^xsd:integer`. These
  are different RDF terms, and SPARQL 1.1 basic graph pattern matching under
  simple entailment (section 18.3) matches terms, so 0 rows conforms. Virtuoso
  and QLever match the value. Not a Factoidal defect (SBM11 stage 4 record,
  section 2.2).
- **q20** `?s dbo:weight ?o` (100,666 rows): 2 rows differ. Virtuoso's SPARQL
  JSON writer prints `xsd:double` with 6 significant digits (`74.6667` for
  74.66666666666667); SBM11 and QLever agree at 12 digits. Not a Factoidal
  defect.

Per-query row counts and SBM11 paths: `report.md` from `run.sh` (all
`path=ids` except d11, `path=reference`).

## 6. Method

- **Order.** `run.sh` steps: data, pack, load, answers, timing, report. Each
  timing phase starts one Virtuoso thread configuration (`1t`, then
  `default`). Phase `1t` times SBM11 `none`, SBM11 `merkle` and Virtuoso;
  phase `default` times SBM11 `none` and Virtuoso (the SBM11 columns below are
  from phase `1t`).
- **Cold.** The page cache cannot be dropped here (writing
  `/proc/sys/vm/drop_caches` was refused). A cold run is the first run in a
  new process after the engine's own files were evicted with
  `posix_fadvise(POSIX_FADV_DONTNEED)`: SBM11, a new `l4sbm11 query` process
  after eviction of the generation; Virtuoso, the first query of a new server
  process started after eviction of `virtuoso.db`. `mincore` gave 0 resident
  bytes of those files in all 432 checks (one per engine, query and cold
  round). Median of 3 cold rounds.
- **SBM11 process.** Wall time of one `l4sbm11 query` process (start,
  manifest, PRM1 files, plan, scans, SPARQL JSON to `/dev/null`), median of 7
  rounds.
- **SBM11 warm.** The execution median that `l4sbm11 query --repeat 5`
  reports (the opened permutations and caches kept between runs), median over
  7 rounds. d11 (process over 5 s): 3 rounds, warm is the faster of 2 runs.
- **Virtuoso warm.** Client wall time of one HTTP POST to `/sparql` on
  localhost, from the request to the last byte of the SPARQL JSON response,
  median of 7 rounds after one warm-up pass. It includes parsing, compiling,
  HTTP and JSON (about 2 to 3 ms for a 1-row answer).
- **RSS.** SBM11: VmHWM of the query process, maximum over the rounds.
  Virtuoso: VmHWM of the server, reset (`/proc/PID/clear_refs` 5) before each
  request, maximum over the rounds; it includes the resident buffer pool.
  Load: VmHWM of the packer (`wait4`) and of the Virtuoso server since its
  start.
- **Interleaving and load.** In each round every query runs on every engine,
  with the engine order rotated per query and round. Before each round the
  driver waits up to 90 s for the 1-minute load average to fall under 2.0 and
  records it. Every round started under 2.0 (ranges in the tables). The
  load and pack steps ran at load 0.8 to 4.5 (the other agent).

## 7. Tables

### 7.1 Load

| Dataset | Engine | load s | peak RSS MB | on-disk MB | triples | load avg before / after |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| olympics | SBM11 `l4sbm11-pack` (4 workers) | 39.2 | 195 | 34.8 | 1,781,625 | 1.14 / not recorded |
| olympics | Virtuoso bulk load (1 loader) + checkpoint | 14.5 | 970 | 132.1 | 1,781,625 | 1.61 / 2.73 |
| olympics | QLever `qlever index` (recorded 2026-10-11) | 4.35 | 250 | 38.5 | 1,781,625 | not recorded |
| DBpedia slice | SBM11 `l4sbm11-pack` (4 workers) | 1,334.3 | 552 | 567.7 | 23,269,559 | 0.80 / 2.66 |
| DBpedia slice | Virtuoso bulk load (1 loader) + checkpoint | 202.7 | 2,871 | 1,746.9 | 23,269,559 | 2.04 / 4.53 |
| DBpedia slice | QLever `qlever-index -p true -j 4 -m 4G` (image-extracted, ceace86; section 11.8) | 56.5 | 2,069 | 872.5 | 23,269,559 | 0.16 / 3.37 |

SBM11 pack phases, DBpedia slice (ms): parse 211,843; term-run merge
799,203; remap and sort 259,695; permutation merge and blocks 44,272; hashes
and manifest 19,264. 8,877,307 distinct non-inline terms. Virtuoso on-disk
size is `virtuoso.db` plus `virtuoso-temp.db` after checkpoint and shutdown;
it includes the database's own system tables (not subtracted).

### 7.2 Olympics (19 queries)

Load average at round start: phase `1t` 0.76 to 1.98, phase `default` 1.89
to 1.98. Times in ms; RSS in MB.

| Query | SBM11 none cold / process / warm | RSS | SBM11 merkle cold / process / warm | RSS | Virtuoso 1t cold / warm | RSS | Virtuoso default cold / warm | RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q01-count-all | 24.7 / 19.9 / 0.34 | 15 | 25.2 / 20.6 / 0.34 | 17 | 21.4 / 21.60 | 280 | 27.2 / 23.44 | 288 |
| q02-predicate-counts | 60.8 / 18.3 / 1.69 | 15 | 51.4 / 36.6 / 1.78 | 19 | 100.5 / 84.50 | 280 | 88.0 / 86.21 | 288 |
| q03-scan-bound-predicate-int | 24.5 / 18.0 / 0.49 | 17 | 48.2 / 44.7 / 0.40 | 19 | 27.9 / 4.97 | 280 | 31.4 / 5.19 | 288 |
| q04-subject-lookup | 41.9 / 43.8 / 0.22 | 17 | 92.8 / 74.6 / 0.11 | 21 | 14.2 / 2.90 | 280 | 10.9 / 2.88 | 288 |
| q05-object-bound-type | 23.2 / 17.1 / 0.70 | 17 | 66.7 / 59.1 / 0.41 | 21 | 10.6 / 3.58 | 280 | 9.8 / 3.19 | 288 |
| q06-join-two | 24.3 / 18.1 / 0.94 | 17 | 48.4 / 45.7 / 0.49 | 19 | 45.2 / 5.32 | 280 | 38.8 / 4.03 | 288 |
| q07-join-three | 206.7 / 88.6 / 53.11 | 23 | 466.3 / 322.6 / 54.32 | 33 | 390.5 / 16.08 | 280 | 450.5 / 14.79 | 288 |
| q08-filter-lang-literal | 95.4 / 38.7 / 15.45 | 21 | 152.6 / 86.9 / 14.34 | 23 | 65.0 / 2.82 | 280 | 68.1 / 2.44 | 288 |
| q09-bgp-lang-literal | 42.3 / 17.3 / 0.50 | 15 | 86.8 / 65.6 / 0.22 | 21 | 65.8 / 2.45 | 280 | 97.6 / 2.42 | 288 |
| q10-orderby-limit-double | 45.0 / 60.6 / 26.58 | 23 | 102.4 / 98.2 / 24.41 | 25 | 361.9 / 218.63 | 280 | 239.2 / 92.16 | 288 |
| q11-filter-numeric | 123.3 / 72.8 / 40.96 | 21 | 184.7 / 171.2 / 40.74 | 23 | 65.6 / 3.48 | 280 | 60.9 / 3.38 | 288 |
| q12-group-medals | 71.2 / 28.4 / 7.33 | 17 | 96.9 / 69.8 / 7.05 | 19 | 86.3 / 4.68 | 280 | 89.9 / 4.36 | 288 |
| q13-subclass-of | 33.5 / 16.9 / 0.32 | 17 | 129.5 / 43.2 / 0.15 | 19 | 5.0 / 2.81 | 280 | 5.1 / 2.38 | 288 |
| q14-typed-int-object | 19.4 / 19.3 / 0.48 | 15 | 110.0 / 45.9 / 0.36 | 19 | 16.4 / 2.39 | 280 | 18.7 / 2.29 | 288 |
| q16-strstarts | 63.3 / 42.4 / 22.64 | 21 | 107.9 / 122.5 / 21.65 | 25 | 285.8 / 212.79 | 280 | 210.1 / 84.90 | 288 |
| q17-noc-team-join | 25.9 / 18.1 / 0.76 | 17 | 82.1 / 54.7 / 0.45 | 21 | 121.2 / 2.38 | 280 | 103.1 / 2.60 | 288 |
| q18-games-by-year-limit | 18.0 / 17.7 / 0.37 | 17 | 47.0 / 40.4 / 0.24 | 19 | 30.6 / 2.79 | 280 | 29.4 / 3.10 | 288 |
| q19-scan-bound-predicate-iri | 232.9 / 207.6 / 162.38 | 35 | 462.9 / 452.6 / 114.95 | 47 | 918.0 / 823.19 | 280 | 950.1 / 917.88 | 288 |
| q21-scan-bound-predicate-lang | 423.2 / 326.0 / 281.30 | 27 | 691.4 / 578.2 / 270.38 | 37 | 4,801.1 / 5,249.84 | 281 | 4,827.0 / 5,364.31 | 289 |

QLever on olympics, recorded 2026-10-11 (`tests/qlvr/bench.sh`, the qlvr
format record section "Measurements"; same machine, not re-measured today):
`curl` time of a warm HTTP request with the result cache cleared, median of
3, default server threads, no load average, no cold time, no server RSS. In
ms: q01 15, q02 37, q03 3, q04 5, q05 3, q06 5, q07 19, q08 3, q09 3, q10 18,
q11 4, q12 4, q13 2, q14 2, q16 37, q17 4, q18 3, q19 198, q21 717.

### 7.3 DBpedia slice (17 queries)

Load average at round start: phase `1t` 1.01 to 1.96, phase `default` 1.00
to 1.41. Times in ms; RSS in MB.

| Query | SBM11 none cold / process / warm | RSS | SBM11 merkle cold / process / warm | RSS | Virtuoso 1t cold / warm | RSS | Virtuoso default cold / warm | RSS |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| d01-subject-lookup | 582.3 / 483.8 / 0.24 | 41 | 761.6 / 748.0 / 0.11 | 45 | 60.0 / 3.54 | 891 | 67.3 / 3.42 | 682 |
| d02-object-lookup | 512.1 / 306.5 / 0.28 | 33 | 592.7 / 573.7 / 0.14 | 37 | 197.5 / 3.52 | 891 | 177.5 / 3.26 | 682 |
| d03-predicate-object | 215.1 / 75.3 / 2.35 | 23 | 3,015.7 / 2,832.3 / 1.62 | 67 | 440.1 / 20.11 | 891 | 497.1 / 22.67 | 682 |
| d04-lang-literal-lookup | 77.9 / 41.4 / 0.62 | 17 | 488.3 / 318.6 / 0.32 | 27 | 794.2 / 4.54 | 891 | 698.6 / 3.62 | 682 |
| d05-star-three | 1,100.1 / 672.0 / 574.79 | 83 | 7,111.8 / 6,962.6 / 609.22 | 135 | 1,816.0 / 54.90 | 875 | 1,939.9 / 48.92 | 682 |
| d06-star-film | 235.4 / 147.9 / 67.77 | 25 | 2,138.2 / 1,862.1 / 66.83 | 51 | 405.5 / 8.58 | 875 | 437.7 / 7.24 | 682 |
| d07-path-two-hops | 382.0 / 209.4 / 136.34 | 37 | 1,501.0 / 1,331.3 / 143.45 | 51 | 410.7 / 5.34 | 875 | 433.7 / 6.33 | 682 |
| d08-path-three-hops | 602.1 / 245.6 / 152.05 | 41 | 4,525.9 / 3,931.1 / 213.30 | 83 | 757.3 / 44.07 | 875 | 778.1 / 42.72 | 682 |
| d09-group-birthplace | 257.0 / 165.5 / 75.84 | 27 | 1,101.0 / 885.4 / 75.22 | 45 | 261.2 / 3.61 | 875 | 303.0 / 3.71 | 682 |
| d10-group-predicates | 119.7 / 94.7 / 42.55 | 21 | 935.6 / 974.6 / 46.60 | 37 | 1,314.5 / 1,123.97 | 875 | 484.8 / 355.68 | 682 |
| d11-optional | 49,632.6 / 50,688.7 / 48,732.18 | 849 | 52,925.4 / 57,349.3 / 47,407.98 | 961 | 633.6 / 19.07 | 875 | 621.8 / 21.12 | 682 |
| d12-filter-numeric | 210.8 / 158.6 / 49.69 | 25 | 986.2 / 919.2 / 58.90 | 37 | 328.9 / 8.62 | 875 | 394.5 / 8.02 | 682 |
| d13-filter-strstarts | 700.2 / 642.3 / 557.62 | 19 | 2,124.3 / 2,098.2 / 557.55 | 45 | 4,332.5 / 3,754.06 | 879 | 4,679.8 / 3,736.20 | 682 |
| d14-filter-date | 300.1 / 179.3 / 81.30 | 29 | 1,079.5 / 1,038.6 / 88.88 | 45 | 460.0 / 6.78 | 881 | 485.0 / 7.94 | 682 |
| d15-orderby-limit | 163.1 / 132.3 / 42.18 | 25 | 638.0 / 476.3 / 39.22 | 35 | 559.4 / 9.15 | 883 | 583.2 / 9.85 | 682 |
| d16-orderby-limit-scan | 327.6 / 279.8 / 79.77 | 37 | 484.4 / 582.5 / 81.81 | 43 | 1,659.4 / 1,301.85 | 884 | 763.8 / 471.91 | 682 |
| d17-count-all | 46.6 / 44.7 / 6.16 | 17 | 67.8 / 103.9 / 4.68 | 21 | 288.2 / 272.20 | 885 | 86.9 / 86.08 | 682 |

d01 after https://github.com/danbri/factoidal/issues/805 (2026-10-13, the
PRM1 entries of one key range by binary search over positioned reads; the
other rows of this table are not measured again here): SBM11 none process
12.0 ms (483.8 above), merkle process 170.3 ms (748.0 above);
section 8 item 3.

### 7.4 Threads

SBM11 queries are single-threaded; the packer ran with its default 4
workers only. Virtuoso `default` against `1t`: the warm time falls on scans
and aggregates over many rows (d10 1,124 to 356 ms, d16 1,302 to 472, d17
272 to 86, olympics q10 219 to 92, q16 213 to 85) and does not change on
joins and lookups. The Virtuoso load ran once, in the `default`
configuration with one loader.

## 8. SBM11 findings (issue texts; no issue filed by this work)

1. **Pack phase 2 grows about with the square of the distinct terms.**
   Olympics: 543,967 terms, phase 2 3.4 s. Earlier scaling log
   (`tests/sbm11/dict_scaling.sh`): 950,691 terms, 9.2 s. DBpedia slice:
   8,877,307 terms, 799 s. 16.3 times the terms of olympics gave 234 times
   the time. Phase 2 is the k-way merge of the term runs that writes GDV1,
   GDX1 and the remap files (`Harness/Sbm11PackLib.lean`, stage 3 record
   section 4). The machine load was 0.8 to 4.5 during the pack; that does not
   explain a factor of 14 over linear. Proposed issue: "SBM11 pack phase 2
   (term-run merge) time is superlinear in distinct terms: 799 s of 1,334 s
   on 8.9 M terms"; acceptance: phase 2 time within 2.2 times per doubling of
   terms on the n/2n/4n ladder, and a `danbri-function-precrime-checkers`
   scaling assertion.
   Repaired (https://github.com/danbri/factoidal/issues/804, 2026-10-13): the
   merge scanned all k run heads per record and k grows with the source; it
   now uses a loser tree and an 8-byte-word key comparison proved equal to
   `cmpBytes`. DBpedia slice, same source, generation byte-identical (21
   files): phase 2 26.2 s (799.2 s), pack 288.3 s (1,334.3 s), peak RSS
   584 MB, load 1.4 to 3.6. Cause, fix, the scaling test and the other phase
   times: `2026-10-12-sbm11-stage3.md` section 4.1.
2. **OPTIONAL goes to the reference fallback, which materialises the
   selected quads.** d11: 48.7 s warm, 849 MB peak RSS (all `dbo:birthPlace`
   and `dbo:deathDate` quads decoded into a dataset); Virtuoso 19 ms. This is
   https://github.com/danbri/factoidal/issues/775 and SBM11 stage 4 open item
   2; add this measurement to that issue.
3. **Each process reads PRM1 whole.** On the DBpedia slice the SPO PRM1 is
   8,185,170 bytes and the OSP PRM1 5,596,106 bytes; d01 takes 484 ms per
   process and 0.24 ms warm. Under `--verify none` PRM1 is still read whole
   (stage 4 record section 9.1). Proposed issue: "SBM11 query: read PRM1
   entries by binary search with positioned reads, not whole files";
   acceptance: d01 process time under 50 ms on the DBpedia slice. Related:
   stage 4 open item 4 (process start-up).
   Repaired (https://github.com/danbri/factoidal/issues/805, 2026-10-13): the
   query engine asks its store for the PRM1 entries of one key range, found
   by two binary searches over positioned reads of the PRM1 file, and the
   process reads the 22-byte header at the first use of a permutation. d01
   with `--verify none` on the DBpedia slice: process 220.0 ms before,
   12.0 ms after (median of 7 processes, load average 0.69); file
   bytes read per process 8,210,091 before, 27,795 after; peak RSS
   42.2 MB before, 16.2 MB after. With `--verify merkle`: 408.5 ms before, 170.3 ms
   after (4,106,727 bytes read, most of them the GDX1 file read whole and
   the dictionary chunks). Answers of all 40 queries of both sets
   byte-identical before and after, in both modes. Record:
   `2026-10-12-sbm11-stage4.md` section 13; failing-first test
   `tests/sbm11/process-start.sh`.
4. **Joins.** Warm SBM11 joins are 3.6 to 26 times Virtuoso's on the DBpedia
   slice (d05 575 against 49 ms, d07 136 against 6, d09 76 against 3.6).
   Tracking: https://github.com/danbri/factoidal/issues/787 (SBM11 stages)
   and https://github.com/danbri/factoidal/issues/799 (parallel block scans,
   then PushIR).
5. **`--verify merkle` cold and process times** are 1.5 to 38 times those of
   `none` on the DBpedia slice (d03 2,832 against 75 ms process): every read
   is widened to 65,536-byte chunks that are read and checked. Warm times are
   equal. No issue proposed; this is the cost the option was made for.

## 9. What could not be measured, and why

- **QLever:** measured on both datasets on 2026-10-12 (section 11): index,
  answers, cold and warm times, server RSS, load average. Image-extracted
  binaries only; the source build was stopped by the owner on 2026-10-12.
- **QLever with one thread: not available as a QLever option.** The ceace86
  server has no option for the number of threads of one query (`-j` is the
  number of simultaneous queries; only the spatial join has a thread
  option). The DBpedia slice was timed a second time with the server pinned
  to one CPU (`taskset -c 0`, section 11.8). That limits the CPUs; it does
  not limit the threads. Olympics has no one-CPU run.
- **QLever index build with one thread:** not measured (`-j 4` only).
- **QLever in the same rounds as SBM11 and Virtuoso:** not done. The QLever
  timings are separate runs (section 11), not interleaved with the other
  engines as in section 6; the load averages are given per run.
- **What a QLever cold request reads:** not measured. The cold time of d17
  (167 ms against a warm 1.9 ms) is the cost of the first request of a new
  server on evicted index files; which files it reads was not traced.
- **Cold runs with the whole OS page cache dropped:** refused (it would
  affect the other workload on the machine). Cold here means section 6.
- **SBM11 threads in this record:** the SBM11 columns of section 7 use the
  single-thread query path of commit 408898bd. The parallel block scans
  (`--threads N`, https://github.com/danbri/factoidal/issues/799) were timed
  on the 8 DBpedia BGP joins at 1, 2, 4, 8 threads (4/1 ratio 0.58 to 0.72):
  `docs/designissues/2026-10-12-parallel-block-scans.md` section 5.1. They
  were not timed against Virtuoso or QLever in the interleaved rounds of
  section 6, and the streamed scans (d10, d13, d16, d17) are single-thread.
  The packer was measured only with 4 workers.
- **Virtuoso load with one thread or with several loaders:** one
  configuration only.

## 10. Rerun

```
apt-get install -y virtuoso-opensource
tools/bench/three-engines/run.sh            # data, pack, load, answers, timing, report
```

Needs about 4.3 GB of free disk at the peak (the SBM11 pack's temporary row
runs) and 3.2 GB of `/dev/shm` for the staged N-Triples file. `olympics.nt`
comes from `tools/qlvr/build-instance.sh` (`QLVR_WORK`). Outputs go to
`$BENCH_DATA/results` (default `/home/user/bench-data/results`):
`results.json` holds every number above, with the per-round records and
load averages. Running all steps takes about 3 hours on this machine.

## 11. QLever native (2026-10-12)

Label: every QLever number in this section is **image-extracted (Docker Hub
adfreiburg/qlever, ceace86)**. The binaries are
`/home/user/qlever-image/rootfs/qlever/qlever-index` and `qlever-server`
(version `ceace86`; image digest `sha256:b2087ec9...`, manifest `769924e6...`).
They were accepted by the owner on 2026-10-12 ("Stop src build - we didn't
need it before ... Accept image binaries. regenerate (or refetch)."). The
source build of `qlever-native-build.sh` was stopped and its output is not
used.

Status: QLever on olympics (sections 11.2 to 11.4) and on the DBpedia slice
(section 11.8) is measured: index, answers, timing.

### 11.1 Flag test (olympics, run before the measurement)

Two flags in the 2026-10-11 bench code were not valid for the ceace86
binaries. Commit 7208c783 said the native QLever path was untested. This
test found both defects:

| Flag set | Binary message | Result | Repair in `bench.py` / `run.sh` |
| --- | --- | --- | --- |
| `qlever-index -p` (no value) | required argument for option `--parallel-parsing` is missing | rc 1, no index | `-p true` |
| `qlever-server --cache-max-size 0` (and `--cache-max-size-single-entry 0`) | `'0' could not be parsed as a memory size` | server exits at start | `0 B` |

With the repairs, `qlever-index -p true -j 4 -m 4G -s <settings>` built the
olympics index (rc 0), and the server started (median start 219 ms).

What the cache flags do (`--cache-max-size 0 B`, `--cache-max-size-single-entry 0 B`,
`--cache-max-num-entries 0`), measured on olympics with the bench harness,
six requests of the same query per server process, client wall time in ms:

| Query | Flags | Request 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| q12-group-medals (small result) | cache off | 6.94 | 3.94 | 3.39 | 3.88 | 3.35 | 3.29 |
| q12-group-medals | default cache | 6.23 | 1.74 | 1.31 | 1.57 | 1.97 | 1.56 |
| q19-scan-bound-predicate-iri (39,768 rows) | cache off | 203.9 | 176.1 | 157.9 | 129.8 | 230.4 | 177.0 |
| q19-scan-bound-predicate-iri | default cache | 161.4 | 172.5 | 204.9 | 163.4 | 153.5 | 162.3 |

Reading: with the default cache, a repeated small query is answered from the
result cache from its second request on (about 1.6 ms against 3.4 ms). With the
cache off, every request runs the engine, so the warm number measures the
engine. The 39,768-row result was not cached by the default settings in this
test, so the two rows for q19 do not differ. Cache-off is the setting for every
warm number below.

Flag test artifacts: the scratch harness `flagtest.py` (not in the repository)
and the server logs under `$BENCH_DATA/qlever/olympics/`.

### 11.2 Index build (olympics)

Command: `qlever-index -i <base> -f olympics.nt -F nt -p true -j 4 -m 4G -s
<settings>` (`run.sh`, step `qindex`). Input: 1,781,625 triples (337,695,911
bytes). Index: 2,055,677 triples including 680,749 QLever-internal ones.

| Measure | Image-extracted QLever, 2026-10-12 | Recorded 2026-10-11 (docker, same commit) |
| --- | ---: | ---: |
| Wall time | 4.71 s | 4.35 s |
| Peak RSS (rusage, `qlever-index`) | 291,936 kB (285 MB) | 250 MB |
| On-disk size (index files, no logs) | 38,462,166 B (38.5 MB) | 38.5 MB |
| Load average before / after | 0.63 / 0.74 | not recorded |

Index build as reported by the binary: parse 2.6 s, 15 partial vocabularies,
543,754 words, internal vocabulary 11.8 MB compressed.

### 11.3 Answer check (olympics, 21 queries)

Compared as multisets with `bench.py` `term_key` (section 5), against SBM11
(`--verify none`), Virtuoso and the qlvr oracle (`tests/qlvr/queries`).

| Result | Count |
| --- | ---: |
| Equal on QLever, SBM11, Virtuoso and the oracle | 19 of 21 |
| Different (not timed) | 2 of 21: q15, q20 |

The two differences are the same as in section 5, and they have the same
causes:

- **q15** `?g dbp:year 1936`: QLever 2 rows; SBM11 0 rows; Virtuoso 2 rows;
  oracle 2 rows. QLever is equal to Virtuoso and the oracle, and different from
  SBM11. Cause: the data term is `"1936"^^xsd:int` and the query constant is
  `"1936"^^xsd:integer`. SBM11 matches the terms. Not a QLever or SBM11 defect.
- **q20** `?s dbo:weight ?o` (100,666 rows): QLever equal to SBM11 and to the
  oracle; QLever different from Virtuoso in 2 rows, which print `xsd:double`
  with 6 significant digits in Virtuoso. Cause: section 5.

Record: `$BENCH_DATA/results/qlever-answers-olympics.json`.

### 11.4 Timing (olympics, 19 queries)

Method: section 6. Warm: one server, one warm-up pass, then 7 rounds; median.
Cold: first request of a new server process after the index files were
evicted with `posix_fadvise` (`resident_before` was 0 bytes in all 57 cold
runs, 19 queries times 3 rounds); median of 3 rounds. Cache off (section 11.1).
Load average (1-minute) at the start of every round: warm rounds 1.08
to 1.16; cold rounds 1.01 to 1.01
(all under the target 2.0). Server start (median of the 19 cold starts):
221 ms.

Times in ms; RSS of the server in MB (maximum over the warm rounds, VmHWM,
reset before each request). The last column is the SBM11 `none` warm median
from section 7.2, for comparison only.

| Query | QLever warm | QLever cold | QLever warm RSS MB | SBM11 none warm |
| --- | ---: | ---: | ---: | ---: |
| q01-count-all | 2.57 | 20.8 | 85.8 | 0.34 |
| q02-predicate-counts | 32.84 | 37.4 | 88.0 | 1.69 |
| q03-scan-bound-predicate-int | 2.75 | 4.9 | 86.9 | 0.49 |
| q04-subject-lookup | 4.45 | 8.3 | 86.9 | 0.22 |
| q05-object-bound-type | 2.75 | 5.9 | 87.0 | 0.70 |
| q06-join-two | 3.68 | 6.5 | 87.0 | 0.94 |
| q07-join-three | 18.09 | 41.3 | 87.2 | 53.11 |
| q08-filter-lang-literal | 3.69 | 7.2 | 87.2 | 15.45 |
| q09-bgp-lang-literal | 2.89 | 7.1 | 87.2 | 0.50 |
| q10-orderby-limit-double | 13.51 | 19.4 | 87.2 | 26.58 |
| q11-filter-numeric | 2.97 | 10.1 | 87.2 | 40.96 |
| q12-group-medals | 3.13 | 6.8 | 87.2 | 7.33 |
| q13-subclass-of | 1.76 | 5.2 | 87.2 | 0.32 |
| q14-typed-int-object | 1.96 | 4.9 | 87.0 | 0.48 |
| q16-strstarts | 27.09 | 33.2 | 86.9 | 22.64 |
| q17-noc-team-join | 4.71 | 8.6 | 86.6 | 0.76 |
| q18-games-by-year-limit | 2.46 | 6.7 | 86.5 | 0.37 |
| q19-scan-bound-predicate-iri | 162.70 | 184.9 | 90.4 | 162.38 |
| q21-scan-bound-predicate-lang | 591.06 | 624.2 | 91.4 | 281.30 |

Excluded from timing: q15 and q20 (section 11.3).

Comparison notes, all on olympics at load below 2.0:

- Warm, QLever faster than SBM11 (QLever against SBM11, ms): q07 18.1 against
  53.1; q10 13.5 against 26.6; q11 3.0 against 41.0; q12 3.1 against 7.3; q08
  3.7 against 15.5.
- Warm, SBM11 faster than QLever: q02 1.7 against 32.8; q04 0.2 against 4.4;
  q16 22.6 against 27.1; q21 281 against 591. On q01, q03, q05, q06, q09, q13,
  q14, q17 and q18 SBM11 is faster by 1.4 to 4.0 ms per query (both below 5 ms).
- Equal within 0.3 ms: q19 (162.7 for QLever, 162.4 for SBM11).
- Warm times for the same query differ between this table and the 2026-10-11
  `curl` numbers in section 7.2 (the same engine, another client method and
  load). Use this table for the 2026-10-12 comparison.

### 11.5 Not measured, and why

- **First attempt on the DBpedia slice (2026-10-12, afternoon): stopped.**
  Free space fell to 2.7 GB during the index step (other work on the same
  disk), under the owner's 3 GB stop line. No index was built. The second
  attempt (section 11.8) started with 6.7 GB free and completed.
- **QLever with one thread, index build with one thread, cold runs with the
  page cache dropped:** section 9.

### 11.6 DBpedia slice regenerated (sha256 check)

Sources: `mappingbased_objects_en.ttl.bz2` (sha256 `a5811aa5...c9953`) and
`mappingbased_literals_en.ttl.bz2` (sha256 `0d0d6b55...d518`), both
re-verified from `$BENCH_DATA/dl` (the files of 2026-10-12 16:05, not refetched).
`slice.py` run by `run.sh` step `data` into `/home/user/bench-data/stage/dbpedia.nt`
(3,121,628,229 bytes; not `/dev/shm`).

| Check | Expected | Observed |
| --- | --- | --- |
| sha256 of the N-Triples file | `94025f74d5c4643ce05984524e5583c59a057b8110544ec9a7c55fbd21de85e1` | `94025f74d5c4643ce05984524e5583c59a057b8110544ec9a7c55fbd21de85e1` (match) |
| Lines | 23,269,560 | 23,269,560 |
| Distinct triples | 23,269,559 | 23,269,559 (by a 64-bit BLAKE2b digest per line, sorted; a collision could only lower the count, so the true distinct count is 23,269,559 or 23,269,560) |
| Statements selected from `mappingbased_literals_en` | 4,523,386 | 4,523,386 |
| Dropped by the IRI rule | 0 | 0 |

The sha256 check is the gate in `run.sh`: a mismatch stops the step. It passed.
The distinct count used the 64-bit hash, not an exact sort, because the disk
was too low for a sort with temporary files.

### 11.7 Commands run

```
QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever STEPS="qindex qanswers" DATASETS=olympics tools/bench/three-engines/run.sh
QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever STEPS="qtiming" DATASETS=olympics tools/bench/three-engines/run.sh
STEPS=data DATASETS=dbpedia SHM=/home/user/bench-data/stage tools/bench/three-engines/run.sh
# DBpedia slice, second attempt (section 11.8):
STEPS="qindex" DATASETS=dbpedia SHM=/home/user/bench-data/stage QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever tools/bench/three-engines/run.sh
STEPS="qanswers" DATASETS=dbpedia SHM=/home/user/bench-data/stage QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever tools/bench/three-engines/run.sh
STEPS="qtiming" DATASETS=dbpedia SHM=/home/user/bench-data/stage QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever tools/bench/three-engines/run.sh
# one CPU: QLEVER_NATIVE_BUILD names a directory whose qlever-server is
#   exec taskset -c 0 /home/user/qlever-image/rootfs/qlever/qlever-server "$@"
QLEVER_NATIVE_BUILD=/home/user/bench-data/qlever-1cpu python3 -I tools/bench/three-engines/bench.py qlever-timing \
  --dataset dbpedia --queries tools/bench/three-engines/queries/dbpedia \
  --index /home/user/bench-data/qlever/dbpedia/dbpedia --answers /home/user/bench-data/results/qlever-answers-dbpedia.json \
  --rounds 7 --cold-rounds 3 --out /home/user/bench-data/results/qlever-timing-dbpedia-1cpu.json
```

Results: `$BENCH_DATA/results/qlever-index-olympics.json`,
`qlever-answers-olympics.json`, `qlever-timing-olympics.json`, and the same three files for `dbpedia`
(`qlever-timing-dbpedia.json` is the default run, also saved as
`qlever-timing-dbpedia-default.json`; `qlever-timing-dbpedia-1cpu.json` is the
one-CPU run); logs in
`$BENCH_DATA/logs/`.

### 11.8 DBpedia slice (17 queries), 2026-10-12, evening

Input: `/home/user/bench-data/stage/dbpedia.nt`, sha256
`94025f74d5c4643ce05984524e5583c59a057b8110544ec9a7c55fbd21de85e1`, checked
with `sha256sum` before the index step (match). Free disk at the start: 6.7
GB. `guarded.sh` (a check every 5 s, stop under 3 GB) did not stop the step;
the lowest free space seen in the manual checks was 5.8 GB.

**Index build** (`run.sh` step `qindex`: `qlever-index -i <base> -f
dbpedia.nt -F nt -p true -j 4 -m 4G -s <settings>`):

| Measure | QLever | SBM11 (section 7.1) | Virtuoso (section 7.1) |
| --- | ---: | ---: | ---: |
| Wall time | 56.5 s | 1,334.3 s | 202.7 s |
| Peak RSS | 2,118,784 kB (2,069 MB) | 552 MB | 2,871 MB |
| On-disk size | 872,478,541 B (872.5 MB) | 567.7 MB | 1,746.9 MB |
| Load average before / after | 0.16 / 3.37 | 0.80 / 2.66 | 2.04 / 4.53 |

User CPU 169.2 s, system CPU 26.6 s. As reported by the binary: parse 26.4 s
(23,269,560 lines, 4 threads); 30,006,852 triples including QLever-internal
ones; 157 partial vocabularies merged into 8,779,200 words (vocabulary 122.9
MB compressed); 23,269,559 distinct triples after the sort. The on-disk size
is the sum of the index files without logs (it includes the 3,204-byte
resource-usage log of the index step; that file is not a `.log`).

**Answer check** (`run.sh` step `qanswers`; multisets, `bench.py` `term_key`,
section 5):

| Result | Count |
| --- | ---: |
| Equal on QLever, SBM11 (`--verify none`) and Virtuoso | 17 of 17 |
| Different | 0 of 17 |

Row counts are the same on the three engines for each query (d03 1,083, d05
1,130, d11 1,084, d17 1 row). There is no QLever oracle for DBpedia.
Record: `$BENCH_DATA/results/qlever-answers-dbpedia.json`.

**Timing.** Method of section 11.4: cache off; warm is the median of 7 rounds
after one warm-up pass on one server; cold is the median of 3 rounds, each
the first request of a new server process after `posix_fadvise` eviction of
the index files (`resident_before` 0 bytes in all 51 cold runs of each
configuration). Two configurations:

- **default**: the server as in section 11.4 (no CPU limit; 4 vCPU).
- **1 CPU**: the same server pinned to CPU 0 with `taskset -c 0` (checked:
  `Cpus_allowed_list: 0`, 8 threads). QLever has no option for the number of
  threads of one query (section 9), so this limits the CPUs, not the
  threads.

1-minute load average at the start of each round: default warm 0.75 in all 7
rounds, default cold 0.29, 0.51, 0.63; 1-CPU warm 0.46 to 0.84, 1-CPU cold
0.04, 0.35, 0.45. Server start (median of the cold starts): 217 to 223 ms.

Times in ms. RSS: server VmHWM in MB, maximum over the warm rounds. SBM11
warm is the in-process execution median (`--verify none`, section 7.3);
Virtuoso default warm is a client HTTP time (section 7.3). QLever times are
client HTTP times (they include HTTP and SPARQL JSON).

| Query | QLever default warm / cold | RSS | QLever 1 CPU warm / cold | RSS | 1 CPU / default (warm) | SBM11 none warm | Virtuoso default warm |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| d01-subject-lookup | 4.81 / 8.4 | 137 | 4.80 / 7.8 | 66 | 1.00 | 0.24 | 3.42 |
| d02-object-lookup | 3.92 / 8.7 | 137 | 3.20 / 7.8 | 66 | 0.82 | 0.28 | 3.26 |
| d03-predicate-object | 5.49 / 62.8 | 137 | 4.90 / 63.5 | 66 | 0.89 | 2.35 | 22.67 |
| d04-lang-literal-lookup | 2.68 / 6.6 | 137 | 2.30 / 6.9 | 66 | 0.86 | 0.62 | 3.62 |
| d05-star-three | 43.10 / 151.2 | 142 | 105.03 / 236.7 | 69 | 2.44 | 574.79 | 48.92 |
| d06-star-film | 10.54 / 36.4 | 139 | 15.27 / 36.9 | 69 | 1.45 | 67.77 | 7.24 |
| d07-path-two-hops | 11.70 / 27.9 | 141 | 24.83 / 38.3 | 69 | 2.12 | 136.34 | 6.33 |
| d08-path-three-hops | 21.35 / 89.7 | 141 | 33.91 / 105.4 | 69 | 1.59 | 152.05 | 42.72 |
| d09-group-birthplace | 11.75 / 20.0 | 138 | 23.53 / 43.0 | 69 | 2.00 | 75.84 | 3.71 |
| d10-group-predicates | 248.31 / 250.5 | 137 | 745.41 / 833.4 | 68 | 3.00 | 42.55 | 355.68 |
| d11-optional | 12.79 / 76.6 | 139 | 14.81 / 78.6 | 66 | 1.16 | 48,732.18 | 21.12 |
| d12-filter-numeric | 7.38 / 17.8 | 137 | 10.10 / 19.7 | 66 | 1.37 | 49.69 | 8.02 |
| d13-filter-strstarts | 26.60 / 30.7 | 137 | 26.45 / 33.6 | 66 | 0.99 | 557.62 | 3,736.20 |
| d14-filter-date | 6.09 / 13.9 | 137 | 6.09 / 14.9 | 66 | 1.00 | 81.30 | 7.94 |
| d15-orderby-limit | 8.75 / 13.9 | 137 | 15.18 / 22.6 | 66 | 1.74 | 42.18 | 9.85 |
| d16-orderby-limit-scan | 42.61 / 46.2 | 137 | 119.34 / 131.2 | 66 | 2.80 | 79.77 | 471.91 |
| d17-count-all | 1.91 / 167.1 | 137 | 1.79 / 583.1 | 66 | 0.94 | 6.16 | 86.08 |

No query failed (0 failures in warm and cold runs, both configurations).

Comparison notes (warm; the SBM11 column is in-process, the others include
HTTP and JSON, about 2 to 3 ms for a small answer):

- QLever against SBM11: QLever is faster on every join (d05 43.1 against
  574.8, 13 times; d06 6.4 times; d07 11.7 times; d08 7.1 times; d09 6.5
  times), on d11 OPTIONAL (12.8 against 48,732; SBM11 uses its reference
  fallback, section 8 item 2), on the filters d12, d13 (21 times), d14 and on
  d15, d16, d17. SBM11 is faster on the lookups d01 to d04 (under 2.4 ms
  against 2.7 to 5.5 ms, which includes HTTP) and on d10 (42.6 against 248.3).
- QLever against Virtuoso (default threads): QLever is faster on d03, d04,
  d05, d08, d10 to d17. Virtuoso is faster on d01, d02, d06, d07 and d09 (d09 3.7
  against 11.7; d07 6.3 against 11.7).
- 1 CPU against default: joins, aggregates and the whole-predicate ORDER BY
  take 1.4 to 3.0 times longer on one CPU (d05 2.44, d10 3.00, d16 2.80), so
  the default QLever run uses more than one core for these queries. Lookups
  and d13, d14, d17 do not change (0.82 to 1.00). The server RSS is half on
  one CPU (66 to 69 MB against 137 to 142 MB).
- The cold time of d17 (167 ms default, 583 ms on 1 CPU, against a warm 1.9
  ms) is the cost of the first request of a new server on evicted index
  files. Which files that request reads was not traced (section 9).

### 11.9 SBM11 with sideways information passing, DBpedia slice (2026-10-13)

https://github.com/danbri/factoidal/issues/809; record: section 11 of
[`2026-10-12-sbm11-stage4.md`](2026-10-12-sbm11-stage4.md). SBM11 `--verify
none` before (build of commit f2c87e47) and after (build of commit
94bfd329, the right scan of a join takes the left values of the join
variable as candidates), measured on 2026-10-13 in three interleaved rounds
(warm: execution median of `--repeat 7` in one process; process: median
wall time of 7 processes; RSS: median VmHWM of those processes; each cell
the median of the three rounds; load average 0.65 to 0.95). The SBM11 warm
times of this table were measured on a different day and binary than
section 7.3 (d05 365 ms before here, 575 ms there): compare the before and
after columns with each other. QLever and Virtuoso: the warm medians of
sections 11.8 and 7.3, not measured again. Answers of all 17 queries equal
to the stored SBM11, Virtuoso and QLever answers (`bench.py` comparison).

| Query | SBM11 none warm before / after | process before / after | RSS MB before / after | rows decoded after | QLever default warm (11.8) | Virtuoso default warm (7.3) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| d01-subject-lookup | 0.12 / 0.10 | 231.9 / 245.2 | 41 / 41 | 12 | 4.81 | 3.42 |
| d02-object-lookup | 0.11 / 0.10 | 159.4 / 162.8 | 33 / 33 | 17 | 3.92 | 3.26 |
| d03-predicate-object | 1.00 / 0.95 | 40.0 / 40.4 | 23 / 23 | 1,083 | 5.49 | 22.67 |
| d04-lang-literal-lookup | 0.31 / 0.48 | 24.2 / 24.5 | 17 / 17 | 55 | 2.68 | 3.62 |
| d05-star-three | 365.33 / 75.92 | 389.1 / 126.6 | 83 / 27 | 3,164 | 43.10 | 48.92 |
| d06-star-film | 35.02 / 3.30 | 79.9 / 47.0 | 25 / 19 | 308 | 10.54 | 7.24 |
| d07-path-two-hops | 77.15 / 8.77 | 128.3 / 48.5 | 37 / 19 | 440 | 11.70 | 6.33 |
| d08-path-three-hops | 81.98 / 29.68 | 150.0 / 84.2 | 41 / 22 | 11,628 | 21.35 | 42.72 |
| d09-group-birthplace | 57.83 / 7.00 | 95.0 / 45.3 | 27 / 19 | 440 | 11.75 | 3.71 |
| d10-group-predicates | 30.20 / 23.38 | 52.3 / 63.9 | 21 / 21 | 23,269,559 | 248.31 | 355.68 |
| d11-optional | 19.28 / 8.39 | 79.2 / 63.1 | 25 / 25 | 1,479 | 12.79 | 21.12 |
| d12-filter-numeric | 27.50 / 12.61 | 73.6 / 51.3 | 25 / 20 | 6,228 | 7.38 | 8.02 |
| d13-filter-strstarts | 327.84 / 328.93 | 372.0 / 378.9 | 19 / 19 | 3,368,646 | 26.60 | 3,736.20 |
| d14-filter-date | 56.32 / 20.80 | 104.8 / 70.9 | 29 / 22 | 2,036 | 6.09 | 7.94 |
| d15-orderby-limit | 27.47 / 11.49 | 73.2 / 48.8 | 25 / 19 | 6,228 | 8.75 | 9.85 |
| d16-orderby-limit-scan | 53.00 / 63.68 | 79.8 / 90.6 | 37 / 37 | 327,277 | 42.61 | 471.91 |
| d17-count-all | 2.94 / 3.87 | 27.6 / 29.2 | 17 / 17 | 23,269,559 | 1.91 | 86.08 |

Of the queries with joins (d05 to d09, d11, d12, d14, d15), SBM11 warm is
now faster than QLever warm on d06, d07, d09 and d11 (d07 8.8 against 11.7
ms, d11 8.4 against 12.8 ms) and slower on d05, d08, d12, d14 and d15 (d05
75.9 against 43.1 ms); faster than Virtuoso on d06, d08 and d11, slower on
the other six. As in section 11.8, the SBM11 column is in-process and the
QLever and Virtuoso columns include HTTP and JSON (about 2 to 3 ms for a
small answer). The queries with no join (d01 to d04, d10, d13, d16, d17)
run the same plan as before; their differences are inside the spread
between rounds.

### 11.10 d18 and d19 on Virtuoso and QLever; SBM11 after issue 825 (2026-10-15)

Queries d18 and d19 were added to the DBpedia directory on 2026-10-13, after the
indexes of 11.8 were built, and the indexes were deleted. So neither engine had
a time for them. On 2026-10-15 both indexes were rebuilt from the same
`/home/user/bench-data/stage/dbpedia.nt` (23,269,559 triples), the two queries
were run on every engine on the same machine and day, and the indexes were
deleted again. The SBM11 column is the build with the grouped aggregates on ids
(https://github.com/danbri/factoidal/issues/825, stage 4 record sections 15 and
16).

Builds. Virtuoso 7.2.5.3229: load 112.2 s, 3.01 GB peak RSS, 1.77 GB on disk
(`virtuoso-load-dbpedia-d18-d19.json`). QLever (the image binaries of 11.7):
index 64 s, 2.07 GB peak RSS, 833 MB on disk.

Commands (from the repository root; `$BD` is `/home/user/bench-data`, `$T` is
`$BD/tmp-d1819`, which holds `queries/` with d18 and d19 only; the results are
copied to `$BD/results/*-d18-d19*.json` and the answers to
`$BD/answers/dbpedia/`):

```
python3 -I tools/bench/three-engines/bench.py virtuoso-load --nt $BD/stage/dbpedia.nt \
  --graph http://factoidal.org/bench/dbpedia --dbdir $BD/virtuoso/dbpedia --out $T/virtuoso-load-dbpedia.json
python3 -I tools/bench/three-engines/bench.py answers --dataset dbpedia --queries $T/queries \
  --gen $BD/sbm11/dbpedia --dbdir $BD/virtuoso/dbpedia --graph http://factoidal.org/bench/dbpedia \
  --outdir $T/answers --out $T/answers-dbpedia.json
python3 -I tools/bench/three-engines/bench.py timing --dataset dbpedia --queries $T/queries \
  --gen $BD/sbm11/dbpedia --dbdir $BD/virtuoso/dbpedia --graph http://factoidal.org/bench/dbpedia \
  --answers $T/answers-dbpedia.json --rounds 7 --cold-rounds 3 --repeat 5 --out $T/timing-dbpedia.json
# QLever: the qlever-index command of run.sh step qindex, then
QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever python3 -I tools/bench/three-engines/bench.py \
  qlever-answers --dataset dbpedia --queries $T/queries --index $BD/qlever/dbpedia/dbpedia \
  --answers-dir $T/answers --outdir $T/answers --out $T/qlever-answers-dbpedia.json
QLEVER_NATIVE_BUILD=/home/user/qlever-image/rootfs/qlever python3 -I tools/bench/three-engines/bench.py \
  qlever-timing ... --rounds 7 --cold-rounds 3 --out $T/qlever-timing-dbpedia-default.json
QLEVER_NATIVE_BUILD=$BD/qlever-1cpu python3 -I tools/bench/three-engines/bench.py qlever-timing ... \
  --out $T/qlever-timing-dbpedia-1cpu.json                     # taskset -c 0, as in 11.7
```

Answers. d18 (143 rows) and d19 (10 rows) are equal on SBM11 (`none` and
`merkle`, byte-identical to each other), Virtuoso and QLever
(`answers-dbpedia-d18-d19.json`, `qlever-answers-dbpedia-d18-d19.json`).

Times in ms (7 rounds, medians; cold = first run in a new process after the
engine's files were evicted, 3 rounds; the SBM11 column is the process-level
`none` run of phase `1t`; Virtuoso and QLever times include HTTP and JSON,
about 2 to 3 ms for a small answer). Peak RSS in MB.

| Query | | SBM11 `none` | SBM11 `merkle` | Virtuoso 1 thread | Virtuoso default | QLever 1 CPU | QLever default |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| d18-filter-regex | warm | 59.0 | 58.3 | 11.7 | 11.6 | 84.9 | 32.6 |
| | cold | 179 | 665 | 875 | 870 | 155 | 96.7 |
| | peak RSS | 23.8 | 91.8 | 627 | 611 | 65.6 | 151 |
| d19-group-aggregates | warm | 511 | 511 | 293 | 95.6 | 103 | 62.6 |
| | cold | 779 | 1,367 | 609 | 398 | 121 | 84.3 |
| | peak RSS | 52.3 | 128 | 628 | 612 | 85.2 | 161 |

SBM11 `none` divided by the engine (below 1: SBM11 faster):

| | Virtuoso 1 thread | Virtuoso default | QLever 1 CPU | QLever default |
| --- | ---: | ---: | ---: | ---: |
| d18 warm | 5.0 | 5.1 | 0.69 | 1.8 |
| d18 cold | 0.20 | 0.21 | 1.15 | 1.85 |
| d19 warm | 1.7 | 5.3 | 4.9 | 8.2 |
| d19 cold | 1.3 | 2.0 | 6.4 | 9.2 |

The cold figure of d19 here (779 ms) is the wall time of the first process of
the harness; `l4sbm11 query` alone, measured with the same eviction by a
separate script, gave an execution time of 546 ms and a wall time of 567 ms
(stage 4 record section 16.5). The remaining cost of d19 on SBM11 is split in
https://github.com/danbri/factoidal/issues/862 (the grouped pass 69 percent,
the scans 17 percent, the merge join 12 percent). The warm RSS of the engines
is the server's after the warm rounds, not the load.

### 11.11 d13 with the STRSTARTS window (2026-10-22)

https://github.com/danbri/factoidal/issues/929 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Cause before the change:
the one-pattern streamed path took PSO (rows sorted on the subject after
the predicate) and tested the object id of all 3,368,646 foaf:name rows (823
blocks, 9,362,714 bytes). The STRSTARTS conjunct already gave the dictionary
rank ranges of the keys with the needle as prefix (`FKind.strRange`).

Change (`formal/lean4/L4Factoidal/Storage/Sbm11/IdQuery.lean`): when a
`strRange` conjunct tests a variable of the single pattern, the planner takes
the permutation sorted on that variable after the bound positions
(`windowPref`: POS for d13), and the scan does not read a selected block
whose PRM1 first and last rows bound the object ids inside the ids that the
rank test rejects (`windowSkip`, `windowStore`; only without a delta
overlay). The FILTER still runs on every row read. `--explain` gives
`FILTER window on the scan column: K of N selected blocks not read`.
Theorems (`Storage/Sbm11/WindowTheorems.lean`, axioms propext,
Classical.choice, Quot.sound only): `strRangeFast?_of_span`,
`windowSkip_row`, and `scanFoldM_window` (the scan over the window store and
the full scan give equal tuple lists after the removal of the tuples that
the rank test rejects).

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d13-filter-strstarts.rq --verify
none --repeat 7 --explain`, execution median of 7 runs in one process, 3
interleaved rounds; "before" is the `l4sbm11` of the main checkout (built
2026-10-18), "after" the build of this change. 1-minute load average 1.03
to 1.04 in all rounds. Answers of all 6 runs equal to
`/home/user/bench-data/answers/dbpedia/d13-filter-strstarts.sbm11-none.json`
(2 rows).

| | before | after | QLever 1 CPU warm (11.8) | QLever default warm (11.8) |
| --- | ---: | ---: | ---: | ---: |
| warm, round 1 / 2 / 3 (ms) | 498.2 / 433.2 / 431.8 | 1.95 / 2.49 / 1.91 | | |
| warm, median of rounds (ms) | 433.2 | 1.95 | 26.45 | 26.60 |
| blocks read of selected | 823 of 823 | 2 of 2 (821 not read) | | |
| block bytes read | 9,362,714 | 29,822 | | |
| peak RSS (VmHWM, kB) | 23,780 to 24,048 | 21,768 to 21,812 | 66 MB (server) | 137 MB (server) |

SBM11 is in-process; the QLever times include HTTP and JSON (about 2 to 3
ms for a small answer). The "before" median here (433.2 ms) is above the
328.9 ms of section 11.9 (other binary and day); the ratio to QLever 1 CPU
goes from 12.4 to 0.07. The other queries of KR 1.1 have their own issues:
d14 https://github.com/danbri/factoidal/issues/930, d12
https://github.com/danbri/factoidal/issues/931, d17
https://github.com/danbri/factoidal/issues/932, d19
https://github.com/danbri/factoidal/issues/862.

### 11.12 d14 with the delta loops on machine words (2026-10-22)

https://github.com/danbri/factoidal/issues/930 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Target: d14 warm at most
QLever 1 CPU warm (6.09 ms, section 11.8). Target not met; result 12.4 ms.

Plan (unchanged by this work): POS scan of `dbo:birthPlace dbr:Edinburgh`
(1,083 subjects), then the PSO scan of `dbo:birthDate` with the 1,083
subjects as candidates (sideways information passing, section 11.9): 145 of
154 selected blocks read, 593,920 join-key values tested, 953 rows gathered,
merge join, then the FILTER on 953 rows (54 rows out).

Cause, from `perf record -e cpu-clock --call-graph dwarf` of `l4sbm11 query
... --repeat 60` (perf of linux-tools 6.8.0-146): 62 percent of the samples
were in the two delta loops of `Storage/Sbm11/Sip.lean`, `deltaGatherGo`
(the object column up to the last found row of each block, 36 percent) and
`deltaFindGo` (the subject column, 26 percent), plus 8 percent in
`advGo` (the candidate pointer). The loops kept the byte position, row
number, fuel, previous value and varint accumulator as `Nat`; a term id is
near `2 ^ 61`, so the test `prev + z / 2 < two64` compared with a number
above the scalar range on every row (`lean_nat_big_lt`). A second cost was
allocation: the compiled `cands[q]!` on an `Array UInt64` boxes a `UInt64`
default, one `malloc` and one `free` per row (24 percent of the samples in
an intermediate build, before the guarded reads below).

Change (`formal/lean4/L4Factoidal/Storage/Sbm11/Sip.lean`):

- `deltaFindGoW`, `deltaGatherGoW`: the same loops with the byte position
  as `USize` (`ByteArray.uget`), the previous value and the accumulator as
  `UInt64`, no fuel (`termination_by b.size - i`). While the accumulator is
  below `2 ^ 57`, the word operations give the `Nat` results; above it the
  loop continues as the `Nat` loop from the same state. `deltaFindStart`
  and `deltaGatherStart` use them when the frame bytes are fewer than
  `2 ^ 31` (so that a `USize` position is exact on wasm32 too), else the
  `Nat` loops.
- `probeFast` (the candidate pointer with its frequent case first, no
  call) and `candAt` (the candidate test with a guarded read, no boxed
  default).
- `--explain`: the sideways text gives `key values tested N (on words in K
  blocks)`; d14: `(on words in 145 blocks)`.

Theorems (`Storage/Sbm11/SipFastTheorems.lean`; `#print axioms`: propext,
Classical.choice, Quot.sound; `candAt_eq` propext only): `candAt_eq`,
`probeFast_eq`, `deltaFindGoW_eq` and `deltaGatherGoW_eq` (each word loop
equals its `Nat` loop from the same state with the fuel `b.size - i + 3`),
`deltaFindStart_eq` and `deltaGatherStart_eq` (the starts equal the `Nat`
loops with the fuel the callers gave before). `SipTheorems.findWords_spec`
and `gatherWords_spec` now go through the two start theorems, so the scan
theorems of `SipScanTheorems` hold of the changed scan unchanged (the scan
returns the same tuples).

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d14-filter-date.rq --verify none
--repeat 7 --explain`, execution median of 7 runs in one process, 3
interleaved rounds; "before" is the build of commit aba9a13a, "after" the
build of this change. 1-minute load average 3.96 in all rounds (other
sessions on the machine). Answers of all 6 runs equal to
`/home/user/bench-data/answers/dbpedia/d14-filter-date.sbm11-none.json`
(54 rows).

| | before | after | QLever 1 CPU warm (11.8) | QLever default warm (11.8) |
| --- | ---: | ---: | ---: | ---: |
| warm, round 1 / 2 / 3 (ms) | 22.56 / 22.87 / 22.07 | 12.07 / 13.43 / 12.41 | | |
| warm, median of rounds (ms) | 22.56 | 12.41 | 6.09 | 6.09 |
| peak RSS (VmHWM, kB) | 25,828 to 26,164 | 26,088 to 26,240 | | |

The QLever times include HTTP and JSON (about 2 to 3 ms for a small
answer). The ratio to QLever 1 CPU goes from 3.7 to 2.0.

Remaining cost (profile of the "after" build, inclusive samples):
`deltaGatherGoW` 36 percent, `deltaFindGoW` 28 percent, the FILTER
(`applyFilters`) 18 percent, of which `Session.termOf` 13 percent (the
dictionary key of each of the 953 dates decoded to a `Term`, 7 percent in
`decodeTyped?`), `readFrames` 6 percent, the POS scan 3 percent.

- The two loops are now tight (about 15 instructions per byte, no call, no
  allocation). Their remaining cost is one varint per row: the length of
  each varint of the object column (random literal ranks) varies, and the
  branch on the continuation bit is not predictable. Removing it needs a
  different frame codec for unsorted columns (a wire format change) or a
  branch-free decoder of several bytes at a time with its own proof.
- In the find loop, a third of the samples are the reads of `cands[p]`
  (an `Array UInt64` holds boxed words: two dependent loads per row).
  Keeping the current candidate value in the loop state removes them.
- The FILTER decodes the date of every joined row to a `Term` before the
  comparison (about 2 microseconds per row).

### 11.13 d17, COUNT(*) from the PRM1 entries (2026-10-22)

https://github.com/danbri/factoidal/issues/932 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Query d17 is `SELECT
(COUNT(*) AS ?n) WHERE { ?s ?p ?o }`. Cause before the change: the counted
path (`scanFoldM` with `countStepM`) ran `scanBlockM` on each of the 5,941
PSO blocks. For 5,940 of them the PRM1 entry already decides the count (the
graph frame is a constant frame of graph 0, so the default-graph check holds
for every row and no frame is read), but each block still made a plan, a
chunk, a scan state and a group-map update. A profile (`perf record -e
cpu-clock --call-graph dwarf,16384`, 50 runs in one process) put `mi_free`,
`mi_malloc_small`, `scanBlockM`, `readFrames`, `countChunk` and
`chunkOfCols` at the top; no time was in block decoding.

Change (`formal/lean4/L4Factoidal/Storage/Sbm11/IdQuery.lean`): a COUNT with
no FILTER, no GROUP BY and an empty delta overlay goes to `metaCountM`. One
loop over the selected PRM1 entries (`metaSplitGo`) adds `metaStep` of each
block: 0 when the block is not selected or a check fails on a column that is
constant over the block (`checkFails`); all its rows when every row carries
the key prefix (`fullFor`), every check is on a constant column, and the
scan has no repeated variable and no named-graph test. The other blocks go
through `scanBlockM` with a count as the accumulator (`countAdd`). The
default graph is still a check on the graph column, so `?s ?p ?o` counts the
default graph only, as SPARQL 1.1 section 13 requires; a block whose graph
frame is not provably constant is read. `--explain` gives `counted while
streaming from PRM1 entries (K blocks decided by their entries)`.

Theorems (`Storage/Sbm11/MetaCountTheorems.lean`, axioms propext,
Classical.choice, Quot.sound only): `metaStep_sound` (on an admitted block,
the number `metaStep` gives is the number of output tuples of the block),
`forIn_count`, `metaSplitGo_sum`, and `metaCountM_eq_scan` (over a store in
memory of an admitted permutation with no overlay, `metaCountM` gives the
length of the tuple list of `ScanFoldTheorems.scanFoldM_tuples`, the rows
that carry the key prefix and pass the checks, the named-graph test and the
repeated-variable tests).

Gate: `tests/sbm11/run.sh` part (l1c) packs `tests/sbm11/gate/count-meta.nq`
(32 default-graph triples) in blocks of 10 rows and runs five COUNT queries
against the reference engine; the count of all must decide some blocks and
read some. Three gate queries (`ids-count-all`, `ids-count-repeat-var`,
`ids-count-graph-var`) run in parts (d) and (l1) on the gate fixture, which
has named graphs.

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d17-count-all.rq --verify none
--repeat 7 --explain`, execution median of 7 runs in one process, 3
interleaved rounds; "before" is `l4sbm11` built from `origin/main` at
`0383de52`, "after" the build of this change. 1-minute load average 2.56 to
2.70 in all rounds (another session was building on the machine). The
answers of all 6 runs are byte-identical to
`/home/user/bench-data/answers/dbpedia/d17-count-all.sbm11-none.json`
(23,269,559).

| | before | after | QLever 1 CPU warm (11.8) | QLever default warm (11.8) |
| --- | ---: | ---: | ---: | ---: |
| warm, round 1 / 2 / 3 (ms) | 3.897 / 3.416 / 3.890 | 0.433 / 0.456 / 0.437 | | |
| warm, median of rounds (ms) | 3.890 | 0.437 | 1.79 | 1.91 |
| blocks counted from the PRM1 entry | 0 of 5,941 | 5,940 of 5,941 | | |
| blocks read | 1 (9 bytes) | 1 (9 bytes) | | |
| rows through a chunk | 23,269,559 | 3 | | |
| peak RSS (VmHWM, kB) | 21,700 to 22,332 | 21,736 to 22,292 | | |

SBM11 is in-process; the QLever times include HTTP and JSON. The ratio to
QLever 1 CPU goes from 2.2 to 0.24. Both builds
read the whole PSO PRM1 file (550,132 bytes from file); the remaining time is
that read and the decoding of 5,941 entries.

Gates on this change (exit codes 0): `lake build` (837 jobs);
`tests/sbm11/run.sh` 3,101 pass, 0 fail, 29 expected-fail (out of 3,130);
`SBM11_THREADS=4 tests/sbm11/census.sh` 605 executed, 605 matched the
reference engine (438 on the id path); `tests/planner/sbm11_gate.sh` 8 pass,
0 fail (out of 8 accepted); `tools/lean-tail-recursion-audit.py`,
`tools/lean-unbuilt-modules.py` and `tools/lean-csimp-reach.py` with `--gate`.

### 11.14 d12 re-measured after the d14 word loops (2026-10-22)

https://github.com/danbri/factoidal/issues/931 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Target: d12 warm at most
QLever 1 CPU warm (10.10 ms, section 11.8). Target met with no code change.

The 13 ms of section 11.8 was measured before the d14 delta word loops
(section 11.12, commit a407748f). On `origin/main` at `0a7fab49`, `l4sbm11
query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d12-filter-numeric.rq --verify
none --repeat 7 --explain`, execution median of 7 runs in one process, 3
rounds: 7.55 / 7.09 / 7.83 ms (median of rounds 7.55 ms). 1-minute load
average 3.4 to 3.7 (other sessions on the machine). Answers of all 3 runs
byte-identical to
`/home/user/bench-data/answers/dbpedia/d12-filter-numeric.sbm11-none.json`
(69 rows). Peak RSS (VmHWM) 23,868 to 24,124 kB.

Plan unchanged: POS scan of `dbo:country dbr:Norway` (5,520 rows), then the
PSO scan of `dbo:populationTotal` with 5,520 candidates (80 of 80 selected
blocks read, 327,277 key values tested on words, 708 rows gathered), merge
join, FILTER on 708 rows. The ratio to QLever 1 CPU is 0.75. An id window on
the filter column was not built: the filter variable is on the candidate
scan, whose key values tested are the cost, and the target is met.

### 11.15 d14, candidate in the loop state and the date compare on key bytes (2026-10-22)

https://github.com/danbri/factoidal/issues/930 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Continues 11.12. Target:
d14 warm at most QLever 1 CPU warm (6.09 ms, section 11.8). Target not met;
result 9.7 ms (before 12.0 ms).

Three changes, cheapest first. Each has a theorem that it equals the loop or
the evaluator it replaces.

1. Find loop, current candidate in the loop state
   (`Storage/Sbm11/Sip.lean`, `deltaFindGoC`). `deltaFindGoW` read `cands[p]`
   and `cands[p - 1]` for every row; an `Array UInt64` holds boxed words.
   `deltaFindGoC` carries `c = cAt cands p` and `lc = lAt cands p` as
   `UInt64` loop variables. When `isFast` holds (`p < cands.size`, `c` is not
   below the value, `lc` is below it or `p = 0`), the pointer stays and no
   array is read. Otherwise the pointer is `probeFrom` and `c`, `lc` are read
   for it. Theorems (`SipFastTheorems.lean`): `candAt_cAt`,
   `probeFast_isFast`, `deltaFindGoC_eq` (equals `deltaFindGoW` from the
   same state when `c`, `lc` are the guarded reads at `p`); `deltaFindStart_eq`
   holds unchanged for the changed start.
2. Gather loop, next wanted row in the loop state (`deltaGatherGoK`): the
   test `idx == pos[k]!` compares with a loop variable `nk = posAt pos k`;
   `pos` is read once per found row. Theorems: `posAt_eq`,
   `deltaGatherGoK_eq` (equals `deltaGatherGoW`); `deltaGatherStart_eq`
   holds unchanged.
3. FILTER on key bytes (`Storage/Sbm11/TypedCmp.lean`, new `FKind.typedCmp`).
   For `?v OP c` or `c OP ?v` with `c` a typed literal that has no value for
   the operators (`typedConstOk`: no language tag, datatype not `xsd:string`,
   not numeric, not derived from `xsd:integer`, not `xsd:boolean`, no `0x00`
   in the datatype), `Expr.valueCompare` compares two literals of that
   datatype by the code point order of the lexical forms. `typedCmpKey?`
   reads that order off the dictionary key `[5] ++ datatype ++ [0] ++
   lexical form` of a tag 3 id (`Store.keySlice`, no copy): it checks the
   prefix, decodes the lexical form with `String.fromUTF8?` and applies the
   operator. A key it does not decide (another datatype or class, a lexical
   form that is not UTF-8, an inline id) gives `none` and goes to the
   reference path with the memo, as before. Theorems:
   `TypedCmpTheorems.typedCmpKey?_some` (what an answer says about the key
   bytes), `typedCmpKey_sound` (a key that `decodeKey?` reads as the term
   `t` and that `typedCmpKey?` decides: `ebvOrFalse (Expr.evalIn {} [(v, t)]
   e) = r`, for both operand orders and all six operators),
   `TypedCmpFilterTheorems.typedCmpOf?_spec` and `typedCmp_fast_eq_ref` (the
   compiled conjunct: `refFilter e [(v, t)] = r`). The theorems state the
   relation between `Store.keySlice` and `Store.termOf` as `decodeKey?` of
   the key range, which is how `Session.termOf` is defined
   (`TermKeyFast.decodeKeySlice?_eq`); the abstract `Store` does not carry
   that as a field, the same as for the `.str` conjunct. The rule applies to
   every datatype that `typedConstOk` admits (so also `xsd:dateTime`), not
   only to `xsd:date`.

`#print axioms` of every theorem above: propext, Classical.choice,
Quot.sound, except `candAt_cAt` and `posAt_eq` (propext only) and
`deltaGatherGoK_eq` (propext, Quot.sound).
No `sorry`, no `native_decide`, no `partial`. Tests:
`IdQueryTests` `#guard`s run `typedCmpKey?` on 5 admitted constants (two
dates, a dateTime, a gYear, an unknown datatype) and 2 refused ones, against
the stored samples, all six operators and both orders, against `refFilter`,
and check that at least 10 keys are decided (not vacuous), that a key with
a lexical form that is not UTF-8 is not decided, and which constants
`typedCmpOf?` accepts. New gate queries `tests/sbm11/gate/ids-filter-typed-swap.rq`,
`ids-filter-typed-datetime.rq`, `ids-filter-typed-ne.rq`, and the existing
`ids-sip-date-filter.rq`, run in `tests/sbm11/run.sh` against the reference
engine.

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d14-filter-date.rq --verify none
--repeat 7 --explain`, execution median of 7 runs in one process, 3
interleaved rounds; "before" is the build of `origin/main` at `0a7fab49`,
"after" the build of this change. 1-minute load average 2.2 to 2.5 in all
rounds (other sessions on the machine, 4 cores). Answers of both builds
byte-identical to
`/home/user/bench-data/answers/dbpedia/d14-filter-date.sbm11-none.json`
(54 rows).

| | before | after | QLever 1 CPU warm (11.8) | QLever default warm (11.8) |
| --- | ---: | ---: | ---: | ---: |
| warm, round 1 / 2 / 3 (ms) | 12.02 / 11.67 / 15.75 | 10.20 / 9.72 / 9.32 | | |
| warm, median of rounds (ms) | 12.02 | 9.72 | 6.09 | 6.09 |
| peak RSS (VmHWM, kB) | 26,372 to 26,492 | 26,372 to 26,488 | | |

Contribution of each change, from a second series (`taskset -c 2`,
`--repeat 41`, 3 interleaved rounds, medians per round, median of rounds):
before 11.63; find loop only 11.04; find loop and FILTER 9.69; all three
9.20 ms. The gather change is within the spread of the rounds (8.66 to
10.00). The QLever times include HTTP and JSON (about 2 to 3 ms for a small
answer). The ratio to QLever 1 CPU goes from 2.0 to 1.6.

Remaining cost (`perf record -e cpu-clock --call-graph dwarf,16384` of the
"after" build, inclusive samples): `deltaGatherGoK` 45 percent,
`deltaFindGoC` 31 percent, pread of blocks 7 percent, the FILTER
(`applyFilters`) 5 percent (before: 18 percent), of which `typedCmpKey?` 1.7
percent and `Session.keySlice` 2.8 percent; `readFrames` 5 percent.

- The two loops are 76 percent. Per row they spend a state machine step per
  byte (bounds check, accumulator test, `k` or `idx` test, byte test). The
  length of each varint of the object column (random literal ranks) varies
  and the branch on the continuation bit is not predictable. What would
  remove it: a decoder of several bytes at a time (read 8 bytes, find the
  terminating byte with a mask and a count of trailing zeros, gather the
  7-bit groups) with its own equality proof against the byte loop, or a
  different frame codec for unsorted columns (a wire format change). Neither
  is done here.
- The FILTER is no longer a cost that matters. A prefix test with
  `ByteArray.extract` allocates 42 bytes per row; it is 1.7 percent of the
  samples, so a loop-based prefix test is not worth its proof.

Gates on this change (exit codes 0): `lake build` (1872 jobs);
`tests/sbm11/run.sh` 3,115 pass, 0 fail, 29 expected-fail (out of 3,144);
`SBM11_THREADS=4 tests/sbm11/census.sh` 605 executed, 605 matched the
reference engine (438 on the id path); `tools/lean-tail-recursion-audit.py`,
`tools/lean-unbuilt-modules.py` and `tools/lean-csimp-reach.py` with `--gate`;
`tools/lean-hygiene-audit.py` clean.

### 11.16 d14, row numbers on machine words, sign without a branch, varint read without a branch (2026-10-22)

https://github.com/danbri/factoidal/issues/930 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Continues 11.15. Target:
d14 warm at most QLever 1 CPU warm (6.09 ms, section 11.8). Result: median 6.2
to 6.4 ms in the series below (before 8.7 to 10.7 ms in the same series); the
target is met within the spread of the rounds, not by a margin.

Cause, from `valgrind --tool=cachegrind --branch-sim=yes --cache-sim=no` of
one run of d14 (deterministic; `perf` has no hardware counters in this
container). The claim of 11.15, that the branch on the continuation bit of
the object column is the cost of both loops, holds for one loop:

| loop | instructions | conditional branches | mispredicted |
| --- | ---: | ---: | ---: |
| find (`deltaFindGoC`), before | 43.9 M | 10.8 M | 13,516 |
| gather (`deltaGatherGoK`), before | 29.3 M | 7.6 M | 455,383 |

- The find loop is bound by instruction count (74 per row, 593,920 rows), not
  by mispredicted branches. The row number, `lo`, `hi` and the candidate
  pointer were `Nat`: every `idx + 1`, `idx >= hi`, `idx >= lo` and `p <
  cands.size` is a tag test, a shift and an overflow branch.
- The gather loop mispredicts 0.75 branches per row: the sign of the zigzag
  step (`z % 2`, taken in 50 percent of rows of an unsorted column) and the
  length of the varint.

Changes (`Storage/Sbm11/Sip.lean`, `Storage/Sbm11/VarintWord.lean`):

1. `deltaFindGoY`, `deltaGatherGoY`: `deltaFindGoC` and `deltaGatherGoK` with
   the row number, `lo`, `hi`, the candidate pointer, the index into `pos`
   and the next wanted row as `USize`. The starts use them when `findFits`
   or `gatherFits` holds (the bytes, `lo`, `hi`, the candidates, `pos` and
   its entries all fewer than `smallBytes`, 2 ^ 31, so that no `USize` wraps
   on wasm32), else the earlier loops (`deltaFindStartNat`,
   `deltaGatherStartNat`).
2. `VarintWord.zzV`, `zzOk`: the zigzag step with no branch on the sign
   (`prev + ((z >>> 1) ^^^ (0 - (z &&& 1)))`; the step is inside the 64-bit
   range when `(v < prev) == (z is odd)`).
3. `VarintWord.lenMask`, `vLen`, `vVal`, used by `deltaGatherGoY` at the start
   of a varint (accumulator 0, eight bytes in the window, a byte that ends a
   varint among them): `y = w ||| 0x7f7f7f7f7f7f7f7f`; the mask of the bytes
   up to the first byte whose continuation bit is clear is `y ^^^ (y + 1)`
   (the carry of `y + 1` runs through the bytes that are `0xFF`); the length
   is the number of those bytes (one multiplication); `vCompress` packs the
   seven-bit groups in three shift-or steps and a variable shift drops the
   bytes after the last. No C primitive: `Prim.Bytes.ldU64LE` loads the
   window. A window with no varint end (a varint of nine bytes or more), a
   window past the end of the array and a varint that began in an earlier
   window go through the byte step. The loop takes fuel (`b.size + 1`)
   because the positivity of the length is a theorem about `vLen`, not
   something the termination check sees.

Theorems (`Storage/Sbm11/VarintWordTheorems.lean`, `SipWordTheorems.lean`;
`#print axioms`: propext, Classical.choice, Quot.sound, except `K_row`,
`bt_ld`, `probeFrom_le` (propext, Quot.sound)). No `sorry`, no
`native_decide`.

- `lenMask_eq`: for a window whose bytes `0 .. n-1` have the continuation bit
  set and whose byte `n` has it clear (`n < 8`), `lenMask (w ||| C7)` is
  `2 ^ (8 n + 8) - 1`. From `xor_add_one_bit`: bit `i` of `x ^^^ (x + 1)` is
  set exactly when the bits of `x` below `i` are all set
  (`BitVec.carry_succ_one`); no case split on `n`.
- `vVal_eq`: the value is `hf (bt w) 0 n`, the Horner form of the groups of
  the bytes `0 .. n`. One bit-level proof per `n` (`val_0` .. `val_7`, 64
  output bits each, 1 min 40 s of wall time for the module on 4 cores).
- `hz_eq_hf`: the accumulation of the byte loop (`acc * 128 + group`) equals
  the Horner form. `exists_term`: a window with `w ||| C7 ≠ allOnes` has such
  an `n`. `fastRead_spec`: length `n + 1` and value, together.
- `zz_even`, `zz_odd`, `SipWordTheorems.zz_spec`: `zzV` and `zzOk` are the
  two branches of the zigzag step of the earlier loops.
- `SipWordTheorems.K_row`: `deltaGatherGoK` over one varint of `n + 1` bytes
  equals the row step with the value `hz`; `gatherFast` joins it with
  `fastRead_spec` and `bt_ld` (byte `k` of the load is `getOr0 b (i + k)`).
- `deltaFindGoY_eq`, `deltaGatherGoY_eq`: each equals its `Nat`-state loop
  (`deltaFindGoC`, `deltaGatherGoK`) from the same state, with the bounds
  above. `deltaFindStart_eq`, `deltaGatherStart_eq`: the starts equal the
  `Nat` loops with the fuel they had before, so `SipTheorems.findWords_spec`
  and `gatherWords_spec` hold of the changed scan unchanged (the starts of the
  earlier loops are now `deltaFindStartNat_eq`, `deltaGatherStartNat_eq` in
  `SipFastTheorems`).

Tests: the `#guard`s of `Sip.lean` run `findWords` and `gatherWords` against
the decoded reference; two columns are added: deltas of 1 to 9 bytes up and
down (the read at every length, and the byte step for nine bytes), and 300
rows with lengths of 1 to 5 bytes in one column.

Measurement. Instruction and branch counts, one run of d14 (cachegrind):

| build | find: instructions / mispredicted | gather: instructions / mispredicted | all: mispredicted |
| --- | ---: | ---: | ---: |
| before (11.15) | 43.9 M / 13,516 | 29.3 M / 455,383 | 1,009,818 |
| sign without branch only | 46.3 M / 13,748 | 30.7 M / 209,831 | 745,971 |
| varint read in both loops, sign without branch | 79.9 M / 3,596 | 43.0 M / 2,283 | 532,460 |
| row numbers as `USize` in both loops | 25.5 M / 12,687 | 23.4 M / 209,720 | 914,952 |
| this change (`USize`; varint read in gather only) | 27.9 M / 12,961 | 35.7 M / 2,456 | 552,463 |

The varint read in the find loop removes 10,000 mispredictions and adds 34 M
instructions; it is not used there. In the gather loop it removes 207,000
mispredictions and adds 12 M instructions; it is used there. Intermediate
builds, same series (3 interleaved rounds, medians of 31 runs): sign without
branch only 8.1 to 8.8 ms against 9.5 to 9.9 ms before; `USize` in both
loops 6.8 to 7.0 ms; plus the varint read in the gather loop 6.2 to 6.3 ms.

`l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d14-filter-date.rq --verify none
--repeat 7 --explain`, execution median of 7 runs in one process, 3
interleaved rounds; "before" is the build of `eaf0274d`, "after" the build of
this change. 1-minute load average 1.7 to 2.3 (other sessions on the machine,
4 cores). Answers of all runs equal to
`/home/user/bench-data/answers/dbpedia/d14-filter-date.sbm11-none.json`
(54 rows), and the answers of d05, d08 and d13 are byte-identical between the
two builds.

| | before | after | QLever 1 CPU warm (11.8) | QLever default warm (11.8) |
| --- | ---: | ---: | ---: | ---: |
| warm, round 1 / 2 / 3, `--repeat 7` (ms) | 9.49 / 12.39 / 12.81 | 8.88 / 6.40 / 5.78 | | |
| warm, round 1 / 2 / 3, `--repeat 41` (ms) | 8.75 / 12.34 / 10.65 | 6.29 / 8.00 / 6.20 | | |
| warm, minimum over the runs of the rounds (ms) | 8.17 to 8.52 | 5.57 to 5.64 | | |
| warm, median of rounds, `--repeat 41` (ms) | 10.65 | 6.29 | 6.09 | 6.09 |

The QLever times include HTTP and JSON (about 2 to 3 ms for a small answer).
The ratio to QLever 1 CPU goes from 1.7 to 1.0 on the median, and the minimum
of the after build (5.6 ms) is below QLever. The spread of single rounds
(5.8 to 8.9 ms after) comes from other sessions on the machine.

Other queries, same method (`--repeat 21`, 3 rounds, median of rounds, ms):
d13 1.40 before and 1.51 after (minimum 1.26 and 1.26; the difference is
inside the spread); d05 23.1 before and 16.0 after (minimum 19.6 and 14.6);
d08 15.8 before and 12.6 after (minimum 13.9 and 11.3).

What is left in d14 (cachegrind): the find loop is 15 percent of the
instructions (27.9 M for 593,920 rows, 47 per row, the candidate test and the
state of the loop); the remaining mispredictions (552,463) are 13,000 in the
find loop, 2,500 in the gather loop and the rest outside both loops. A decoder
that finds the row boundaries of a whole word at once (the terminator mask of
eight bytes, the rows taken one set bit at a time) would decouple the
boundary search from the value, and is not done.

Gates on this change (exit codes 0): `lake build` (1,876 jobs);
`tests/prim/run.sh` 24,896 pass, 0 fail on native and 24,896 pass, 0 fail on
wasm32 (no primitive changed; the wasm32 run shows the 32-bit `USize` build
of `Prim.Bytes` is intact); `tests/sbm11/run.sh` with
`FACTOIDAL_TESTING_ROOT=/home/user/factoidal-core/third_party/testing`
3,115 pass, 0 fail, 29 expected-fail (out of 3,144) (the run in a worktree
without the fixtures gives 1,052 pass, 3 fail, 11 expected-fail for stages 4
and 5; the 3 failures are the missing fixture directories of
`w3c_roundtrip.sh`, `w3c_update.sh` and `quad_source.sh`, which pass with the
fixtures: 1,281 + 94 + 688 pass); `SBM11_THREADS=4 tests/sbm11/census.sh` 605
executed, 605 matched the reference engine (438 on the id path);
`tools/lean-tail-recursion-audit.py` (one line added to
`tools/lean-tail-recursion-allow.txt`: `VarintWord.hf`, specification only),
`tools/lean-unbuilt-modules.py` and `tools/lean-csimp-reach.py` with
`--gate`; `tools/lean-hygiene-audit.py` clean. The wasm32 build of the
changed loops is not run by these gates; the loops use only `USize` values
below 2 ^ 31 (`findFits`, `gatherFits`).

### 11.17 d19, grouped aggregates on ids: a pure two-pass loop (2026-10-22)

https://github.com/danbri/factoidal/issues/862 (OKR batch 3 KR 1.1). Section 11.18
ended at 302 ms warm, with the acceptance of 300 ms missed in 2 of 3 rounds. Profile
of the 11.18 binary (`perf record -e cpu-clock --call-graph dwarf,16384`, 5 runs in
one process): `aggregateM` row loop 17 percent in its own frames, `lean_dec_ref_cold`
9 percent called from `aggregateM`, `mi_malloc_small` and `mi_free` 9.5 percent,
`clear_page_erms` (kernel zeroing of fresh pages for the join columns and index
arrays) 11 percent, `deltaRangeGoF` (frame decode) 9 percent, `mergeGo` and `runEnd`
8 percent. The d19 scans use the merge join, not the sideways scan, so the delta
loop changes of branch `batch3/kr11-d14b` (`Sip`) do not apply to them.

Cause found in the generated C of the row loop: it ran in `ExceptT String m` with
the decoder `termOf` as a closure, so each row allocated a closure for `termOf`, a
`ForInStep` and a state tuple, and unwrapped an `ExceptT` result, although the decoder
is needed for 48,815 of 326,365 rows only.

Change (`Storage/Sbm11/IdAgg.lean`):

1. `assignGroups` (pass 1, pure): the group number of each row and the first row of
   each group. `accs` is built once from the group count.
2. `stepRows` (pass 2, pure, tail call with fuel, `Array.foldl` for the inner
   loops): steps every accumulator in row order from row `i`. It stops at the first
   row whose argument id is bound and absent from the summary table, before that
   row changes any accumulator, and returns the id. `aggregateM` decodes that id
   once, inserts its summary, and resumes at the same row. The monad is run 48,815
   times instead of 326,365.
3. The argument ids are not kept in `terms` (only their summaries). `decoded` is
   computed at the end as the number of summaries plus the representative ids that
   are not argument ids, which is the number the earlier code reported.

Theorems (`IdAgg.lean`; dependencies: propext, Classical.choice, Quot.sound; no
sorry): `Cache.insert_valid`, `Cache.hit_eq`, `Cache.fill_valid` and
`sums_fill_valid`: the summary table is valid for `sumOf termOf` however it is
filled (hits, misses, any order, repeats), so a step with a cached summary equals a
step with a recomputed one, which is what stop-and-resume relies on. That
`aggregateM` as a whole equals `AggStream.selectPost_aggPlan`'s specification is
still not proved (end-to-end lemma L5k); `tests/sbm11/agg_ids.sh` and the census
compare it with `--no-agg-ids` and with the reference engine.

Tried and not kept: reserving the capacity of the two index arrays in
`Qlvr.mergeJoin` (`Array.emptyWithCapacity`; `mergeJoin_eq` stays `rfl`): no change
beyond the noise.

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d19-group-aggregates.rq --verify none
--repeat 7`, execution median in one process, interleaved with the 11.18 binary
("before", built from the parent commit). The machine carried a second session
(load average 1.3 to 2.8), so each pair is listed.

| round | before (ms) | after (ms) |
| --- | ---: | ---: |
| 1 | 311 | 232 |
| 2 | 320 | 237 |
| 3 | 401 | 267 |
| earlier 5 rounds, after (ms) | | 253, 265, 282, 292, 319 (first version of the change) |
| QLever 1 CPU (11.10) | | 103 |

Last measurement with the final binary, `tests/sbm11/agg_ids.sh`: warm 227 ms.
The acceptance of 300 ms holds in all 3 rounds, so `xfail-d19-warm-300ms` is now the
assertion `d19-warm-300ms`. Ratio to QLever 1 CPU: 2.2 (11.18: 2.9). Peak RSS
54,160 kB (VmHWM, one run). The answer is byte-identical to the answer of the
parent commit, to `--no-agg-ids` and to
`/home/user/bench-data/answers/dbpedia/d19-group-aggregates.sbm11-none.json`.

Remaining cost (profile of the final binary): kernel page zeroing 15 percent (join
columns, gather outputs and the group-number array are fresh allocations in each
run), frame decode `deltaRangeGoF` 11 percent, `stepRows` 11 percent plus 5 percent
in its inner folds, `lean_dec_ref_cold` 7 percent (freeing the 48,815 summaries and
the table), `mergeGo` and `runEnd` 9 percent. Next candidates: aggregate during the
merge join without the joined columns; a flat numeric `Summary`; reuse of the join
output buffers between runs.

Gates: `lake build` (1868 jobs); `tests/sbm11/agg_ids.sh` 29 pass, 0 fail, 8
expected-fail (out of 37); `tests/sbm11/run.sh` 3,113 pass, 0 fail, 28 expected-fail
(out of 3,141); `SBM11_THREADS=4 tests/sbm11/census.sh` 605 executed, 605 matched the
reference engine (438 on the id path); `lean-unbuilt-modules.py`,
`lean-tail-recursion-audit.py`, `lean-registry-audit.py`, `lean-csimp-reach.py` with
`--gate` exit 0; `lean-hygiene-audit.py` clean.
### 11.18 d19, grouped aggregates on ids: four candidates of issue 862 (2026-10-22)

https://github.com/danbri/factoidal/issues/862 (OKR batch 3 KR 1.1,
https://github.com/danbri/factoidal/issues/875). Query d19 groups 326,365 join
rows into 730 groups and takes COUNT, MAX and AVG. Profile before (`perf record
-e cpu-clock --call-graph dwarf,16384`, 10 runs in one process): `IdAgg.aggregateM`
69 percent. Removing the argument-column work (lookup, decode and steps) from the
loop left 123 ms of about 330, so aggregation was about 200 ms; decoding the 48,815
distinct argument ids was 20 to 30 ms of that.

Changes, in the order of the issue (`Storage/Sbm11/IdAgg.lean`, `SPARQL/AggStream.lean`):

1. One `UInt64` key for a single GROUP BY column (no `List UInt64` per row), and one
   summary lookup per row and argument column (MAX and AVG of one column shared one
   lookup each). 446 to 370 ms (one round).
2. MIN and MAX keep the `Summary` of the best value and compare numeric readings
   with `cmpScaled` (equal scales compare mantissas). Theorem `cmpSummary_of`:
   on the summaries of two values, `cmpSummary` equals `sparqlOrder` of their
   `numericView`s. `best_stream` and `stepKeep_some` are restated over `Summary`.
   `cmpScaled_eq`: `cmpScaled a b = Scaled.cmp a b`.
3. SUM and AVG state holds mantissa and scale (no `Scaled` per step). `addScaled_eq`
   and `stepNum_ofScaled`: the in-place step equals `Scaled.add` of the operand's
   reading. `num_stream` and `evalAggregate_stream` keep their statements over
   `AggAcc.ofScaled`. All new theorems depend on propext, Classical.choice and
   Quot.sound only.
4. Not in the issue: the id hash. `Std.HashMap` takes the bucket from the low bits of
   the hash and the hash of a `UInt64` is the number. `Id64` hashes `id * C`
   with the high half folded onto the low half; keys are not boxed. 15 to 30 ms in 3
   of 3 interleaved rounds. Multiplication alone (no fold) showed no gain. The group
   and argument columns are read from a held `ByteArray` (3 of 3 rounds not slower;
   gain within the noise).

Tried and removed (no gain beyond the noise, so not kept): `getD` against `get?`;
a flat open-addressing id table in a `ByteArray` (slower than `Std.HashMap` at
first because of `2 ^ bits` per lookup, then equal); a pure tail-recursive row loop
with pauses for decoding; flat numeric fields in `Summary`; a pre-sized cache.
Removing the group lookup altogether saved 45 ms, but that run also kept all rows in
one group, so the saving is not the cost of the hash alone.

Measurement: `l4sbm11 query /home/user/bench-data/sbm11/dbpedia --file
tools/bench/three-engines/queries/dbpedia/d19-group-aggregates.rq --verify none
--repeat 7`, execution median in one process, 3 interleaved rounds, "before" built
from `origin/main` at `0a7fab49`. Load average 1.0 to 3.2 (another session was
building); one build gave 285 to 342 ms in different rounds, so differences under
about 20 ms are not resolved.

| | before | after | QLever 1 CPU (11.10) |
| --- | ---: | ---: | ---: |
| warm median, round 1 / 2 / 3 (ms) | 451 / 423 / 518 | 302 / 301 / 334 | 103 |
| warm median of rounds (ms) | 451 | 302 | 103 |
| peak RSS, one run (VmHWM, kB) | 53,796 | 53,736 | |

Answers are byte-identical to the answer of `0a7fab49` (and to `--no-agg-ids`:
`tests/sbm11/agg_ids.sh`). The acceptance of 300 ms is not reached
on every round (302, 301 and 334 ms), so `xfail-d19-warm-300ms` stays an expected failure.
QLever 1 CPU (103 ms) is not reached: ratio 2.9 from 4.4. Remaining cost: the join
and scan (about 120 ms: `deltaRangeGoF`, `mergeJoin`), the 48,815 dictionary decodes
(20 to 30 ms), and per-row hash lookups, accumulator updates and frees (about 150 ms).
Peak RSS is 53.7 MB, above the 52 MB of the task; the base build is 53.8 MB.

Gates: `lake build` (1868 jobs); `tests/sbm11/agg_ids.sh` 28 pass, 0 fail, 9 expected-fail
(out of 37); `tests/sbm11/run.sh` 3,112 pass, 0 fail, 29 expected-fail (out of 3,141);
`SBM11_THREADS=4 tests/sbm11/census.sh` 605 executed, 605 matched the reference engine
(438 on the id path); `tools/lean-unbuilt-modules.py`, `lean-tail-recursion-audit.py`,
`lean-registry-audit.py` and `lean-csimp-reach.py` with `--gate` exit 0;
`lean-hygiene-audit.py` clean (no sorry, axiom or native_decide added).
