# Shardborough and QLever on the same data, and a layout with global term ids

Date: 2026-10-11. Status: measurements done; layout proposed, not
implemented. Tracking: https://github.com/danbri/factoidal/issues/775,
https://github.com/danbri/factoidal/issues/776,
https://github.com/danbri/factoidal/issues/778,
https://github.com/danbri/factoidal/issues/781.

Owner, 2026-10-11, verbatim:

> "My understanding is that a compact infeger representation of triple parts
> is key, plus all standard indexes and pre-sorting where possible."
> "As for “all in memory” that undermines whole point of Shardcore which is
> to support very large persistent stores efficiently."
> "I am interested to see if we can create Lean that approximates qlever perf
> avainst native qlever data, so we can work out why our own efforts are too
> slow: how much is lean vs approach."
> "Design - sure" (approval of this record).

This record measures Shardborough on the QLever reference instance with the
21 oracle queries, explains each difference from QLever with the source line
on both sides, and proposes a Shardborough layout (wire version 11) with one
global term dictionary, 64-bit term ids, sorted permutations and joins over
ids. It changes no Shardborough code.

## 1. Result

- Both Shardborough disk query paths answer the oracle queries correctly
  where SPARQL 1.1 and QLever agree. Of 21 queries, 17 are equal to the
  oracle on each path. The other 4 are: one order difference that is
  QLever's collation (q07), one QLever datatype folding (q15), one QLever
  rounding (q20), and one Lean evaluator defect that loses every row (q11,
  `xsd:int` in a numeric FILTER; section 3.3).
- On the 12 queries that take more than 1 s on IBK3, Shardborough is 2.1 to
  362 times slower than the same Lean code on QLever's layout, and it reads 38
  to 312 times more bytes. Lean on QLever's layout is 1.4 to 31 times slower
  than QLever's C++ on the same queries. On 10 of the 12, the layout and the
  materialise-then-evaluate query path cost more than Lean does (section
  4.6).
- The generation is 437 MB (IBK3) or 222 MB (IBK5) on disk for a 38.5 MB
  QLever index of the same 1,781,625 triples. 86 % of the IBK3 block bytes are
  the per-block dictionaries.
- Three structural causes, with their measured cost: materialisation of terms
  and an in-memory hash index before evaluation (section 4.1), block-local
  dictionaries (4.2), and rows in source order with no sorted access path
  (4.3). One accidental cost: the IBK5 term parser computes `List.length` of
  the rest of the page for every term, 65 % to 70 % of IBK5 query time
  (4.4).
- The proposed layout (section 6) stores one byte-ordered global dictionary,
  64-bit term ids with inline canonical numerics, four sorted permutations of
  quads in column blocks with first/last-key metadata, and runs scans and
  merge or hash joins on ids, materialising terms only for output.

## 2. Subject and method

| Item | Value |
| --- | --- |
| Data | `/home/user/qlvr-work/instance/olympics.nt`, 337,695,911 bytes, 1,781,625 triples, sha256 `44e15095…01ce0` (manifest `tests/qlvr/instance.json`) |
| Queries | `tests/qlvr/queries/q01`–`q21`; oracle answers `/home/user/qlvr-work/oracle/*.srj` from QLever commit `ceace86e` |
| Shardborough | danbri/factoidal-core `main` at `9e82a507`; `l4block-shard-pack`, `l4block-shard-activate`, `l4block-id-v3-query` (IBK3, SBM6), `l4block-quad-query` (IBK5, SBM10), built with `lake build` in `formal/lean4` |
| Lean on QLever's layout | `l4qlvr query` (stage 4, `L4Factoidal/Qlvr/*`), same commit |
| Machine | linux x86_64, 4 vCPU Intel Xeon 2.10 GHz, 15 GB RAM, Lean 4.33.1 |
| Time, memory | wall time and `ru_maxrss` (VmHWM) of each process from `wait4` (`tools/shardborough-cmp/rusage.py`) |
| Profile | `perf record -F 199` (49 for runs above 20 s) with DWARF call graphs, `perf report --children`; perf 6.8 from `linux-tools-6.8.0-146-generic` |
| Answer check | `tests/qlvr/compare_query.py`: multisets of solutions, numbers by value, ORDER BY keys in order; also without the ORDER BY check |

Commands, all from the repository root:

```
bash tools/shardborough-cmp/pack.sh            # pack and activate both layouts
bash tools/shardborough-cmp/run.sh             # 21 queries x 2 layouts, 1 warm-up + 3 measured runs
bash tools/shardborough-cmp/profile.sh ibk3 q07-join-three   # phase shares
bash tools/shardborough-cmp/qlvr_bytes.sh      # l4qlvr --explain: bytes on QLever's layout
python3 -I tools/shardborough-cmp/block_stats.py COLLECTION/gen-1
python3 -I tools/shardborough-cmp/codec_estimate.py /home/user/qlvr-work/instance
python3 -I tools/shardborough-cmp/dict_estimate.py /home/user/qlvr-work/instance.qlvr-side /home/user/qlvr-work/instance/olympics.nt
```

Work data stays outside the repository in
`/home/user/qlvr-work/shardborough-cmp/` (`col-ibk3`, `col-ibk5`, `measure/`,
`perf/`).

Only disk query paths are measured. The in-memory snapshot mode
(`l4block-snapshot-session`) is not a Shardborough result (CLAUDE.md,
2026-10-11) and is not run here.

QLever's times are from the format record
(`docs/designissues/2026-10-11-qlever-index-format.md`, section "Basic graph
patterns from Lean (stage 4)", `tests/qlvr/bench.sh`, same machine, warm,
median of 3): "HTTP" is `curl` time for SPARQL JSON, "total" is the server's
own `time.total` with no rows exported.

## 3. Measurements

### 3.1 Storage

`bash tools/shardborough-cmp/pack.sh`, 2026-10-11.

| Step | IBK3 (wire version 6) | IBK5 (wire version 10) | QLever `qlever index` |
| --- | ---: | ---: | ---: |
| pack wall time | 200.5 s | 203.7 s | 4.35 s (index log 17:23:51.749 to 17:23:56.098) |
| pack CPU (user) | 191.7 s | 193.3 s | about 15 s (resource log: 220 % to 390 % CPU over 4 s) |
| pack peak RSS | 120 MB | 196 MB | 250 MB (resource log, sampled once a second) |
| activation wall time | 85.4 s | 115.8 s | (none) |
| activation peak RSS | 440 MB | 60 MB | |
| blocks | 437 | 200 | 67 per permutation |
| files | 3,498 | 1,202 | 23 |
| bytes on disk | 437,355,334 | 222,031,394 | 38,461,842 (the 23 index files of `instance.json`) |

Bytes per file type (`pack.sh` prints this table):

| IBK3 file type | files | bytes | IBK5 file type | files | bytes |
| --- | ---: | ---: | --- | ---: | ---: |
| `.ibk3` blocks | 437 | 209,710,571 | `.ibk5` blocks | 200 | 215,898,787 |
| `.tli1` term index | 437 | 198,306,243 | `.lgi4` literal gram index | 200 | 5,797,972 |
| `.sri2` subject postings | 437 | 14,396,445 | `.gbi1` geometry index | 200 | 13,000 |
| `.oli2` object postings | 437 | 14,396,445 | `.merkle` (all) | 600 | 122,976 |
| `.merkle` (all) | 1,748 | 241,088 | manifest and TSV | 2 | 198,659 |
| manifest and TSV | 2 | 304,542 | | | |

Rows against dictionary inside the primary blocks
(`block_stats.py`, which reads only the fixed headers):

| | IBK3 | IBK5 | QLever |
| --- | ---: | ---: | ---: |
| row bytes | 28,506,000 (16 per row) | 35,632,500 (20 per row) | 3.0 to 3.5 MB per permutation, zstd |
| dictionary bytes | 181,197,142 | 180,261,287 | 16,133,525 (`words.external` + `.offsets`) |
| dictionary bytes per row | 101.7 | 101.2 | 9.1 |
| dictionary entries, summed over blocks | 2,043,367 | 2,028,079 | 543,754 words (one global vocabulary) |

The QLever index size is the sum of the 23 `index_files` sizes in
`tests/qlvr/instance.json`: six permutations (20,445,036 bytes), two internal
permutations (1,854,901), the vocabulary (16,159,082), the patterns and the
metadata. The format record's text says "about 46 MB"; the file sizes it lists
add up to 38.5 MB, and this record uses the sum.

### 3.2 Queries

`bash tools/shardborough-cmp/run.sh`, 2026-10-11: one unmeasured run, then
three measured runs; the medians are shown (kept in
`/home/user/qlvr-work/shardborough-cmp/measure/final-runs3/`). A second run of
the IBK3 column with `RUNS=1` the same day gave every time above 100 ms within 21 %, every time below
100 ms within 15 ms, and every byte count and answer unchanged. "Equal" is the oracle comparison
with ORDER BY keys; section 3.3 explains every "no". "Bytes" is the tool's
`logical-read-bytes`. "Blocks" is `shards=`. The `l4qlvr` columns are Lean on
QLever's layout: bytes are the compressed column frames the plan reads
(`qlvr_bytes.sh`; the 16 MB vocabulary, read whole by `l4qlvr`, is not
counted), time and RSS are from the format record's bench table.

| Query | Rows | IBK3 equal | IBK3 ms | IBK3 RSS MB | IBK3 bytes | IBK3 blocks | IBK5 ms | IBK5 RSS MB | IBK5 bytes | IBK5 blocks | l4qlvr ms | l4qlvr RSS MB | l4qlvr bytes | QLever HTTP ms | QLever total ms |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| q01 count all | 1 | yes | 30,804 | 1,020 | 209,707,075 | 437 | 122,933 | 1,046 | 215,898,787 | 200 | 85 | 29 | 0 | 15 | 16 |
| q02 predicate counts | 16 | yes | 1,647 | 23 | 38,135,622 | 437 | 124,565 | 1,480 | 215,898,787 | 200 | 194 | 31 | 2,535 | 37 | 33 |
| q03 bound predicate, int | 51 | yes | 24 | 23 | 5,854 | 1 | 21 | 20 | 6,074 | 1 | 18 | 29 | 320 | 3 | 1 |
| q04 subject lookup | 5 | yes | 1,955 | 23 | 10,885,688 | 437 | 57,625 | 518 | 93,147,026 | 89 | 46 | 33 | 92,578 | 5 | 3 |
| q05 object bound type | 51 | yes | 121 | 23 | 721,514 | 35 | 486 | 20 | 1,030,093 | 2 | 27 | 33 | 32,739 | 3 | 1 |
| q06 join two | 52 | yes | 27 | 23 | 17,950 | 2 | 22 | 20 | 11,295 | 2 | 23 | 29 | 556 | 5 | 2 |
| q07 join three | 313 | order (QLever ICU) | 13,640 | 496 | 109,246,680 | 179 | 62,147 | 495 | 111,664,711 | 88 | 351 | 46 | 1,252,206 | 19 | 17 |
| q08 FILTER lang literal | 1 | yes | 3,199 | 170 | 23,961,401 | 35 | 16,085 | 169 | 24,508,194 | 16 | 93 | 37 | 315,580 | 3 | 2 |
| q09 BGP lang literal | 1 | yes | 2,960 | 148 | 23,961,401 | 35 | 15,683 | 149 | 24,508,194 | 16 | 50 | 31 | 76,853 | 3 | 2 |
| q10 ORDER BY double LIMIT | 10 | yes | 1,761 | 90 | 8,876,505 | 34 | 5,705 | 90 | 9,163,551 | 9 | 511 | 59 | 232,097 | 18 | 17 |
| q11 FILTER numeric | 34 | no: 0 rows (defect) | 1,694 | 131 | 12,095,764 | 34 | 7,102 | 133 | 12,775,744 | 16 | 115 | 37 | 255,436 | 4 | 2 |
| q12 GROUP BY medals | 3 | yes | 468 | 47 | 5,094,231 | 48 | 2,498 | 47 | 5,242,320 | 5 | 28 | 31 | 11,628 | 4 | 2 |
| q13 bound IRI object | 10 | yes | 30 | 23 | 43,159 | 1 | 50 | 20 | 82,007 | 1 | 20 | 29 | 1,012 | 2 | 1 |
| q14 typed int object | 2 | yes | 20 | 23 | 11,357 | 1 | 19 | 20 | 6,074 | 1 | 18 | 29 | 311 | 2 | 1 |
| q15 `1936` matches int | 2 | no: 0 rows (SPARQL) | 27 | 23 | 5,802 | 1 | 19 | 20 | 6,074 | 1 | 19 | 29 | 311 | 2 | 1 |
| q16 STRSTARTS | 5 | yes | 3,069 | 170 | 23,961,401 | 35 | 16,229 | 169 | 24,508,194 | 16 | 214 | 37 | 315,580 | 37 | 34 |
| q17 NOC team join | 1 | yes | 1,665 | 90 | 12,501,892 | 35 | 7,450 | 90 | 12,822,731 | 14 | 34 | 33 | 72,025 | 4 | 3 |
| q18 ORDER BY int LIMIT OFFSET | 5 | yes | 22 | 23 | 5,854 | 1 | 26 | 20 | 6,074 | 1 | 23 | 29 | 320 | 3 | 1 |
| q19 scan, IRI objects | 39,768 | yes | 656 | 71 | 5,094,231 | 48 | 2,832 | 59 | 5,242,320 | 5 | 336 | 44 | 54,395 | 198 | 2 |
| q20 scan, doubles | 100,666 | no: 2 rows (QLever rounding) | 1,595 | 103 | 8,876,505 | 34 | 5,820 | 105 | 9,163,551 | 9 | 756 | 46 | 232,097 | 517 | 4 |
| q21 scan, lang literals | 137,026 | yes | 3,566 | 175 | 23,961,401 | 35 | 16,404 | 169 | 24,508,194 | 16 | 968 | 45 | 315,580 | 717 | 5 |

The IBK5 path gives the same answers as IBK3 on all 21 queries (the same
four "no" rows, for the same reasons).

### 3.3 The four answers that differ from the oracle

| Query | Difference | Whose behaviour | Evidence |
| --- | --- | --- | --- |
| q07 | Equal as multisets; the ORDER BY `?label` sequence differs from row 49 (`"Domenico Mordini"` before `"dn Zombori …"`) | QLever orders words by ICU collation of the `en_US` locale (`index/vocabulary/StringSortComparator.h:307-333`); SPARQL 1.1 section 15.1 orders simple literals and language-tagged strings by code point, so `D` (U+0044) sorts before `d` (U+0064). Shardborough follows SPARQL. | `answers/ibk3-q07-join-three.cmp`; multiset comparison passes |
| q15 | 0 rows against 2 | QLever folds `1936` (`xsd:integer`) and `"1936"^^xsd:int` to one `Int` Id (format record section 1). Under RDF term equality the pattern matches nothing. Shardborough follows SPARQL. | the query file's own comment says so |
| q20 | 2 of 100,666 rows differ in the 13th significant digit (`77.3333333333333` against QLever's `77.33333333333`) | QLever drops 4 mantissa bits and prints `%.13g` (`index/ExportIds.cpp:233-292`). Shardborough returns the input value. | all differences within 1e-11 relative |
| q11 | 0 rows against 34 | **Defect in the Lean evaluator.** `FILTER(?age >= 72)` over `"72"^^xsd:int` is true under SPARQL 1.1 section 17.3 (`xsd:int` is derived from `xsd:integer`, a numeric type). The in-memory reference path gives the same 0 rows: `l4block-corpus` over 8 lines of the data answers 0 rows for `>=`, `=` and `>`, and the answer is correct when the data says `xsd:integer`. So the defect is in numeric comparison of derived integer types, not in storage. | scratch fixture of 8 `foaf:age` lines; needs an issue (section 8) |

### 3.4 Where the time goes

`bash tools/shardborough-cmp/profile.sh LAYOUT QUERY`, 2026-10-11. Shares are
inclusive, of all samples; "read and materialise" contains the next three
rows. The three slowest IBK3 queries and the same three on IBK5:

| Phase (marker function) | IBK3 q01 | IBK3 q07 | IBK3 q21 | IBK5 q01 | IBK5 q07 | IBK5 q21 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| read and materialise the selected blocks (`materializeEntries`; `QuadQuery.readEntriesV5`) | 61.8 % | 64.4 % | 56.2 % | 86.1 % | 90.0 % | 88.5 % |
| — fetch and verify: `pread`, SHA-256, Merkle leaves (`readVerifiedRangeCached?`; `artifactAdmitted`) | 22.4 % | 24.0 % | 21.3 % | 5.2 % | 4.9 % | 4.0 % |
| — decode the dictionary into RDF terms (`PTD.decodePageArray?`; `PTD.decode?`) | 36.0 % | 37.5 % | 32.6 % | 77.2 % | 81.2 % | 81.5 % |
| — of which `List.length` in the term parser | 4.8 % | 4.5 % | 3.8 % | 65.1 % | 69.1 % | 69.8 % |
| build the in-memory graph or dataset and its hash index (`indexedGraphBackend`; `indexedDatasetBackend`) | 30.2 % | 28.6 % | 23.9 % | 7.8 % | 5.7 % | 4.6 % |
| evaluate (`evalSelectBackendOnGraph`) | 6.9 % | 5.9 % | (not seen) | 1.7 % | 1.5 % | (not seen) |
| write SPARQL JSON (`toSrjFast`) | 0 | 0 | 8.8 % | 0 | 0 | 2.5 % |

The top self-time symbols in the IBK3 profiles are the allocator and
reference counting: `mi_free` 10 % to 11 %, `mi_malloc_small` 8 % to 10 %,
`lean_dec_ref_cold` 6 % to 9 % (each run). Every decoded term is a heap
object, and every triple is a `Triple` of three `Term`s in a `List`.

Evaluation proper is 2 % to 7 %. Shardborough's time is spent turning bytes
into RDF terms and turning the terms into a hash index, for every row of every
selected block, before the query runs.

## 4. Why: the structural differences

### 4.1 Materialise, then evaluate

Shardborough reads every selected block whole, decodes every dictionary term
into an `RDF.Term`, builds a `List Triple` (IBK3,
`Harness/IndexedBlockV3Materialize.lean:996` `materializeEntries`) or a
`Dataset` (IBK5, `Harness/QuadQuery.lean:135` `readEntriesV5`, then
`Storage/QuadDataset.lean:83` `datasetOfQuads`), wraps it in an in-memory hash
index (`SPARQL/StoreDataset.lean:133` `indexedGraphBackend` =
`OWL.RL.Index.ofGraph`, `OWL/RLClosureIndexed.lean:178`), and then runs the
reference evaluator over it (`Harness/IndexedBlockV3Query.lean:104` `finish`;
`Harness/QuadQuery.lean:195` `finish`). A query whose shape is not one of the
fast paths and whose predicate is a variable takes the whole generation
(`Harness/IndexedBlockV3Query.lean:664-667`, mode
`ibk3-paged-merkle-full-manifest`). This is issue
https://github.com/danbri/factoidal/issues/775.

QLever never builds terms for intermediate results. A scan returns columns of
64-bit Ids (`index/CompressedRelationReader.h:525`
`readAndDecompressBlock`); joins read Ids
(`engine/JoinImpl.cpp:308-397`); a COUNT over a full scan reads the metadata
row counts only. Terms are made from Ids only for the exported rows
(`engine/ExportQueryExecutionTrees.cpp:334` `idToStringAndType`).

Measured cost: q01 reads 209,707,075 bytes and peaks at 1,020 MB to count
rows that the metadata already counts (l4qlvr reads 0 frame bytes; QLever
16 ms). In the q07 profile, decode plus index build is 66 % of the time.

### 4.2 Block-local term ids and per-block dictionaries

An IBK3 row is four `u32`: source position, subject, predicate, object, each a
LOCAL id into the block's own PTD1 dictionary
(`Storage/IndexedBlockWireV3.lean:51-52`, `:93-96` `encodeRow`); IBK5 adds a
graph column (20 bytes, `Storage/IndexedBlockWireV4.lean:225-227`). A term
that occurs in several blocks is stored in each. The packer cuts one block
per predicate per publication batch of 64 chunks of 65,536 bytes
(`Storage/PackStream.lean:70` `publicationChunkCount`,
`Storage/PredicateBlocks.lean:51-53`), so one athlete IRI is repeated in up
to 16 blocks of each batch. A bound term in a query must be looked up in the
TLI1 index of every candidate block (`Harness/IndexedBlockV3Materialize.lean:95`
`subjectIdsViaTli?`), and ids from two blocks cannot be compared, so no join
can work on ids.

QLever has one vocabulary for the whole index (`index/vocabulary/CompressedVocabulary.h:39-44`),
and an Id is the same 64-bit value in every permutation and every block
(`global/FoldedValueId.h:36-37`). Integers, decimals, doubles, booleans and
dates are values inside the Id and never enter the vocabulary
(`parser/RdfParser.cpp:676-721`).

Measured cost: 181,197,142 dictionary bytes in the IBK3 blocks (86 % of block
bytes; 101.7 bytes per row against QLever's 9.1); 2,043,367 dictionary
entries summed over blocks, 3.8 times the 543,754 words of QLever's
vocabulary; 198,306,243 more bytes of TLI1 term index. q04 (one bound
subject, 5 rows) fetches 53,224,183 bytes from all 437 blocks on IBK3 and
93,147,026 bytes from 89 blocks on IBK5; l4qlvr reads 92,578 bytes from 1
block of SPO.

### 4.3 No sorted permutation; skipping by predicate and zone map only

Shardborough keeps rows in source order inside a block
(`Storage/IndexedBlockWireV3.lean:98-99` `positionedRows`; the blockengine
skill: "Do not sort V1 rows merely to obtain input-order-independent
bytes"). The only access paths are: the predicate of a block (manifest
entry), the SRI2/OLI2 postings and TLI1 term index inside an IBK3 block
(spec section 6.2), and, for IBK5, a subject and an object zone map per block
(`Storage/ShardManifest.lean:184-190`, `:374` `zoneBytes`, `:406-407`
`zoneMayContain`). A zone map is the minimum and maximum key of an unsorted
block, so it is wide; IBK5 q04 excluded 111 of 200 blocks and still read 89.
Joins run inside the reference evaluator over the materialised terms
(`SPARQL/StorePlan.lean` `evalBgpBackend`: hash-index lookups per bound
pattern, 5 % of q07).

QLever stores six permutations (PSO, POS, SPO, SOP, OSP, OPS; built in
`index/IndexImpl.cpp:903` `createPermutations`), each sorted, each cut into
blocks of 31,250 rows whose metadata holds the first and the last triple
(`index/CompressedRelationMetadata.h:92-93`). A scan selects blocks by binary
search on that metadata (`index/CompressedRelationReaderBlockSelection.cpp:257-275`
`getRelevantBlocks`). Two scans sorted on the join column are joined by a
zipper (merge) join (`util/JoinAlgorithms/JoinAlgorithms.h:125`
`zipperJoinWithUndef`), with galloping when one side is much smaller
(`engine/JoinImpl.cpp:349-361`), and before the join each scan drops the
blocks whose key range has no partner in the other scan
(`engine/IndexScan.cpp:639` `lazyScanForJoinOfTwoScans`,
`engine/JoinImpl.cpp:561-597`). A hash join is used when the inputs are not
sorted on the join column (`engine/JoinImpl.cpp:431` `hashJoinImpl`).

Measured cost: q07 reads 4 whole predicates, 109,246,680 bytes in 179
blocks (IBK3), against 1,252,206 bytes in 17 blocks for l4qlvr's plan (POS,
POS, PSO, PSO; two merge joins and one hash join, format record plan rule 5).
q21 reads 23,961,401 bytes against 315,580.

### 4.4 An accidental cost in the IBK5 term parser

`TermWireV2.parseInline bs = parseInlineGo bs.length bs`
(`Storage/TermWireV2.lean:240-241`) takes the fuel from the length of the
whole remaining list, and the page decoder calls it once per term on the rest
of the page (`Storage/PagedTermDictionaryCore.lean:229-233` `decodeTermsGo`).
So a page of `n` terms walks the page about `n` times. `List.length` is 65 %
to 70 % of the IBK5 query time (section 3.4), and it is why IBK5 is 4.6
times slower than IBK3 on q21 for the same 24 MB of blocks. The IBK3 term
codec (`Storage.parseTerm`) has the same shape at a smaller share (3.8 % to
4.8 %). The fuel only has to bound the triple-term nesting depth, so it can
be a value that does not depend on the rest of the page. This is the sixth
accidental cost of this kind in the tree
(`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md` section 2
lists five). Repaired by https://github.com/danbri/factoidal/issues/783:
`TermWireV2.parseInlineLoop`, a tail loop with no fuel, is the compiled form of
`parseInline` through the `@[csimp]` theorem `parseInline_eq_fast`; bytes and
admitted inputs do not change. Measured after the repair on the same IBK5
generation, warm, median of 3, answers byte-identical: q01 121,206 to 41,773 ms,
q07 63,480 to 20,000 ms, q08 16,247 to 4,610 ms, q21 16,351 to 4,655 ms.
Gate: row `termwire-page-decode` of `tests/stack/lean_scaling.py`.

### 4.5 Comparison table

| Feature | Shardborough today | QLever (`ceace86`) | Cost of Shardborough's choice, measured here |
| --- | --- | --- | --- |
| Term identity in rows | `u32` local id into the block's dictionary (`IndexedBlockWireV3.lean:93-96`) | 64-bit Id, 4-bit datatype tag, global (`global/FoldedValueId.h:36-37`, `global/Datatype.h:24-49`) | ids cannot be joined or compared across blocks; every bound constant is looked up per block (q04: 437 TLI1/SRI2 lookups, 53 MB fetched for 5 rows) |
| Numbers, booleans, dates | dictionary terms | inline values in the Id (`parser/RdfParser.cpp:676-721`) | 382,953 numeric literals in block dictionaries; QLever's inline form loses the datatype IRI and 4 mantissa bits (q15, q20), which Shardborough must not copy |
| Vocabulary | one PTD1/PTD2 dictionary per block, pages of terms in first-occurrence order | one vocabulary, sorted by ICU collation, FSST twice (`CompressedVocabulary.h:39-44`, `StringSortComparator.h:307-333`) | 181 MB against 16 MB; 2.04 M entries against 0.54 M |
| Sort orders | source order inside a block; blocks per (predicate, batch) or (predicate, graph) | six sorted permutations (`IndexImpl.cpp:903`) | no range scan by subject or object; joins cannot merge |
| Block metadata for skipping | predicate, graph set, IBK5 subject/object zone maps over unsorted rows (`ShardManifest.lean:184-190`) | first and last triple per block (`CompressedRelationMetadata.h:92-93`), binary search (`CompressedRelationReaderBlockSelection.cpp:257`) | IBK5 q04 reads 89 of 200 blocks for 5 rows |
| Selective access in a block | IBK3: SRI2, OLI2, TLI1 sidecars; IBK5: none (whole block) | the sort order itself | IBK3 sidecars are 227 MB, 52 % of the generation |
| Join algorithm | reference evaluator over a hash index of materialised terms | merge (zipper) join on Ids with block prefiltering, galloping, hash join fallback (`JoinImpl.cpp:308-597`) | q07: 13.6 s and 109 MB against 0.35 s and 1.25 MB (same Lean, QLever layout) |
| Materialisation | all rows of the selected blocks become `Term`s and a hash index before evaluation | Ids until export | 60 % to 90 % of query time (section 3.4); q01 1.02 GB RSS |
| Compression | none on rows (fixed 16 or 20 bytes); none on dictionary pages | zstd level 3 per column per block (`ZstdWrapper.h:21-26`); FSST on words | rows 28.5 MB (IBK3) against 3.0 to 3.5 MB per permutation |
| Integrity | SHA-256 per artifact, Merkle leaves per 65,536-byte chunk, verified on every read (`readVerifiedRangeCached?`) | none at read time | 21 % to 24 % of IBK3 query time; kept in the proposal (section 6.6), at a smaller share |
| Update path | DLOG delta log, replayed at query time; compaction writes a new generation (spec section 6.4) | delta triples in memory, merged into each scanned block (`index/LocatedTriples.h:198` `mergeTriples`); `.update-triples` file (`index/DeltaTriples.cpp:654-677`) | not measured here; both keep the base immutable |
| Bulk build | one pass with a per-batch fold; no sort | parallel parse, partial vocabularies merged (`index/VocabularyMergerImpl.h:36`), external sort per permutation (`engine/idTable/CompressedExternalIdTable.h:1083`) | 200.5 s against 4.35 s wall; 120 MB to 196 MB against 250 MB RSS |

### 4.6 How much is Lean and how much is the approach

The owner's question has two parts, and this data answers the second for the
21 queries; the first is the subject of the parallel qlvr work
(https://github.com/danbri/factoidal/issues/778):

Two factors per query, computed from the table of section 3.2:

- **Approach**: IBK3 wall time divided by `l4qlvr` wall time (same Lean, two
  layouts and two query paths).
- **Lean**: `l4qlvr` wall time divided by QLever HTTP time (two
  implementations, one layout and similar plans). Each `l4qlvr` run includes
  process start and a 16 MB vocabulary load (11 to 85 ms, format record);
  QLever is a running server.

| Query | IBK3 ms | Approach factor | Lean factor | Bytes, IBK3 / l4qlvr |
| --- | ---: | ---: | ---: | ---: |
| q01 | 30,804 | 362 | 5.7 | (l4qlvr reads 0) |
| q09 | 2,960 | 59 | 17 | 312 |
| q17 | 1,665 | 49 | 8.5 | 174 |
| q04 | 1,955 | 42 | 9.2 | 118 |
| q07 | 13,640 | 39 | 18 | 87 |
| q08 | 3,199 | 34 | 31 | 76 |
| q11 | 1,694 | 15 | 29 | 47 |
| q16 | 3,069 | 14 | 5.8 | 76 |
| q02 | 1,647 | 8.5 | 5.2 | 15,044 |
| q21 | 3,566 | 3.7 | 1.4 | 76 |
| q10 | 1,761 | 3.4 | 28 | 38 |
| q20 | 1,595 | 2.1 | 1.5 | 38 |

The approach factor is the larger one for 10 of these 12 queries. The Lean
factor is larger for q10 (ORDER BY over 100,666 doubles, which `l4qlvr`
decodes at every comparison, format record) and q11 (a numeric FILTER over
282,287 rows). On the six single-block queries (q03, q06, q13, q14, q15, q18)
the approach factor is 0.9 to 1.5: both pay process start, and the data read
is a few kilobytes. The format record measured the Lean zstd decoder at 113
MB/s against libzstd's 1,785 MB/s; that is part of the Lean factor.

## 5. What the proposal keeps

- The generation protocol: immutable generations, `CURRENT` replaced only
  after full verification, the DLOG/DLB1/DLE1 delta log and CEP1 compaction
  marker (spec section 6.4), and the rule that a failed pack never becomes
  current.
- The SBM manifest with per-artifact SHA-256 and 65,536-byte Merkle chunk
  commitments (spec section 6.3), and range verification on `pread`.
- The term codec v2 for what goes into the dictionary, including out-of-line
  literals above 65,536 bytes as `blob-<sha256>.lit` artifacts (SBM10).
- The SPARQL parser, the reference evaluator as the specification and as the
  fallback for operators the id engine does not run, and the planner-soundness
  pattern (`docs/designissues/2026-09-06-planner-soundness-theorem.md`).
- The rules: the Lean definition is the format; encoder admission equals
  decoder admission; a byte change is a new wire version.

## 6. Proposed layout: SBM11 (wire version 11)

Wire version 10 (SBM10, IBK5) is the newest in the format registry
(`docs/shardborough-storage-spec.md` section 6.3), so the next free wire
version is 11. The names below were checked against the repository on
2026-10-11 (`grep -rn -E 'GDV1|GDX1|PRB1|PRM1|SBM11'`: no match).

| Name | Role |
| --- | --- |
| `SBM11` | manifest of a wire-version-11 generation |
| `GDV1` | global term dictionary: front-coded pages of terms in key order |
| `GDX1` | dictionary page directory: first key and byte offset of every page |
| `PRM1` | permutation metadata: per block, first and last key, row count, column frames |
| `PRB1` | permutation data: column frames of the blocks of one permutation |

### 6.1 Term ids

A term id is a `UInt64`. Bits 63 to 60 are a tag, bits 59 to 0 the payload.

| Tag | Term | Payload | Order of payloads |
| ---: | --- | --- | --- |
| 1 | blank node | sequence number within the generation (scope committed by the manifest, as SBM7 does) | by number |
| 2 | IRI | rank in the dictionary | key order (6.2) |
| 3 | literal stored in the dictionary | rank in the dictionary | key order |
| 4 | `xsd:integer`, canonical lexical form, value in 56 bits | 4-bit integer subtype (`xsd:integer`, `xsd:int`, `xsd:long`, … the 12 types QLever folds, `parser/RdfParser.h:227-242`) and a 56-bit offset-binary value | value, then subtype |
| 5 | `xsd:boolean`, canonical form (`true`, `false`) | 0 or 1 | value |
| 6 | `xsd:decimal` with a canonical form that fits a scaled 56-bit value (later stage) | scale and value | value |
| 7 | `xsd:double`, canonical form, low 4 mantissa bits zero (later stage) | the 60 high bits | value |
| 8 | `xsd:date`, `xsd:dateTime` in canonical form (later stage) | as QLever's `Date` bits | value |
| 14 | term added by the delta log after the generation was built | index into the generation's delta vocabulary | none (compared by key) |
| 0, 15 | reserved; 0 is never a term | | |

Rule: a literal is inline only when its lexical form is the canonical lexical
form (XML Schema 1.1 Part 2) of its value for its own datatype. Then the id
determines the RDF term exactly: `ofId (toId t) = t`, and `toId` is injective
on terms, so RDF term equality is id equality and a basic graph pattern is
matched on ids. This is where the proposal must differ from QLever, whose
inline form folds `"1936"^^xsd:int` and `1936` together (q15) and drops
mantissa bits (q20). A non-canonical literal (`"070"^^xsd:int`,
`"70"^^xsd:double`) goes into the dictionary as tag 3.

Measured on this data (`dict_estimate.py`, 2026-10-11): 282,287 `xsd:int`
literals, all canonical, become inline; 100,666 `xsd:double` literals have 220
distinct lexical forms, none canonical (`"70"`, not `"7.0E1"`), so they cost
220 dictionary entries.

Value comparison (`=`, `<`, ORDER BY on numbers) decodes tag 4 to 8 in
constant time; it never reads the dictionary. Comparison of two dictionary
literals of a numeric datatype (tag 3) needs their lexical forms; the
dictionary stores numeric literals of one datatype contiguously (6.2), so a
range of numeric tag-3 ids is known from the page directory.

The graph column uses a graph id: 0 is the default graph, any other value is
the term id of the graph name. A graph id is a separate type in Lean from a
term id (blockengine skill: "Use one cross-position TermId relation and a
tagged GraphId. Do not reserve a normal term ID for the default graph.").

### 6.2 The global dictionary (GDV1, GDX1)

- One dictionary per generation, sorted by an unsigned byte comparison of a
  term key. The key is: a class byte (2 IRI, 3 simple literal or
  `xsd:string`, 4 language-tagged string, 5 other datatype), then the UTF-8
  bytes of the IRI or lexical form, then `0x00`, then the language tag in
  lower case or the datatype IRI. Within each class, unsigned byte order of
  UTF-8 is Unicode code point order, which is the order SPARQL 1.1 section
  15.1 and `fn:compare` with the code point collation give for IRIs and
  strings. So ORDER BY on IRIs or on strings of one class is ORDER BY on ids,
  and no ICU collation is needed. A string-to-id lookup is a binary search
  over GDX1 (one page directory read, about 20 probes for 543,754 terms) and
  a scan of one page.
- The key is injective on RDF terms, with the language tag folded to lower
  case (RDF 1.1 Concepts section 3.3: the value space of language tags is in
  lower case, and lexical forms of language tags may be converted to lower
  case; the blockengine skill records the same rule for RDF 1.2). A term
  written with `@en-US` in one place and `@en-us` in another is one term and
  one id. This also removes the zone-key defect that the planner-soundness
  proof found for language-tagged constants (`2026-09-06-planner-soundness-theorem.md`
  section 6.3 item 2).
- Pages of a fixed number of terms (64 proposed), front coded: the first key
  complete, every next key as (shared prefix length, suffix). The page of id
  rank `r` is `r / 64`, so id to term is one page read and at most 63 suffix
  steps. GDX1 holds, per page, its byte offset and its first key.
- Measured (`dict_estimate.py` over the side index's byte-ordered word list,
  543,754 words, 41,771,588 raw bytes): front coding with 64 terms per page
  is 9,776,991 bytes; with zstd level 3 per page 6,589,903; with 256 per page
  9,338,132 and 5,436,337. QLever's FSST vocabulary is 16,133,525 bytes. The
  current IBK3 block dictionaries are 181,197,142.
- Out-of-line literals (above 65,536 bytes) stay `blob-<sha256>.lit` artifacts
  of SBM10; the dictionary entry is the term codec v2 `blob` form.
- Ids are dense ranks of one sorted list, so a term added later cannot get a
  rank. The delta log gives new terms tag-14 ids (6.7); compaction rebuilds
  the dictionary.

### 6.3 Permutations

Rows are quads `(s, p, o, g)` of ids. Four permutations are stored, each
sorted by its key and then by the graph id:

| Pattern bound positions | Permutation | Sorted next by |
| --- | --- | --- |
| none | PSO (smallest, 2,995,176 bytes zstd here) | subject |
| p | PSO or POS | subject or object, as the join needs |
| s, sp | SPO | predicate, then object |
| o | OSP | subject |
| po | POS | subject |
| so | OSP | predicate |
| spo | SPO | — |

PSO and POS give the two sort orders a predicate scan needs for merge joins:
a star join `?x p1 ?a . ?x p2 ?b` merges two PSO scans on `?x`, and `?i p
<const>` gives `?i` in order from POS (q07's first two patterns). SPO and OSP
serve a bound subject or a bound object with a variable predicate. SOP and
OPS add only the order "object within a subject" or "subject within an
object" for a variable predicate, which none of the 21 queries and none of
the plan rules of `L4Factoidal/Qlvr/Bgp.lean` needs. QLever's own minimum is
PSO and POS (`has-all-permutations: false`, format record section 3).
Measured (`codec_estimate.py`): the four chosen permutations take 12,658,926
bytes of zstd frames for columns 0 to 2 here, against 19,162,081 for all six.
The decision is reversible per generation: the manifest names the
permutations present, and a planner uses the ones named.

Blocks: each permutation is cut into blocks of at most 65,536 rows. As in
QLever, a predicate (for PSO, POS) or a subject (SPO) with many rows gets
blocks of its own, so a bound key reads only its own blocks.

### 6.4 Block format (PRB1) and codecs

A block is one column frame per column (`col0`, `col1`, `col2`, `g`), each
an array of `u64` ids before encoding. Each frame has a one-byte codec tag:

| Codec | Content | Size here, columns 0 to 2, all six permutations (`codec_estimate.py`) |
| --- | --- | ---: |
| 0 constant | no bytes; the value is in the block metadata | (part of the next two) |
| 1 raw | `8 × rows` bytes | 256,554,000 |
| 2 delta | LEB128 of the gap to the previous row when the key prefix is unchanged, otherwise of the value | 43,089,939 |
| 3 zstd | an RFC 8878 frame of the raw column (the Lean decoder `L4Factoidal/Codec/Zstd.lean`) | 19,162,081 |

The packer chooses the smallest encoding per frame, deterministically, and the
choice is part of the bytes. zstd is 2.2 times smaller than delta here.
Decoding speed: the Lean zstd decoder decodes 113 MB/s of output (format
record, "Column frames"), so the 42.8 MB of three columns of one full
permutation decode in about 0.38 s; one 31,250-row column in about 2.2 ms.
The delta decoder is not written; its Lean speed must be measured before the
default is fixed. The graph column of a generation with one graph is codec 0
in every block.

### 6.5 Block metadata (PRM1)

Per permutation, one PRM1 artifact read at open: per block, the first and the
last key (four ids each), the row count, the graph-id set when it has at most
a fixed number of members (as IBK4's graph-set summary), and per column the
codec, byte offset and length in PRB1 and the CRC32C of the frame. A scan
binary-searches the first keys for its key prefix and reads only the frames
of the columns it needs, as `l4qlvr` does (format record, plan rule 2: a
count with no output reads no frame). The row counts answer `COUNT(*)` of a
key prefix without a frame (q01 reads 0 frame bytes in `l4qlvr`).

The zone maps of SBM10 are not needed: on sorted data the first and last key
are exact bounds.

### 6.6 Manifest, integrity and the generation protocol

SBM11 keeps every SBM10 field that is not block-specific: wire version,
source identity, blank-node publication profile and scope, the blob table,
and per artifact a key, byte extent, SHA-256 and 65,536-byte Merkle chunk
commitment. It names the artifacts by role: `GDV1`, `GDX1`, and per present
permutation one `PRM1` and one `PRB1`. Six to eleven files replace one file
per block per sidecar (3,498 files for IBK3 here).

A `pread` of a block's frames is verified against the Merkle leaves of the
chunks it touches (`Harness/PosixRangeIO.lean:211` `readVerifiedRangeCached?`
does this today). The verification cost stays proportional to the bytes read,
which fall by the factors in section 4.3; it was 21 % to 24 % of IBK3 query
time.

Activation checks, in addition to what it checks today: every frame decodes
to its row count; every block's rows are sorted and lie between its first and
last key; consecutive blocks are ordered; every permutation denotes the same
multiset of quads (one pass per permutation computing an order-independent
digest of the quads, compared across permutations); every id of tag 2 or 3
is below the dictionary size; the dictionary keys are strictly increasing.

`CURRENT`, the CEP1 marker and the DLOG protocol are unchanged.

### 6.7 Updates: the delta log over ids

DLOG batches keep their term-level content (DLE1 serialises terms), so the log
format does not change. At open, the reader replays the committed batches
into an overlay: each term is looked up in the dictionary; a term that is
absent gets a tag-14 id in a per-open delta vocabulary. The overlay holds, per
permutation, the sorted inserted and deleted quads, and every scan merges its
block rows with the overlay rows of the same key range, as QLever's
`LocatedTriplesPerBlock::mergeTriples` does (`index/LocatedTriples.h:198`).
Compaction is the packer run over the base generation plus the log. The
overlay is in memory and grows with the log, so compaction is due when it
reaches a configured size; this is the same rule QLever has for its delta
triples.

### 6.8 A streaming packer with bounded memory

The packer today keeps memory bounded by batching publication
(`docs/designissues/2026-09-05-pack-publication-every-batch.md`; IBK5 here:
196 MB peak for a 338 MB source), and the shard-pack memory record measured
the cost of keeping a whole generation live until the end: 3.76 bytes of peak
footprint per source byte
(`docs/designissues/2026-09-05-shard-pack-profile-and-memory.md` section 3).
Sorted permutations need a sort, and a sort over more data than memory needs
an external sort. The proposed packer has three phases, each with a memory
bound set by the operator:

1. **Parse and collect terms.** Stream the source as today
   (`PackStream.quadIngestFeed`). For each batch of B source bytes, collect
   its distinct terms, sort them by key, write a sorted term run, and write the
   batch's quads with batch-local term numbers to a quad run file.
2. **Merge the dictionary.** k-way merge of the term runs by key into GDV1 and
   GDX1, writing per batch a remap file (batch-local number to global id).
   Inline terms (6.1) never enter a run. `l4qlvr side-index` already does this
   merge in Lean: 543,754 words in 9 runs of 65,536, merged by positioned reads
   of 1 MiB, 3.3 s, peak RSS 83 MB (format record, "String to Id"), with
   `L4Factoidal/Qlvr/Sort.lean` (`cmpBytes`, `mergeSortBy`).
3. **Sort the permutations.** Rewrite each batch's quads to global ids through
   its remap file, then sort runs of fixed-width 32-byte rows per permutation
   in memory (at most M bytes), write them, and merge the runs into PRB1
   blocks and PRM1 metadata.

Peak memory is about `max(B × c, M + k × read buffer)` with `c` the parse
cost per source byte, independent of the source size. Disk use during the
pack is about four times the row runs plus the dictionary runs. This is the
structure of QLever's builder (`index/VocabularyMergerImpl.h:36`
`mergeVocabulary`, `engine/idTable/CompressedExternalIdTable.h:1083`
`CompressedExternalIdTableSorter`). Every loop over runs, rows and keys is a
loop or tail call (CLAUDE.md, 2026-10-11), checked by
`tools/lean-tail-recursion-audit.py --gate` and a `tests/stack` case.

### 6.9 The query path

1. Parse (unchanged) and check the fragment the id engine runs (below);
   otherwise use the fallback.
2. Map every constant to an id: inline encoding, or a GDX1 binary search and
   one GDV1 page. A constant that is not in the dictionary and not inline
   makes its pattern empty. A non-canonical numeric constant in a pattern
   (`"070"^^xsd:int`) is a dictionary lookup like any literal.
3. Plan the BGP as `L4Factoidal/Qlvr/Bgp.lean` does (its header lists the
   rules): permutation by bound prefix, estimates from PRM1 row counts,
   least-estimate first, merge join when the left side is sorted on the join
   variable, hash join on the smaller side otherwise.
4. Run scans as block-at-a-time streams over `pread` (`Qlvr.scanFoldM`,
   `L4Factoidal/Qlvr/Bgp.lean:318`, is generic over the fetch monad and runs
   from `pread` today). Intermediate tables are columns of `UInt64` in
   `ByteArray`s (the format record's lesson: an `Array Id` boxes every value).
   LIMIT stops the scan; FILTER on `sameTerm` and on equality of two IRIs is id
   equality; FILTER and ORDER BY on numbers decode inline ids; FILTER on
   strings reads the dictionary pages of the candidate ids only.
5. Make RDF terms only for output rows (and for expressions that need a
   lexical form), page by page through GDV1.
6. Fallback: for an operator outside the fragment, the selected blocks are
   materialised as today and the reference evaluator runs, with the same
   guard rule as `quadEntriesForQuery` (the run-time guard and the theorem's
   hypothesis are one definition). The mode line names which path ran, so
   the census can count both.

The first fragment is the one `l4qlvr` runs today plus the four operators
`plannerFragment` admits (OPTIONAL, UNION, MINUS, BIND with a local
expression), and SPARQL 1.1 section 15.1 order, never QLever's order
(https://github.com/danbri/factoidal/issues/781 item 2).

### 6.10 Proof obligations

What changes:

| Obligation | Statement | Status |
| --- | --- | --- |
| Term id codec | `ofId (toId t) = some t` for every admitted term, and `toId` injective; inline only on canonical forms | new |
| Dictionary codec and order | `decode? (encode? terms) = terms` for GDV1/GDX1; keys strictly increasing; `key` injective on RDF terms (with the language-tag fold) | new; the page layout can reuse the generic paged-dictionary proof pattern of `PagedTermDictionaryCoreTheorems` |
| Column codecs | round trip for codecs 0, 1, 2; codec 3 by differential test against libzstd (1,860 frames today) until a proof exists | new |
| Block sortedness and metadata | a decoded block is sorted and between its first and last key; activation recomputes both (admission equals the decoder's check, as IBK4 does for its graph-set summary) | new |
| Permutation equivalence | the four permutations denote one multiset of quads | new; checked at activation, a theorem over the packer |
| Block skipping | a block whose key range excludes a prefix holds no row with that prefix (follows from sortedness; the analogue of `zoneMap_sound`) | new, short |
| Merge join | merge join on sorted inputs equals the reference join as multisets of solutions | new; hash join already proved (`SPARQL/IndexedEvalRefinement.lean`, list equality) |
| Planner soundness | `plannerSoundnessSelect`/`Ask` (`Storage/PlannerSoundness.lean`) are stated over manifest entry selection; the evaluator-side restriction lemmas (`SPARQL/DatasetRestriction.lean`) carry over unchanged; the storage side becomes "the selected block ranges contain every quad that matches a key prefix of the pattern" | adapted |
| End to end | the answer of the persisted query equals the reference evaluator over the generation's dataset | open: https://github.com/danbri/factoidal/issues/776 |

What still holds unchanged: the term codec v2 round trip for dictionary
entries; SBM decode and encode round trip pattern; Merkle leaf construction;
the DLOG/DLB1 framing; the evaluator theorems below the BGP.

### 6.11 Test plan

1. **Oracle.** `run.sh` with a third layout: q01 to q21 against the QLever
   oracle, with the documented differences of section 3.3 as listed expected
   differences (each with its reason), and q11 as an expected failure naming
   its issue until the evaluator defect is repaired.
2. **SPARQL-order answers.** For q07 and q16 (string ORDER BY), expected
   answers in section 15.1 order from the reference evaluator over
   `olympics.nt`, so that the new path is checked against SPARQL and not
   against QLever's collation.
3. **W3C persisted census.** `tools/w3c-persisted-census.sh` on the new layout:
   today 535 executed, 535 matched, 0 differed on the default graph and 29, 29,
   0 on named graphs (shardborough skill); the target is the same with the id
   path taken where admitted, and the mode counted.
4. **Differential.** IBK5 against SBM11 on every census input and on the
   oracle queries, as wire version 9 is for 10.
5. **Memory.** The expected-failure test of
   https://github.com/danbri/factoidal/issues/775: a query on a generation
   whose materialised size is above a fixed RSS cap (`ulimit -v`); it passes
   when the id path answers within the cap.
6. **Stack.** `tests/stack` cases for the external merge, a 65,536-row block
   decode and a merge join at a size above the wasm stack limit.
7. **Tail recursion audit** `--gate` exit 0 on every new module.

## 7. Migration in stages

Each stage has a target measured with the commands of section 2 on this
instance, and the stage is done when the target and the tests of 6.11 that
it reaches pass.

| Stage | Content | Acceptance target (olympics, this machine) | Issues |
| --- | --- | --- | --- |
| 0 | This record: baselines, scripts | (done) | 775, 776 context |
| 1 | Repair the two defects found: the IBK5 term parser fuel (4.4) and numeric comparison of derived integer types (3.3, q11) | IBK5 q21 within 1.3 times IBK3 q21 (today 16.4 s against 3.6 s); q11 34 rows on both paths and in `l4block-corpus` | two new issues (section 8) |
| 2 | Term ids (6.1) and the global dictionary GDV1/GDX1 with codecs and theorems; packer phases 1 and 2 | dictionary at most 10 MB (front coding, 64 per page: 9.8 MB measured); string-to-id under 1 ms per constant; packer phases 1 and 2 under 30 s, peak RSS under 300 MB, and peak RSS unchanged within 10 % when the source doubles | https://github.com/danbri/factoidal/issues/788; landed 2026-10-12, record [`2026-10-12-sbm11-stage2.md`](2026-10-12-sbm11-stage2.md) |
| 3 | PRM1/PRB1 for PSO, POS, SPO, OSP; SBM11 manifest; packer phase 3; activation checks of 6.6 | generation at most 2 times QLever's 38.5 MB (77 MB) with zstd frames; pack under 120 s wall; activation under 30 s; peak RSS of pack bounded as in stage 2 | https://github.com/danbri/factoidal/issues/789; landed 2026-10-12 without zstd frames (34.8 MB, 40 s, activation 6.4 s), record [`2026-10-12-sbm11-stage3.md`](2026-10-12-sbm11-stage3.md) |
| 4 | Id query path (6.9) for the BGP fragment with FILTER, ORDER BY, GROUP BY with COUNT, DISTINCT, LIMIT/OFFSET, with the reference fallback | q01–q21 equal to the oracle up to section 3.3; per query wall time at most 1.5 times the `l4qlvr` time of section 3.2 and peak RSS under 64 MB; q01 reads 0 frame bytes; q07 reads under 2 MB | closes part of 775 (BGP fragment); new issue for OPTIONAL/UNION/MINUS over ids; https://github.com/danbri/factoidal/issues/790 landed 2026-10-12 (oracle 21 pass, 0 fail; census 603 matched of 605 executed), record [`2026-10-12-sbm11-stage4.md`](2026-10-12-sbm11-stage4.md) |
| 5 | Delta overlay over ids (6.7); compaction through the packer | an INSERT then a query sees the row; compaction time within 1.2 times pack time; quad generations replay their log (https://github.com/danbri/factoidal/issues/770 for IBK4/IBK5 today) | 770 for the new layout; new |
| 6 | Proofs of 6.10 | `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only; theorem registry updated | 776 when the end-to-end theorem lands |
| 7 | Scale | the 775 benchmark at 10^8 triples or more, peak RSS and on-disk size beside latency, against QLever with comparable memory settings | 775 |

IBK3 and IBK5 stay readable and remain the differential oracle for SBM11 until
stage 7 (as wire version 9 is for 10).

## 8. Issues needed (not created by this work)

1. The IBK5 term parser takes its fuel from the length of the rest of the
   page (`Storage/TermWireV2.lean:240-241`), 65 % to 70 % of IBK5 query time
   (section 4.4). The IBK3 codec has the same shape at 4 % to 5 %.
2. SPARQL numeric comparison fails for `xsd:int` (and probably the other
   derived integer types): `FILTER(?age >= 72)` answers 0 rows over
   `"72"^^xsd:int` in `l4block-corpus`, `l4block-id-v3-query` and
   `l4block-quad-query` (section 3.3, q11). Needs a failing test per derived
   type before the repair.
3. Stage 2: global term ids and dictionary (6.1, 6.2).
4. Stage 3: sorted permutations, SBM11 (6.3 to 6.6, 6.8).
5. Stage 4: id query path for the BGP fragment (6.9).
6. Stage 5: delta overlay over ids (6.7).

Existing issues this design serves: https://github.com/danbri/factoidal/issues/775
(materialisation), https://github.com/danbri/factoidal/issues/776
(end-to-end theorem), https://github.com/danbri/factoidal/issues/778 (qlvr:
the planner, the external merge sort and the zstd decoder are reused) and
https://github.com/danbri/factoidal/issues/781 (SPARQL 15.1 order for a
Factoidal query path).

## 9. Limits of these measurements

- One dataset with 16 predicates, one graph, no blank nodes and short
  literals. The share of dictionary bytes and the benefit of PSO/POS depend on
  that shape; the stage-7 measurement at 10^8 triples is the check.
- Wall times are of one process per query: Shardborough and `l4qlvr` pay
  process start and open (20 to 85 ms) on every query; QLever is a running
  server. For the queries under 50 ms the comparison is of start-up costs.
- The python estimates (`codec_estimate.py`, `dict_estimate.py`) compute
  sizes, not Lean decode times. The delta codec and front-coded dictionary
  decode speeds in Lean are not measured.
- QLever's per-query RSS was not measured. Its server's resource log
  (`/home/user/qlvr-work/instance/olympics.server.resource-usage-log.tsv`,
  one sample every 2 s over the session that ran the oracle and the bench)
  shows 27 MB to 181 MB, median 87 MB. The 250 MB in section 3.1 is of the
  index build.
- The profile shares are of `perf` cpu-clock samples with 16 KiB DWARF
  stacks; a stack deeper than that is attributed to its leaf frames only.

## 10. Related work

- T. Neumann and G. Weikum. "RDF-3X: a RISC-style engine for RDF".
  *Proceedings of the VLDB Endowment* 1(1):647–659, 2008.
  https://doi.org/10.14778/1453856.1453927
- C. Weiss, P. Karras and A. Bernstein. "Hexastore: sextuple indexing for
  semantic web data management". *Proceedings of the VLDB Endowment*
  1(1):1008–1019, 2008. https://doi.org/10.14778/1454159.1454274
- H. Bast and B. Buchhold. "QLever: a query engine for efficient
  SPARQL+Text search". *Proceedings of CIKM 2017*, ACM, pp. 647–656.
  https://doi.org/10.1145/3132847.3132921
- J. D. Fernández, M. A. Martínez-Prieto, C. Gutiérrez, A. Polleres and
  M. Arias. "Binary RDF representation for publication and exchange (HDT)".
  *Journal of Web Semantics* 19:22–41, 2013.
  https://doi.org/10.1016/j.websem.2013.01.002
- D. Arroyuelo, A. Hogan, G. Navarro, J. L. Reutter, J. Rojas-Ledesma and
  A. Soto. "Worst-case optimal graph joins in almost no space". *Proceedings
  of SIGMOD 2021*, ACM. https://doi.org/10.1145/3448016.3457256 (the ring:
  one structure that answers all six triple orders; extended as "The Ring:
  worst-case optimal joins in graph databases using (almost) no extra
  space", *ACM Transactions on Database Systems*, 2024).
- D. Vrgoč, C. Rojas, R. Angles, M. Arenas, D. Arroyuelo, C. Buil-Aranda,
  A. Hogan, G. Navarro, C. Riveros and J. Romero. "MillenniumDB: an
  open-source graph database system". *Data Intelligence* 5(3):560–610,
  2023. https://doi.org/10.1162/dint_a_00209

Bibliographic details checked 2026-10-12 against dblp, the publishers' DOI
records as reported by dblp and the authors' pages
(https://users.dcc.uchile.cl/~gnavarro/abstracts/sigmod21.html,
https://users.dcc.uchile.cl/~gnavarro/abstracts/di23.html,
https://repositorio.uchile.cl/handle/2250/126366).
