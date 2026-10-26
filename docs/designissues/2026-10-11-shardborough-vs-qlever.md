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
| End to end | the answer of the persisted query equals the reference evaluator over the generation's dataset | open: https://github.com/danbri/factoidal/issues/776; plan, lemmas and status (block skipping, dictionary lookup, frame decoders and merge-join row pairs proved 2026-10-12): [`2026-10-12-sbm11-end-to-end-theorem.md`](2026-10-12-sbm11-end-to-end-theorem.md) |

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
| 5 | Delta overlay over ids (6.7); compaction through the packer | an INSERT then a query sees the row; compaction time within 1.2 times pack time; quad generations replay their log (https://github.com/danbri/factoidal/issues/770 for IBK4/IBK5 today) | 770 for the new layout; https://github.com/danbri/factoidal/issues/791 landed 2026-10-12 (compaction 0.33 times pack time; compacted generation byte-identical to a fresh pack), record [`2026-10-12-sbm11-stage5.md`](2026-10-12-sbm11-stage5.md) |
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

## 11. The source syntax of the store (2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/837. Owner, 2026-10-14,
verbatim: "SMB11 should store rdf graphs regardless of source formats - this is
why we have reflected w3c rdf core concepts into Lean. I don't see any reason
for the format to be made so explicit for internal data manipulation- file
formats are for exchange and publishing".

Sections 3 and 6 describe a store of RDF terms and quads. They do not depend on
the syntax of the source. Until 2026-10-14 the SBM11 packer read N-Triples and
N-Quads only, and each IBK packer chose its syntax module itself. Since
2026-10-14 every packer reads its source through
`L4Factoidal/RDF/Source.lean`. No file under `L4Factoidal/Storage/` imports a
module of `L4Factoidal.Syntax`. The gate is `tests/sbm11/storage_layering.py`.
The layer and its theorems are in
[`2026-09-03-rdf-parsing-strategy.md`](2026-09-03-rdf-parsing-strategy.md)
section 3f. The operating manual is `skills/shardborough-storage/SKILL.md`,
section "The source layer".

Results:

1. `l4sbm11-pack SOURCE OUTDIR [--format F]` reads N-Triples, N-Quads, Turtle,
   TriG, RDF/XML and JSON-LD. One dataset gives the same generation in every
   syntax. The data files are byte-identical. The manifests differ in the
   source length and the source digest (`tests/sbm11/syntax_independence.sh`).
2. A valid N-Triples or N-Quads source gives the same generation as before the
   change: the old and the new `l4sbm11-pack` give the same hash for the
   generated dataset of 88,000 quads (`multi.nt` and `multi.nq` of section 11.1).
3. The measurements of sections 3 and 6.8 used N-Triples and N-Quads sources.
   They do not change.
4. `l4sbm11 export GEN --format F` writes the dataset of a generation in the same
   six syntaxes, through the serialiser layer `L4Factoidal/RDF/Sink.lean`
   (section 11.2). Packing the export again gives the same data files (blank
   nodes: the same RDFC-1.0 canonical N-Quads).
5. The W3C RDF tests, read from the manifests on disk, run through the store:
   `tests/sbm11/w3c_roundtrip.sh` (section 11.3). 1,281 pass, 0 fail, 18
   expected-fail (out of 1,299).
6. `l4sbm11-dict-pack` and `l4factoidal parse FILE` read through the source layer.
   They have no format table of their own, and their output for a valid input did
   not change (`2026-09-03-rdf-parsing-strategy.md` section 3f).
7. The entry of the packer takes producers of RDF quads (`QuadSource`), not a file path.
   A file is one producer. A `Dataset` in memory and an HDT file are others, and their
   generations are tested (section 11.4,
   https://github.com/danbri/factoidal/issues/866).

### 11.1 What each syntax costs in a pack

Command: `tests/sbm11/syntax_bench.sh`, 2026-10-14, 4 CPUs, `l4sbm11-pack --workers 4`. The
dataset comes from `tests/sbm11/syntax/gen_multi.py`: the set "big" has 110,000
subjects (880,000 quads) and the set "small" has 11,000 subjects (88,000
quads). "generator" means that `gen_multi.py` wrote the text. "Lean writer"
means that `l4source-convert` wrote it with the library serialiser
(`turtleOfGraphAuto`, `StoreEndpoint.datasetToTrig`, `RdfXmlWrite.graphToRdfXml`,
`FromRdf.fromRdf`). The N-Triples, Turtle, RDF/XML and JSON-LD texts hold the
default graph. The N-Quads and TriG texts hold four named graphs and the default
graph. "Wall" is the wall time of the whole pack. The peak RSS comes from
`tests/trig-pack/peak_rss.py`, a small wrapper process. The column "Generation"
says whether the data files of the generation equal the files of the first
(reference) pack of the same kind.

| Set | Syntax (writer) | Source MB | Kquads | Workers | Wall s | MB/s | Kquads/s | Peak RSS MB | Phase 1 s | Generation |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| big | N-Triples (generator) | 84.4 | 880 | 4 | 8.8 | 9.6 | 100 | 204 | 3.09 | reference |
| big | Turtle (generator) | 39.0 | 880 | 1 | 15.6 | 2.5 | 56 | 227 | 10.88 | same |
| big | Turtle (Lean writer) | 31.0 | 880 | 1 | 14.7 | 2.1 | 60 | 225 | 9.53 | same |
| big | N-Quads (generator) | 102.0 | 880 | 4 | 8.9 | 11.5 | 99 | 200 | 3.39 | reference |
| big | TriG (generator) | 40.8 | 880 | 1 | 17.2 | 2.4 | 51 | 228 | 12.21 | same |
| big | TriG (Lean writer) | 84.4 | 880 | 1 | 27.7 | 3.0 | 32 | 225 | 22.32 | same |
| small | N-Triples (generator) | 8.3 | 88 | 4 | 0.7 | 11.8 | 126 | 77 | 0.28 | reference |
| small | Turtle (generator) | 3.8 | 88 | 1 | 1.7 | 2.2 | 52 | 79 | 1.28 | same |
| small | Turtle (Lean writer) | 3.0 | 88 | 1 | 1.2 | 2.5 | 73 | 77 | 0.77 | same |
| small | RDF/XML (Lean writer) | 6.9 | 88 | 1 | 2.1 | 3.3 | 42 | 137 | 1.51 | same |
| small | JSON-LD (Lean writer) | 7.4 | 88 | 1 | 2.0 | 3.7 | 44 | 135 | 1.56 | same |
| small | N-Quads (generator) | 10.0 | 88 | 4 | 0.8 | 12.5 | 110 | 73 | 0.35 | reference |
| small | TriG (generator) | 4.0 | 88 | 1 | 1.8 | 2.2 | 49 | 77 | 1.23 | same |
| small | TriG (Lean writer) | 8.3 | 88 | 1 | 2.5 | 3.3 | 35 | 77 | 2.06 | same |

Reading of the table:

- The 10 generations that are not a reference have the same data files as their
  reference. The syntax of the source does not change the store. The manifests
  differ in the source length and digest.
- N-Triples and N-Quads text is read in 4 byte ranges at the same time: 9.6 and
  11.5 MB/s for the whole pack on the big set. Turtle, TriG, RDF/XML and JSON-LD text is read by one
  worker: 2.1 to 3.7 MB/s. Phase 1 of Turtle takes 2.8 to 3.2 times as long per
  quad as phase 1 of N-Quads, and phase 1 of TriG takes 3.6 to 6.6 times as long
  (https://github.com/danbri/factoidal/issues/842).
- The peak RSS of the six big packs is 200 to 228 MB for every syntax. One
  batch holds all 880,000 quads and their terms. The two whole-document readers
  peak at 137 MB (RDF/XML) and 135 MB (JSON-LD) on the small set, where the other
  syntaxes peak at 73 to 79 MB
  (https://github.com/danbri/factoidal/issues/838,
  https://github.com/danbri/factoidal/issues/839). The slope of peak RSS against
  source size is in the rows `sbm11-pack-*-memory` of
  `tests/stack/lean_scaling.sh`: 0.23 (Turtle) and 0.21 (TriG) bytes per source
  byte, against 13.4 (RDF/XML) and 11.3 (JSON-LD).
- The Lean writers for RDF/XML and JSON-LD take time quadratic in the dataset
  (https://github.com/danbri/factoidal/issues/845 and
  https://github.com/danbri/factoidal/issues/712; rows `rdfxml-write` and
  `jsonld-write` of `tests/stack/lean_scaling.sh`: 4 times the data takes 15
  and 24 times as long). `l4source-convert` wrote the 8.3 MB of N-Triples text
  of the small set as RDF/XML in 21.8 s and as JSON-LD in 43.5 s. So those two
  syntaxes are in the small set only. For the big set, `l4source-convert` read the 82 MB of
  N-Triples text and wrote Turtle in 39.8 s, and read 100 MB of N-Quads text and
  wrote TriG in 21.9 s.
- Three runs of the script differ in wall time by up to 20 % for the big set.
  The first run started with a load average of 4.9 and took 1.6 s for the
  small N-Triples pack. The other two took 0.9 s and 0.7 s. The machine has 4
  CPUs, and another build ran during the first two runs. The table is the
  third run: it started with a load average of 1.7, on the tree that holds the
  triple term work of https://github.com/danbri/factoidal/issues/792.
- `oxigraph` was not on PATH on this machine, so the script printed no
  comparison row. It times `oxigraph load` of the N-Quads file when the command
  exists.

A cost that the script found: before 2026-10-14 the strict N-Triples reader
took 2,996 ms of phase 1 for the 8.3 MB of N-Triples text of the small set (4
workers). N-Quads text with the same quads took 477 ms.
`readTriple12` computed `r5.length + 1` for each statement. Section 3f of the
parsing record has the repair and the gate (`sbm11-pack-nt-vs-nq`).
### 11.2 Export: the dataset of a generation in any syntax (2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/837 item 6.

`l4sbm11 export GEN --format F [--out FILE] [--graph default|all|IRI]
[--prefix LABEL=IRI]... [--verify merkle|none]` reads the SPO permutation block
by block, in key order, and gives each quad to `Sink.Writer`
(`L4Factoidal/RDF/Sink.lean`). `Harness/Sbm11Export.lean` names no syntax. F is
`ntriples`, `nquads`, `turtle`, `trig`, `rdfxml` or `jsonld`. The writers and the
rules for a syntax with no graph name are in
[`2026-09-03-rdf-parsing-strategy.md`](2026-09-03-rdf-parsing-strategy.md)
section 3g.

How each syntax streams, in SPO order:

- N-Triples and N-Quads write one line for each quad.
- Turtle writes the triples of one subject as one statement. SPO order gives
  them in one run.
- TriG writes the Turtle statements inside a block. It opens a new block
  `GRAPH <name> { ... }` (`{ ... }` for the default graph) each time the graph of the
  next quad is not the open graph. SPO order visits the subjects in dictionary
  order, so a graph whose subjects interleave with those of other graphs gets
  several blocks. The TriG grammar allows several blocks of one name, and a reader
  merges them into one graph (the W3C tests `alternating_iri_graphs` and
  `alternating_bnode_graphs`). The generated dataset of 1 MB in
  `tests/sbm11/export_roundtrip.sh` (12,000 quads, the default graph and four named
  graphs) gives a TriG export of 641 blocks, and packs again to the same data files.
- RDF/XML and JSON-LD keep the quads and write at the end, because the library
  writers (`graphToRdfXml`, `fromRdf`) take a whole graph or dataset
  (https://github.com/danbri/factoidal/issues/846 and
  https://github.com/danbri/factoidal/issues/847).

Round trip through the store (`tests/sbm11/export_roundtrip.sh`, 51 pass, 0
fail, 1 expected-fail, out of 52). The fixtures are those of
`tests/sbm11/syntax_independence.sh`. For each one the generation is exported,
the export is packed, and the data files of the two generations are compared
byte for byte; the manifests differ in the source length and digest.

| Fixture | Content | Syntaxes exported and compared | Result |
| --- | --- | --- | --- |
| D1 | no blank nodes, default graph | N-Quads, N-Triples, Turtle, TriG, RDF/XML, JSON-LD | byte-identical (RDF/XML: an expected failure until 2026-10-14, below) |
| D2 | D1 and four quads in two named graphs | N-Quads, TriG, JSON-LD | byte-identical |
| D2 | the same | N-Triples, Turtle, RDF/XML | refused before any output, naming the first graph; `--graph default` gives D1, `--graph all` the union, `--graph IRI` that graph |
| D3 | blank nodes | all six | equal RDFC-1.0 canonical N-Quads |
| D4 | RDF 1.2: nested triple terms, a directional language string | N-Triples, N-Quads, Turtle, TriG | byte-identical |
| D4 | the same | RDF/XML, JSON-LD | refused: no form for a triple term |
| multi | 1 MB generated (2 sets) | N-Quads, TriG (named graphs); N-Triples, Turtle, RDF/XML (default graph) | byte-identical |
| empty | no quad | all six | each export packs to the empty generation |

The expected failure until 2026-10-14 (https://github.com/danbri/factoidal/issues/841):
the RDF/XML of D1 was correct, but the Lean RDF/XML reader applied the `xml:lang`
of a property element to the property elements after it, so `"Alice"` read back
as `"Alice"@en`. The reader is repaired (`docs/designissues/2026-09-03-rdf-parsing-strategy.md`
section 3c.7) and the case is an assertion; the generated set of 12,000 triples
also goes through RDF/XML now (before the repair, 3,000 of its quads read back
different). Also tested: an
N-Quads export is `dump` byte for byte (D1 to D4); `--out` and standard output
give the same text and a failed export leaves no file; `--prefix` shortens the
IRIs of Turtle and TriG and the export reads back the same; the usage errors
exit 2.

Memory (`tests/stack/lean_scaling.py`, 4 CPUs, 2026-10-14). The export holds one
block of the permutation, a window of 256 dictionary pages, the verified chunks of
the block and pages it reads (dropped as it goes) and a 64 KiB output buffer.
Each row measures peak RSS at x, 2x and 4x statements and bounds the slope
(RSS at 4x minus RSS at x) divided by (output bytes at 4x minus output bytes at x).

| Row | Syntax | Statements | Output at x and 4x | Peak RSS at x and 4x | Slope, bytes per output byte (bound 0.75) |
| --- | --- | ---: | ---: | ---: | --- |
| `sbm11-export-nq-memory` | N-Quads | 25,000 / 50,000 / 100,000 | 10.7 and 43.0 MB | 33 and 34 MB | 0.01 pass |
| `sbm11-export-ttl-memory` | Turtle | the same | 10.8 and 43.1 MB | 46 and 45 MB | -0.01 pass |
| `sbm11-export-trig-memory` | TriG, 100 graphs | the same | 10.9 and 43.7 MB | 34 and 46 MB | 0.39 pass |
| `sbm11-export-rdfxml-memory` | RDF/XML | 2,000 / 4,000 / 8,000 | 0.94 and 3.77 MB | 24 and 39 MB | 5.90 expected failure, https://github.com/danbri/factoidal/issues/846 |
| `sbm11-export-jsonld-memory` | JSON-LD | the same | 0.89 and 3.57 MB | 23 and 38 MB | 5.53 expected failure, https://github.com/danbri/factoidal/issues/847 |

A run by hand at 400,000 statements (172 MB of output) gave a peak RSS of 36 MB
for N-Quads (two runs) and 38 and 46 MB for Turtle, so the peak does not grow
beyond 100,000 statements. Three runs of the same Turtle export at 100,000
statements gave 46.6, 36.3 and 46.8 MB: the peak of one run varies by up to
10 MB. The 5.9 and 5.5 bytes per output byte of the two expected failures come
from the writers, which keep the quads until the end.

An early version of the export kept every dictionary chunk it had verified and
grew by about 4 bytes of RSS for each output byte (63 MB to 189 MB between 25,000
and 100,000 statements). Two changes made the peak flat: a window of 256
dictionary pages (`termOfIdLimit`), and `dropChunkRange` after each block and
each page window. A merkle-verified generation keeps a verified-chunk table per
file (`--verify merkle`); the export clears the entries it has finished with.

Stack. The N-Triples, N-Quads, Turtle and TriG exports of a node with 200,000
references and 200,000 literals run under `LEAN_STACK_SIZE_KB=512`, as does the
RDF/XML export of 100,000 references, and the case `sbm11-export` of
`tests/stack/run.sh` exports 600,001 quads with a 300,000-byte literal as N-Quads,
Turtle and TriG under that stack (and packs the Turtle and TriG exports again to
the same data files). The JSON-LD export of 20,000 references overflows a 512 KB
stack (https://github.com/danbri/factoidal/issues/853, row `JLD-WSTACK` of
`tests/known-defects/run.sh`); under the default stack the export of 30,000
references takes 67 s (https://github.com/danbri/factoidal/issues/712).

#### Time: the Merkle proof of each chunk (issue 854, 2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/854.

Symptom. Before the repair, the N-Quads export took 1.1 s for 25,000 statements,
5.5 s for 100,000 and 35 s for 400,000 (one run each, on a shared machine).
`l4sbm11 dump` took the same time. Four times more data took 5 to 6.4 times more
time. A pass over one permutation does work for each quad that does not depend on
the size of the store, so 4x data must take 4.0 times as long. The rows
`sbm11-dump-time` and `sbm11-export-nq-time` of `tests/stack/lean_scaling.py`
measure the CPU time of the child process at 100,000, 200,000 and 400,000
statements (the source of `sbm11_ttl`: 370 characters of literal for each
statement; generations of 38 MB, 76 MB and 152 MB) and bound the time at 4x data
to 5.25 times the time at x. Linear time gives 4.0. The bound lies between 4.5 (the
highest ratio after the repair, in three runs of each row) and 6.0 (the lowest before
it). The rows were committed first, as expected failures that name the issue.

| Row (CPU time, `--verify merkle`) | 100,000 | 200,000 | 400,000 | 4x data |
| --- | ---: | ---: | ---: | ---: |
| `sbm11-dump-time`, before the repair | 6.2 s | 13.3 s | 37.0 s | 6.0, expected failure |
| `sbm11-export-nq-time`, before the repair | 5.5 s | 13.0 s | 37.0 s | 6.7, expected failure |
| `sbm11-dump-time`, after | 3.5 s | 6.9 s | 13.7 s | 3.9, pass |
| `sbm11-export-nq-time`, after | 3.1 s | 5.8 s | 12.0 s | 3.9, pass |

A second run after the repair, with a load average of 3, gave 4.1 s, 6.9 s and 13.5 s
for `dump` (3.3) and 2.8 s, 6.3 s and 12.3 s for the export (4.5); a third gave 4.1 s,
7.3 s and 15.2 s (3.7) and 3.5 s, 6.8 s and 11.9 s (3.4). A row at 25,000 and
100,000 statements would have passed with the defect: `dump` took 1.5 s and 5.8 s
there (3.8 for 4x data, by hand).

Where the time went. A generation that no CURRENT pointer names is read with
`--verify merkle` by default: each 65,536-byte chunk of a file is admitted once,
by a Merkle proof against the root of the manifest. With `--verify none` (no
proof) `dump` took 3.2 s at 100,000 statements and 13.1 s at 400,000 (4.0 for 4x
data), so the growth was in the proofs. `perf` does not work on this VM (its
wrapper does not match the kernel), so the profile is gdb: 30 stack samples
(`thread apply all bt`, about one a second) of `l4sbm11 dump GEN --verify merkle`
at 400,000 statements. 12 samples are inside `BlockMerkle.proofWith?`, 7 are in the
check of the chunk (`verifyWith`, the leaf hash), 11 are elsewhere (id to term, the
N-Quads line). In those 12, `nextLevelWith` is up to 1,107 frames deep (one frame
for each pair of leaves). The stack of those samples, outermost first:
`_lean_main`, `Sbm11Cli.runDump`, `Sbm11Cli.quadText`, `Sbm11Gen.termOfIdLimit`,
`Dict.pageM`, `Dict.pageBytesM`, `Sbm11Gen.gdvFetch`, `Sbm11Gen.verifiedRead`,
`PosixRangeIO.readVerifiedRangeCached?`, `readCachedChunks`,
`readVerifiedChunkCached?`, `readVerifiedChunk?`, `BlockMerkle.proofFuelWith`,
`nextLevelWith` (repeated), `nodeWith`, then `sha256` or `List.toArray`.

Cause. `proofWith?` gives the proof of one leaf by computing every level of the
tree again from the leaves: `n - 1` node hashes for a file of `n` chunks. The reader
called it for each chunk that it admitted. A pass over the dictionary file (GDV1,
149 MB, 2,274 chunks) hashed about `n * (n - 1)` = 5.2 million nodes at about 3 µs
each (`concat` made lists of bytes for each node). Taking the proofs out
removed 28 percent of the CPU time of `dump` at 100,000 statements (5.8 s to 4.2 s)
and 55 percent at 400,000 (36.7 s to 16.4 s). The export drops the verified
dictionary chunks each time its window of 256 pages is full, so that its memory
stays flat, and then admits them again: more proofs than `dump`, the same cause.
The window of 256 pages is not the cause (`dump` with 4,096 pages took 5.1 s at
100,000 statements, the export with 256 took 5.6 s: the earlier measurement).

Repair (`L4Factoidal/Storage/BlockMerkle.lean`, `Harness/PosixRangeIO.lean`,
`Harness/Sbm11Gen.lean`).

1. `BlockMerkle.Tree` holds the levels of the tree in arrays, computed once
   (`Tree.ofLeavesWith`). A proof is one sibling for each level (`Tree.proof?`,
   `log2 n` reads). `Tree.proof?_ofLeavesWith` proves that it returns the proof of
   `proofWith?` for every hasher, every list of leaves and every index, by
   `proofFuelWith_eq_levels` and `proofArr_ofLevels`. The axioms are `propext`,
   `Classical.choice` and `Quot.sound`. `#guard`s compare the two for trees of 0 to
   9 leaves.
2. `PosixRangeIO.VerifiedChunkCache` is a structure: the chunks, and the tree,
   built from the leaves at the first chunk that the cache does not hold. Every
   cached read uses it, so the IBK3 readers (`readVerifiedRangeCached?`) have the
   same repair. `ChunkedArtifact.verifyChunkWith` still checks each chunk against the
   root of the manifest: a wrong table can refuse a chunk and cannot admit one.
   `dropDictChunks` and `dropChunkRange` clear the chunks and keep the tree. The
   count of the leaves is checked once, when the tree is built, and no longer by a
   walk down the list of leaves on every read. The reader without a cache,
   `readVerifiedRange?`, still computed `proofWith?` for each chunk; it is repaired in
   the next subsection. (This item said "the Merkle session tools of the IBK3
   layouts" until 2026-10-14. Those tools read through the cached reader. The callers
   of `readVerifiedRange?` are `l4block-shard-merkle-pread` and
   `l4block-shard-merkle-scan`.)
3. `BlockMerkle.concat` (the bytes of `a` and then of `b`, in the leaf hash and the
   node hash) made a list cell for each byte: 65,536 for a chunk. It is now
   `a ++ b`, one byte copy, and `concat_eq_spec` proves it the same bytes. It took
   2.0 s of the 16.4 s of `dump` at 400,000 statements (14.4 s after).
4. `tools/lean-tail-recursion-allow.txt` has a line for `levelsFuel` (one call for
   each level of the tree: `ceil(log2 n) + 1` deep).

After the repair the two rows pass (table above). The output is byte-identical:
`dump` of the generations of 25,000, 100,000 and 400,000 statements (md5 of the
output of the binary before the repair and of the repaired binary), and `dump` and
`export` in N-Quads, Turtle and TriG of the olympics generation under both read
checks. Other commands that read through the Merkle check, CPU time before and
after: `scan GEN spo` over all rows at 100,000 statements 6.3 s and 3.4 s; `verify`
(the activation checks) 3.5 s and 1.6 s at 100,000 statements and 27.1 s and 4.7 s
at 400,000 (the phase that checks the dictionary keys: 22.0 s and 1.7 s of wall time).

The olympics generation (`sbm11/s3/wfull`: 1,781,625 quads, 543,967 terms; GDV1 is
9.2 MB, 140 chunks, so the quadratic term is small here). One run each on the 4
vCPUs shared with another process (load average 1 to 3, 2026-10-14); peak RSS is
`ru_maxrss` of the child, the measure of `tests/trig-pack/peak_rss.py`. The
CLI default for this generation is `--verify none`, because a CURRENT pointer names
it; the repair does not change that path.

| Command | `--verify none`, before: wall / CPU / peak RSS | after | `--verify merkle`, before | after | Output |
| --- | --- | --- | --- | --- | ---: |
| `dump` | 15.9 s / 15.6 s / 77 MB | 17.2 s / 16.9 s / 80 MB | 18.2 s / 18.1 s / 120 MB | 17.9 s / 17.6 s / 117 MB | 337,695,911 bytes |
| `export` N-Quads | 19.7 s / 19.4 s / 40 MB | 19.2 s / 18.9 s / 40 MB | 79.9 s / 79.0 s / 46 MB | 28.1 s / 27.6 s / 46 MB | 337,695,911 bytes |
| `export` Turtle | 20.2 s / 19.9 s / 40 MB | 21.8 s / 21.5 s / 40 MB | 81.4 s / 80.0 s / 54 MB | 29.2 s / 28.9 s / 54 MB | 216,804,341 bytes |
| `export` TriG | 19.4 s / 19.2 s / 40 MB | 20.7 s / 20.5 s / 40 MB | 83.0 s / 81.7 s / 46 MB | 28.6 s / 28.2 s / 42 MB | 216,804,345 bytes |

Per statement, CPU time of the N-Quads export: 10.6 µs with `--verify none`; with
`--verify merkle` 44 µs before and 15.5 µs after. The CPU times of the `none`
columns before and after differ by -3 to +9 percent: the repair does not change that
path, so this is the noise of a shared machine. With
`merkle` the export is 8.7 s slower than with `none`: it drops the dictionary chunks
whenever its window of 256 pages is full, and each chunk that it needs again is read
and hashed again (SHA-256 of 65,536 bytes). Its summary line shows it: 2,020 MB
fetched to read 182 MB (11 times), against 182 MB with `none`. At this point `dump` kept
its chunks, so it had no such cost, and its peak RSS was 117 MB against 80 MB (it
forgets them since issue 859, next subsection). The output of N-Quads is the source
file byte for byte (337,695,911 bytes).

Oxigraph. The `oxigraph` command is not on PATH. pyoxigraph 0.5.11 (the same Rust
store, installed in a virtual environment) loaded `olympics.nt` in 9.7 s (a store of
172 MB, load peak 1.3 GB) and dumped it with `Store.dump` (one run each, same VM, same
load):

| Dump | wall / CPU / peak RSS | Output | Our `export` after, default read check (CPU time) |
| --- | --- | ---: | ---: |
| N-Quads | 11.7 s / 11.5 s / 114 MB | 338,825,059 bytes | 18.9 s (1.6 times) |
| Turtle | 12.0 s / 11.8 s / 115 MB | 200,593,437 bytes | 21.5 s (1.8 times) |
| TriG | 10.8 s / 10.7 s / 114 MB | 200,593,437 bytes | 20.5 s (1.9 times) |

The two N-Quads dumps hold the same 1,781,625 quads except the datatype of 282,287
integer literals: the source and our export have `xsd:int`, the dump of Oxigraph has
`xsd:integer`. The count of `xsd:int` in the source is 282,287. When `xsd:int` in our
export is rewritten to `xsd:integer`, the two sorted dumps have the same md5. Our
export takes 1.6 to 1.9 times the CPU time of the dump of Oxigraph and 40 MB against
114 MB of peak RSS.

#### Memory of dump, and the reader without a cache (issue 859, 2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/859. The measurements are of a
VM with 4 vCPUs that another job shared (load average 1.6 to 3.9); a time varies by up
to 10 percent between runs, and a peak RSS by up to 10 MB.

##### `dump --verify merkle` kept every chunk

Symptom. `l4sbm11 dump GEN --verify merkle` is the default for a generation that no
CURRENT pointer names. Its peak RSS grew with the store, and `export` under the same
check stayed flat. The row `sbm11-dump-memory` of `tests/stack/lean_scaling.py`
measures the peak RSS (the `peak-rss` that the command prints, which is VmHWM) at
100,000, 200,000 and 400,000 statements (output of 43 MB, 86 MB and 173 MB), and
bounds the slope (RSS at 4x minus RSS at x) divided by (output bytes at 4x minus
output bytes at x) at 0.75, as for the export rows. The repaired `dump` has a peak RSS
of 43, 62 and 61 MB at 25,000, 50,000 and 100,000 statements: it stops rising at about
50,000 statements, where GDV1 (19 MB) is above the budget of 16 MiB that the repair
keeps. The row starts at 100,000 statements so that it measures the slope on that
plateau. The row was committed first, as an expected failure that names the issue.

| `dump --verify merkle` | 100,000 | 200,000 | 400,000 | Slope, bytes per output byte | Slope, bytes per statement |
| --- | ---: | ---: | ---: | ---: | ---: |
| before the repair (the row; the peak RSS is the `peak-rss` that the command prints) | 184 MB | 238 MB | 390 MB | 1.66, expected failure | 719 |
| after the repair (the row, first run) | 60 MB | 62 MB | 64 MB | 0.03, pass | 14 |
| after the repair (the row, second run) | 61 MB | 61 MB | 64 MB | 0.02, pass | 9 |
| after the repair (the row, on the tree merged with origin/main) | 62 MB | 63 MB | 78 MB | 0.13, pass | 54 |
| after, by hand (three generations, one run each) | 62.9 MB | 63.6 MB | 65.4 MB | 0.02 | 8 |

By hand, before the repair: 192 MB, 238 MB and 405 MB (the issue said 387 to 437 MB at
400,000 statements). After the repair the peak at 400,000 statements has one of two
values: 64 MB (three of six runs) or 78 MB (three of six). At 100,000 statements it is
62 MB in every run.

Cause. `runDump` called `termOfId`, which is `termOfIdLimit` with a window of 4,096
dictionary pages and no `dropChunks`, and it never cleared the chunk cache of the
permutation file. Three things held memory: the verified chunks of GDV1 (the dictionary
values: 150 MB at 400,000 statements), the window of decoded pages (up to 4,096 pages
of 64 keys; about 110 MB when each key is a literal of 370 characters, by computation),
and the chunks of the SPO file. Only the first grows with the store; the window stops at
4,096 pages. With a window of 4,096 pages, no budget and `dropChunksBefore`, the peak
RSS at 400,000 statements is 267 MB.

Repair (`Harness/Sbm11Cli.lean` `runDump`; `Harness/Sbm11Gen.lean`
`dropChunksBefore`, `dropDictChunks`, `chunkKeepBytes`). Under `merkle`:

1. After each block, `dump` forgets the chunks of the permutation file that lie wholly
   before the next block (`dropChunksBefore`). `export` calls `dropChunkRange` for the
   block it has finished, which also forgets the chunk that holds the end of this block
   and the start of the next one; the next block then reads and checks that chunk
   again. The SPO file of the olympics generation has 6,902 blocks in 212 chunks, so
   that costs 452 MB of fetches (the two runs in the table below took 32.0 s and
   25.9 s).
2. The window of dictionary pages is the one of `export` (256 pages,
   `Sbm11Export.pageLimit`), and `dump` forgets the dictionary chunks when the window
   is full, unless a file holds at most `chunkKeepBytes` (16 MiB) of them. The window
   bounds the chunks read since the last drop: at most 256 pages, 16 MiB for each file.
   The budget keeps the dictionary of a small store: GDV1 of the olympics generation
   is 9.2 MB, so it is read and checked once.
3. Under `none` nothing changes (4,096 pages, no chunk is held).

The output of `dump` is the same byte for byte. md5 of the output of the binary before
the repair and of the repaired binary are equal for `dump` at 100,000, 200,000 and 400,000
statements (`--verify merkle`; also `none` at 100,000), for `dump` of the olympics
generation under both read checks (d0e42d33...; 337,695,911 bytes), for `dump GEN
pso`, `pos` and `osp` of the olympics generation, and for `dump-ids GEN spo`.

The choice of window and budget on the olympics generation (`--verify merkle`, one run
each; GDV1 is 9.2 MB, 8,500 pages, and the objects are read in any order):

| `dump` | Wall time | Peak RSS | Bytes fetched | Note |
| --- | ---: | ---: | ---: | --- |
| before the repair | 15.5 to 18.5 s | 116 to 118 MB | 23 MB | every chunk stays |
| the code of `export` (`dropChunkRange` for each block, all chunks forgotten at each window of 256 pages) | 32.0 s | 44.6 MB | 2,020 MB | the first version |
| the same with `dropChunksBefore` | 25.9 s | 45.6 MB | 1,568 MB | |
| window 256, budget 16 MiB, `dropChunksBefore` (this repair) | 17.0 to 17.7 s | 45.7 MB | 23 MB | three runs against three of the original |
| window 1,024, budget 16 MiB | 17.2 s | 50.8 MB | 23 MB | |
| window 4,096, budget 16 MiB | 16.0 s | 93.8 MB | 23 MB | |

Against the original in three runs taken one after the other, the repair takes 9 to 11
percent more user CPU time on the olympics generation under `merkle` (16.6 s against
14.9 s at the minimum) and 39 percent of the memory (45.7 MB against 116 MB). The
window causes the difference: the objects of the olympics generation are read in any order, and a window of 256 pages
holds a small part of the 8,500 pages, so pages are fetched and decoded again (182 MB
of ranges read, against 29 MB with a window of 4,096). Under `none` a window of 256
pages takes 16 to 20 percent more time than 4,096 (18.7 to 20.6 s against 15.6 to
17.0 s), so `none` keeps its window. With sequential data (the generations of 100,000
to 400,000 statements) the window does not matter: 12.5 to 14.3 s before the repair at
400,000 statements and 11.8 to 12.9 s after. The peak RSS at 400,000 statements for a
budget of 0, 8, 16, 32 and 64 MiB is 36, 48, 63, 108 and 160 MB: the memory rises by about
2.2 bytes for each byte of budget.

##### The reader without a cache computed the whole tree for each chunk

`PosixRangeIO.readVerifiedRange?` reads a range of a file by admitting each chunk it
touches under a Merkle proof. It called `BlockMerkle.proofWith?` for each chunk, which
computes every level of the tree from the leaves: `n - 1` node hashes for a file of `n`
chunks. A read of `c` chunks cost `c * (n - 1)` hashes. The callers are
`l4block-shard-merkle-pread` (any range of one artifact) and `l4block-shard-merkle-scan`
(four ranges of one artifact). The 854 repair covered the readers with a cache
(`readVerifiedRangeCached?`, `readVerifiedChunkCached?`), which the IBK3 tools and
`l4sbm11` use.

The shard packer cuts its blocks at 2 MiB (`maxBlockWireBytes`), so a shard directory
has at most about 64 chunks for each artifact, and the defect cannot show in a store
that the packer wrote. A first version of the row packed one statement with a literal of
8 MB, 16 MB and 32 MB (128, 256 and 512 chunks) and read the artifact with
`l4block-shard-merkle-pread`: 0.070 s, 0.149 s and 0.342 s of CPU time, 4.9 for 4x
chunks, which is under the bound of 5.25 on the unrepaired reader. The row was an
unexpected pass. In user time the cost of the unrepaired reader is 0.35 ms for each
chunk plus 0.8 microsecond for each pair of chunks (a fit to 512 and 2,048 chunks), so
the quadratic term is the larger one from about 450 chunks. The packer needs 11 s and
1.1 GB for a literal of 16 MB and 43 s and 3.0 GB for one of 64 MB (1,024 chunks), so a
row of 4x chunks above that size cannot use it.

`l4merkle-range-read` (`Harness/MerkleRangeRead.lean`) writes a file of `n` chunks of
pseudo-random bytes, its `.merkle` sidecar and its root in 1 s for 128 MB, and reads a
range with one of three readers (`leaves`: `readVerifiedRange?`; `tree`:
`readVerifiedRangeTree?`; `cached`: `readVerifiedRangeCached?`). The row
`merkle-range-read-time` reads the whole file at 512, 1,024 and 2,048 chunks (32 MB,
64 MB, 128 MB), and bounds the user CPU time (minimum of three runs) at 4x chunks to
5.25 times the time at x. The row bounds the user time because the reader holds the
chunks, their concatenation and the copy of the range (770 MB of RSS for 128 MB), and
the page faults of that memory cost 0.2 s to 1.9 s of system time in the same read of
64 MB on this VM, more than the user time of the repaired reader. The row prints the
system time. The row was committed first, as an expected failure that names the issue.

| `merkle-range-read-time`, user CPU time of one read of the whole file | 512 chunks | 1,024 | 2,048 | 4x chunks |
| --- | ---: | ---: | ---: | ---: |
| before the repair (the row) | 0.332 s | 1.229 s | 4.011 s | 12.1, expected failure |
| before, minimum of 5 runs by hand | 0.389 s | 1.097 s | 4.088 s | 10.5 |
| after the repair (the row) | 0.153 s | 0.320 s | 0.630 s | 4.1, pass |
| after, minimum of 5 runs by hand | 0.166 s | 0.305 s | 0.635 s | 3.8 |

By hand, at 4,096 chunks (268 MB): 18.6 s of CPU time (user plus system, minimum of 3
runs) before the repair and 1.39 s of user time after. The repaired reader at 512,
1,024, 2,048 and 4,096 chunks takes 0.166 s, 0.305 s, 0.635 s and 1.388 s of user time:
1.8 to 2.2 for each doubling. Seven runs of the row after the repair gave 3.5 to 4.7 for
4x chunks (the row takes the minimum of five reads at each size). The bound of 5.25 lies
between 4.7 and 10.5, the lowest ratio before the repair.

Repair (`Harness/PosixRangeIO.lean`, `Harness/ShardMerkleScan.lean`):

1. `treeOfLeaves` builds the proof table (`BlockMerkle.Tree`) of a file from its leaves;
   `treeOf? ref leaves` gives it when the leaves are `ref.chunkCount` many
   (`treeOf?_eq_some`, `treeOf?_eq_none`, by `Tree.leafCount_ofLeavesWith`).
2. `readVerifiedChunkTree?` admits a chunk under the proof of the table.
   `readVerifiedChunkTree?_eq` proves that this is the proof `proofWith?` computes from
   the leaves, for every list of leaves and index (it follows `Tree.proof?_ofLeavesWith`
   of the 854 work). The chunk is still checked against the root of the manifest, so a
   wrong table can refuse a chunk and cannot admit one. `treeOf?_eq_some` and
   `treeOf?_eq_none` depend on `propext` and `Quot.sound`; `readVerifiedChunkTree?_eq`
   depends on `propext`, `Classical.choice` and `Quot.sound`.
3. `readVerifiedRangeTree?` reads a range with a table that the caller built.
   `readVerifiedRange?` builds the table once for the call and keeps its signature.
   The loop over the chunks of the range (`readVerifiedChunksTree`) is a tail call with
   the chunks read so far in an accumulator; the old function recursed once for each
   chunk, read the rest of the range after a refused chunk, and had a line on the
   allow list of `tools/lean-tail-recursion-allow.txt` that is removed.
4. `l4block-shard-merkle-scan` builds the table once for its four reads.
5. `readVerifiedSingleChunkRange?` (no caller) takes its proof from the table too.

A refused chunk still gives `none`, and the bytes of an accepted range are the same.
`tests/merkle-range/run.sh` reads files of 1 to 17 chunks (whole, short and one-byte last
chunks) at random ranges with the three readers and compares the SHA-256 of the result
with the one that Python computes from the file, checks that a range outside the file or
of length 0 is refused, and changes one byte in each chunk in turn: every reader refuses
a range that touches the chunk and reads a range that does not. 1,223 pass, 0 fail
(out of 1,223), in 16 s. With the check in `readVerifiedChunkProof?` taken out
(`if true || ...`) the same test gives 746 pass, 477 fail (out of 1,223). The outputs of
`l4block-shard-merkle-pread` and `l4block-shard-merkle-scan` on a packed shard
(`docs/fstar-extracted/samples/music.ttl`) are equal to those of the binaries before the
repair.

### 11.3 The W3C RDF tests through the store (2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/837 item 5. Command:
`bash tests/sbm11/w3c_roundtrip.sh`, part (p) of `tests/sbm11/run.sh`.

For every positive evaluation test of the W3C suites for N-Triples, N-Quads,
Turtle, TriG and RDF/XML (RDF 1.1 and RDF 1.2, 19 manifests) and of the JSON-LD
toRdf manifest, and for every positive syntax test of the same suites:

1. The manifest is read from disk (`l4sbm11-w3c list-rdf`, `list-jsonld`, which use
   `Harness.loadManifest` of the Lean W3C runners). The row gives the action file,
   the result file and the base IRI that the manifest states for the test
   (`mf:assumedTestBase` and the path; for JSON-LD `option.base`, else `baseIri` and
   the input).
2. Store route: `l4sbm11-pack ACTION GEN --format F --base BASE`, `l4sbm11 verify
   GEN`, `l4sbm11 dump GEN`. The dump is compared with the result file by dataset
   isomorphism (`l4sbm11-w3c compare`: `Dataset.isomorphicOutcome`, and RDFC-1.0
   canonical N-Quads where the bounded search cannot decide). Language tags compare
   in lower case, lexical forms exactly, blank nodes up to a bijection. A syntax test
   has no result file: the expected dataset is the one the parser gives.
3. Parser route: the same document with `Source.parseDocument`, the same base, the
   RDF version of the manifest, compared with the result file in memory.

Nine empty documents (not from a W3C suite) must pack to a valid generation that
holds no quad.

A test that the parser passes and the store fails is a failure of the run. A test
that fails in both routes is a failure unless the table
`tests/sbm11/w3c_roundtrip_xfail.tsv` has a row for it with the URL of an open issue;
a listed test that passes in the store fails the run. Result, 2026-10-14, 4 jobs,
36 s:

| Suite | Store | Parser |
| --- | --- | --- |
| N-Quads RDF 1.1 syntax | 53 pass, 0 fail (out of 53) | 53 pass, 0 fail (out of 53) |
| N-Triples RDF 1.1 syntax | 41 pass, 0 fail (out of 41) | 41 pass, 0 fail (out of 41) |
| TriG RDF 1.1 | 143 pass, 0 fail (out of 143) | 143 pass, 0 fail (out of 143) |
| TriG RDF 1.1 syntax | 99 pass, 0 fail (out of 99) | 99 pass, 0 fail (out of 99) |
| Turtle RDF 1.1 | 145 pass, 0 fail (out of 145) | 145 pass, 0 fail (out of 145) |
| Turtle RDF 1.1 syntax | 74 pass, 0 fail (out of 74) | 74 pass, 0 fail (out of 74) |
| RDF/XML RDF 1.1 | 126 pass, 0 fail (out of 126) | 126 pass, 0 fail (out of 126) |
| N-Quads RDF 1.2 | 41 pass, 0 fail (out of 41) | 41 pass, 0 fail (out of 41) |
| N-Quads RDF 1.2 syntax | 7 pass, 0 fail (out of 7) | 7 pass, 0 fail (out of 7) |
| N-Triples RDF 1.2 | 41 pass, 0 fail (out of 41) | 41 pass, 0 fail (out of 41) |
| N-Triples RDF 1.2 syntax | 7 pass, 0 fail (out of 7) | 7 pass, 0 fail (out of 7) |
| TriG RDF 1.2 | 26 pass, 0 fail (out of 26) | 26 pass, 0 fail (out of 26) |
| TriG RDF 1.2 syntax | 24 pass, 0 fail (out of 24) | 24 pass, 0 fail (out of 24) |
| Turtle RDF 1.2 | 32 pass, 0 fail (out of 32) | 32 pass, 0 fail (out of 32) |
| Turtle RDF 1.2 syntax | 41 pass, 0 fail (out of 41) | 41 pass, 0 fail (out of 41) |
| RDF/XML RDF 1.2 | 29 pass, 0 fail (out of 29) | 29 pass, 0 fail (out of 29) |
| JSON-LD toRdf | 327 pass, 0 fail, 18 expected-fail (out of 345) | 327 pass, 0 fail, 18 expected-fail (out of 345) |
| JSON-LD toRdf syntax | 16 pass, 0 fail (out of 16) | 16 pass, 0 fail (out of 16) |
| Empty documents | 9 pass, 0 fail (out of 9) | 9 pass, 0 fail (out of 9) |
| Total | 1,281 pass, 0 fail, 18 expected-fail (out of 1,299) | |

Findings of the first run:

- 21 store-only failures, all RDF 1.2 TriG documents with an annotation block
  `{| ... |}` (15 of the 26 evaluation tests and 6 of the 24 syntax tests of the
  TriG 1.2 suites; the first run was 1,260 pass, 21 fail, 18 expected-fail, out of
  1,299). The cause was the TriG chunk scanner, which read
  the braces of an annotation as graph block braces. The repair is in
  `TriGChunkFold.lean` and its theorems
  (`2026-09-03-rdf-parsing-strategy.md` section 3e). The IBK4 and IBK5 packers use
  the same scanner, so they read these documents now (`l4block-shard-pack` with
`ibk5` refused `trig12-eval-annotation-01.trig` with "expected '.' after triple"
before, and packs it now).
- 18 JSON-LD toRdf tests fail in both routes. The in-memory Lean runner passes them
  (`l4jsonld-probe`: 467 pass, 0 fail, 0 skip, out of 467) because it passes a
  document loader and the options of the test entry. The source layer passes none:
  10 tests need a loader (remote, scoped or sourced contexts), 4 need
  `rdfDirection`, 3 need the processing mode `json-ld-1.0` and 1 needs
  `expandContext`. They are rows of the expected-failure table with
  https://github.com/danbri/factoidal/issues/848.
- The parser and the store agree on the other 1,281 tests.

### 11.4 The packer entry: a producer of RDF quads (2026-10-15)

Tracking: https://github.com/danbri/factoidal/issues/866. Owner, 2026-10-15,
verbatim: "isn't packing (into shardborough?) done against abstract rdf graph or
dataset API not a text file format???". The question follows the rule of
2026-10-14 at the start of this section.

**Before.** Below its entry, the packer used RDF terms only. Phase 1 took
`Triple × Option Subject`, and the dictionary key is a function of the `Term`. The
entry of phase 1 was a file. `phase1Worker cfg source outDir w start stop runTerms`
took a path and a byte range, and read them through `RDF.Source`. No function packed
the quads of a `Dataset` value, of the reader of another store, or of the answer of
a query. `l4sbm11 compact` packed without text, from the generation and the delta
log, through its own route (ids and key bytes).

**After.**

1. `L4Factoidal/RDF/QuadSource.lean` is in the library. It imports `RDF.Graph` and no
   syntax module. `QuadSource` has one field, `next : IO (Option Batch)`. A batch is an
   array of quads. A quad is a `Triple` and an `Option Subject` (`none` is the default
   graph). `next` gives the next batch. At the end, and at every later call, it gives
   `none`. A batch is never empty. When a call throws, every later call throws.
2. `Pull σ` is the pure form of a producer: from a state, the next batch and the next
   state, or `none`. `ofStep` and `ofPull` make a producer from a state and a step.
   `ofDataset` and `ofArray` make the producers of a `Dataset` and of an array of quads.
3. `Sbm11Pack.packQuads sources outDir runTerms blockRows sortRowsMax sourceId`
   (`Harness/Sbm11PackLib.lean`) is the entry. `sources` has one `IO QuadSource` for
   each phase-1 worker. Each worker opens its producer and gives each batch to the
   phase-1 sink (`openPhase1`: `consume` and `finish`). Then the entry runs phases 2 and
   3 (`packBatches`). Phase 1 knows RDF terms, triples and graph names.
4. `fileRangeSource cfg path start stop` is the producer of a file. It reads the bytes
   `[start, stop)` through the source layer, in chunks of 64 KiB. The syntax is named in
   the code that makes the producers (`chooseFormat`, `readCfg`, `planRanges`,
   `fileRangeSource`, `openDatasetSource`) and nowhere in `packQuads` or in the phases it
   runs. `runPack` makes one producer for each byte range of an N-Triples or N-Quads file
   (the cut at line starts is the optimisation of that producer, `planRanges`), and one
   producer for a file of any other syntax.
5. `sourceId` is what the manifest records about the source: a length and a SHA-256. A
   file gives its own. `SourceId.noDocument` is the length 0 and the SHA-256 of the empty
   byte string.
6. Command line: `l4sbm11-pack FILE.hdt OUT` (or `--format hdt`) packs the triples of an
   HDT file. `l4sbm11-pack FILE OUT --via-dataset` reads the whole document into a
   `Dataset` and packs the `Dataset`. The first log line names the producer.

**Producers.**

| Producer | Code | Reads |
| --- | --- | --- |
| a byte range of a file | `fileRangeSource` | the six syntaxes of the source layer |
| a `Dataset` in memory | `QuadSource.ofDataset` | the default graph, then each named graph, in list order |
| an array of quads | `QuadSource.ofArray` | the array, in order |
| an HDT file | `HDT.GraphStore.quadSource` | subject by subject, with the HDT reader (`HDT/Triples.lean`, `HDT/Dictionary.lean`). A structure that it cannot read stops the pack with an error. |

The TDB2 reader (`Tdb2/Read.lean`) gives N-Quads lines as text (`quadLines`). The HDT
reader gives RDF terms (`HDT.idToTerm`). So the store in this record is an HDT file.

**Why `packQuads` takes `IO QuadSource`.** A producer keeps its state in a mutable
reference. Lean marks the objects that the closure of `IO.asTask` reaches as shared
between threads, and it copies a shared object at an update. A reference that is made
before the task and used in the task keeps its array shared at every update. Measured
2026-10-15 (Lean 4.33.1, linux x86_64, `lean -c` and `leanc -O2`):

```lean
def loop (r : IO.Ref (Array Nat)) (n : Nat) : IO Unit := do
  for i in [0:n] do
    let a ← r.swap #[]
    r.set (a.push i)

def main : IO Unit := do
  let r ← IO.mkRef (Array.range 5000000)            -- made before the task
  let r1 ← IO.asTask (do
    let t ← IO.monoNanosNow
    loop r 100
    pure ((← IO.monoNanosNow) - t)) .dedicated
  match r1.get with
  | .ok dt => IO.println s!"before the task: {dt / 1000000} ms"
  | .error e => throw e
  let r2 ← IO.asTask (do
    let r ← IO.mkRef (Array.range 5000000)          -- made in the task
    let t ← IO.monoNanosNow
    loop r 100
    pure ((← IO.monoNanosNow) - t)) .dedicated
  match r2.get with
  | .ok dt => IO.println s!"in the task: {dt / 1000000} ms"
  | .error e => throw e
```

Two runs printed `before the task: 9557 ms` and `in the task: 29 ms`, then
`before the task: 7351 ms` and `in the task: 23 ms`. Each round copies the array of
5,000,000 numbers when the reference is made before the task. So each worker opens its
producer in its own thread (`IO QuadSource`), and `ofStep` takes the state out of its
reference with `swap` while the step runs, so that the step holds the only reference.

**Output before and after (2026-10-15).** The packer of origin/main 3e832dfe and the
packer of this change, both built in the same tree, packed the same sources. The
comparison covers the exit status, the log lines (the times and the peak RSS masked) and
every file of the generation directory (`diff -r`: the 10 data files, their 10 `.merkle`
files and `manifest.sbm11`, 21 files). It ran twice: with the build of this change
before the merge of origin/main 724fdd79 (the Turtle reader commits of issue 865), and
with the final build, which includes them. Both runs gave the result in the table.

| Sources | Packs | Result |
| --- | ---: | --- |
| the 27 fixtures of `tests/sbm11/syntax` (D1 to D4, `bnode_collide`, `lang_scope`, `scope_paths`), each with `--workers 4` and with `--workers 1` | 54 | identical |
| `tests/sbm11/gate/gate.nq` and `tests/sbm11/gate12/gate12.nq`, `--workers 4` | 2 | identical |
| the generated sets of `gen_multi.py` (1,500 and 11,000 subjects) in four syntaxes, with `--workers 4` and with `--workers 3 --run-terms 3000` (many term runs) | 16 | identical |
| the positive evaluation and syntax tests of the W3C RDF suites and of the JSON-LD toRdf manifest, as `tests/sbm11/w3c_roundtrip.sh` lists them, with `--format F --base IRI --workers 1` | 1,290 | identical: 1,278 packs, and 12 that exit 1 in both packers with the same message |
| `olympics.nt` (337,695,911 bytes, 1,781,625 quads), `--workers 4` | 1 | identical, 21 files |

In the final comparison, `l4sbm11-pack`, `l4sbm11`, `l4factoidal` and `l4sbm11-w3c` have the
same SHA-256 as the binaries of the final build.

**Time and memory on olympics (2026-10-15).** `l4sbm11-pack olympics.nt OUT --workers 4`,
4 CPUs. Five runs of each packer, alternating, the old packer first in each pair. The new
packer is the build before the merge of origin/main 724fdd79. Another session used the
machine: the load average at the start of a run was between 0.85 and 3.03.
`/usr/bin/time -f "%e %U %S %M"` gives the wall time, the CPU time (user plus system) and
the peak RSS. The phase 1 time is `phase1-ms` of the log.

| Packer | Wall s | CPU s | Phase 1 s | Peak RSS kB |
| --- | --- | --- | --- | --- |
| origin/main 3e832dfe | 18.42 (17.95 to 20.05) | 45.72 (43.82 to 48.10) | 9.26 (8.29 to 9.53) | 208,956 (206,980 to 218,304) |
| this change | 18.00 (17.24 to 18.58) | 43.99 (42.57 to 45.41) | 8.57 (7.98 to 8.66) | 206,208 (201,620 to 220,468) |

Median, and the least and the greatest value in brackets. The medians of the new packer are
2 % (wall time), 4 % (CPU time), 7 % (phase 1) and 1 % (peak RSS) below those of the old
packer. The ranges overlap in every column, so the difference is inside the noise of this
machine: the new packer is not slower and does not use more memory. The greatest peak RSS
of the new packer (220,468 kB) is 2,164 kB above the greatest of the old one, and the peak
RSS of one packer differs by 11,000 to 19,000 kB between runs.

**Tests of the new producers.** `bash tests/sbm11/quad_source.sh`, part (u) of
`tests/sbm11/run.sh`: 555 pass, 0 fail, 0 expected-fail (out of 555), 12 to 14 s.

1. `l4sbm11-quad-source selftest` (468 checks, in process, no document text). For seven
   datasets and eight batch sizes (0, 1, 2, 3, 7, 100, 4,096 and 1,000,000): the batches
   of `ofDataset` and `ofArray`, taken together, are `Dataset.quadList`. Each batch has at
   least one quad and at most `max 1 batch` quads. They are the batches of the pure model
   (`Pull.batches`). `next` gives `none` again after the end. A step that throws makes
   every later call throw. Then each dataset is packed ten ways: from the `Dataset`, from
   1, 2 and 5 producers, with batches of 1, 3 and 4,096 quads, with term maps of 7, 40 and
   262,144 terms, with the quads in reverse order, and with the default graph and the
   named graphs as two datasets. Every file of the nine packs, the manifest included, is
   byte-identical to the file of the first.
2. A `Dataset` in memory is packed, verified (`l4sbm11 verify`), dumped (`l4sbm11 dump`)
   and compared with the `Dataset`. The comparison is by dataset isomorphism
   (`l4sbm11-w3c compare`) and by the RDFC-1.0 canonical N-Quads of both
   (`l4factoidal canonicalize`). Seven datasets: empty; a default graph; named graphs; a
   mixed one (blank nodes as subject, object and graph name, a repeated triple, a triple
   in two graphs, a named graph with no triple); one that stresses the dictionary
   (Unicode, escapes, a literal of 100,000 characters, integers and other datatypes);
   one with RDF 1.2 terms (a directional literal, nested triple terms); and 8,800
   generated quads. RDFC-1.0 is defined on RDF 1.1 datasets, so the RDF 1.2 dataset is
   compared by isomorphism only. Three of the datasets are also packed from 3 producers
   with batches of 5 quads and a term map of 50: the files are byte-identical to those
   of 1 producer.
3. The file route and the Dataset route (`--via-dataset`) give byte-identical generations,
   the manifest included, for 33 sources: every syntax fixture of `tests/sbm11/syntax`,
   the two gate fixtures and a generated dataset of 1,500 subjects in four syntaxes.
4. HDT. Two fixtures of hdt-cpp 1.3.3 (`third_party/testing/hdt`; 343 quads and 1 quad).
   The dump of the generation equals the HDT store's own dump (`HDT.searchTriples`,
   by isomorphism and by RDFC-1.0) and the N-Triples file that the fixture was made
   from. The manifest holds the length and the SHA-256 of the HDT file. `--workers 4`
   and `--format hdt` on a file named `store.bin` give the same files as the default.
   A truncated file and a text file are refused with an error. On each fixture, an id of
   the subject, predicate or object role that is 0 or lies outside the dictionary gives an
   error and not a term, and so does a subject after the last subject of the triples
   section (`hdt-errors`, 9 checks). The query decoders of `HDT/Store.lean` give a sentinel
   term in these cases, and a pack would copy it into the generation.
5. `tests/sbm11/storage_layering.py` reads 128 files and finds 0 violations. It checks
   that `RDF/QuadSource.lean` imports no syntax module and names no syntax.

**Compaction (item 3 of the issue).** `l4sbm11 compact` ends in the code of the pack.
`Sbm11Compact.packCompacted` calls `packBatches` (phases 2 and 3) and writes the epoch
files. Its phase 1 works on ids. Steps A to C of `Harness/Sbm11Compact.lean` scan the SPO
permutation twice and write one term run and one quad run. A term run holds the used
dictionary keys, which the dictionary stores in key order, merged with the keys of the
used overlay terms. The steps build no RDF term. The phase 1 of `packQuads` builds a
`Term` for each id, hashes it into a map, builds its key and sorts the keys.

`l4sbm11 compact GEN OUT --via-quads` is compaction through that phase 1. One SPO scan of
the overlaid generation decodes each row to RDF terms (`Session.termOf`) and gives the
quads of a block, as one batch, to a phase-1 sink (`openPhase1`), as the producers of a
pack do. Its output is byte-identical to the output of the default route in every test
that compares them: the olympics generation (23 files) and parts (h) (the gate fixture
with its updates), (i) (olympics after updates) and (m) (a base with RDF 1.2 triple
terms) of `tests/sbm11/run.sh`. The cost, measured 2026-10-15 on the olympics generation
(1,781,625 quads, no delta log), 3 runs of each route, alternating, with a load average of
2.27 to 2.62 at the start of a run:

| Route | Wall s | CPU s | Peak RSS kB | Phase 1 s | Phase 2 s |
| --- | --- | --- | --- | --- | --- |
| default (ids and key bytes) | 10.35 (9.91 to 13.34) | 13.89 (13.70 to 17.04) | 234,860 (225,960 to 257,800) | 1.31 (1.23 to 1.82) | 1.24 (1.15 to 1.49) |
| `--via-quads` (terms) | 20.35 (20.13 to 20.90) | 23.86 (23.19 to 24.00) | 253,964 (246,804 to 255,580) | 10.00 (9.69 to 10.11) | 1.80 (1.77 to 2.10) |

Median, and the least and the greatest value in brackets. For the default route, phase 1
is steps A to C. Phases 3a and 3b take 6.10 s and 1.56 s in the default route, and 6.52 s
and 1.51 s in the reference route. The reference route takes 1.97 times the wall time, 1.72
times the CPU time and 1.08 times the peak RSS of the default route. Its phase 1 runs in
one thread. The default route does not decode or hash a term: compaction moves data that
the store already holds as ids and as key bytes in key order. So the default stays the id
route. The reference route is the specification-shaped route and the differential oracle
of the default route: both give the same bytes in the three states above. The condition
`viaQuads` in `Sbm11Compact.main` selects the route.

**Theorems** (`RDF/QuadSourceTheorems.lean`; their axioms are `propext`,
`Classical.choice` and `Quot.sound`; `tools/lean-unbuilt-modules.py --gate` passes).
`Cursor.take` adds quads of a dataset to a batch until the batch is full or the dataset
ends. `take_quads`: the quads of the accumulator and of the start position are the quads
of the result and of the end position. `take_size_le`: the result has at most `n` quads
(or as many as the accumulator had). `take_short`: when the result has fewer than `n`
quads, the end position has no quad. `datasetPull_spec`: one step of the producer
either ends with no quad left, or gives a batch of at least one and at most `max 1 batch`
quads and a position that holds the others. `ofDataset_flatten`: the batches of the
producer, taken together in order, are `Dataset.quadList`, in at most as many steps as
there are quads. `datasetPull_batches_size`: each batch has at least one quad and at most
`max 1 batch` quads. `quadList_eq_foldDataset`: `Dataset.quadList` is the order of
`Source.foldDataset`. So a `Dataset` that the parser returns and the producer of that
`Dataset` give the quads in the order in which the source layer gives them for a
document that it parses as a whole. The statements are about `Pull`, the pure form.
`ofPull` and `ofStep` add a reference, and `l4sbm11-quad-source selftest` checks that the
batches of the producer are those of `Pull.batches`.
