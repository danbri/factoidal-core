# SBM11: the end-to-end theorem, its lemmas and their status

Date: 2026-10-12. Status: plan written; 12 lemmas proved in the first
landing; L3b, L4d and L4e proved in the second (OKR batch 2 KR 1.5,
https://github.com/danbri/factoidal/issues/801; sections 9 and 10); the
end-to-end theorem open (section 2 table, section 3 obstacles); L5g and L5g′
(the left outer join of OPTIONAL on ids, https://github.com/danbri/factoidal/issues/775)
proved 2026-10-13, L5g″ open; L4g, L4h, L4i and L5h (the scan with candidates
and the semi-join reduction of sideways information passing,
https://github.com/danbri/factoidal/issues/809) proved 2026-10-13 (section
12). Gap issue: https://github.com/danbri/factoidal/issues/776.
Tracking: https://github.com/danbri/factoidal/issues/787. Related work
issues: https://github.com/danbri/factoidal/issues/792 (dictionary, item 4),
https://github.com/danbri/factoidal/issues/793 (items 2 and 4),
https://github.com/danbri/factoidal/issues/795 (item 3).

Owner, 2026-10-12, verbatim: "Work on #776 in subagent".

Earlier records: [`2026-10-12-sbm11-stage2.md`](2026-10-12-sbm11-stage2.md)
(dictionary, term ids), [`2026-10-12-sbm11-stage3.md`](2026-10-12-sbm11-stage3.md)
(permutations, PRM1, PRB1), [`2026-10-12-sbm11-stage4.md`](2026-10-12-sbm11-stage4.md)
(the id query path and the reference fallback). Design:
[`2026-10-11-shardborough-vs-qlever.md`](2026-10-11-shardborough-vs-qlever.md)
section 6.10. The planner theorem of the earlier layout:
[`2026-09-06-planner-soundness-theorem.md`](2026-09-06-planner-soundness-theorem.md).

## 1. The statement

Names that do not exist yet are in *italics*; section 4 lists them.

- `D`: a source dataset, a list of quads of RDF terms.
- `G`: the files of a generation: GDV1, GDX1, four PRM1, four PRB1 and the
  manifest, as byte arrays.
- *`packSpec D`*: the generation that `l4sbm11-pack` writes for `D` (today an
  `IO` program over run files; it has no pure specification).
- *`Admitted G`*: the checks of `l4sbm11 activate` as a pure predicate (today
  `IO` code in `Harness/Sbm11Gen.lean`).
- *`denote G`*: the quads of permutation SPO of `G`, decoded with the
  dictionary: rows by `Block.decodeBlock`, ids by `TermId.ofId?`.
- *`storeOf G`*: an `IdQuery.Store Id` that reads the byte arrays of `G`
  (the `IO` store of `Harness/Sbm11Query.lean` reads the same bytes after a
  Merkle check).
- `ref D q`: the reference evaluator, `evalSelect env (datasetOfQuads D) q`
  (`Harness/Sbm11Query.lean`, `runReference`, with every quad selected).

**E1 (the id path).** For every `D`, every query `q` with
`IdQuery.translate q = .ok plan`, and `G = packSpec D`:

    decode (runPlanM (storeOf G) plan) ≡ ref D q

where `decode` maps the ids of each output row to terms with `TermId.ofId?`,
and `≡` is equality of solution multisets; with ORDER BY, equality of lists
up to the order of rows that the ORDER BY keys do not separate (SPARQL 1.1
section 15.1 leaves that order open).

**E2 (the fallback).** For every `D` and every query `q` with
`IdQuery.translate q = .error _`:

    fallback G q ≡ ref D q

where `fallback G q` is `runReference` over the quads that the planner guard
selects (predicate scans of PSO, or all of SPO), with `env.dataset` set to
the same selection.

**E0 (the generation).** For every `D`: `Admitted (packSpec D)` and
`denote (packSpec D) = norm D` as sets, where `norm` is the term
normalisation the packer applies (stage 2 record: language tags in lower
case, canonical inline integers).

E1 and E2 do not assume their conclusion: their hypotheses are the plan
(E1), the refusal (E2) and that `G` is the packer's output. A form "for
every `G` with `denote G = norm D`" is also acceptable; a form "for every
`G` whose id answers equal the reference" is not.

## 2. Decomposition

| Id | Lemma | Status | Where |
| --- | --- | --- | --- |
| L1a | Dictionary codec: `decodeDict (encodeDict? keys) = keys`; decoded keys strictly increasing | proved before (stage 2) | `Storage/Sbm11/DictTheorems.lean`: `decodeDict_encodeDict?`, `decodeDict_sorted` |
| L1b | Term ids: `ofId? (toId? t) = t`; `toId?` injective; graph ids | proved before (stage 2) | `Storage/Sbm11/TermIdTheorems.lean`: `ofId?_toId?`, `toId?_eq_iff`, `graphId_ofName_ne_default` |
| L1c | Page decoder over a byte array equals the list decoder | proved before (stage 2) | `Storage/Sbm11/DictFastTheorems.lean`: `decodePageAt_eq` |
| L1d | Lookup: over the bytes `encodeDict? keys` writes, `Dict.lookupM` answers without error a result `res` with `res = some r ↔ keys[r]? = some k` (the rank of `k` when it is a key, `none` when it is not), and the GDX1 header decodes to the key and page counts (https://github.com/danbri/factoidal/issues/792 item 4) | **proved now** | `DictLookupTheorems.lookupM_encodeDict` (with `cmpBytesAt_eq`, `searchPagesM_spec`, `pageM_dict`, `firstKeyAt_page`, `entryM_gdxBytes`, `parseGdxHeader_gdxBytes`) |
| L1e | `DictRange.lowerBoundM` over the same bytes answers `lowerBoundList` of the keys (the number of keys below the target) | **proved now** | `DictRangeTheorems.lowerBoundM_encodeDict` |
| L2a | `Column.decodeColumnAt` equals `Column.decodeColumn` | proved before (stage 3) | `ColumnTheorems.decodeColumnAt_eq` |
| L2b | `FrameWords.decodeWords b n i = decodeWordsRef b n i` (the words of `decodeColumnAt`), `n ≤ 2^64` | **proved now** | `FrameWordsTheorems.decodeWords_eq` |
| L2c | `FrameWords.decodeWordsRange b n i lo hi` = rows `[lo, hi)` of the words, when the whole frame decodes | **proved now** | `FrameRangeTheorems.decodeWordsRange_eq` |
| L2d | `PrmAt.decodePrmAt` equals `Block.decodePrm` (https://github.com/danbri/factoidal/issues/793 item 2) | **proved now** | `PrmAtTheorems.decodePrmAt_eq`, `decodePrmAt_admitted` |
| L2e | `Block.decodeBlockAt` equals `Block.decodeBlock` | tested only | `Block.lean` `#guard`s; `stage3_check.sh` tamper cases |
| L2e′ | What activation's block check gives: a block that `decodeBlockAt` admits has four frames that `decodeColumnAt` decodes to `m.rows` ids below `2^64`, ending at the PRM1 lengths, rows strictly increasing from `m.first` to `m.last`; the word decoder on those frames gives the words of the checked columns | **proved now** | `BlockAtTheorems.decodeBlockAt_ok`, `colsSortedGo_sorted`, `decodeColumnAt_lt`, `decodeWords_of_decodeBlockAt` |
| L2f | `Column.encodeColumnFast` equals `Column.frameBytes` (https://github.com/danbri/factoidal/issues/795 item 3) | tested only | `Column.lean` `#guard`s (8 columns); the packer decodes every frame it writes; activation re-encodes every frame |
| L2g | `at64 (words xs) r = xs[r].toUInt64` (the word read of `Codec.Zstd.word64`) | **proved now** | `ScanWordsTheorems.word64_bytes`, `at64_words` |
| L3a | Block, PRM1 and manifest round trips; a decoded block is sorted between its PRM1 first and last row | proved before (stage 3) | `BlockTheorems`, `ManifestTheorems` |
| L3b | An admitted generation's four permutations denote one quad set (https://github.com/danbri/factoidal/issues/793 item 4) | **proved (second landing)**, over the exact check that activation now runs (section 9); the bucket files of the check are tested, not proved | `PermSet.perms_same`, `perms_same_mem`, `sameQuads_perm`; `Harness/Sbm11PermCheck.lean`; `tests/sbm11/run.sh` part (j) |
| L3c | Packer correctness, E0 | open | — |
| L4a | Block skipping is complete: a row of block `k` whose key prefix equals the scan key is in a block that `blocksFor` returns and `selects` admits | **proved now** | `ScanTheorems.blocksFor_complete`, `decodedRow_selected`, `chain_sorted` |
| L4b | Inside a block, the two binary searches select exactly the rows whose comparison is `.eq`, given that `rowKeyCmp` is monotone over the rows; the `full` shortcut | **proved now** | `ScanTheorems.keyBound_spec`, `blockRows_exact`, `fullFor_row` |
| L4c | `rowKeyCmp` over the words of decoded columns is `prefixCmp` of the rows; so the in-block range is exact over decoded columns, and over the columns of every block that activation admitted | **proved now** | `ScanWordsTheorems.rowKeyCmp_words`, `scanRows_exact`; `BlockAtTheorems.scanRows_exact_of_decodeBlockAt` |
| L4d | The metadata shortcuts of `scanFoldM`: `colConst?` is sound on a block that activation admitted: columns 0 to 2 from the row order; the graph column because a frame of nine bytes that holds nine rows or more can only be a constant frame (a raw frame takes 8 bytes per row, a delta frame at least one), so L2f is not needed | **proved (second landing)** | `ScanFoldTheorems.colConst_sound`, `decodeColumnAt_short`, `between_agree` |
| L4e | `scanFoldM` as a whole: the chunks are the rows of the permutation with the key prefix, filtered by `checks`, `named`, `eqs` | **proved (second landing)** for a store over the PRM1 entries and PRB1 bytes in memory (`m = Id`) with no overlay, under the activation checks (`prmAdmitted`, `decodeBlockAt` of every block); the chunk tuples (`tuples`: constants, else columns) and, with `fill = true`, the columns alone (`colTuples`) | `ScanFoldTheorems.scanFoldM_tuples`, `scanFoldM_columns`, `blockChunk_tuples`, `chunkOfCols_tuples`, `keyRange_spec`, `readFrames_slice`, `selectRows_spec`, `blockPlan_keep` |
| L4f | A frame decoder reads only the bytes of its frame: in any slice `[s, e)` of the array that contains the frame, the column (and the words) at the shifted start are the same (`readFrames` reads one such slice per block) | **proved now** | `FrameLocalTheorems.decodeColumn_local`, `decodeColumnAt_extract`, `decodeWords_extract` |
| L4g | Sideways information passing, frame level (https://github.com/danbri/factoidal/issues/809): on a frame that `decodeWords` decodes to the words `ws`, `Sip.findWords` returns exactly the rows of `[lo, hi)` whose word is a candidate, in order, with their words, from any candidate pointer, for candidates in non-decreasing order; `Sip.gatherWords` and `Sip.pickWords` return the words of strictly increasing rows; the pointer test is membership | **proved (2026-10-13)** | `SipTheorems.findWords_spec`, `gatherWords_spec`, `pickWords_data`, `probe_mem`, `sorted_spec` (with `deltaFindGo_step`, `deltaFindGo_eq`, `deltaGatherGo_step`, `deltaGatherGo_eq`, `wordsFindGo_spec`, `decodeWords_delta`) |
| L4h | Block skipping by candidates: a block that `Sip.mayHold` rules out (no candidate between the join-column values of its first and last rows, `IdQuery.sipRange`) holds no row the scan keeps whose join column is a candidate | **proved (2026-10-13)** | `SipTheorems.mayHold_false`; `SipScanTheorems.sipRange_bounds`, `sipSkip_none`, `col_le_of_le`, `prefixCmp_eq_cols` |
| L4i | The scan with candidates (`IdQuery.scanFoldSipM`) is the full scan filtered: over an in-memory store of an admitted permutation with no overlay, the output tuples of exactly the rows the full scan keeps whose join column holds a candidate; with the join column first, the full scan's tuples (L4e) filtered by the candidate test on the first value | **proved (2026-10-13)** for `m = Id`, no overlay, `key.size < 4`, candidates in non-decreasing order | `SipScanTheorems.scanFoldSipM_tuples`, `scanFoldSipM_filter`, `sipChunk_tuples`, `scanBlockSipM_step`, `forIn_blocks_sip` |
| L5a | Merge join, index part: for join columns in non-decreasing order, the index arrays `Qlvr.mergeJoin` builds its output from zip to every pair of rows whose join values are equal and whose other shared columns agree, in left-then-right row order | **proved now** | `Qlvr.MergeTheorems.mergeGo_spec`, `mergeGo_pairs`, `mergeJoin_eq` |
| L5a′ | Merge join, solution part: a row pair of id tables is a pair of compatible solutions exactly when its shared columns are equal, so the join output equals the reference join (SPARQL 1.1 section 18.5) of the decoded solutions, as multisets | open | — |
| L5b | Hash join (`Qlvr.hashJoin`) on id tables equals the reference join | open | — |
| L5c | FILTER: a conjunction is applied conjunct by conjunct | proved before (stage 4) | `IdQueryTests.ebvOrFalse_evalIn_and` |
| L5d | FILTER on ids: rule 1 (term identity) and rule 2 (STRSTARTS as a rank range) agree with `Expr.evalIn` | tested only | `IdQueryTests.lean` `#guard`s on 23 terms |
| L5e | ORDER BY shortcuts on ids agree with `sparqlOrderValue` | tested only | `IdQueryTests.lean` `#guard`s |
| L5g | Left outer join (OPTIONAL on ids, https://github.com/danbri/factoidal/issues/775), index part: `OptJoin.outerPairs` over the inner pairs gives `ljSpec` (each left row with the right rows it accepts, in order, or alone with `none`), also directly over the index arrays of `Qlvr.mergeGo` (join columns sorted on both sides); (a) every left row is in the output; (b) an output row is an accepted pair, or a left row that accepts no right row, and every accepted pair is in the output; (c) left row `i` occurs `max 1 c` times, `c` the right rows it accepts, and the length is the sum | **proved (2026-10-13)** | `OptJoinTheorems.outerPairs_eq`, `outerPairs_merge`, `ljSpec_left_row`, `ljSpec_mem_some`, `ljSpec_mem_none`, `ljSpec_complete`, `ljSpec_count_row`, `ljSpec_length` (with `runPairs_spec`, `outerGo_spec`) |
| L5g′ | Left outer join, solution part over rows of ids (`IdRow`: (variable, id), unbound absent): decoding `idLeftJoin L R` is SPARQL 1.1 `leftJoin` (section 18.5) of the decoded rows with condition `true`, as a list, when `Term.eqb` of two decoded ids is id equality on the ids that occur; `idLeftJoin` is `ljSpec` with id compatibility as the candidate relation; the index arrays of `outerPairs` mapped to rows and decoded are that `leftJoin`; `LeftJoin(Ω1, Ω2, c)` is `LeftJoin(Ω1, Filter(c2, Ω2), true)` when `c` on a compatible merge is `c2` on the right row (the id path applies a group's FILTER, which reads only the group's variables, to the group's rows) | **proved (2026-10-13)** | `OptJoinTheorems.leftJoin_decode`, `idLeftJoin_eq_ljSpec`, `outerPairs_leftJoin`, `leftJoin_filter_right` |
| L5g″ | Left outer join, table part: the `Table` `OptJoin.leftOuterJoin` builds (`gather`, `gatherOpt` over `ByteArray` columns, id 0 for an unbound variable) denotes the rows of `idLeftJoin` of the denotations of its inputs; the hash path (`OptJoin.hashPairs`, `Std.HashMap`) computes `innerSpec`; on two id tables whose shared variables are bound in every row (`IdQuery.flattenOptional`), id compatibility of two rows is equality of the shared columns | open; tested | `OptJoinTheorems` `#guard`s (9 sample joins: merge, hash with one and two shared columns, cross product, empty sides, unbound ids on the left); `tests/sbm11/run.sh` part (d), 16 `ids-optional-*` queries against the reference engine |
| L5h | Semi-join reduction (issue 809): a join whose right input is filtered to the rows whose join value passes a test that every left value passes is the same join; over rows (inner join pairs, left outer join), over the index arrays of the merge loop and of `OptJoin.outerPairs` over it (join columns non-decreasing), and over solution mappings of ids (SPARQL 1.1 Join and LeftJoin; `join_decode`: decoding `idJoin` is SPARQL Join); the planner's candidates are in non-decreasing order and contain every left value | **proved (2026-10-13)**; the hash join over a reduced right side and the `Table` of `scanSipTableM` are tested only (the open steps L5b and L5a′) | `SemiJoinTheorems.joinRows_semijoin`, `ljRows_semijoin`, `mergeGo_semijoin`, `outerPairs_merge_semijoin`, `mergeSpec_rows`, `ljSpec_rows`, `idJoin_semijoin`, `idLeftJoin_semijoin`, `join_decode`; `SipScanTheorems.sipCands_sound` |
| L5i | Post-processing on decoded rows (https://github.com/danbri/factoidal/issues/823): `substituteExistentials` returns an EXISTS-free expression unchanged, so the id path's residual FILTER (`IdQuery.residualHolds`) is the reference FILTER closure for every active graph; `evalConstruct` is `constructGraphOf` of `formSolutions`; the first-rows cut of `IdQuery.firstRowsOf` does not change `formHasSolution` (ASK), `formSolutions` (CONSTRUCT) or `selectPost` (SELECT). The id path calls `selectPost`, `formHasSolution`, `formSolutions` and `constructGraphOf` on the decoded rows, so each step equals the reference once L6a gives equal input | **proved (2026-10-13)**; that `Expr.evalIn` and the post-WHERE functions read no `EvalEnv.dataset` is by inspection | `IdPostTheorems.substituteExistentials_existsFree`, `substituteExistentialsList_existsFree`, `residualHolds_eq`, `evalConstruct_eq`, `formHasSolution_take_one`, `firstRowsOf_ask`, `formSolutions_take`, `numberRows_take`, `selectPost_take` |
| L6a | E1 from L1 to L5 | open | — |
| L6b | E2: the fallback selection keeps every quad the query can read (the planner theorem of 2026-09-06 restated for PSO scans), and the `datasetOfQuads` bridge (that record's section 6.6 item 1) | open | — |
| L6c | The JSON printer (`keyJsonInto`) equals `jsonOfTerm` | tested only | `tests/sbm11/run.sh` part (b), byte comparison on 21 queries |
| L7a | Delta overlay (stage 5, https://github.com/danbri/factoidal/issues/791): for sorted `base` and `del`, `filterDel cl base del = base.filter (r ∉ del ∧ ¬ cl r.g)` | **proved (stage 5)** | `OverlayTheorems.filterDel_eq` |
| L7b | The sorted union holds the rows of both lists and is strictly sorted | **proved (stage 5)** | `OverlayTheorems.unionRows_mem`, `unionRows_sorted` |
| L7c | `mergeRows cl base del ins` is strictly sorted and `r ∈ it ↔ (r ∈ base ∧ r ∉ del ∧ cl r.g = false) ∨ r ∈ ins`; a strictly sorted list is determined by its members, so the merge is THE sorted list of that set | **proved (stage 5)** | `OverlayTheorems.mergeRows_spec`, `sorted_eq_of_mem_iff`, `mergeRows_eq_of_spec` |
| L7d | One replay step changes the denoted quad set as INSERT DATA (`∪ {q}`), DELETE DATA (`∖ {q}`) and CLEAR/DROP (graph `g` removed) say, over the `Std.HashSet` state the reader uses | **proved (stage 5)** | `OverlayTheorems.step_add`, `step_remove`, `step_clear`, `replay_append`, `denote_empty` |
| L7e | `scanFoldM` with an overlay: each insert with the key prefix is merged into exactly one chunk (the first selected block whose last row is not below it, else the last chunk), the deletes of a block are the slice `[lowerIdx first, upperIdx last)`, and the chunks stay in row order | tested only; not direct from L4e (section 3) | `tests/sbm11/run.sh` parts (h), (i); `tests/stack/run.sh` case `sbm11-delta` |
| L7f | Replay's term-to-id map: a term with a base id keeps it; any other term gets one tag-14 id (`Overlay.tagDelta`), so ids stay injective and never collide with base ids | tested only | `Harness/Sbm11Query.lean` `Session.idOrNew`; parts (h), (i) |
| L7g | Compaction: the generation `l4sbm11 compact` writes for `G` with log `L` equals `packSpec` of the updated quads | tested only (byte-identical artifacts to a fresh pack, gate and olympics); open with L3c | `tests/sbm11/run.sh` parts (h), (i) |

## 3. Open lemmas: the obstacle of each

- **L2e.** `decodeBlock` decodes each frame from `bs.take len` and wants an
  empty rest; `decodeBlockAt` decodes from the whole array and checks the end
  position. One direction of the bridge is proved (`decodeColumn_local`: a
  frame read from `P ++ R` is read the same from `P ++ R'`); the other
  direction (a frame that decodes from `P` alone with an empty rest) and
  `colsSortedGo` against `rowsSorted` remain. The scan does not need L2e:
  `BlockAtTheorems` works from `decodeBlockAt` directly.
- **L2f.** `pushVar` writes the groups by shifts (`n >>> (7 * j)`), `putVar`
  by division through `vbeGo`; `varExtraGo` counts the groups. The codec
  choice compares `d.size - 1 < 8 * size` against
  `(deltaBytes xs).length < 8 * length`. Not started.
- **L3b.** Closed in the second landing by an exact check in activation
  (section 9). Until then activation compared the four permutations only by
  an order-independent digest, and digest equality does not give set
  equality.
- **L3c.** The packer is an `IO` program over run files with four parallel
  tasks. A proof needs a pure specification (sort, deduplicate, block,
  encode) and a refinement of the run-and-merge program to it.
- **L4e.** Closed in the second landing (section 10). What stays open of
  the scan: the overlay branch (L7e) and a store in `IO` (the theorem is over
  `m = Id`; the `IO` store of `Harness/Sbm11Query.lean` reads the same
  bytes by `pread`).
- **L5a′, L5b.** `Qlvr.mergeJoin` and `hashJoin` work on `Table` (one
  `ByteArray` of words per column). A statement needs the table's
  denotation (rows of ids, then solutions through `TermId.ofId?`), and the
  reference join over lists of solutions (`SPARQL/IndexedEvalRefinement.lean`
  proves a hash join for a different representation). L5a gives the row
  pairs; the remaining step is that equal shared ids are compatible
  solutions (ids are injective, `TermIdTheorems.toId?_eq_iff`) and that
  `joinOutput`'s `gather` copies the rows of the pairs. `hashJoin` uses
  `Std.HashMap` and needs a lookup characterisation of its own.
- **L5g″.** The same step as L5a′ and L5b, for the left outer join: a
  denotation of a `Table` as rows of ids (columns read with `word64`, id 0
  left out), a lemma that `gather` and `gatherOpt` copy the rows of their
  index arrays (`copySlice` of runs, `put64`), and a lookup characterisation
  of `Std.HashMap.alter` and `getD` for `hashPairs`. L5g and L5g′ give
  everything from the index arrays on.
- **L6a.** Needs everything above, plus the plan rules: the permutation
  chosen by `permFor` holds the bound positions as a prefix, and the join
  order does not change the multiset. Since issue 823 (L5i) the id path also
  answers ASK, CONSTRUCT, SELECT expressions and aggregates by the reference
  post-WHERE functions on its decoded rows, and FILTERs outside
  `backendLocal` by the reference FILTER on decoded terms; for those queries
  L6a is the remaining step, with two more pieces: `decodeRowsM` gives one
  solution mapping per row (a variable for each column whose id is not 0,
  through `Store.termOf`), and a residual FILTER applied after the joins of
  the whole BGP has the value it has on its group's rows (stage 4 record
  section 12.1, an argument, not yet a theorem).
- **L6b.** The planner theorem of 2026-09-06 is stated over IBK manifest
  entries; SBM11 selects by PSO key prefix, so the storage side is "a PSO
  scan of predicate `p` returns every quad with predicate `p`" (L4a, L4b,
  L4e) and the evaluator side reuses `SPARQL/DatasetRestriction.lean`. The
  `datasetOfQuads` bridge is open since 2026-09-06.

- **L7e.** L4e cut the loop into `scanBlockM` and pure per-block functions,
  but its proof covers only the branch with no overlay (`ox.on = false`).
  The overlay branch still needs: `upperIdx` and `lowerIdx` over a sorted
  array give the slice of inserts and deletes in a block's row range (no
  lemma yet); the tuples of `chunkOfRows` (`selectRows` over `colsOfRowsGo`
  of the merged rows; `selectRows_spec` is proved, `colsOfRowsGo` is not);
  `rowsOfColsGo` of the key range (`keyRange_spec` gives the range); then
  L7c (`mergeRows_spec`) and the tail chunk. Not direct, so not done here.
- **L7f, L7g.** The session and the compaction are `IO` programs; L7g needs
  L3c (a pure `packSpec`) and a pure statement of the two compaction scans.
- **E1 and E2 with a log.** With the overlay, `denote G` is replaced by
  `Overlay.denote (denote G) (replay {} ops)` (L7d). E1 then needs L7c, L7e
  and L7f in addition to the lemmas above.

## 4. Definitions the statement needs and that do not exist

`packSpec`, `Admitted`, `denote`, `storeOf` (section 1). Each is a pure
function over byte arrays or quads; the `IO` programs that exist today would
be refined to them.

## 5. What was changed for the proofs (output unchanged)

| Function | Before | After | Equality shown by |
| --- | --- | --- | --- |
| `IdQuery.prefixCmp` | `for` loop with early `return` | `prefixCmpGo`, a tail call with fuel | `#guard` against the old form on 7 rows × 11 keys (`ScanTheorems.OldForms`); `tests/sbm11/run.sh` |
| `IdQuery.blocksFor` | `for` loop with `break` | `blocksForGo`, a tail call with fuel | `#guard` against the old form on 4 metadata arrays × 11 keys; `tests/sbm11/run.sh` |
| `FrameWords.repeatWords` | `for` loop over `[0:64]` with `break` | `repeatGo`, a tail call with fuel 64 | `#guard` against the old form for 10 row counts |
| `IdQuery.rowKeyCmp` | `for` loop with early `return` | `rowKeyCmpGo`, a tail call with fuel | `#guard` against the old form on 4 columns × 9 keys × 6 rows (`ScanWordsTheorems`); `tests/sbm11/run.sh` |
| `FrameWords.words` (the reference only) | `for` loop | `Array.foldl` | the same fold; `#guard`s of `FrameWords.lean` |
| `Dict.lookupM`, `DictRange.lowerBoundM` | `for` loop over `[0:log2 n + 2]` with mutable `lo`, `hi`, `probes` and `break` | `Dict.searchPagesM`, a tail call with fuel, shared by both | `#guard`s of `Dict.lean` (lookup against `memLookup`) and `DictRange.lean` (22 targets); `tests/sbm11/run.sh` |
| `Dict.indexInPage`, `DictRange.firstNotBelow` | `for` loops with early `return` | `indexInPageGo`, `firstNotBelowGo`, tail calls with fuel | `#guard` against the old `firstNotBelow` (`DictRangeTheorems`); the lookup `#guard`s |
| `IdQuery.scanFoldM` (second landing) | one `for` loop over the blocks with eight mutable variables, early `continue` and `break`, and nested `for` loops for the checks, the frames to read, the key columns and the cut columns | `forIn` over `blocksFor` with the body `scanBlockM` and an explicit state `ScanState`; per block the pure functions `blockPlan` (with `planChecksGo`), `constOutOf`, `needOf` (with `needCol`, `outNeedGo`), `keyWordsOf` (with `colsAllGo`), `keyRange`, `cutCol`, `chunkOfCols`; the overlay context `ovCtx` and `stepOf` | `#guard`s in `Storage/Sbm11/ScanFoldTests.lean`: the old scan (`OldForms.scanFoldMOld`, the code as it was) and the new one over an in-memory store of a sample permutation of 11 blocks, 23 scan specifications × 5 overlays × `fill` true and false × 3 stop points, every chunk (columns, rows, constants, variables, sort variable) and the statistics equal; `tests/sbm11/run.sh`; the theorem of section 10 is about the new form only |
| `IdQuery.readFrames` | `for` loop over `[0:4]` | `frameSpan` (the first and the last needed frame) | the same `#guard`s (bytes read are in the statistics) |
| `IdQuery.constWords` | `for` loop over `[0:rows]` | `constWordsGo`, a tail call with a count | `#guard` against the old form for 5 row counts × 3 values |
| `IdQuery.overlayChunkM` | `for` loop over `[0:4]` with `throw` | `colsAllGo` | the overlay `#guard`s |
| `Qlvr.mergeJoin` | one `for` loop with nested `for` loops and `break` | `mergeGo` with `runEnd`, `pairsRow`, `pairsBlock`, tail calls with fuel, `@[specialize]` | `#guard` against the old form on 4 × 4 sample tables and 3 join variables (`MergeTheorems`); `tests/qlvr/run.sh`, `tests/sbm11/run.sh`. Without `@[specialize]` q07 was slower (warm minimum 56 to 67 ms against 50 to 53 ms, 8 processes of 20 runs); with it 47 to 52 ms |

## 6. Axioms

`#print axioms` of every theorem added here lists `propext`,
`Classical.choice`, `Quot.sound` or a subset. No `sorry`, no user `axiom`, no
`native_decide`, no `partial`, no raised `maxHeartbeats`.

## 7. What the proofs taught

- **A monadic definition over `Id` unfolds by `rfl`.** `entryM`,
  `pageBytesM`, `pageM`, `searchPagesM` and `lookupM` with `m = Id` and an
  in-memory fetch were opened with `have e : f … = (do …) := rfl` and then
  `rw [e, h, pure_bind]`. `simp only [f]` and `rw [lift_bind]` did not
  match the `liftM` of `ExceptT`.
- **A statement with a proof-dependent index resists `rw`.**
  `cmpBytesAt ks[firstNotBelow ks k] k` with the bound proof in the type
  gave "motive is not type correct". Stating the loop result as a variable
  (`∀ r, f … = r → P r`) and using `ks[j]!` in the statement removed it.
- **A function argument costs time on a hot path.** The merge loop as
  tail calls taking the join columns and the column test as closures was
  slower on q07 than the `for` loop that read the columns inline;
  `@[specialize]` on the four functions restored it (section 5).
- **`List.drop_drop` reads `drop n (drop m l) = drop (m + n) l`.** Write
  the target offset as `m + n` in the order of the drops before `rw [←
  List.drop_drop]`.

## 8. Gates (2026-10-12, this landing)

Measured on the worktree at the merge-join commit (every executable change of
this landing; the later commits add theorem modules only), olympics
generation `/home/user/qlvr-work/sbm11/s3/wfull`:

| Gate | Result |
| --- | --- |
| `lake build` (whole tree, after the last commit) | 1,538 jobs, 0 errors |
| `python3 tools/lean-tail-recursion-audit.py --gate` | exit 0; one new allow-list line, class (c), for `Dict.searchPagesM` (fuel `log2 pageCount + 2`); the proof-only `pagesBefore` is `noncomputable` |
| `formal/lean4/Wasm/native-smoke.sh` | 350 pass, 0 fail, 0 xfail (out of 350) |
| `tests/known-defects/run.sh` | 13 XFAIL, 0 XPASS, 0 probe errors (out of 13) |
| `tests/sbm11/run.sh` | 96 pass, 0 fail (out of 96); oracle 21 pass, 0 fail (out of 21) |
| `tests/qlvr/run.sh` | 39 pass, 0 fail (out of 39) |
| new `import Std` | none |

## 9. L3b: the exact permutation check (second landing)

The task (https://github.com/danbri/factoidal/issues/801 KR 1.5) gave two
mechanisms: (i) an exact check in activation, or (ii) a theorem about the
packer, which needs a pure specification of its phases (L3c).

**Choice: (i).** Reasons:

- Cost of (ii): the packer is an `IO` program over run files with four
  parallel tasks (`Harness/Sbm11PackLib.lean` phases 3a and 3b: spill sorted
  runs, k-way merge with deduplication). A proof needs a pure specification
  of each phase and a refinement of the run-and-merge program to it. That is
  L3c, not done here.
- Reach of (ii): a theorem about the packer says nothing about a generation
  that another program wrote, or one changed and resealed after packing. A
  check in activation makes L3b a property of every admitted generation,
  which is the form E1 needs ("for every `G` with `Admitted G`").
- Cost of (i): measured below. It is linear in the rows and stays on the
  disk-resident path with bounded memory.

**Method** (`Harness/Sbm11PermCheck.lean`, called from `Sbm11Cli.verifyGen`,
so `l4sbm11 verify` and `activate` both run it). The PSO blocks are cut
into groups of at most `G` rows (`SBM11_VERIFY_GROUP_ROWS`, default
262,144); the first row of each group after the first is a bound. While
activation decodes POS, SPO and OSP for its other checks, every row is
re-keyed to the PSO row of its quad (`PermSet.rekey`) and appended to the
file of its bucket (`PermSet.bucketOf bounds`). Then each bucket is read
back (refused unread when its row count differs from its group's), sorted
(`PermSet.sortRows`, `Array.mergeSort`) and compared row by row with the
PSO rows of its group, decoded block by block; every PSO row must fall in
its group's bucket. The digest comparison stays (it is cheap and names the
permutation); `SBM11_VERIFY_DIGEST=0` turns it off for the test that shows
the exact check alone refuses.

**Bound.** Memory: one bucket of at most `G + b` rows (`b` the rows of the
largest PSO block) as file bytes and as rows, the sort's arrays, one
decoded block, and `3 nb` write buffers (`nb ≤ N / G + 1`), each written
out at `max(4 KiB, min(64 KiB, 16 MiB / 3 nb))` bytes, so at most
`max(32 MiB, 24 KiB × nb)` of buffers. It does not load the generation:
with `G = 262,144`, about 25 MB for the bucket, and about 90 MB of buffers
for a billion quads. Disk: 32 bytes per row of the three permutations, in
`GEN.verify-PID` next to the generation, removed at the end (also on an
error).

**Theorem** (`Storage/Sbm11/PermSet.lean`). `sameQuads key nb a c` is the
check as a function of row lists. `sameQuads_perm`: for any bucket function
`key`, `sameQuads key nb a c = true → a ~ c` (equal multisets; by
`List.perm_iff_count`: a row's count in a list is its count in its own
bucket, and each bucket's sorted rows equal the other side's, with
`Array.mergeSort_perm`). `perms_same`: if the check holds for the re-keyed
rows of permutation `p` against the rows of PSO, then
`rowsP.map (ofPermRow p) ~ rows0.map (ofPermRow 0)`: the two permutations
denote the same quads (`perms_same_mem` for membership). The hypothesis is
the check's result; it does not restate the conclusion (the conclusion
compares decoded quads; the check compares sorted re-keyed rows bucket by
bucket). Not proved: that the `IO` code computes `sameQuads` (it appends
rows to bucket files and reads them back); tested by `tests/sbm11/run.sh`
part (j): the gate fixture admitted with groups of 1, 3 and 1,000,000 rows
(12, 10 and 1 buckets, blocks of 2 rows), and a copy whose POS files come
from a pack of the fixture with one quad changed (same dictionary, same row
count, another quad set; resealed) refused by the exact check with the
digest off ("pos holds other quads than pso" or "pos holds 1 rows in bucket
5, pso 2") and by the digest with it on.

**Cost on olympics** (1,781,625 quads, generation
`/home/user/qlvr-work/sbm11/s3/wfull/gen-1` copied; `l4sbm11 verify`, old
and new binary interleaved, 3 rounds each; load average 1.0 to 1.6, 4
vCPU):

| | old (digest only) | new (digest and exact check) |
| --- | ---: | ---: |
| wall ms per round | 6,357 / 6,625 / 7,434 | 14,954 / 15,368 / 13,826 |
| permutation pass ms (decode, digest, and for new the bucket writes) | 4,346 / 4,589 / 5,151 | 6,681 / 6,861 / 6,150 |
| exact check ms (read, sort, compare 7 buckets × 3) | — | 6,269 / 6,585 / 5,738 |
| bytes read from the generation | 33,842,366 | 45,357,500 (PSO read three more times) |
| bucket file bytes written, and read back | — | 171,036,000 each |
| peak RSS kB | 87,640 / 87,860 / 88,168 | 111,276 / 111,032 / 111,100 |

With `G = 1,048,576` (2 buckets) the exact check took 7,504 to 9,312 ms
and peak RSS was 200 to 208 MB; with `G = 65,536` (28 buckets) 5,473 ms and
94 MB (one run each, load 0.7). The default is `G = 262,144`. Activation
time about doubles (about 4.5 µs per quad more); it stays linear in the
quads.

## 10. L4e: the scan as a whole (second landing)

`scanFoldM` was cut into `scanBlockM` and pure per-block functions (section
5), with output equal to the old form on the `#guard` samples. Theorems
(`Storage/Sbm11/ScanFoldTheorems.lean`):

- `scanFoldM_tuples`: for a store over `m = Id` whose `metas` are the PRM1
  entries `ms`, whose `prb` reads a byte array `prb`, with no overlay; with
  `prmAdmitted perm ms` and every block admitted by `decodeBlockAt` (the
  activation checks), and a scan specification of the planner's shape
  (`SpecOk`: columns below 4, a key of at most 4 columns, one variable per
  output column): `scanFoldM` with an `f` that appends each chunk's tuples
  returns the output tuples (`proj`) of exactly the rows of the permutation
  (`blockRows`, in block order) that `keep` admits: the key prefix, the
  named-graph test, the checks, the repeated-variable tests. `tuples ch`
  reads a chunk's constant when it has one (`fill = false`, the aggregate
  path), else its column.
- `scanFoldM_columns`: with `fill = true` (the BGP and join path), the same
  with the chunks read from their columns alone.
- Per block: `blockChunk_tuples` (the chunk of an admitted block that the
  plan does not skip), `blockOut_unselected`, `blockOut_skipped`,
  `readFrames_slice` and `frame_in_slice` (the slice `readFrames` reads
  decodes every needed frame), `keyRange_spec` (the rows `[lo, hi)` are
  exactly the rows with the key prefix), `chunkOfCols_tuples`,
  `selectRows_spec`, `blockPlan_keep` (the checks and the named test as the
  plan splits them), `colConst_sound` (L4d).

What the theorem does not cover: the overlay branch (L7e, section 3); a
store in `IO`; the old form. The old loop and the new one are shown equal by
the `#guard`s of `ScanFoldTests.lean` only. An equality theorem with the old
loop was not written: the theorem above is about the code that runs, the old
loop no longer runs and was never proved, so such a theorem would add no
assurance about the scan.

What the proofs taught:

- **Name the intermediate values of a monadic function.** `blockChunk`
  first bound its key columns with `if bp.full then pure #[] else ...`
  inside the `do` block; the elaborator turned that into a join point that
  `rw` could not reach. `keyWordsOf`, `keyRange` and `chunkOfCols` as named
  functions made each step one `rw` with a lemma about that function.
- **`liftExcept` exists in Lean core.** A local `IdQuery.liftExcept` made
  every use ambiguous in the proof file; it is now `ofExceptM`.
- **State a loop over blocks as a fold of what each block appends.**
  `forIn_blocks` is an induction over the block list with the step lemma
  `scanBlockM_step`; the blocks outside `blocksFor` add nothing
  (`blocksFor_complete`), so the fold over `blocksFor` equals the fold over
  all blocks (`flatMap_range_interval`, `blocksForGo_range`).

Query timings before and after the restructure (olympics, `--repeat 10`
warm median per run, 7 interleaved rounds alternating the order of the two
binaries, load average 1.1 to 1.5 at the start of each round, 4 vCPU; other
agents shared the machine):

| Generation | Query | before median ms | after median ms | before min | after min |
| --- | --- | ---: | ---: | ---: | ---: |
| base | q01 | 0.46 | 0.31 | 0.30 | 0.29 |
| base | q07 | 60.34 | 58.81 | 53.36 | 54.41 |
| base | q10 | 25.97 | 26.89 | 24.01 | 24.81 |
| base | q19 | 165.79 | 182.85 | 153.13 | 156.22 |
| base | q21 | 306.29 | 292.41 | 274.70 | 275.69 |
| overlay (2 batches) | q01 (the stage 5 merge) | 8.50 | 8.38 | 8.21 | 8.06 |
| overlay | q03 | 1.40 | 1.23 | 0.96 | 0.97 |
| overlay | q19 | 163.34 | 160.41 | 147.29 | 153.33 |

One binary's runs of one query vary by up to 30 % between rounds (q19:
153 to 210 ms after, 153 to 196 ms before). The differences above are
inside that noise; no change is claimed. The loop is per block, so its
cost does not grow with the rows.

## 11. Gates (2026-10-12, second landing)

On the worktree with every change of this landing:

| Gate | Result |
| --- | --- |
| `lake build` (whole tree) | 1,601 jobs, 0 errors |
| `python3 tools/lean-tail-recursion-audit.py --gate` | exit 0, no new allow-list line |
| `tests/sbm11/run.sh` | 149 pass, 0 fail (out of 149); oracle 21 pass, 0 fail (out of 21); part (j) 7 pass, 0 fail (out of 7) |
| `tests/qlvr/run.sh` | 39 pass, 0 fail (out of 39) |
| `tests/prim/run.sh` | native 21,581 pass, 0 fail; wasm32 21,581 pass, 0 fail (out of 21,581 each) |
| `formal/lean4/Wasm/native-smoke.sh` | 350 pass, 0 fail, 0 xfail (out of 350) |
| `tests/known-defects/run.sh` | 13 XFAIL, 0 XPASS, 0 probe errors (out of 13) |
| `tests/stack/run.sh --canary` | 59 pass, 0 fail (out of 59) |
| `#print axioms` of `scanFoldM_tuples`, `scanFoldM_columns`, `blockChunk_tuples`, `colConst_sound`, `perms_same` | `propext`, `Classical.choice`, `Quot.sound` |
| new `sorry`, `native_decide`, user `axiom`, `import Std`, raised heartbeats | none |


## 12. Sideways information passing (2026-10-13)

https://github.com/danbri/factoidal/issues/809. The id path passes the left
values of a join variable into the right scan; the record of the algorithm,
the rule and the measurements is
[`2026-10-12-sbm11-stage4.md`](2026-10-12-sbm11-stage4.md) section 11.
Lemmas L4g, L4h, L4i and L5h (section 2) in
`Storage/Sbm11/SipTheorems.lean`, `SipScanTheorems.lean` and
`SemiJoinTheorems.lean`.

How the pieces compose: L4i says the scan with candidates returns the full
scan's tuples filtered by "the join value is a candidate"; `sipCands_sound`
says every left value is a candidate; L5h says a join over a right input
filtered that way is the join over the full right input (for the merge loop
and for `outerPairs` over it, as index arrays; for SPARQL Join and LeftJoin
over solution mappings of ids). The hash join (L5b) and the `Table` the
scan appends (L5a′) stay open for the scans with candidates as for the full
scans; `tests/sbm11/run.sh` part (l), the W3C census with `--sip always`
and the DBpedia and olympics answers cover them.

What the proofs taught:

- **Prove a loop that writes nothing for most rows with the step lemma of
  the loop that writes every row.** `deltaFindGo` and `deltaGatherGo` follow the shape of
  `FrameWords.deltaRangeGo`: a step lemma that consumes one varint
  (`getVarAtGo`), then an induction over the row count against
  `Column.deltaAtGo` with the decoded values given as a function `val` of
  the row number. Stating the values as `val t` (with `a[t - idx]! = val t`
  as the invariant) kept the index arithmetic out of the induction.
- **Make a search hint unnecessary for correctness.** The
  candidate pointer starts at a binary search result; `startFor` falls back
  to 0 when the hint is too far, so `probe_mem` holds for any start and the
  binary search needs no lemma. `mayHold` checks its hint in the same way.
- **Generalise each Boolean subterm before `cases`.** `cases` needs the
  subterm as written. After
  `blockPlan_keep`, the keep test reads `List.all (chk r)` while the chunk's
  tests read `List.all fun ck => rowCol r ck.1 == ...`; `have e : ... := rfl`,
  `rw [e]` and `generalize` on each Boolean, then `cases` on the variables,
  closed the case analysis.
- **Check at run time what a function without theorems must give.**
  `sipCands` sorts with
  `mergeSortBy`, which has no theorem; the planner uses the candidates only
  when they are in order and contain every left value, both checked at run
  time, and `sipCands_sound` uses only those checks.
