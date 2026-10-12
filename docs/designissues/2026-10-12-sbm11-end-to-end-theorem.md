# SBM11: the end-to-end theorem, its lemmas and their status

Date: 2026-10-12. Status: plan written; 12 lemmas proved in this landing,
the end-to-end theorem open (section 2 table, section 3 obstacles). Gap issue: https://github.com/danbri/factoidal/issues/776.
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
| L3b | An admitted generation's four permutations denote one quad set (https://github.com/danbri/factoidal/issues/793 item 4) | open | — |
| L3c | Packer correctness, E0 | open | — |
| L4a | Block skipping is complete: a row of block `k` whose key prefix equals the scan key is in a block that `blocksFor` returns and `selects` admits | **proved now** | `ScanTheorems.blocksFor_complete`, `decodedRow_selected`, `chain_sorted` |
| L4b | Inside a block, the two binary searches select exactly the rows whose comparison is `.eq`, given that `rowKeyCmp` is monotone over the rows; the `full` shortcut | **proved now** | `ScanTheorems.keyBound_spec`, `blockRows_exact`, `fullFor_row` |
| L4c | `rowKeyCmp` over the words of decoded columns is `prefixCmp` of the rows; so the in-block range is exact over decoded columns, and over the columns of every block that activation admitted | **proved now** | `ScanWordsTheorems.rowKeyCmp_words`, `scanRows_exact`; `BlockAtTheorems.scanRows_exact_of_decodeBlockAt` |
| L4d | The metadata shortcuts of `scanFoldM`: `colConst?` for columns 0 to 2 (from sortedness) and for the graph column (from the canonical encoder, L2f, and activation's re-encode check) | tested only | `tests/sbm11/run.sh` parts (a), (c), (d); census |
| L4e | `scanFoldM` as a whole: the chunks are the rows of the permutation with the key prefix, filtered by `checks`, `named`, `eqs` | open | — |
| L4f | A frame decoder reads only the bytes of its frame: in any slice `[s, e)` of the array that contains the frame, the column (and the words) at the shifted start are the same (`readFrames` reads one such slice per block) | **proved now** | `FrameLocalTheorems.decodeColumn_local`, `decodeColumnAt_extract`, `decodeWords_extract` |
| L5a | Merge join, index part: for join columns in non-decreasing order, the index arrays `Qlvr.mergeJoin` builds its output from zip to every pair of rows whose join values are equal and whose other shared columns agree, in left-then-right row order | **proved now** | `Qlvr.MergeTheorems.mergeGo_spec`, `mergeGo_pairs`, `mergeJoin_eq` |
| L5a′ | Merge join, solution part: a row pair of id tables is a pair of compatible solutions exactly when its shared columns are equal, so the join output equals the reference join (SPARQL 1.1 section 18.5) of the decoded solutions, as multisets | open | — |
| L5b | Hash join (`Qlvr.hashJoin`) on id tables equals the reference join | open | — |
| L5c | FILTER: a conjunction is applied conjunct by conjunct | proved before (stage 4) | `IdQueryTests.ebvOrFalse_evalIn_and` |
| L5d | FILTER on ids: rule 1 (term identity) and rule 2 (STRSTARTS as a rank range) agree with `Expr.evalIn` | tested only | `IdQueryTests.lean` `#guard`s on 23 terms |
| L5e | ORDER BY shortcuts on ids agree with `sparqlOrderValue` | tested only | `IdQueryTests.lean` `#guard`s |
| L6a | E1 from L1 to L5 | open | — |
| L6b | E2: the fallback selection keeps every quad the query can read (the planner theorem of 2026-09-06 restated for PSO scans), and the `datasetOfQuads` bridge (that record's section 6.6 item 1) | open | — |
| L6c | The JSON printer (`keyJsonInto`) equals `jsonOfTerm` | tested only | `tests/sbm11/run.sh` part (b), byte comparison on 21 queries |

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
- **L3b.** Activation compares the four permutations by an order-independent
  digest (sum and xor of `mix64` of each quad, `Harness/Sbm11Gen.lean`). A
  digest equality does not imply set equality, so L3b cannot be proved from
  activation as it is. Two routes: prove it of the packer (L3c), or make
  activation compare the permutations exactly (each permutation is sorted in
  its own order, so an exact check needs a sort or a merge per pair).
- **L3c.** The packer is an `IO` program over run files with four parallel
  tasks. A proof needs a pure specification (sort, deduplicate, block,
  encode) and a refinement of the run-and-merge program to it.
- **L4e.** `scanFoldM` is one monadic `for` loop over blocks with eight
  mutable variables and early `continue` and `break`. It needs to be cut
  into pure per-block functions (select, read, cut, filter) before a
  statement about its chunks can be proved.
- **L5a′, L5b.** `Qlvr.mergeJoin` and `hashJoin` work on `Table` (one
  `ByteArray` of words per column). A statement needs the table's
  denotation (rows of ids, then solutions through `TermId.ofId?`), and the
  reference join over lists of solutions (`SPARQL/IndexedEvalRefinement.lean`
  proves a hash join for a different representation). L5a gives the row
  pairs; the remaining step is that equal shared ids are compatible
  solutions (ids are injective, `TermIdTheorems.toId?_eq_iff`) and that
  `joinOutput`'s `gather` copies the rows of the pairs. `hashJoin` uses
  `Std.HashMap` and needs a lookup characterisation of its own.
- **L6a.** Needs everything above, plus the plan rules: the permutation
  chosen by `permFor` holds the bound positions as a prefix, and the join
  order does not change the multiset.
- **L6b.** The planner theorem of 2026-09-06 is stated over IBK manifest
  entries; SBM11 selects by PSO key prefix, so the storage side is "a PSO
  scan of predicate `p` returns every quad with predicate `p`" (L4a, L4b,
  L4e) and the evaluator side reuses `SPARQL/DatasetRestriction.lean`. The
  `datasetOfQuads` bridge is open since 2026-09-06.

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
