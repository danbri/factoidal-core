---
name: lean4-performance
description: Improve performance-sensitive Lean 4 code in Factoidal while preserving total semantics, observable order, and executable proof boundaries. Use for large parser, RDF/block ingestion, data-structure, recursion, or hot-path work; not for unmeasured micro-optimisation.
---

# Lean 4 performance in Factoidal

Start with a concrete phase and an observable baseline: text read, parse,
bucket/index build, block encode/decode, range I/O, query evaluation, or result
formatting. A green semantic test is not a throughput result, and a fast host
shim is not a semantic replacement.

For rounded aggregates, preserve the chosen operation order in both reference
and streaming paths. A bag's permitted enumeration can avoid buffering, but
write the exact list identity rather than assuming floating associativity.
The SUM/AVG reconciliation and its remaining grouping obligation are recorded
in [the aggregate-order note](../../docs/designissues/2026-10-22-shared-aggregate-order.md).

## Recursion and collection rules

- In a repeatedly invoked path, treat `xs.length`, `List.reverse`, `++`, and
  `String.toList` as costs to account for. `remaining.length` used to choose
  fuel inside every parser step is often an accidental quadratic scan.
- Build ordered lists with a reverse accumulator and restore order exactly once
  at a named boundary. State the preserved order in the doc comment and test
  it where it affects RDF/SPARQL results.
- Make a scanner tail-recursive when it consumes a flat stream and only needs
  a token/result accumulator. A reverse accumulator is normally the right
  representation.
- Keep structurally recursive or fuelled recursion for grammar nesting and
  semantic tree traversal when it supports totality or proofs. Do not replace
  it with `partial` merely to obtain a loop-like shape.
- A recursive map over a small, bounded metadata list may be appropriate. Do
  not generalise that exception to data-sized lists, graph rows, or tokens.

## Keyed collections: association lists, shared maps, appends at the end

A collection keyed by a set the caller sizes (node identifiers, blank node
labels, graph names, the values of one property) is a map, not a
`List (String × _)`. Paid for 2026-10-10 in JSON-LD node map generation
(`JSONLD/Flatten.lean`, record:
[`docs/designissues/2026-10-10-jsonld-node-map-scaling.md`](../../docs/designissues/2026-10-10-jsonld-node-map-scaling.md)):
the node map, each graph, the graph list and the blank node map were
association lists, and a document with one node that holds 1,600 node
references took 3.9 s to build its node map (4.7 s to flatten, 8.5 s to
frame). After the repair the same input takes 8.2 ms, 7.6 ms and 91 ms.
Rules from that repair:

- **Use `Std.TreeMap` (or `Std.HashMap`) for a collection that grows with
  the input.** Keep an association list only for the members of one input
  object.
- **Prefer a persistent map where a value can be referenced twice.** An
  `Array` or a `Std.HashMap` updates in place only when the reference is
  unique; through a second reference the update copies the bucket array,
  and the code stays correct and becomes quadratic. `Std.TreeMap` copies a
  path of `O(log n)` nodes whatever the reference count.
- **`let st ← get; set { st with a := st.a.push x }` keeps the old state
  alive, so it copies `a`.** `Frame.allocM` did this and copied the whole
  output arena on every allocation. Use `modifyGet` or `modify`, which use
  the state once.
- **A map in the accumulator of a streaming fold is shared once per chunk.**
  `NQuadsFold.feedChunkC` reads `st.pos` after the fold over `st.acc`, so
  `st` is alive during the fold and the first insert of every chunk finds
  the map shared and copies it. Cost, 2026-10-12, `l4sbm11-dict-pack`
  phase 1 on the olympics N-Triples (338 MB, 5,153 chunks of 64 KiB, a set
  of up to 262,144 terms): 96 s, against 72 s when the fold only conses the
  chunk's terms onto a list and the caller inserts them into a set it took
  out of an `IO.Ref` with `swap` (unique while it is updated). An `IO.Ref`
  read with `get` and written back with `set` has the same defect: the ref
  still holds the old map during the insert.
  Paid again 2026-10-13 in two forms, by an agent that had not read this
  bullet (https://github.com/danbri/factoidal/issues/813):
  (1) `StrictFeed.LineFeed.feed` was written with `st.pos` after the walk,
  as above; (2) the command line's chunk loop returned the OLD line state
  `lf` in its error branch, so the compiler emitted `lean_inc(lf)` before
  `LineFeed.feed` and the count's `FastDataset` was copied at the first quad
  of every chunk: 400,000 N-Triples counted in 8.6 s of CPU against 2.9 s
  after both repairs (take the state apart with `match st with | {..} =>`
  before the walk; return a fresh empty state on the error branch). A
  value named in ANY later branch of the caller is alive during the call.
  Check the emitted C: `grep -n "lean_inc(v_x)" .lake/build/ir/<Module>.c`
  just above the call that updates the map.
- **State that a task reaches through a reference made before the task is copied
  at every update.** Lean treats the objects that the closure of `IO.asTask`
  reaches as shared between threads (`lean_is_exclusive` in `lean.h` is false for
  them), and a reference that the task reaches keeps what it stores shared. An update
  of a shared object copies it. Measured
  2026-10-15 (Lean 4.33.1, linux x86_64, two runs): 100 rounds of `let a ← r.swap #[];
  r.set (a.push i)` on an array of 5,000,000 numbers took 9,557 ms and 7,351 ms for a
  reference made before the task, and 29 ms and 23 ms for a reference made inside the
  task (the program is in section 11.4 of
  `docs/designissues/2026-10-11-shardborough-vs-qlever.md`). Make the state inside the
  task: pass the task an `IO` action that makes it, as `Sbm11Pack.packQuads` does with
  `Array (IO QuadSource)` (https://github.com/danbri/factoidal/issues/866). Take the state
  out of its reference with `swap` while a step updates it (`QuadSource.ofStep`).
- **When insertion order is observable, use `OMap`** (`JSONLD/OrderedMap.lean`:
  a `Std.TreeMap` plus the keys newest first). Lookup and update agree with
  `flLookup` and `flUpd` on the entries in insertion order
  (`OMap.find?_eq`, `OMap.toList_upsert`).
- **Appending at the end is a reverse accumulation.** `xs ++ [v]` once per
  value is quadratic in the number of values; cons onto the front and
  reverse once at the boundary (`DedupArr.rev`, `OCont.arr`, the `@list`
  accumulator of `nmg`).
- **A "not already in the array" test over a growing array compares keys in
  a set, not by scanning.** The scan called `expandedEqual` (two JCS
  serialisations) on every item already present, which was most of the 3.9 s
  above. `DedupArr` keeps the canonical form of each item in a
  `Std.TreeSet`; `DedupArr.contains_iff` proves the set answers the scan's
  question.
- **Prove the new operations against the old definitions, and compare raw
  output.** The old list definitions stay as `Spec.*` in
  `JSONLD/NodeMapTheorems.lean`. For a change that must not alter output,
  run both builds with `L4_JSONLD_DUMP=<file>` on every manifest and on
  `l4jsonld-api --dump-shapes`, then `cmp` the files: the suites compare
  with RFC 8785 canonical forms, which ignore member order, and the raw
  dump does not.
- **An association list answers the FIRST entry of a key; `Std.TreeMap.insert`
  keeps the LAST.** To replace a `lookup` over a list that can hold a key twice,
  insert the entries last first (`labelTree` in `RDF/Canonical.lean`:
  `m.reverse.foldl insert`, proved by `labelTree_get?` through
  `List.foldl_reverse`).
- **Measure first, with a ladder.** `l4jsonld-api --scale` prints the time
  of each phase at n, 2n, 4n, 8n and 16n for five document shapes and
  asserts time(4x) at most 9.0 times max(time(x), 20 ms) for the node map,
  flatten and frame core phases (`tests/stack/jsonld_scaling.sh`). One
  shape is not enough: at 1,600 nodes the hub shape (every node links to
  one hub) cost 0.27 s to build its node map and the fan-out shape (one node
  holds all the references) cost 3.9 s, so a ladder over the hub shape alone
  would have under-reported the cost 14-fold.

## The 2026-10-10 survey: the shapes that were slow

The survey in
[`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`](../../docs/designissues/2026-10-10-lean-vs-fstar-performance.md)
found six quadratic costs and three constant factors in the Lean tree. Look for
these shapes first in any module that is slow on a large input.

- **A specification that scans, used as the implementation.** `RDFS.step` read
  premises with `g.filter` once per triple, and added conclusions with
  `Graph.add` (a scan). Repair: keep the scanning definition, add an indexed
  twin that returns the same LIST, prove the equality, and register
  `@[csimp]` so every caller gets the fast one (`RDFS/Closure.lean`,
  `RDFS/FullClosure.lean`). 100 to 500 times faster; 0.9 to 1.6 times the F*
  time at the largest sizes measured.
- **An indexed twin that nothing calls.** `OWL/RLClosureIndexed.lean` had the
  indexed OWL RL closure with `indexedClosure_eq` (same list at every fuel)
  since August; only the probe harness called it, and the command line called
  the scanning `closure`. Two `csimp` theorems closed the gap (chain of 80
  axioms: 8.6 s to 0.22 s; schema.org: over 120 s to 6.4 s). Before writing a
  twin, grep for `*Indexed`, `*Fast` and `*Ix` definitions and check who calls
  them.
- **`List.length` of the remaining input in a loop.** The TriG reader did
  `r1.length` per statement. `Syntax.Turtle.parseStatements` already declined a
  fuel counter and compared positions; `Syntax/TriG.lean` had not been changed
  with it. Grep for `.length` inside every recursive reader.
- **An insertion sort in the algorithm.** `RDF/Canonical.lean`
  (`sortBy`) and `Syntax/TurtleSerialize.lean` (`sortStrs`). Repair:
  `List.mergeSort`. For a total preorder with ties, the equality with a stable
  insertion sort has a general proof by way of `List.zipIdxLE`
  (`CanonicalTheorems.sortBy_eq_mergeSort`); for strings, where equal means
  identical, antisymmetry is enough (`TurtleSerialize.sortStrs_eq`).
- **A list of groups searched and appended to per row.** `SPARQL/Query.lean`
  `addToGroups`. Repair: array of groups plus a hash index on a bucket key that
  is constant on order-equal values (`erEqual_erBucket`).
- **A string built by prepending.** `SPARQL.rowsJoined` was
  `rowJson r ++ "," ++ rowsJoined rest`: each row's text is copied in front of
  the text of all later rows, so the whole result document is copied once per
  row (`SELECT *` over 5,000 paragraphs of `gene.ttl`: 9.8 s, F* 1.4 s).
  Append at the end of a string the function owns (`rowsJoinedTR` in
  `SPARQL/ResultsJson.lean`, proved and registered with `csimp`); Lean extends a unique string in place.
- **`acc ++ [v]` inside a `mutual` block.** `JSON.parseItems` and
  `parseMembers` appended each element at the end of the list read so far,
  and `l4factoidal query` parses the JSON envelope of every answer it prints:
  `SELECT *` over 10,000 paragraphs of `gene.ttl` spent 72.2 s in that parse
  (https://github.com/danbri/factoidal/issues/729). A `csimp` cannot replace a
  call between two members of one `mutual` block, so the repair twins the
  WHOLE block (`parseValueR` ... `parseItemsR`, a reversed accumulator
  reversed once at the closing bracket), proves every twin equal to its
  member at every fuel in one induction over the fuel (`parseR_eq`, the
  accumulators related by `reverse`), and puts the `csimp` on the first
  function outside the block (`parseJsonTextChars_eq_R`): 0.88 s. The same
  module built the `Array Char` it indexes from `s.toList.toArray`; read the
  `String` with `String.foldl` and `push` instead (`charsOfString`,
  `String.foldl_eq_foldl_toList` and `List.foldl_push_eq_append'`).
- **A per-character map into strings.** `escapeString` was
  `(s.toList.map escapeChar).foldl (· ++ ·) ""`: a list cell, a `Char` and a
  one-character `String` per character before the join. On wasm32 a `Char`
  in a list is a heap object as well (`Wasm/build-wasm.sh` step 1b). The wasm
  `parse()` escapes the whole N-Quads text of the dataset into its envelope
  this way, and that held most of the module's linear memory
  (https://github.com/danbri/factoidal/issues/744). `escapeStringFast` walks
  the `String` with `String.foldl`, pushes a character outside the escape set
  and appends the escape of one inside it (`escapeString_eq_fast`, `csimp`).
  To find such a holder in the wasm module, run the op's phases as separate
  dispatch calls in fresh Node processes and compare linear memory
  (`tests/perf/l4_parse_memory_ladder.mjs`): `datasetOpen` (parse and index,
  no text out) ended at 88 MB where `parseToDatasetJson` ended at 641 MB.
- **A comparison that converts to lists.** `Canonical.strLe` built two
  character lists per call: 57 percent of the instructions of `canonicalize`
  after the sorts were repaired. Lean's native `String` order is the same order
  (`charsLe_eq_not_lt`); a `csimp` theorem makes the compiler use it. SPARQL's
  `strCompare` had the same shape (53.6 percent of an ORDER BY): the three-way
  form is `listCharCompare_eq_lt`, and `strCompare_eq_strCompareFast` reaches
  every ordering on the query path (ORDER BY, GROUP BY and DISTINCT-aggregate
  keys, MIN, MAX, `<` on IRIs and literals).

- **A table that a call computes from the whole input to answer one question.**
  `BlockMerkle.proofWith?` computed every level of a Merkle tree again for each
  chunk it admitted, so one proof of a file of `n` chunks cost `n - 1` node
  hashes and a pass over the file cost `n * (n - 1)`. `l4sbm11 dump` of a
  generation with a 149 MB dictionary (2,274 chunks) took 37.0 s of CPU time
  with `--verify merkle` against 13.1 s with `--verify none`; the gdb stacks
  showed `nextLevelWith` up to 1,107 frames deep under `readVerifiedChunk?`
  (https://github.com/danbri/factoidal/issues/854). Removing the proofs took 28
  percent of the CPU time at 100,000 statements (5.8 s to 4.2 s) and 55 percent
  at 400,000 (36.7 s to 16.4 s), so a pass at 25,000 and 100,000 statements gave
  3.8 for 4x data (by hand) and a scaling row at those sizes would have passed
  with the defect. Repair: keep the table with the object that is read many
  times (`BlockMerkle.Tree`, built at the first chunk that the file's
  `VerifiedChunkCache` does not hold) and prove that the fast lookup returns what
  the old function returns (`Tree.proof?_ofLeavesWith`, for every hasher, leaf
  list and index); the chunk is still checked against the root of the manifest.
  The same pass found a linear cost: `concat` made a list cell for each byte of a
  65,536-byte chunk to hash it (`a ++ b` is one byte copy; `concat_eq_spec`),
  2.0 s of the 16.4 s that remained after the proof table. 400,000 statements:
  37.0 s to 13.7 s (row `sbm11-dump-time`).
  The reader without a cache kept the same defect until 2026-10-14
  (https://github.com/danbri/factoidal/issues/859): `readVerifiedRange?` called
  `proofWith?` for each chunk of the range, 4.0 s of user time for a file of 2,048
  chunks and 0.63 s with the table built once (`readVerifiedRangeTree?`; the loop over
  the chunks is a tail call; `readVerifiedChunkTree?_eq` proves the proof is the old
  one). A second cost in the same pass: `dump --verify merkle` held every chunk it had
  verified, 405 MB at 400,000 statements against 65 MB after it forgets them (row
  `sbm11-dump-memory`). A reader of a file in order forgets the chunks that lie wholly
  before the next block (`dropChunksBefore`); forgetting the block just read also
  forgets the chunk that the next block starts in, and the next block reads and hashes
  it again (452 MB of fetches on the olympics generation).

Two more costs are not in an algorithm, and one hazard follows from the repairs:

- **Top-level constants are evaluated when the module is initialised**, in every
  executable that links the module. Five storage modules held 70,000-byte test
  fixtures hashed with SHA-256 as `private def`s next to their `#guard`s;
  together they cost 280 million instructions at process start (43 ms of CPU
  time, 7 ms after the move). Keep fixtures that need real computation in a
  `*Tests.lean` module that no executable imports.
- **The command line is a client of the JSON ABI.** `l4factoidal parse` built
  the whole dataset as N-Quads text in a JSON string, then parsed the JSON to
  read one number: half the instructions of `parse`, and 3,659 MB of resident
  memory for a 6.8 MB Turtle file (256 MB after the repair). Profile a verb by
  phase before ranking a parser. `query`, `canonicalize`, `update` and `closure`
  read their input through `readAsNQuads` (parse, write N-Quads text, parse the
  text again) until 2026-10-10: 75 percent of the instructions of a COUNT
  query. They now take the parsed dataset (next item).
- **A graph read per focus node needs an index carried by the caller.**
  SHACL `objectsOf` filtered the data graph once per focus node and shape:
  74.6 percent of the instructions of `l4shacl` on 500 persons, 27.8 s at
  4,000 persons (F*: 7.5 s). A `csimp` cannot repair this, because the
  function gets only the graph. `SHACL/DataIndex.lean` builds the index once in
  `ValidationConfig.envFor`, `ValidationEnv.dataIx` carries it, and indexed
  twins are proved equal under `DataIndex.Coherent`; theorems that quantify
  over every environment take the coherence as a hypothesis, which
  `envFor_dataIx_coherent` discharges for `validate` (0.24 s at 4,000).
  After the index, two list folds with `acc ++ [x]` (`distinctSubjects`,
  `dedupTerms`) were 80 percent of what was left: profile again after each
  repair (https://github.com/danbri/factoidal/issues/723).
- **A filter over the whole input once per key, where the specification
  builds a map.** RDFC-1.0 §4.4 step 2 builds a "blank node to quads map" in
  one pass. The port's `hashFirstDegreeQuads` filtered every quad for its
  blank node instead, and `hfdqTableOf` called it once per blank node: 79
  percent of the instructions of `canonicalize` at 4,000 blank nodes, 9.49 s
  at 8,000 blank nodes in 24,000 quads
  (https://github.com/danbri/factoidal/issues/745). A `csimp` could repair
  it, because `hfdqTableOf` receives the quads AND every key, so its twin
  builds the map once (`bnodeQuadIndex`, proved equal per key by
  `quadsForBnodeIx_bnodeQuadIndex`): 1.19 s. The same filter one level down,
  in `buildBucketsFor`, runs once per Hash N-Degree Quads call and gets one
  key; a `csimp` on it would rebuild the map per call. The map has to come
  from a caller that sees all the keys, which changes the signatures down the
  chain. Look for a `.filter` whose predicate names the element of an
  enclosing `map` over all keys.
- **A twin chain from the caller that sees every key, with the state type
  replaced.** The repair of that second filter
  (https://github.com/danbri/factoidal/issues/751, 2026-10-13) twins the
  whole §4.4 step 5 chain in `RDF/Canonical.lean`, from
  `buildCanonicalMappingBudgetedFast` (which builds the map once and shares
  it with the first-degree hashes) down to `hndqRunF`, and puts the one
  `csimp` on the top function. The issuer list was the second cost:
  `issueIdentifier` scanned it and appended at its end, and `issueFresh`
  adds at its FRONT. `FIssuer` holds the list as `front ++ backRev.reverse`
  (both ends in constant time) and a `Std.TreeMap` beside it, with the
  invariant as a field (`tree_get`), so no lemma needs a hypothesis about the
  tree: every value carries the proof. Each twin is proved equal through
  `toSpec`; a closure argument (`HndqRec`) becomes a hypothesis that the fast
  closure maps to the slow one, discharged by induction on the fuel. 16,000
  blank nodes with one shared first-degree hash: 10.83 s to 0.54 s; 64,000:
  327.67 s to 2.66 s, byte-identical output. A row that passed
  (`rdfc-bnode-unique`) did not show this cost: profile each shape that
  sends the work down a different step of the algorithm.
- **A text round trip that a caller depends on is a function: name it and
  prove it.** The command line's canonical N-Quads round trip is not the
  identity: it lowers language tags and keeps each quad of a graph once (RDF
  1.1 Concepts §3.3 and §3), so on a Turtle file with a repeated triple
  `parse` printed 3 and `query` `COUNT(*)` printed 2
  (https://github.com/danbri/factoidal/issues/724). The repair
  (`RDF/DatasetNormalize.lean`) is `normalizeDataset`, the two steps as a
  function on `Dataset`, and `parseNQuadsFast_toCanonicalNQuads`: the round
  trip equals it for every dataset that `roundTripSafe` accepts (print-safe
  IRIs, BLANK_NODE_LABEL labels, LANGTAG tags, no `\u`-escaped character). The
  check is decidable, so `datasetForOps` tests it at run time and falls back
  to the text otherwise, and `datasetForOps_eq` holds for EVERY dataset with no
  hypothesis: the command line's output did not change, row order included.
  A theorem with a decidable hypothesis plus a run-time fallback is how to
  replace a slow path whose general equality is false or out of reach.
- **The check that guards a fast path is itself on the hot path.** The first
  `roundTripSafe` walked each IRI with `String.toList`: 36 percent of the
  instructions of the COUNT query it was meant to speed up, as much as the
  Turtle parse. `String.all` walks the UTF-8 bytes without a list
  (`String.all_bool_eq`); a `csimp` for `iriPrintSafe` took the check to 21
  percent and the query from 335 to 272 million instructions. Profile the
  repaired path again before recording its number.
- **Memory is a resource of its own; rank it and measure it by phase.** The
  first three survey rounds ranked by time only, and a COUNT query that held 9
  times the F* engine's resident memory did not rank
  (https://github.com/danbri/factoidal/issues/729). `l4query-phases FILE
  --stop-after PHASE` (`Harness/QueryPhases.lean`) runs the phases of
  `l4factoidal query` and prints `VmRSS`/`VmHWM`; run it under `/usr/bin/time
  -v` once per phase over a ladder that spans at least 16 times, and divide
  the difference of the peaks by the difference of the input sizes. The peak
  was `parseTurtle`'s `text.toList`: a `List Char` costs 35 bytes of peak
  resident memory per input byte, and nothing after it raised the peak
  (`--stop-after chars` reproduces it alone). Read a `String` that is already
  in memory with `String.foldl` or `String.all`, never with `toList`, on a
  whole-document path (`Syntax.parseTurtleText`). A change that removes a
  transient structure can leave the peak where it was: `normalizeDataset`
  without its quad list was proved equal and changed nothing at the peak, and
  interning IRIs after the parse (proved equal) took 9 MB off 188 MB for 8
  percent more CPU time; neither was landed. The gate rows are `query-memory` and
  `query-memory-fstar` in `tests/stack/lean_scaling.py`.
- **A test module that nothing imports never runs.** `lake build` builds the
  modules the umbrella `L4Factoidal.lean` reaches. Until 2026-10-10
  `TurtleChunkFoldTests.lean`, `TurtleStatementScanTests.lean` and
  `Utf8StreamTests.lean` were reached by nothing, and a design record cited
  the chunk-split guards of the first as evidence. After adding a `*Tests.lean`
  module, check that `.lake/build/lib/lean/.../<Module>Tests.olean` exists
  after `lake build`.
- **`csimp` makes a guard compare a function with itself.** After
  `closure = indexedClosure` is registered, a guard `indexedClosure g n ==
  closure g n` in a later module runs the same code on both sides. Restate the
  specification under another name in the test module and prove the two equal
  (`RLTests.closureScan_eq`), so the guard still compares two programs. The
  guards on `strLe` compare with `charsLe a.toList b.toList` for the same reason.
- **A csimp replacement needs its import.** The compiler applies a `@[csimp]`
  theorem only while compiling a module that imports the module stating it.
  `Wasm/Ops/Reason.lean` called `OWL.RL.closureFix` and got the indexed closure
  through an import of `OWL.Refute` it did not need for that call. On
  2026-10-10 the OWL DL ops moved to `ReasonDl.lean` (issue 713 stage 4, the
  core wasm), the import went with them, and `owlClosure` silently compiled to
  the scanning closure: the build, every guard and native-smoke stayed green.
  The wasm size table found it, because the scanning rules of
  `OWL/RLClosure.lean` were linked in again (113,186 bytes). Rule: a module
  that calls a function with a `csimp` twin imports the module of the `csimp`
  theorem explicitly, with a comment that says why; after moving imports,
  compare the size table (`tools/wasm-size-profile.py`) of the module before
  and after, and treat growth in a specification module as a lost `csimp`.
  `tools/lean-csimp-reach.py` finds the callers that lack the import (reason
  `not-imported`). First run, 2026-10-15: `Qlvr/Side.lean` and `Harness/Qlvr.lean`
  called `cmpBytes` without importing `Qlvr.CmpBytesFast`, so the side index
  compared words byte by byte.
- **A `csimp` twin of a loop does not reach the other callers of its
  round.** `closure_eq_closureFast` makes `RDFS.closure` run indexed rounds,
  but `RDFS.step`, the round it is built from, has no twin. `rhoDfClosure`
  (`Wasm/Ops/Reason.lean`) computed its closure with `closureFix` (indexed)
  and its `rounds` field with `roundsToFixpoint RDFS.step` (scanning), so the
  round counter took almost all of the op's time: no result in 120 s on a
  160-class `rdfs:subClassOf` chain, against 1.6 s for the closure. The
  2026-10-10 survey compared the op's output byte for byte but timed only
  `closure --regime rdfs`. Found 2026-10-12 by gdb stack samples of the
  running command; repaired with `stepFast` and `rhoDfRounds_eq`
  (https://github.com/danbri/factoidal/issues/756,
  `docs/designissues/2026-10-10-rdfs-seminaive.md` § 5). Rule: after adding
  a `csimp` twin, grep for every other call of the scanning pieces it replaces
  (here `step`, `stepConclusions`) and time each production entry that calls
  them, not only the one the twin was written for.

- **A faster loop keeps the readable loop's ORDER when it drops only what
  the deduplication drops.** The OWL 2 RL closure's output order is the
  naive rounds' list order, and the command line prints it. The semi-naive
  rounds (`OWL/RLClosureIndexed.lean` Section 11) evaluate, at a driving
  triple the previous round already held, only each row's delta term; the
  list they emit is the naive round's list with some triples removed, all
  of them already in the round's input. `addAll` drops exactly those, so
  `addAll_filter_of_subset` and one obligation per row (`RowSpec.Ok`: equal
  after filtering out what the row concludes from the previous input) give
  the same LIST at every fuel (`indexedClosureSN_eq`), and one `csimp`
  theorem installs it. A form that found the same SET by delta joins in
  another order would have needed a sort with its own proof, or a measured
  order. Issue https://github.com/danbri/factoidal/issues/756 item 2;
  `docs/designissues/2026-10-10-owl-real-ontologies.md` § 11.

## Input-proportional recursion is a stack bug, and the scanner is the gate

A function that recurses once per element of an input the CALLER sizes -- a
list, a string, a byte stream, a declared entry count -- costs one C stack
frame per element. On the host that is a slow path; in the wasm module it is a
crash, because the stack we ship there is far smaller. The rule:

> **Recursion over an input-proportional structure is tail-recursive or
> worklist-driven. Never rely on a bigger stack.**

### How to tell, by tool and not by reading

Lean compiles a DIRECT TAIL self-call into a jump: the emitted C function opens
with `_start:` and the call becomes `goto _start;`. Any self-call that survives
as a real C call is a real stack frame. Read that from the compiled output:

    lake build                                   # in formal/lean4/
    python3 tools/lean-tail-recursion-audit.py   # counts, areas, ranked table
    python3 tools/lean-tail-recursion-audit.py --json /tmp/t.json
    python3 tools/lean-tail-recursion-audit.py --gate   # CI form

`--gate` fails when a NEW input-proportional recursion appears that is not in
`tools/lean-tail-recursion-allow.txt`. Removing a line from that file is the
goal; adding one needs a reason in the commit message. Read the script's
docstring for what the method cannot see -- inlining, specialisation, and
recursion that runs through an unspecialised core combinator.

The first measurement, 2026-09-07: 833 self-recursions without a loop, 268
mutual cycles; 598 input-length, 42 input-depth. Per area (length): JSON-LD 71,
Shardborough 66, SPARQL 65, SHACL/ShEx 36, OWL 33, RDF parsers 18, XPath/XSLT
18, XML 11.

**The audit lists candidates; Node finds the ones that break first.** On
2026-10-10 (issue 713 stage 5) the npm bench ran the wasm module under Node,
whose default stack is about 1 MB and whose wasm frames are larger than native
ones. A SELECT of 16,000 rows and a canonicalization of 24,000 blank-node
quads failed with `RangeError: Maximum call stack size exceeded`, while the
native build answered the same SELECT with a 512 KB stack. All four
functions were already on the audit's allow-list: `SPARQL.numberRows`,
`SPARQL.rowsJoined` (which also copied the rest of the Results JSON document
once per row), `RDF.Canonical.collapseKeyedQQuads` and `dedupAdj`. To name
the function of a wasm overflow, link the module once more with
`--profiling-funcs` (same objects, about 4 minutes; `Wasm/build-wasm.sh`'s
link line plus that flag) and print the `RangeError`'s stack in Node: the
repeated frame is the recursion. Repair one, rebuild, run again: the next
one appears only after the first is gone. `npm/factoidal/test/large-inputs.test.mjs`
is the regression test.

### The repair: `csimp`, not a rewrite of the specification

Keep the specification's shape -- every theorem is stated about it -- and add a
tail-recursive twin plus a proved `@[csimp]` replacement. The code generator
then emits the twin and the proofs are untouched. `csimp` replaces one CONSTANT
by another, so the accumulator's empty start needs its own `def`:

```lean
def decodeEntriesTR (version : Nat) : Nat -> List UInt8 -> List Entry ->
    Option (List Entry × List UInt8)
  | 0, bytes, acc => some (acc.reverse, bytes)
  | n + 1, bytes, acc =>
      match decodeEntry version bytes with
      | none => none
      | some (entry, after) => decodeEntriesTR version n after (entry :: acc)

theorem decodeEntriesTR_eq (version : Nat) : ∀ n bytes acc,
    decodeEntriesTR version n bytes acc =
      (decodeEntries version n bytes).map (fun p => (acc.reverse ++ p.1, p.2)) := ...

def decodeEntriesImpl (version n : Nat) (bytes : List UInt8) := decodeEntriesTR version n bytes []

@[csimp] theorem decodeEntries_eq_decodeEntriesImpl :
    @decodeEntries = @decodeEntriesImpl := ...
```

`@[implemented_by]` reaches the same runtime effect with no proof. It is an
unchecked assumption about the two functions agreeing, and this tree does not
take those. Use `csimp`.

A `csimp` theorem changes only the code compiled after it. After `lake build`, run
`python3 tools/lean-csimp-reach.py --gate`: it lists the callers that still call the
replaced function (a caller above the theorem, a module that does not import it, an
inlined instance, a `where` helper of the only caller) and shows the callers of the
replacement (`skills/lean4-proof-patterns/SKILL.md`, 9e;
`docs/designissues/2026-10-15-csimp-reach.md`).

### What it cost

* <https://github.com/danbri/factoidal/issues/670>. `ShardManifest.decodeEntries`
  recursed once per manifest entry. The published SKOS manifest declares 36,106,
  so a browser tab answered "Maximum call stack size exceeded", and
  `storeQueryPlan` never returned.
* <https://github.com/danbri/factoidal/issues/673>. Recorded as "XML entity
  expansion is not tail-recursive, near 2,000 sequential entities". The scanner
  plus a bisection said otherwise: `expandEntityValue` was already loop-compiled
  except for its nested-entity dive, and the ceiling tracked DOCUMENT LENGTH,
  not entity count. 500 plain sibling elements and 12,000 characters of ordinary
  text both died, with no entity present. The recursion was
  `normalizeLineEndings`, the section 2.11 line-ending pre-pass, which walks
  every character of the document before parsing starts. The wasm RDF/XML
  parser's ceiling was about 7,000 characters of any input.
  That repair did not close the issue, and "not entity count" was only half
  right: the first recursion hid a second one. `XML.scanRefs`, the scan of a
  text run or a start tag for references, combined each reference's flags
  after its recursive call returned, one native frame per reference. The
  native canary of 2026-10-10 (`LEAN_STACK_SIZE_KB=512`) and `gdb` found it:
  10,000 sequential references aborted natively at 512 KB, and 5,000 threw
  under `node --stack-size=512`. The tail-recursion audit had it in class
  `counter` (its `Chars` argument is an `abbrev` of `Array Char`, which the
  textual classifier does not resolve), and `--gate` does not check that
  class. Repaired the same day with an accumulator loop, `scanRefsLoop`, and a
  `csimp` theorem (https://github.com/danbri/factoidal/issues/673). After a
  repair of one recursion, run the bisection again: a second one can sit
  below the first.
* The 36,106-entry manifest took 322 s natively. That number did NOT come from
  the recursion: `/usr/bin/sample` put every sampled frame in
  `ShardManifest.valid` -> `uniqueArtifactKeys` -> `List.eraseDupsBy`, a
  quadratic duplicate scan over about 150,000 artifact keys. Measure before
  attributing a cost to the defect you happen to be holding.

`tests/stack/run.sh` is the behavioural half of this: deep inputs on two
routes, the wasm module in Node (installed by `tools/fetch-builds.sh` or
built by `Wasm/build-wasm.sh`; not committed since 2026-10-09) and the
native CLI. Add a case there
whenever you repair one of these.

## Idioms that compile to tight C

Each rule below names the generated C or assembly that supports it. Record,
numbers and method:
[`docs/designissues/2026-10-12-lean-to-c-performance.md`](../../docs/designissues/2026-10-12-lean-to-c-performance.md)
(https://github.com/danbri/factoidal/issues/797). Look at the C before you
measure: `lake build` writes it to `.lake/build/ir/<Module>.c`;
`python3 tools/qlvr/bench/c-audit.py FILE.c NAME` counts the runtime
operations per loop iteration; `leanc -O3 -DNDEBUG -S` of a small file gives
the assembly.

- **A `let` is evaluated before the `match` that follows it, in every
  branch.** Lean is strict: `let hash := hashPairs l r shared` written once
  before `match l.sortVar with ...` and used only in the fallback branches
  computed the hash index in the merge branch too and threw it away. On
  DBpedia d11 (OPTIONAL, 2026-10-13) that was 33 ms of a 50 ms warm run:
  a `Std.HashMap` of 197,044 right rows built for a merge join that did not
  use it (found with `valgrind --tool=callgrind`: `hashPairs` called 8 times
  in 8 runs that each printed `merge on ?p`). Put the work in a function and
  call it in each branch that needs it (`OptJoin.hashInner`), or write the
  binding as `fun () => ...`. The compiler does not move it into the
  branches for you.
- **Index bytes with `USize` and `ByteArray.uget`, never with `Nat`.** At a
  `Nat` position each byte read is `lean_nat_add` (a scalar test, an
  overflow test and a box), `lean_byte_array_fget` (an unbox) and `lean_dec`
  (a scalar test). At a `USize` position with one bounds test and eight
  `uget`, clang -O3 emits two compares and ONE 8-byte `movq`; emcc emits one
  `i64.load`. Use `L4Factoidal.Prim.Bytes.ldU64LE` (proved equal to its
  specification, `ldU64LE_eq`); `Codec.Zstd.word64U` reads through it. The q07
  kernel: 31.4 ms with `Nat` indices, 11.3 ms with `USize` indices, pure Lean.
- **Write the bounds test in `USize`, then derive the `Nat` fact.** `if h :
  i < a.usize` costs one compare; `if h : i.toNat < a.size` costs
  `lean_usize_to_nat`, a boxed `lean_byte_array_size`, `lean_nat_dec_lt` and
  two `lean_dec` (16 `Nat` operations and 8 reference-count tests per kernel
  iteration before the repair). The lemmas to reuse are in
  `L4Factoidal.Prim.Bytes`: `usize_lt_size`, `usize_add_small`,
  `window_of_test`, `window_lt`, `test_of_window`; each handles
  `ByteArray.usize = size % 2 ^ numBits` and both 32-bit and 64-bit hosts.
- **Never test against `USize.size`, or any constant of 2^63 or more, at run
  time.** On a 64-bit host it is a big `Nat`: the test calls
  `lean_nat_big_lt` and GMP. Test against a small constant and prove it is
  below `USize.size` (`Codec.Zstd.copyBound`, 2^30, small on wasm32 too).
- **Loop over `USize` with a proved measure, not with `Nat` fuel.**
  `termination_by n.toNat - i.toNat` and `decreasing_by` with
  `Prim.Bytes.usize_succ_toNat` (or `usize_pred_toNat` for a count-down) give a loop
  whose C uses `size_t` only. A `Nat` fuel argument costs
  `lean_nat_dec_eq`, `lean_nat_sub` and `lean_dec` per iteration.
- **A loop that takes a function argument gets `@[specialize]`.** The kernel
  loops take the store function as an argument; specialised, their C calls it
  directly or inlines it, with no `lean_apply_*`.
- **Eight `uset` are eight stores.** Each `uset` tests exclusivity and may
  copy; clang cannot merge them because a byte store may alias the reference
  count. Use `L4Factoidal.Prim.Bytes.stU64LE`: an `@[extern c inline]` 8-byte
  store (one bounds and wrap test, one exclusivity test, byte order explicit
  in the C) whose Lean meaning is `stU64LERef` (eight `uset`). Kernel, native:
  12.3 ms with eight `uset`, 6.4 ms with `stU64LE`, C 5.3 ms; wasm32: 15.6,
  12.6 and 3.8 ms (2026-10-12, load 0.7 to 0.9).
- **A C primitive has a Lean reference and a differential test on every
  target** (owner, 2026-10-12, "library yes"; CLAUDE.md, qlvr section). The
  extern's body is a call of a separate non-extern definition (the
  reference), every theorem is about the reference, and a test executable
  compares the two natively and as wasm32 under node (`tests/prim/run.sh`).
  `tools/lean-wasm-exe.sh MODULE OUT.js` builds any executable whose imports
  have no FFI as a wasm32 program from the same generated C, with the
  runtime objects that `Wasm/build-wasm.sh` leaves in `/tmp/l4wasm-build`.
  In such a program read files through `IO.FS.Handle.read`, not
  `IO.FS.readBinFile` (its size query calls libuv, absent on wasm32).
- **`ByteArray.push` is an out-of-line call** (`lean.h` line 1195 in 4.33):
  14 % of the zstd decoder's self time. Write into a buffer of known size
  where the algorithm allows it.
- **A `for` loop with several `let mut` variables carries an `MProd`.** Each
  iteration tests exclusivity of each cell, takes it apart and builds it again;
  `for x in [i:ie]` allocates its `Std.Range`. In a hot loop write a
  tail-recursive function with the state as arguments.
- **A tuple returned from an inner loop is an allocation per call**
  (`lean_alloc_ctor`, and `lean_box_usize` for a `USize` field). Return one
  value, or fuse the inner loop into the outer one. Fusing: make the inner
  loop a state of the outer loop (extra arguments, a lexicographic
  `termination_by`), keep the nested version as the reference and prove the
  two equal by `fun_induction` on the fused one (`QlvrKernel.mergeFlatU_eq`,
  record section 8). q07 kernel: 40,107 frees per run to 0, 32.1 to 27.9
  million instructions per run.
- **Build an output buffer by appending, not by writing into a copy.** Pure
  Lean has no uninitialised `ByteArray`, so a buffer for `stU64LE` must first
  be a copy of some array of the final size: in the q07 kernel, five copies
  per run, four of 2.16 MB. Start from `ByteArray.emptyWithCapacity n`
  (allocation, no copy) and append with `L4Factoidal.Prim.Bytes.pushU64LE`
  (an `@[extern c inline]` primitive: one exclusivity and capacity test, one
  8-byte store; otherwise eight calls of the runtime's
  `lean_byte_array_push`). A buffer that is too small grows, so the append
  version is also correct for any input.
- **The compiler shares equal pure expressions.** Two
  `ByteArray.emptyWithCapacity (8 * n)` (or two `scratch` calls with the same
  arguments) in one function become ONE object with two references; the first
  write to each then copies or reallocates. An unused "tag" parameter does not
  prevent it: the compiler removes it (`___redArg`) and shares again. Make
  the expressions differ (capacity `n + tag`), and check the generated C for
  `lean_inc_ref_n` on the buffer.
- **Prove the per-load bounds test away with one test before the loop.**
  `Prim.Bytes.ldU64LEIn d p h` is eight `uget` and no test, for
  `h : p.toNat + 8 ≤ d.usize.toNat`; `ldU64LE_eq_in` proves it equal to
  `ldU64LE`. Test `n ≤ d.usize / 8` once in `USize`, then `le_div8_toNat` and
  `idx8_window` give `h` for every row `i < n`. In the q07 merge loop this
  removed the slow-path calls from the loop, and with them the register
  spills: 16.3 to 8.2 million instructions in that loop
  (`QlvrKernel.mergeFlatP_eq`, `mergeFlatIn_eq`).
- **An `@[extern c inline]` primitive cannot run in the interpreter.**
  `#guard`, `#eval` and `decide`-by-evaluation of code that reaches it fail
  at build time: "Could not find native implementation of external
  declaration". So a `@[csimp]` from a widely used function to such a
  primitive breaks every `#guard` on the way (it did for `Qlvr.Side.put64`:
  the `#guard`s of `Qlvr/Side.lean` and `Qlvr/MergeTheorems.lean`, 2026-10-12).
  Call the primitive only in code that no `#guard` evaluates, or keep the
  check as a compiled test.
- **The C compiler options do not repair these costs.** `-O2`, `-march=native`,
  thin LTO over the generated C and PGO (clang 18) changed the kernel and the
  queries by less than the noise and the zstd decoder by +11 to +12 %; the
  `word64U`/`pushCopyU` change gave +26 %. LTO and PGO do not reach the Lean
  runtime (`push`, `copy_slice`, the allocator), which is machine code in the
  toolchain. `tools/qlvr/bench/pipeline.sh` rebuilds `l4qlvr` with other
  options for such a measurement.

## Factoidal RDF/block ingestion

The parsing layers and their entry points are recorded in
[`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md);
read it before changing a parser path.

`L4Factoidal/Syntax/Turtle.lean` preserves source triple order. Its statement
parser and flat name/whitespace scanners use append-free/tail-recursive paths;
retain that order contract when changing them. `parseTurtleFold` lets a packer
consume completed statements without materialising a second source `Graph`,
but it still starts from a complete `String` and character list. Treat genuine
byte-chunk input as the next separate design step: it must carry Turtle prefix,
base-IRI, RDF-mode and blank-node state across chunks. Never split Turtle on
newlines.

`Storage/PredicateBlocks.lean` keeps per-predicate rows in reverse buckets
while ingesting, then restores source order before creating an `IndexedBlock`.
The packer may avoid a duplicate graph, but the current one-block-per-predicate
format still retains each predicate's rows until its immutable block is built.
Do not claim streaming-scale memory until bounded block publication exists.

`Syntax/TurtleStatementScan.lean` is the chunk-stable candidate scanner the
packer runs per character. Any per-character or per-line decision in it must
read O(1) state, never the accumulated candidate. Paid for 2026-09-02: the
no-dot directive test reversed the whole current candidate at every line end
(`dropWs currentRev.reverse`), O(lines × characters) per statement group,
which turned a 134 MB polygon group (4,211 lines) into 334 s of packing and
the UK Parliament dump into 6,134 s. The fix keeps a seven-character `head`
maintained by `pushHead` and proves it equal to the old form
(`TurtleStatementScanTheorems.head_eq_spec`). How it was found: a size
ladder of slices without large literals was linear (34 µs per triple), so
the cost was isolated to the large-literal region and that region packed
alone; do that before reading code for a superlinear ingest.

## A tree read whole, then walked once (RDF/XML, 2026-10-13)

`l4factoidal parse --format rdfxml` took 13 to 15 times Oxigraph's time and
held 48 to 49 bytes of resident memory per input byte
(https://github.com/danbri/factoidal/issues/814,
https://github.com/danbri/factoidal/issues/771; record:
[`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md)
section 3c). Measured with callgrind and `l4query-phases FILE --rdfxml-op`;
100,000 triples went from 7.67 s and 687 MB to 1.66 to 2.23 s and 181 to 190
MB, output bytes unchanged. Rules from it:

- **A conversion of the whole document to `List Char` costs 24 bytes per
  character, and each further pass over it as many again.** The XML layer
  built the list, an array to read the declaration, a second list through the
  line-end rewrite and the final array: 633 MB for 13 MB of text before the
  first element. Build the array from the `String` in one `String.foldl` with
  `Array.emptyWithCapacity s.utf8ByteSize`, and run a rewrite only when the
  text holds a character it changes (`documentChars_eq_fast`).
- **A name split per lookup is a cost per lookup.** `findNsAttr` split every
  attribute name of the element (`String.toList`, two `String.ofList`, about
  5,000 instructions) for each of about 20 lookups per element: 53 percent of
  the instructions. Test a cheap necessary condition first (the name ends with
  the local part; `findNsAttr_eq_fast`). A `String.foldl` with a structure
  state still allocates per character (about 140 instructions per character in
  `splitQNameFast`); call it less often rather than only faster.
- **When a consumer takes the children of a node once, in order, fold them
  while they are read.** `parseChildrenFold` is `XML.parseChildren` with each
  child handed to a step function instead of put on a list. The equality
  theorem generalises over the children already read: the fold state is
  `acc.reverse.foldl f a0`, and each branch of the two definitions, written
  with the same structure, closes by `cases h : <inner call>` and the
  induction hypothesis (`parseChildrenFold_eq`). The `csimp` on the entry
  point (`parseRdfXml_eq_stream`) puts every caller on the fold.
- **A freed array still counts in the peak.** After the 105 MB character
  array of the 100,000-triple file is freed, the resident set does not fall:
  the allocator keeps the huge segment resident, and the N-Quads output and the
  count's set of distinct triples are allocated beside it. Reduce what is live
  while the big array is live, and measure the peak of the whole command.

## Values that two threads can reach (paid for 2026-10-13)

`IO.asTask` marks everything its closure reaches as multi-threaded (MT), and
so does a task's result and every value put in an `IO.Ref` that a task can
reach. The Lean runtime treats an MT object differently in two ways, and
both cost the divided SBM11 scans of
https://github.com/danbri/factoidal/issues/799 (stage 1b; record
[`docs/designissues/2026-10-12-parallel-block-scans.md`](../../docs/designissues/2026-10-12-parallel-block-scans.md)
section "Stage 1b", subsection "What failed on the way"):

- **An MT object is never updated in place.** `lean_is_exclusive` is false
  for it whatever its count (`lean.h`), so every `insert`, `push` or `set`
  copies it. A `Std.HashMap` page cache made in the parent and given to the
  tasks copied its whole bucket array on every insert: olympics q21 took 335
  ms at 4 threads against 158 ms at 1 thread, with `lean_copy_expand_array`
  and `lean_mark_mt` at the top of the profile. Rules: a structure a task
  writes is made by that task (create the `IO.Ref` inside the task body); a
  structure tasks share and write is one whose update copies one path (a
  `Std.TreeMap`), behind a lock.
- **A value reachable from a global is MT too, with no task anywhere.** An
  `initialize` handle table (`IO.Ref (Std.HashMap String Session)`) is a
  global, so the session put in it, its `IO.Ref`s, and every value later
  stored in those references are marked MT. Paid for 2026-10-25
  (https://github.com/danbri/factoidal/issues/1009 KR1, `Wasm/Ops/Sbm11.lean`):
  the single-thread SBM11 session held by the wasm op took 374 ms on olympics
  q19 against 196 ms for native `l4sbm11 query` over the same reads
  (strace: the same 8,396 `pread`s); callgrind gave 25 percent of the
  instructions to `lean_mark_mt` and 22 percent to `lean_del_core_other` and
  `lean_copy_expand_array`, because each page-cache insert marked the whole
  cache and copied its bucket array. Rule: a handle table holds the session;
  each request runs on a copy with references of its own
  (`HostSession.Session.localize`) and writes the caches back once at the end
  (`Session.keep`). Then q19 took 200 ms. Raising the page limit and removing
  a `try` per store call had changed nothing: profile first.
- **Taking and releasing a reference to an MT object is an atomic operation.**
  Reading the parent's `ScanSpec` in every block from 4 tasks made them
  contend on its cache lines: DBpedia d17 took 7.9 ms at 4 threads against
  3.7 ms at 1, and the CPU time grew with the thread count (each task added
  about 2.8 ms). A read through a field also takes a reference
  (`ss.g.dictHdr.termCount` compiled to `lean_inc_ref` of the shared header
  on every `keySlice`). Rules: give each task its own copy of every small
  structure it reads in a loop (`IdQuery.ScanSpec.fresh`, `FKind.fresh`),
  made inside the task; keep a scalar the hot path needs in a field of its
  own; copy a value a task takes from a shared cache (`copyPage`).
- **The compiler removes a copy that rebuilds a structure from its own
  fields.** `⟨x.a, x.b⟩` compiles to `x` (check with
  `set_option trace.compiler.ir.result true`). Arrays copied with `map` and a
  non-identity function and words through `toNat` and back are new objects;
  a pair rebuilt from a shared pair is a new object (the reset/reuse path
  allocates when the pair is shared). **`s ++ ""` and `"" ++ s` are NOT new
  strings**: the compiler emits `s` itself for both (`lean -c`, Lean 4.33.1).
  Use `IdQuery.freshStr` (`String.ofList s.toList`, `@[noinline]`). Cost,
  found 2026-10-23 (KR 1.2 of batch 3): this skill said the opposite from
  2026-10-13, so `ScanSpec.fresh`, `FKind.fresh` and `countPartM` kept the
  shared variable-name strings for ten days; on DBpedia d10 at 4 threads the
  reference counts of the group variable names were 5 percent of the profile
  (0.5 percent at 1 thread). Check a copy in the generated C
  (`.lake/build/ir/...c`) before you write that it is one.
- **Memory a task allocates and the parent frees is not reused at once.**
  mimalloc gives each thread its own heap; a block freed by another thread
  returns to its heap later, and fresh memory in this machine's heaps comes
  in 2 MB huge pages that the kernel clears on first touch (`clear_page_erms`,
  a third of q19's profile at 4 threads with whole-block render buffers).
  Rule: what a task hands to the parent is small pieces (512 rows, about 64
  KB), not one buffer per block.
  The huge pages come from mimalloc (v2.2.3 in Lean 4.33.1, the only
  allocator of the runtime: `LEAN_MIMALLOC` in `include/lean/config.h`), which
  calls `madvise(MADV_HUGEPAGE)` on its memory (`allow_large_os_pages`). With
  `MIMALLOC_ALLOW_LARGE_OS_PAGES=0` (or `prctl(PR_SET_THP_DISABLE)`) peak RSS
  at 4 threads fell by 17 to 31 MB and no 4-thread time changed beyond the
  variation (2026-10-23, stage 1i of the parallel-scans record). The
  `MIMALLOC_*` variables are read at process start (`MIMALLOC_VERBOSE=1`
  prints them). A change of a default allocator setting goes to the owner
  with its measurements first (CLAUDE.md, KR 1.2 decisions of 2026-10-23).

- **A task per small range starts every per-task cache empty.** The divided
  streamed path ran one task per block, each with a new page cache filled
  from the shared level under a lock; olympics q19 at 4 threads used 1.5
  times the CPU time of 1 thread, most of it `copyPage` and lock waits.
  Repair (2026-10-23, `Harness/Sbm11Query.parFold`): at most N worker tasks
  per fold that take ranges from a shared counter and keep their caches; a
  ready page of the shared tree map is read without the lock; a page is
  copied into a worker's cache on its second use only. A worker cache that
  lives longer than one fold must be reachable from two threads, so it is MT:
  tried with a `Std.TreeMap` per worker slot, q19 at 4 threads went from 18
  to 22 ms (tree look-ups on every id). Find what threads wait for with
  `perf sched record` and `perf record -e sched:sched_switch --call-graph
  dwarf`, not only with CPU samples.

- **Comparisons over values that tasks share.** An ORDER BY sort cut into
  blocks, one task per block (`Task.spawn`), each comparing `EvalResult`s of
  one shared array: the closure makes the array and every value in it MT, so
  every `getD` in every comparison took and dropped a reference atomically,
  in the tasks and in the parent's final merge passes. 137,026 labels: 930
  ms at 4 threads against 648 ms single-threaded (2026-10-23, KR 1.2 of
  https://github.com/danbri/factoidal/issues/875; not kept). Rule: a task
  compares values it made itself, or scalar keys.
- **A column passed to a specialised loop as a closure costs an allocation
  per row.** `rangePairs (l.at c) ...` gave `mergeGo` a closure; the loop was
  specialised for the closure *parameter*, so every row read was
  `lean_apply_1` and its `UInt64` result was boxed: a merge join of 6,248 and
  13,369 rows took 2.5 ms in 4 tasks against 0.45 ms on one thread. Repair:
  bind the byte arrays to local names and pass `fun i => word64 ca (8 * i)`
  at the call site, with the helper `@[inline]`, so that `mergeGo` is
  specialised for the lambda (`ParallelJoin.rangePairsOf`). Check the
  generated C for `lean_apply_1` in the loop.
- **A task waits for a worker that sleeps.** The Lean pool's workers block on
  a condition variable when idle; on the 4-vCPU test VM a woken thread runs
  50 to 120 microseconds later (median 79, p90 126, a C condition-variable
  test). The pool also starts workers lazily (a new one only when a task is
  queued and none counts as idle), and `perf sched record` showed 2 worker
  threads in a whole 4-thread q07 process. So a phase of less than about 0.5
  ms single-threaded does not gain from tasks: olympics q07's merge join (0.45
  ms) in 4 ranges took 0.47 to 0.52 ms, its ORDER BY with values read by
  range workers 0.5 ms more. What helped: the calling thread runs the first
  range itself after it has started the tasks of the others (q07 at 4
  threads, 4.25 to 3.68 ms). Starting all N pool workers at open (N tasks
  that wait until all N run) did not: no time gained and peak RSS above 2
  times the 1-thread RSS (each worker's heap). Stage 1f of
  [`docs/designissues/2026-10-12-parallel-block-scans.md`](../../docs/designissues/2026-10-12-parallel-block-scans.md).
- **Workers that stay awake: a per-session pool, and its three traps**
  (2026-10-23, https://github.com/danbri/factoidal/issues/961, stage 1g of the
  same record). `Harness/WorkerPool.lean`: N - 1 threads
  (`Task.Priority.dedicated`) that poll a mailbox `IO.Ref` with `swap` for
  up to 1 ms, then block on a promise; results come back the same way.
  `l4pool-bench`, 3 jobs after 200 microseconds of caller work: start p50 5,
  p90 9 microseconds, against 59 and 87 with `IO.asTask`. Paid for on the
  way: (1) a mailbox and results passed as `IO.Promise` values: start p50
  24 microseconds, because `resolve` and `wait` take the task manager's lock,
  which every thread shares; resolve a promise only for a reader that
  blocked. (2) A mailbox written with `IO.Ref.modify` while the worker
  polled it with `swap`: p90 1,020 microseconds, the whole poll time; write
  with `swap` then `set`. (3) A shutdown that only resolved the published
  promise of a blocked worker: a worker between its last poll and its wait
  had not published one yet, and the process hung; write a value. Polling
  workers beyond the hardware threads (8 on 4 vCPUs) made q07's scans 3 to
  5 times slower, so the pool starts only when N is at most the hardware
  threads (`System.Platform.Internal.getHardwareConcurrency`).
- **Awake workers do not make a small step that reads shared structures
  pay.** Olympics q07's ORDER BY readings (291 values) and rendering (313
  rows), cut into 4 parts on the pool with a view of the session per part:
  each part took 2 to 4 times as long per item as the same part on the
  calling thread with its own page cache (page copies on second use,
  references to shared pages), and the parent's sort of the values that
  workers returned (MT) took 0.48 ms against 0.14 ms. Over 6 processes the
  query was not faster (median 3.29 ms against 2.99 ms). What did pay on
  the pool: the merge join of 6,248 by 13,369 rows in 4 ranges (pure, over
  two byte arrays), 0.42 to 0.19 ms.
- **A job written as a `do` block in the caller does its pure steps on the
  caller.** The compiler moves a pure `let` of a closure body out of the
  closure when it does not depend on the closure's argument, and an `IO`
  `do` block given to `spawnAt` is such a closure. The divided SBM11 scans
  wrote `let spec := spec.fresh`, `let cands := cands.map ...` and
  `rangeMetas ...` at the top of the job "so that the task makes its own
  copies"; the generated C (`.lake/build/ir/Harness/Sbm11Query.c`) called
  `ScanSpec_fresh`, the copy of the candidates and `rangeMetas` in the
  caller's loop, before `lean_alloc_closure` of the job. So the calling
  thread made every task's copies before it scanned its own range (each
  task started 9 to 18 microseconds after the one before), and the copies,
  reached by the job, were shared objects (2026-10-24, stage 1o of
  [`docs/designissues/2026-10-12-parallel-block-scans.md`](../../docs/designissues/2026-10-12-parallel-block-scans.md),
  https://github.com/danbri/factoidal/issues/961). Rule: put the body of a
  job in a `@[noinline]` function of its own (`scanRangeJob`,
  `sipRangeJob`) and pass that function's application to the spawn, or wrap
  the step in `IO.lazyPure fun _ => ...` (`poolMap`); then check the
  generated C for where the copy is called.
- **`Array.ofFn` is slow in compiled code.** `Array.ofFn (n := 312) fun k =>
  word64 b (8 * k)` took 50 to 220 microseconds; the same with
  `Array.mkEmpty n` and a `for` loop of `push`, 4 to 6 microseconds
  (`IdQuery.unpackWords`, stage 1o). Use the loop.
- **Give a job a buffer of words, not the caller's `Array UInt64`.** An
  `Array UInt64` holds one object per word, in the heap and cache of the
  thread that made it; `ByteArray` words are contiguous (312 words: 39 cache
  lines). The divided scan with candidates passes `IdQuery.packWords cands`
  and the job unpacks its own array (`unpackWords_packWords`).
- **A worker cache that lives across queries copies on first use.** A pool
  worker's page cache (`WorkerPages`) is kept from one query to the next, but
  the scans' rule copies a shared page only on its second use in one job;
  rendering reads most pages once, so every query read them again from the
  shared `taskPages` (olympics q07: 2 to 4 times the time per row of the
  calling thread). The rendering beside the ORDER BY sort copies on first use
  (`Session.copyFirst`), and range `j` always goes to worker `j`, so the
  pages are in that worker's cache from the second run on.

- **Make a comparison's per-value work once per value.** `sparqlOrder`
  reads `isNumericOperand`, `numericValue?`, `integerDerivedValue?` and
  `promoteLiteral` of both operands on every comparison; an ORDER BY of `n`
  values does that about `n log n` times. `IdQuery.OrderRead` makes them
  once per value and `SPARQL.sparqlOrderViewed` compares two readings
  (`sparqlOrder_eq_viewed`, `WorkerPoolTheorems.orderRanks_map`): q07's sort
  and ranks 0.33 to 0.14 ms at every thread count.

- **Split the extra CPU of N threads by class before you write a fix**
  (2026-10-23, stage 1h of the same record,
  https://github.com/danbri/factoidal/issues/961). Stage 1g named "shared
  reference counts on PRM1 entries" as the likely cause of slow worker
  ranges; three copies made by the worker (counters, permutation handles,
  PRM1 entries) were then measured and gave nothing: on olympics q07 the
  atomic reference counts are 0.19 ms of 13.2 ms CPU per run at 4 threads.
  Method: `perf record -e cpu-clock --call-graph dwarf` of `--repeat N` and
  of `--repeat 1`, then `tools/perf-cost-split.py`, which subtracts the
  second and puts each sample in a class (pool polling, page faults,
  atomic RC, allocator, kernel, compute). Use
  `/usr/lib/linux-tools/6.8.0-146-generic/perf` (`/usr/bin/perf` refuses the
  container kernel). This VM has no hardware counters: cache misses show
  only as more samples in the same compute symbol. `lean_dec_ref_cold` also
  frees single-threaded objects (a count of 1 reaching 0), so its samples
  are an upper bound for atomic decrements. For wall time per range, mark
  start, end and `IO.getTID` per range and record
  `perf record -k CLOCK_MONOTONIC -e sched:sched_switch`: none of 800 q07
  ranges was switched out, so their extra time is on the CPU.
- **A value per pool thread stays single-threaded.** A value that a worker
  thread makes itself and passes to its jobs as an argument is never marked
  MT (an `IO.Ref` the parent made, or anything a job closure captures, is).
  Tried for a dictionary page cache that lives as long as the pool (stage
  1h): olympics q19 at 4 threads 21.1 to 16.8 ms and 40 percent less CPU,
  but peak RSS 2.03 times the 1-thread RSS against a limit of 2, so not
  kept until the allocator work. Landed 2026-10-23 with transparent huge
  pages off in `l4sbm11` (owner: "Land it"; stage 1i of the record).
- **`IO.Ref.get` on a ref that another thread writes can lose the write.**
  For an MT ref, `lean_st_ref_get` takes the value out with one atomic
  exchange, increments it and puts it back with a second exchange; a `set`
  by another thread between the two is overwritten and its value freed
  (two `xchg` in the disassembly of `lean_st_ref_get`, Lean 4.33.1). Use
  `swap`, `modify` or `modifyGet` on a ref two threads write, and ask
  whether a result is ready through its promise (`IO.hasFinished
  p.result?`), never by `get` of the result's ref. Paid for 2026-10-23
  (stage 1j of the record): `parFold` with the calling thread as a worker
  polled each result slot with `get`; about one fold in 4,000 lost a range's
  result ("block range 1: its worker stopped"), and the process then hung at
  exit because the error skipped the pool's shutdown. Found by the 1b.6
  measurement method, which logs a process that fails: run it before a
  landing, and read its log.
- **`modify` and `modifyGet` lose a concurrent `set` or `swap` too; use one
  family of ref operations per shared ref.** The rule above said "use
  `swap`, `modify` or `modifyGet`"; that was wrong. In the runtime (Lean
  4.33.1, disassembly of `lean_st_ref_get`, `_take`, `_set`, `_swap`) there
  are two families. `set` and `swap` are one atomic exchange each. `get`,
  `take`, and `modify`/`modifyGet` (`take`, then `set`) exchange the value
  for null, spin while they find null, and put a value back with a second
  exchange: they exclude each other, but a `set` or `swap` by another thread
  between their two exchanges is lost (`get` restores the old value and
  frees the new one, `modify` overwrites it, a `swap` that finds null
  returns its own argument). Rule: a ref that two threads reach uses only
  `set`/`swap`, or only `get`/`modify`/`modifyGet`/`take`. A flag that one
  thread reads with `get` is written with `modify fun _ => v`. Paid for
  2026-10-24 (https://github.com/danbri/factoidal/issues/981): the worker
  pool's stop flag was read with `get` and written with `set`; a worker that
  read it while `shutdown` wrote it kept `false` and blocked on its mailbox,
  and `shutdown` waited for its thread for good. Seen once as a 600-second
  hang of `ids-path-star-nested` at 4 threads in `tests/sbm11/threads.sh`
  (not reproduced in 1,350 query processes); `l4pool-bench stress` (start,
  wake, stop the pool in a loop) hangs within 20,000 cycles before the
  repair. `tests/sbm11/pool-stress.sh` runs 500 short query processes with a
  time limit and gdb stacks of a hung process.

- **What the calling thread gives to a job, the calling thread frees with
  atomic operations.** A list, map or array that a job closure captures, or
  that a job returns, is MT; when the calling thread drops it, each of its
  objects is freed with an atomic decrement (and `mi_free_generic_mt` for a
  block another thread allocated). Give a job numbers, and return numbers:
  block ranges as bounds `(lo, hi)` that the job expands
  (`ParallelScan.rangeBounds`, `rangeBounds_map`), group counts as arrays of
  numbers (`IdQuery.FlatGroups`, `mergeFlat_toFlat`). Paid for 2026-10-23
  (stage 1k of the record): on DBpedia d10 at 4 threads the free of the
  5,941-position lists after the fold took 0.11 ms and building them 0.2 ms;
  both went to 0.03 ms. A `Nat` below `2 ^ 63` is a scalar, so an
  `Array Nat` of ids is one object.
- **Borrowed parameters remove reference counts on shared entries.** A
  function that takes a shared structure as an owned parameter increments
  and decrements it at each call; with `(b : @& BlockMeta)` it does neither.
  Stage 1k: the per-block scan functions with borrowed PRM1 entries halved
  the atomic-reference-count CPU of d10 at 4 threads (1.07 to 0.52 ms per
  run). A copy of the entries per job (`rangeMetas`) did the same for the
  counts but cost more in the allocator, and was not kept for that path.
- **A `Nat` literal of `2 ^ 32` or more is read from decimal text where it is
  used.** The C code calls `lean_cstr_to_nat("36028797018963968")` at each
  evaluation, also inside a loop, and arithmetic above `2 ^ 63` makes a
  big-number object. Put the number in an `@[noinline] def` (computed once)
  or compute in `UInt64` with a theorem against the `Nat` form
  (`IdQuery.countId_eq`). Check with
  `grep lean_cstr_to_nat .lake/build/ir/<Module>.c`.

- **A worker reads data that the calling thread made at about half speed.**
  The merge join of olympics q07's first two scans in 4 equal ranges: the
  calling thread's range took 0.065 ms, and it then waited 0.085 to 0.15 ms
  for the worker ranges, because the calling thread had appended both input
  tables and their bytes were in its cache (2026-10-24, stage 1p of
  [`docs/designissues/2026-10-12-parallel-block-scans.md`](../../docs/designissues/2026-10-12-parallel-block-scans.md)).
  Rule: when the input of a divided step was made by the calling thread,
  give the calling thread the larger range (`ParallelJoin.rangesShare`,
  `Par.joinShare`, 1.4 times an equal share), and measure the ranges, not
  only the phase.
- **Compare variants at N threads inside one process.** At 4 threads whole
  processes of q07 are 20 to 35 percent apart in every phase, the serial ones
  too, and the machine changes speed from hour to hour. Paid for 2026-10-24
  (stage 1p): (1) stage 1o reported "25 percent more thread time per block at
  4 threads, cause not found"; the four range times of one query add up to
  the 1-thread scan time, and decode on bytes the thread holds costs the same
  summed thread time at 4 threads as at 1 (1,541.5 against 1,541.5
  microseconds); the 25 percent was the difference between processes. (2) A
  binary that differed from `main` only in `packWords` measured 0.77 against
  0.63 ms in its scan phase over 8 interleaved processes, and 4 percent slower
  at 1 thread in every phase, which the change cannot cause. Method: read the
  setting per run, alternate the variants between the runs of one process,
  compare the medians of the variants inside each process, over 6 or more
  processes. It cannot see an effect that stays in the process once it
  happened (an object marked multi-threaded), and the final decision still
  takes the interleaved 1b.6 run.
- **A phase mark between pure steps does not time them.** The compiler moves
  a pure `let` to where its value is first used, so a mark placed after it in
  an `IO` block can run first. Stage 1p: the block weights and cut points of
  `scanSipTableParM` were computed after the next mark, not before it, and
  `packWords` looked free. Read the order in the generated C
  (`.lake/build/ir/...c`) before you give a phase its cost, or put the step
  in a `@[noinline]` function whose result the mark needs.

Measure every one of these with `perf record` at 1 and N threads and the
CPU time (`perf stat -e task-clock`): CPU time that grows with the thread
count at a fixed amount of work is the sign. Take the two profiles in one
process, or several of each, for the reason above.

A fourth case, 2026-10-14, tried and not kept: `Session.withOverlay` of the
SBM11 replay cut the four permutations of the overlay state in four tasks
(`Task.spawn fun _ => Overlay.forPerm st p`). The tasks capture `st`, so `st` and
the sets inside it become MT. The gate fixture gained 170 ms (850 to 960 ms down
to 640 to 790 ms), olympics gained nothing (4.1 s both ways) and its peak RSS
rose by 46 MB. `Run.sync` then applies the entries of the next operation to the
same `st` with `Std.HashSet.insert`: with an MT set each insert copies the bucket
array. The cut runs on one thread. If a state is cut in tasks, give the tasks a
copy (`toArray`) and keep `st` out of their closures.

## A loop rewritten for a proof keeps its speed only if measured

On 2026-10-12 `Qlvr.mergeJoin` (nested `for` loops that read the join
columns inline) was rewritten as tail calls with fuel (`mergeGo`,
`runEnd`, `pairsRow`, `pairsBlock`) so that its row pairs could be proved
(`Qlvr/MergeTheorems.lean`). The new functions take the join columns and
the column test as closures. q07 on the olympics SBM11 generation (warm,
20 runs per process, 8 processes) went from a minimum of 50 to 53 ms to 56
to 67 ms. `@[specialize]` on the four functions made Lean compile a copy for
the closures at the call site: 47 to 52 ms. Rule: when a hot loop becomes
higher-order for a proof, mark it `@[specialize]` and measure the query that
runs it before and after
(`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md` section 5).

## A whole file as a `List UInt8` costs 60 to 85 bytes for each byte (paid for 2026-10-14)

The delta log of an SBM11 generation was encoded and decoded as a `List UInt8`
(`Storage/DeltaLog.lean`). A list cell is 24 bytes, and the batch encoder
appended lists at three levels, so a request that wrote 36 MB of log needed 2.3
GB and 12.6 s (https://github.com/danbri/factoidal/issues/857), and every open
of a generation with a log held the whole log as a list (84 bytes for each byte
of log, https://github.com/danbri/factoidal/issues/851). Measured by
`tests/stack/lean_scaling.py` (peak RSS from `/usr/bin/time`, slope from x to
4x): 62.5 and 84.3 bytes for each byte of log before; 4.0 and 6.4 to 7.1 after.
Olympics update: 2,310,880 kB and 15.9 s before; 157,904 kB and 3.0 s after.

The repair keeps the list functions as the specification and adds functions that
work by position in a `ByteArray`
(`Storage/DeltaLogBytes.lean`, `DeltaLogBytesTheorems.lean`):

1. Write `f b pos stop` for each list function `f`: it reads bytes `pos .. stop`
   of `b`, returns the position after what it read, and is a tail call with a
   fuel `Nat` first for every loop over the bytes. Check the generated C
   (`formal/lean4/.lake/build/ir/L4Factoidal/Storage/DeltaLogBytes.c`): `goto
   _start` and no self call in each loop. A payload that has a bounded size (one entry of
   about 100 bytes) may go through the list parser: `listOfRange b s e` makes the
   list of those bytes only.
2. Define the window `win b pos stop := (b.data.toList.drop pos).take (stop -
   pos)` and prove `f b pos stop` equal to `f (win b pos stop)` for each function
   in the order of the calls (`win_nil`, `win_cons`, `win_drop`, `win_take`, then
   `readU32LE_win`, `listOfRange_eq`, the entry, the body, the batch, the log).
   Unfold both sides, rewrite with the lemma of each callee, split the guards
   with `by_cases`, and finish with `omega` on the positions.
3. Install the equality with `@[csimp]` for the list-typed API (`appendPlan?`,
   `parseLogChecked`). A `csimp` lemma applies only in a module that imports the
   module that states it, so a tool that must run the fast code imports it
   (every `Harness` tool does) or calls the byte array function directly.
4. `#guard` the two implementations against each other at every cut and at every
   changed byte of a real log (the 8-byte header, a frame, a version 2 log).
5. Run the scaling rows on the unrepaired code first. They must fail there.

The old reader's `List UInt8` of the whole file is the part to remove. A `List`
of the entries is small (one cell per entry) and stays.

## A predicate that builds the list of the characters of a string (paid for 2026-10-15)

`RDF.isIri s` was `!s.isEmpty && s.toList.contains ':'`. `String.toList` makes
one list cell for every character before the search starts. The key decoder,
the inline-id decoder and the parsers call it for every IRI they build: 19
percent of phase 1 of the SBM11 packer
(https://github.com/danbri/factoidal/issues/792 item 5) and 9.2 percent of the
samples of a DBpedia aggregate query
(https://github.com/danbri/factoidal/issues/825). A call on a 50-character IRI
took 653 to 706 ns.

The repair is the `csimp` pattern of the sections above for a function with no
recursion (`L4Factoidal/RDF/Core.lean`):

1. Keep the definition. `isIri` stays what the types and the theorems unfold
   (`Iri` carries a proof about it).
2. Add `isIriFast s = !s.isEmpty && s.contains ':'`. `String.contains` walks
   the UTF-8 bytes and stops at the first colon; it allocates nothing (29 to 31
   ns per call).
3. Prove `isIri s = isIriFast s` (`simp [isIri, isIriFast, String.contains]`)
   and install `@[csimp] theorem isIri_eq_isIriFast : @isIri = @isIriFast :=
   funext isIri_eq_isIriFast_apply`.
4. Look at a profile or the emitted C: the frames must name `isIriFast`
   (`RDF_isIriFast` in the packer's profile), and a call inside a `mutual`
   block is not replaced.

After the repair `isIri` was on the stack of 0.85 percent of the packer's
samples. `l4factoidal parse` of an 83 MB N-Triples file did not change within
the spread (5.3 s of user time before and after); that path was not profiled.

## A function that returns a function runs its `let` again for each call (paid for 2026-10-15)

```lean
def f (n : Nat) : Nat → Nat :=
  let y := expensive n        -- reads as: once, when `f n` is applied
  fun x => x + y
```

The compiler gives a definition the arity of all its arrows. `f` takes `n` and `x`, `f n`
is a partial application, and each call of it runs the body, the `let` included. The
emitted C is `l_f(lean_object* n, lean_object* x)` and its body calls `l_expensive(n)`.
The first version of the prefix index of the Turtle writer
(https://github.com/danbri/factoidal/issues/864) had this shape:
`def tsAbbreviator (table) : String → String := ... let ix := PrefixIndex.ofTable table;
fun iri => ...`. It built the index for each IRI of the document: 16 s for a table of
1,000 rows and 1,000 triples, 63 s for 2,000 (quadratic), where the scan that the index
replaces took 40 ms. Three build-time `#guard`s of the module took 125 s for the same
reason.

Rule: state that a function shares is DATA, and the function that uses it has its own
name.

```lean
inductive Abbreviator where
  | scan (table : PrefixTable)
  | indexed (ix : PrefixIndex)

def Abbreviator.ofTable (table : PrefixTable) : Abbreviator := ...   -- builds the index once
def Abbreviator.run : Abbreviator → String → String
```

A caller writes `let ab := Abbreviator.ofTable table` and passes `ab.run`. `ab` is a
value, so `ab.run` is a partial application that has the index already. A `structure` with
the state in a field does the same. A closure returned from a definition is not
memoisation.

Second cost, 2026-10-20 (https://github.com/danbri/factoidal/issues/881): the indexed
FILTER NOT EXISTS was first written as a condition `fun active => let ix :=
ExistsIndex.ofGraph active; fun row => ...` for the `Graph → Binding → Bool` field of
`GraphPattern.filter`. A `@[noinline]` identity around the inner lambda did not help: the
emitted C was still one function of seven arguments that called `ExistsIndex.ofGraph` for
each row. 10,000 subjects took 424 s, against 7.2 s with no index at all. When the type of
the consumer is a function of the row, give the shared state a level whose argument is
the whole input: here `.modified (fun active rows => let ix := ...; rows.filter ...)`, a
function of the row SEQUENCE, so the `let` runs once for each sequence. Read the arity of
the emitted function in `.lake/build/ir/<Module>.c` before you time.

How it was found: a timed `#eval` of the pieces in a scratch file (`lake env lean
scratch.lean`, `IO.monoMsNow` around the call), at 1,000 and 2,000 rows. Four times the
time for twice the rows, in a function with one pass over its input, means work done for
each call.

## A table in a state that a caller may keep: a hash map is copied whole, a tree along one path (paid for 2026-10-15)

`Std.HashMap.insert` updates the table in place when nothing else refers to it, and copies
the whole bucket array when something does. A reader's state is threaded from statement to
statement, so the table in it is usually unique. It is shared whenever a caller keeps the
state from before an update: the lenient reader keeps the state before a statement to
recover from an error in it. One shared update then costs the size of the table, and a
document of n directives costs n squared. `Std.TreeMap.insert` copies one path
(a logarithm of the size) when the tree is shared, and updates in place when it is not.

Measured (`leanc -O2`; `Share.lean` of 40 lines, one `structure` with the map and a counter,
`{ s with m := s.m.insert k v }` in a loop; unique = nothing else holds the map; shared = the
map from before the update is stored in a variable that is read after the update), n distinct
keys `p0` to `p{n-1}`, milliseconds:

| n | unique HashMap | unique TreeMap | shared HashMap | shared TreeMap |
|---:|---:|---:|---:|---:|
| 10,000 | 2 | 14 | 772 | 11 |
| 20,000 | 3 | 16 | 3,443 | 25 |
| 40,000 | 11 | 41 | 14,870 | 54 |

A shared hash map is 4.5 and 4.3 times slower for twice the keys. A unique tree is about 4
times slower than a unique hash map: 1 microsecond against 0.3 for the insert of a prefix
label, small against the 18 microseconds that one statement of Turtle costs (0.29 s for 16,000
prefix lines and 16,000 triples). The lenient reader keeps the state across the call that
reads a statement (`readGraphBodyRecover`, `TurtleLenient.lean`: the `.error` arm continues
with the old state), so a hash map in `TurtleState` would be shared at each `@prefix`. The state of the
Turtle reader (`TurtleState.prefixIndex`,
https://github.com/danbri/factoidal/issues/865) is a `Std.TreeMap` for this reason. The
hash-map version of the reader state was not built; the choice rests on this measurement and
on the code of the lenient reader. A table that is built once and then only read
(`PrefixIndex`, `Abbreviator`) is a hash map.

Four ways the measurement reported nothing, each a version that was run:

- `time "f" f 20000` with the size in the source: the call is a closed term, the compiler
  evaluates it at initialisation, and the timer reads 0 ms. The size must come from `argv`.
- `let r := f n; IO.println s!"{r} {(← IO.monoMsNow) - t0}"`: the `←` is lifted before the
  statement, so the clock is read before `r` is forced. Read the clock in a term that depends
  on `r`: `let t1 ← (if r == 12345678901 then pure 0 else IO.monoMsNow)`.
- `acc := acc + old.m.size` after the update: a pure read can be moved before the update,
  so the map was not alive at the insert and the shared map was as fast as the unique one.
  Store the old map (`prev := some old`) and read `prev` after the loop.
- A structure named `ST` is the core monad `ST`: "type expected".

Also in `Harness/Sbm11Export.lean`: `prefixes := o.prefixes ++ [x]` for each `--prefix`
argument was quadratic in the number of arguments (16,000 arguments: 1 s of the 3.4 s).
`prefixesRev := x :: o.prefixesRev` and one `reverse`.

## The key of a triple in a hash map reaches every function of a term (https://github.com/danbri/factoidal/issues/867, 2026-10-15)

`FastGraph` keys a triple by `(subject, predicate, Term.joinKey object)` in a `Std.HashMap`, and every parse of a
dataset (`addQuadFast`, the N-Quads reader, TriG) inserts each triple. The key reaches the hash of a `Term`, its
`joinKey`, and, in the streamed reader, `Term.lowerTags`. Each of them took a native frame for each level of a
triple term: a term nested 10,153 deep overflowed a 512 KB stack in the hash. Every function that handles a key must be
a loop: the hash map accepts a key of any depth. A derived `Hashable` instance is replaced by an
instance of higher priority, not by a `@[csimp]` theorem (`skills/lean4-proof-patterns/SKILL.md`, 9d). The time
of the same term: `Term.toNTriples` copied the text of the levels below at each level, 0.28 s, 1.23 s and 8.58 s
for 25,000, 50,000 and 100,000 levels (a factor 4.4 and 7.0 for each doubling), 0.048 s, 0.091 s and 0.208 s as a
loop (`ntriples-nest-time` in `tests/stack/lean_scaling.py`).

## Verification and measurement

After a semantic hot-path change, run the closest Lean guards and targeted
executable path, then the persistent block smoke when ingestion or block bytes
are affected:

```text
cd formal/lean4 && lake build L4Factoidal.Syntax.TurtleTests l4block-shard-pack
cd ../.. && tools/blockengine-shard-merkle-scan-smoke.sh
```

Use a bounded real corpus in addition to fixtures. Record input identity,
triple count, elapsed time, output bytes, host and what is *not* measured in a
dated worknote. Stop or cap long experiments deliberately; do not leave
duplicate background packers competing for the same temporary output.

For the current KGX scale observations and the required future byte-streaming
ingest boundary, read [`docs/20260830-ibk2-ingest-scale.md`](../../docs/20260830-ibk2-ingest-scale.md).

### Two traps in a Lean-against-C timing (paid for 2026-10-12)

The record of 2026-10-12 reported the q07 kernel at 1.1 to 1.3 times C
natively and 2.9 to 3.4 times C in wasm32, and an agent was sent to find the
wasm32 cause. Both ratios were wrong, for the C side; the real figure was 3.5
to 4.9 times C on both targets
([record, section 7](../../docs/designissues/2026-10-12-lean-to-c-performance.md)).

- **glibc returns large buffers to the kernel.** A C program that `malloc`s
  and `free`s buffers above the mmap threshold (128 KiB at first) in its timed
  loop pays the page faults again on every run; the Lean runtime (mimalloc)
  keeps freed memory. The C kernel spent 3.1 of 4.5 ms in about 1,100 faults
  per run. Count the faults (`getrusage` `ru_minflt`) of both programs, and
  set `mallopt(M_MMAP_THRESHOLD, ...)` and `M_TRIM_THRESHOLD` in the C
  reference (as `tools/qlvr/bench/kernel.c` now does).
- **Under node, a loop in a function entered once runs as Liftoff code.**
  V8 uses TurboFan code from the next call only (no on-stack replacement
  for wasm), and wasm-opt inlines timed functions into `main` or the timing
  loop, also against `noinline`. Check with `node --liftoff-only` (if the
  time does not change, the default run was Liftoff code); compare with
  `node --no-liftoff`, as `tools/qlvr/bench/kernel-targets.py` now does.
