---
name: lean4-performance
description: Improve performance-sensitive Lean 4 code in Factoidal while preserving total semantics, observable order, and executable proof boundaries. Use for large parser, RDF/block ingestion, data-structure, recursion, or hot-path work; not for unmeasured micro-optimisation.
---

# Lean 4 performance in Factoidal

Start with a concrete phase and an observable baseline: text read, parse,
bucket/index build, block encode/decode, range I/O, query evaluation, or result
formatting. A green semantic test is not a throughput result, and a fast host
shim is not a semantic replacement.

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
- **A comparison that converts to lists.** `Canonical.strLe` built two
  character lists per call: 57 percent of the instructions of `canonicalize`
  after the sorts were repaired. Lean's native `String` order is the same order
  (`charsLe_eq_not_lt`); a `csimp` theorem makes the compiler use it. SPARQL's
  `strCompare` had the same shape (53.6 percent of an ORDER BY): the three-way
  form is `listCharCompare_eq_lt`, and `strCompare_eq_strCompareFast` reaches
  every ordering on the query path (ORDER BY, GROUP BY and DISTINCT-aggregate
  keys, MIN, MAX, `<` on IRIs and literals).

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
  chain (https://github.com/danbri/factoidal/issues/751, open). Look for a
  `.filter` whose predicate names the element of an enclosing `map` over
  all keys.
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
