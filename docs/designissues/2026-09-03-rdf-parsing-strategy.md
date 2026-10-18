# RDF parsing strategy in the Lean tree: layers, entry points, proofs, costs

Status: record of the design as it stands on 2026-09-03 (section 3a, the
lenient mode, added 2026-10-10; section 3c, RDF/XML, added 2026-10-13, with
section 3c.7, the scope of a property element, added 2026-10-14; section
3f, the source layer, added 2026-10-14; section 3h, the labels of JSON-LD
blank nodes, added 2026-10-14), written because the
owner asked for it to live somewhere findable (2026-09-03: "this and similar
ought to be recorded properly somewhere I can find it. Ephemeral coding logs
aren't that place"). Update this file when a layer, an entry point or a
proof changes; the worknote index and the `factoidal-lean-basics` skill link
here.

## 1. The shape: one meaning, several executions, proofs between them

Every concrete syntax has ONE reference parser that is the meaning, ported
from the F\* source production by production. Faster or streaming executions
are added beside it, never instead of it, and each one carries a theorem (or,
until the theorem lands, a differential test) that it computes the same
function as the reference on the inputs it accepts. The W3C syntax suites
gate the reference parser; byte-identity of packed artifacts and the
theorems gate the other executions.

## 2. Turtle

### 2.1 Reference parser: `L4Factoidal/Syntax/Turtle.lean`

- Entry points: `parseTurtle text base mode : Except ParseError Graph`
  and `parseTurtleFold step init text` (folds completed statements
  without building a second graph). Both turn the whole document into a
  `List Char` and run a fuel-bounded recursive descent that follows the
  W3C Turtle grammar (productions numbered in comments, `[16]
  NumericLiteral`, `[17] String`, `[26] UCHAR`, ...). RDF 1.1 and 1.2 modes
  (triple terms, reifiers, annotations, `VERSION`, base direction).
- Consumers: the W3C runner (`Harness/Manifest.lean`), and every probe and
  pack tool other than the shard packer. Since 2026-10-10 the command line
  (except `parse FILE`, which reads a file in chunks since 2026-10-13,
  section 3b) and the WASM `parse`, `datasetOpen` and `queryDataset` Turtle path
  (`Wasm/Ops/Parse.lean`, `parseTextToDataset`) read Turtle with
  `parseTurtleText` (2.2), which calls `parseTurtle` for a document that
  contains `<<` and for every document the scanner walk refuses.
- Fuel: each bounded loop takes a fuel argument as the F\* source does. The
  statement-level fuel is `cs.length + 2` computed ONCE per document. The
  literal loops (`readShortStringBody`, `readLongStringBody`, `collectNum`)
  take the constant `literalFuel = 2^32` since 2026-09-02; the per-token
  forms are kept as `readTurtleStringSpec` / `readNumericLiteralSpec`.
  Computing `cs.length` per token was quadratic (20,019 lines: 6.16 s, now
  0.74 s).
- Gates: W3C RDF 1.1 Turtle (313) and TriG (356); RDF 1.2 Turtle syntax
  (67) and eval (29), TriG syntax (35) and eval (25); all 0 fail on
  2026-09-02.
- Collections ([15] `collection`, Turtle §2.8), since 2026-10-10
  (https://github.com/danbri/factoidal/issues/678). `readCollection` reads
  the first element and gives the rest to `readCollectionCells`. That function
  reads one element per tail call: `readObject` reads the element, then
  `freshBnode` allocates the element's cell, then the cell (blank node,
  element term, element triples) goes onto a list that holds the newest cell
  first. At the closing `)` the fold `linkCollectionCells` writes the
  `rdf:first`/`rdf:rest` triples, last cell first, so the result lists the
  cells in document order. Both functions compile to a `goto` loop in the
  emitted C, so the LENGTH of a collection uses no stack. The blank-node
  labels do not change: an element's own blank nodes are still allocated
  before its cell's node. The F* source's recursion (`parse_collection_rest`)
  stays as the readable `readCollectionRest`; 2.3 has the theorems.
  - Bound that stays: the NESTING of terms inside a collection (a collection
    or a `[ … ]` as an element) is still a recursion, three frames per level
    (`readObject`, `readCollection`, `readCollectionCells`). Measured
    2026-10-10, native, `LEAN_STACK_SIZE_KB=512`: `ex:s ex:p ( ( ( … ) ) )`
    ran at 2,897 levels and overflowed at 2,909 (before the change: 2,000 ran,
    2,500 overflowed). A triple term cannot hold a collection.
  - Every Turtle reader gets the loop, because all of them reach collections
    only through `readStatement`: `parseTurtle`, `parseTurtleText` and its
    walk, the chunk fold, TriG, and the lenient readers.
- Object lists ([8] `objectList`) and predicate-object lists ([7]
  `predicateObjectList`), since 2026-10-10
  (https://github.com/danbri/factoidal/issues/754). Before, `readObjectList`
  (F* `parse_object_list_rev`) appended each object's triples to its
  accumulator with `acc ++ ...`, so one object list of n objects took time in
  proportion to n²; and `readPredicateObjectList` (F*
  `parse_predicate_object_list_rev`, with `parse_trailing_semicolons_rev` as
  `readPredicateObjectListMore`) made one recursive call per `;` group, so
  one statement of n predicates took n stack frames. Now, in the same mutual
  block:
  - `readObjectListRev` pushes each object's triples (its side triples, the
    statement triple, its RDF 1.2 annotation triples) onto a list that holds
    every triple read so far newest first (`List.reverseAux`, time in
    proportion to that object's own triples), and reads the next object by a
    tail call. It returns the list still reversed.
  - `readPredicateObjectList` is one function for the whole list. Its
    argument `more` says where the input stands: `false` at a verb (the old
    `readPredicateObjectList`), `true` at a run of `;` (the old
    `readPredicateObjectListMore`, which at fuel 0 accepts and reads
    nothing; the flag keeps that behaviour for every fuel). It passes its
    `accRev` to `readObjectListRev`, so every triple of the statement goes
    onto ONE reversed list, and reads the next group by a tail call. Every
    exit reverses the list once. Callers use the defaults `accRev := []`,
    `more := false`, so `readStatement`, `readObject`, `readAnnotations`,
    `readSubjectTurtle` and TriG did not change.
  - Both compile to `goto _start` loops in the emitted C (`readObjectListRev`
    one, `readPredicateObjectList` four), with no self-call left. The F*
    forms stay as the readable `readObjectList`,
    `readPredicateObjectListSpec` and `readPredicateObjectListMoreSpec`; 2.3
    has the theorems.
  - Measured, native, `l4factoidal parse FILE --format turtle`: one object
    list of 25,000 objects 10.33 s before (2026-10-10); 100,000 objects no
    result in 120 s before. After (2026-10-12, `tests/stack/lean_scaling.sh`,
    minimum of 3 runs): 25,000 objects 0.058 s, 100,000 objects 0.403 s
    (ratio 6.9 for 4x input; the row's bound is 9.0). A longer ladder, same
    binary, minimum of 3 runs: 25,000 0.07 s, 50,000 0.15 s, 100,000
    0.45 s, 200,000 1.02 s, 400,000 2.06 s, so 2.0 to 3.0 times per
    doubling. One statement of 10,000 `;` groups: stack overflow before
    under `LEAN_STACK_SIZE_KB=512`, in Node under `--stack-size=512` and in
    Node with its default stack; after, it runs in all three (Node: 264 ms
    and 282 ms, with a wasm module rebuilt from this tree).
  - Bound that stays: NESTING. `[ ... ]` inside an object costs three frames
    per level (`readObject`, `readPredicateObjectList`, `readObjectListRev`):
    `ex:s ex:p [ ex:p [ ex:p ... 1 ] ] .` ran at 1,501 levels and overflowed
    at 1,507 under `LEAN_STACK_SIZE_KB=512`, before and after. Nested
    collections ran at 2,890 levels before and 2,695 after (overflow at 2,902
    and 2,707). The cause is the frame of `readObject`, 16 bytes larger
    (`sub $0x38,%rsp` before, `sub $0x48,%rsp` after): the call to
    `readPredicateObjectList` now has seven arguments, and on x86-64 the
    seventh goes on the stack.
  - All Turtle readers reach the two lists only through `readStatement` or
    (TriG) through `readPredicateObjectList` itself, so every reader gets
    the loops: `parseTurtle`, `parseTurtleText` and its walk, the chunk fold,
    TriG, and the lenient readers.

- Triple terms ([30] `tripleTerm`, [32] `ttObject`) and the table of prefixes, since 2026-10-15
  (https://github.com/danbri/factoidal/issues/865). Before, `readTripleTerm` and `readTtObject`
  called each other, two native frames for each nesting level (a triple term nested 2,536 deep
  ran under `LEAN_STACK_SIZE_KB=512` and 2,537 overflowed; Node overflowed too), and
  `TurtleState.lookupPrefix` scanned the list of the bindings in force for each prefixed name (a
  document with 64,000 `@prefix` lines and 64,000 triples of three prefixed names took 78.8 s).
  Now:
  - `readTripleTermDown` reads the subject and the verb of a level, puts them on a list
    (`OpenTripleTerms`) and goes on to the object by a tail call. It takes two units of fuel for a
    level, as the two functions did, so the errors and the offsets for a given fuel are the
    same. At the first object that is not a triple term, `closeTripleTerms` takes the entries of the
    list one by one: each reads its `)>>` and is the object of the next one out. The object that is not
    a triple term is read by the specification (`readTtObject`), which does not recurse on it. Both
    functions compile to a `goto _start` loop in the emitted C. The two mutual functions stay as the
    readable forms; 2.3 has the theorems.
  - `TurtleState` has two more fields, `prefixIndex` (a `Std.TreeMap` from a label to its latest IRI)
    and `prefixIndex_ok` (the proof that the index answers as the list `prefixes` does). The list
    stays: `parseTurtleWithPrefixes` returns it, newest first, shadowed bindings included.
    `TurtleState.bindPrefix` is the only function that adds a binding, in Turtle, TriG and the TriG
    chunk walk. `lookupPrefix` stays as the specification; the compiler runs `lookupPrefixIndexed`.
    A tree and not a hash table: the lenient readers keep the state from before a statement, a
    shared hash table is copied whole by `insert`, and a shared tree is copied along one path
    (`skills/lean4-performance/SKILL.md`, "A table in a state that a caller may keep").
  - `Term.toCanonicalNTriples` (the text of a term in the N-Quads of the parse operations) is a loop
    with a counter of the open triple terms (`Syntax/NTriples.lean`); the wasm row needs it, because
    the answer of `parseToDatasetJson` holds the term as text (16.2 MB for 300,000 levels).
  - Measured, native, `LEAN_STACK_SIZE_KB=512`: a triple term nested 300,000 deep is read, counted
    and written as canonical N-Quads by `l4wasm-cli call parseToDatasetJson` in 1.3 s (0.74 s at the
    default stack), and by the wasm module in Node in 1.6 s under `--stack-size=512` and 1.9 s at the
    default stack. 64,000 prefixes and 64,000 triples: 1.11 s of CPU time.

### 2.2 Streaming execution for the shard packer

Modules, in data order:

1. `Utf8Stream.lean`: bounded incremental UTF-8 decoding of 64 KiB byte
   chunks; keeps at most the final three undecoded bytes; rejects invalid
   interior data; never chooses a statement boundary.
2. `TurtleStatementScan.lean`: a per-character mode machine (`normal`,
   `iri`, `comment`, short string, long string, opening-quote run) that
   proposes candidate statement texts. A candidate ends at a `.` in normal
   mode followed by whitespace or `#`, or at a line end when the current
   text starts with `PREFIX`, `BASE` or `VERSION` (the SPARQL-style
   directives have no dot). It keeps `head`, the first seven characters
   after leading whitespace, so the directive test is O(1) per line end.
   The scanner never decides syntax; the grammar accepts or rejects every
   candidate.

   Two questions the owner asked on 2026-09-03, with the tests that answer
   them:

   - *Comments.* If a comment precedes a `PREFIX`/`BASE` line inside the
     same candidate, the seven-character head reads `# ...` and the scanner
     does not cut at that line end; the directive stays in the candidate
     until the next dot in normal mode or the end of input (a dot inside a
     comment, an IRI or a string is not a boundary: `pendingDot` is set only
     when the mode after the character is `normal`, and a comment keeps its
     mode until the line end; four comment-dot guards cover it). This is
     safe because a
     candidate may hold several statements and `TurtleChunkFold.consumeText`
     runs the grammar in a loop over it: the head test decides where
     boundaries fall, never what the text means, and the old
     reverse-the-candidate form had the same property (the theorem says
     the two are equal). Fifteen sources (comment before and between
     directives, a comment whose text is `PREFIX ...`, directives inside
     long and short strings and inside an IRI fragment, a trailing
     directive with no newline, CR line ends, `VERSION`, a local name
     `ex:PREFIXED` at a line start) agree with `parseTurtle` at every
     two-way chunk split plus one-character chunks: 1,115 chunkings, 0
     disagreements. They are `#guard`s in `TurtleChunkFoldTests.lean`.
   - *"Keep a flag for whether an E was seen instead."* The keywords are
     matched case-insensitively (Turtle allows `prefix` and `base`), so the
     flag would be "contains e or E". Measured on real files: UK Parliament
     99.7% of statements contain one (26% a capital E); W3C rdf11 Turtle
     test files 89.8%; the Wikidata extracts 44.7% (gene.ttl) and 0.2%
     (disease.ttl, whose statements are all `wd:`/`wdt:` prefixed names).
     So the flag would skip the test on some corpora and almost never on
     others, and on a hit it would still need the reversal. The
     seven-character head is O(1) per character with no skip and is what
     landed. A chat message on 2026-09-03 said "contains an E is true of
     most statements"; the measurement above corrects it.
3. `TurtleChunkFold.lean`: hands each candidate to `readStatement` from
   the reference grammar with the fuel `text.length + 2` computed once per
   candidate, carrying `TurtleState` (prefixes, base, blank-node prefix,
   mode) across candidates and chunks; retains only the unfinished
   candidate.
4. `Harness/PredicateShardPack.lean`: a first pass over the file computes
   the SHA-256 and the blank-node prefix; the second pass feeds chunks to
   the fold and publishes the completed triples as `IBK3` blocks every 64
   chunks (about 4 MiB), so a predicate whose rows span several windows
   gets several blocks (the 309 blocks over 232 predicates of the UK
   Parliament dump).

5. `TurtleChunkFold.parseTurtleText` (2026-10-10,
   https://github.com/danbri/factoidal/issues/729): the same walk over a
   `String` already in memory, one character at a time through
   `String.foldl`, for the command line and the WASM parse ops. `parseTurtle`
   starts with `text.toList`, and that list was the whole peak memory of
   `l4factoidal query` (35 bytes of peak resident set per input byte; 256 MB
   for 6.76 MB of `gene.ttl`). A document that contains `<<` goes to
   `parseTurtle` (the scanner reads `<` as an IRIREF up to the first `>`, so
   inside a triple term its mode can differ from the grammar's), and so does
   every document the walk refuses, so every error is the reference parser's
   (`parseTurtleText_error`). Record:
   `2026-10-10-lean-vs-fstar-performance.md` section 10.

6. `StrictFeed.turtleFeed` (2026-10-13,
   https://github.com/danbri/factoidal/issues/813): the same walk over the
   decoded 64 KiB chunks of a file, for the command line's strict
   `parse FILE`; the walk's accumulator is written and emptied after each
   chunk (`drainRun_eq`). Section 3b.

### 2.3 Proofs

- `TurtleFuelTheorems.lean` (2026-09-02): the three literal loops are the
  same function for every fuel above the remaining length
  (`*_fuel_indep`), so the constant-fuel readers equal the specification
  forms for every input shorter than 2^32 characters
  (`readTurtleString_eq_spec`, `readNumericLiteral_eq_spec`).
- `TurtleStatementScanTheorems.lean` (2026-09-03): `head_eq_spec`, the
  scanner's head field equals `directiveHeadSpec currentRev` (the old
  reverse-and-drop-whitespace form) after any run from `init`.
- `TurtleTheorems.lean`, `SyntaxTheorems.lean`: earlier properties of the
  reference parser (see the files).
- `TurtleTheorems.lean` (2026-09-05): `parseStatements_eq_fold` and
  `parseTurtle_eq_fold` — folding statements with `Syntax.prependReverse`
  and reversing once gives exactly the `Graph` `parseTurtle` returns.
  `Source.turtleStep_collect` (until 2026-10-14
  `PackStream.ingestStep_eq_prependReverse`) ties the shard packer's step to
  that accumulator. This is the ACCUMULATOR half of the streaming
  agreement, the counterpart of instantiating
  `NQuadsFold.streamConsume11_eq_batch` at the accumulator the batch parser
  uses.
- `TurtleChunkFold.lean` (2026-10-10): `freshBnodePrefixText_eq`,
  `parseTurtleText_error` and `parseTurtleText_eq_of_walk` (section 2.2,
  item 5).
- `Turtle.lean` (2026-10-10, collections, 2.1): `readCollectionCells_eq`,
  the loop equals `readCollectionRest` with the cells read before it linked
  in front, for every fuel, errors and positions included;
  `readCollection_eq`, `readCollection` in the F* source's form
  (`parse_collection` with the recursive tail); and the `@[csimp]` theorem
  `readCollectionRest_eq_TR`, so a call of the readable form also compiles to
  the loop. The `#guard`s in `TurtleTests.lean` pin exact blank-node labels
  and triple order for nested collections; those in `TurtleChunkFoldTests.lean`
  run a 500-element collection through the scanner walk, `parseTurtleText`
  and a 97-character chunking.
- `Turtle.lean` (2026-10-10, object and predicate-object lists, 2.1):
  `readObjectList_acc` (starting the readable object list with `acc` puts
  `acc` in front of its result); `readObjectListRev_eq`, the loop returns,
  newest first, its `accRev` behind what `readObjectList` reads;
  `readPredicateObjectList_eq`, the loop started at a verb reads what
  `readPredicateObjectListSpec` reads and started at a `;` run what
  `readPredicateObjectListMoreSpec` reads, with the triples of `accRev` in
  front; and `readPredicateObjectList_eq_spec` at the defaults. All hold for
  every fuel, errors and positions included, and the state is the same, so
  the blank-node labels are the same. Three `@[csimp]` theorems
  (`readObjectList_eq_TR`, `readPredicateObjectListSpec_eq_TR`,
  `readPredicateObjectListMoreSpec_eq_TR`) make a call of a readable form
  compile to the loop. The guards in `TurtleTests.lean` pin labels, order,
  error messages and error offsets taken from the binary built before the
  change (Turtle, RDF 1.2 annotations, TriG); those in
  `TurtleChunkFoldTests.lean` run 500 objects and 500 groups through the
  scanner walk, `parseTurtleText` and a 97-character chunking. The axiom
  audit block of `TurtleTheorems.lean` prints the axioms of these theorems
  and of the collection theorems above: `propext`, `Classical.choice` and
  `Quot.sound` only (2026-10-12).
- `Turtle.lean` (2026-10-15, triple terms and prefixes, 2.1; issue 865):
  `readTripleTermDown_eq`, the loop started with any list of open triple terms reads what
  `readTripleTerm` reads and then closes the list (`closeTripleTerms`), for every fuel, errors and
  positions included, by induction on the fuel of the specification; with `closeTripleTerms_error`,
  `closeTripleTerms_nil`, `closeTripleTerms_cons` (the innermost open term closes first) and
  `readTripleTerm_succ` (one level of the specification with its closing step as
  `closeTripleTerms`). The `@[csimp]` theorems `readTripleTerm_eq_loop` and
  `readTtObject_eq_loop` make every caller compiled after them run the loop. For the prefixes:
  `TurtleState.lookupPrefixIndexed_eq`, `TurtleState.lookupPrefix_eq_indexed` (`@[csimp]`; the proof
  `prefixIndex_ok` is a field of every state) and `TurtleState.lookupPrefix_bindPrefix` (a binding
  answers for its label and leaves the others as they were). `NTriples.lean`:
  `Term.toCanonicalNTriplesLoop_eq`, `Term.toCanonicalNTriplesFast_eq` and the `@[csimp]` theorem
  `Term.toCanonicalNTriples_eq_fast`. `Sink.lean`: `bodyPushBy_ofTable` and
  `trigSwitchBy_ofTable` (the writer's text and state, from an `Abbreviator` built once, are the
  specification's, from the table). All depend on `propext`, `Classical.choice` and `Quot.sound`
  only (`#print axioms` in the modules). The guards in `TurtleTests.lean` pin a triple term nested
  1,000 deep, every kind of term in a nesting, ten error messages with their offsets (taken from
  the binary built before the change), 300 prefixes, the rebinding of a label and the history list.
  A guard that compares a specification with its `csimp` replacement compares the replacement with
  itself, so none does (`skills/lean4-proof-patterns/SKILL.md`, 9b).
- Still not proved: the CHUNK-BOUNDARY half — that the streaming execution
  (2.2) reaches the same accumulator whatever the chunking, and so equals
  `parseTurtle` on the same text. It rests on `TurtleStatementScan` never
  offering a candidate that `readStatement` would read past, which no
  theorem states. The gate today is byte identity of packed generations
  across scanner changes (378 artifacts on a 370,355-triple slice,
  2026-09-03; 261 identical, 0 differed out of 262 inputs including a
  104,179,872-byte Turtle source, 2026-09-05) and the five committed hub
  blocks under `docs/web/hub/assets/blocks/lifesci-crossgraph/`. For
  `parseTurtleText`, 2026-10-10: the guards of `TurtleChunkFoldTests.lean`
  and byte identity of the command line on the 1,130 `.ttl` and `.nt` files
  of the W3C RDF 1.1 and 1.2 suites (13,560 of 13,560 outputs; 13,572 of
  13,572 with 10,000 paragraphs of `gene.ttl` added). Until
  2026-10-10 `TurtleChunkFoldTests.lean`, `TurtleStatementScanTests.lean` and
  `Utf8StreamTests.lean` were imported by no module, so `lake build` did not
  run their guards; the umbrella imports them now. The
  N-Quads tree has the theorem this one still needs
  (`NQuadsStreaming.lean`, section 3).

### 2.4 Costs paid and costs open

| Date | Cost | Cause | Fix |
| --- | --- | --- | --- |
| 2026-04 | stack overflow on large Turtle | non-tail recursion | `docs/2026-04-21-large-turtle-stack-overflow-fix-sketch.md` |
| 2026-09-02 | quadratic `parseTurtle` | per-token `cs.length + 1` fuel in two literal readers | constant `literalFuel` + proofs |
| 2026-10-10 | a Turtle collection of 100,000 elements overflowed a 512 KB native stack and a browser tab's stack; the largest that ran at 512 KB had about 4,500 elements (4,531 overflowed) | `readCollectionRest` (F* `parse_collection_rest`) made one recursive call per element | `readCollectionCells`, a tail call per element, and `linkCollectionCells` at the `)`, proved equal (2.1, 2.3). 100,000 elements run at 512 KB. Outputs of `l4factoidal parse --out nquads`, strict and `--lenient`, on the 1,022 `.ttl` and `.trig` files of the W3C RDF 1.1 and 1.2 suites: 2,044 of 2,044 byte-identical to the binary before (https://github.com/danbri/factoidal/issues/678) |
| 2026-10-10 | one Turtle object list of 25,000 objects took 10.33 s, and 100,000 gave no result in 120 s; one statement of 10,000 predicates overflowed a 512 KB native stack, a Node `--stack-size=512` stack and Node's default stack | `readObjectList` (F* `parse_object_list_rev`) built its result with `acc ++ ...`; `readPredicateObjectList` (F* `parse_predicate_object_list_rev`) made one recursive call per `;` group | `readObjectListRev`, a reversed list and a tail call per object, and `readPredicateObjectList` as one loop over the groups, proved equal to the readable forms (2.1, 2.3). 25,000 objects 0.058 s, 100,000 objects 0.403 s; 10,000 groups run at 512 KB natively and in Node under `--stack-size=512`. `tests/stack/run.sh --canary`: 41 pass, 0 fail (out of 41) before, with three expected failures, and after, with none. Outputs of `l4factoidal parse --out nquads`, strict and `--lenient`, on the 1,022 `.ttl` and `.trig` files of the W3C RDF 1.1 and 1.2 suites: 2,044 of 2,044 byte-identical to the binary before; and the 239 RDF 1.2 files again in the 1.2 mode (`--format turtle12`, `trig12`), 478 of 478 byte-identical. With `turtle` and `trig` the CLI reads the RDF 1.2 files in the 1.1 mode, where 51 of the 239 parse and annotations are refused; in the 1.2 mode 193 parse (https://github.com/danbri/factoidal/issues/754) |
| 2026-10-15 | a triple term nested 300,000 deep could not be read (2,536 levels ran under a 512 KB native stack and 2,537 overflowed; Node overflowed too); the text of the term in the answer of a parse took 0.41 s for 20,000 levels and more than 120 s for 300,000; 64,000 `@prefix` lines and 64,000 triples of three prefixed names took 78.8 s of CPU time; `l4sbm11 export` with 16,000 `--prefix` arguments took 3.4 s | `readTripleTerm` and `readTtObject` called each other (two frames for each level); `Term.toCanonicalNTriples` copied the text of the levels below at each level; `lookupPrefix` scanned the list of the bindings; `Sink.bodyPush` scanned the table for each IRI; `parseOpts` appended each prefix to the end of a list | `readTripleTermDown` and `closeTripleTerms`, `Term.toCanonicalNTriplesLoop`, `TurtleState.prefixIndex` with the proof `prefixIndex_ok`, `Abbreviator` in the stream writer, `prefixesRev`; all proved equal to the specifications (2.1, 2.3, 3g). 300,000 levels: 1.3 s natively at 512 KB, 1.6 s in Node at `--stack-size=512`; 64,000 prefixes 1.11 s; 16,000 `--prefix` arguments 0.15 s. Byte identity with the binary before: `l4factoidal parse` in three modes on 2,637 runs of the W3C and `tests/sbm11/syntax` files, 12,000 random documents in four modes (`tools/turtle-reader-differential.py`), `l4sbm11 export` 14,463 runs on W3C files and 6,400 on random datasets with tables of up to 1,200 prefixes (https://github.com/danbri/factoidal/issues/865) |
| 2026-10-15 | a triple term nested 300,000 deep could not be read from N-Triples, N-Quads or TriG text (4,510 levels ran under a 512 KB native stack and 4,511 overflowed; the wasm module overflowed too), and its N-Triples text took 86.6 s (90.7 s in the answer of a CONSTRUCT query) | `readObject12` called itself once for each level; the hash that `deriving Hashable` made for `Term`, `Term.joinKey` and `Term.lowerTags` took a frame for each level; `Term.toNTriples` took a frame and copied the text of the levels below at each level | `readObject12Down` and `closeObject12`, `Term.hashFast` (the instance `instHashableTermLoop`), `Term.joinKeyLoop`, `Term.lowerTagsLoop`, `Term.toNTriplesLoop`; all proved equal to the specifications (3g). 300,000 levels: 1.3 to 1.6 s natively, 1.8 to 2.3 s in Node, the text 0.57 s. Byte identity with the binary before: 26,205 runs of `l4factoidal parse` and 12,170 of the wasm operations on the W3C files, 24,000 random documents (132,000 comparisons: `tools/ntriples-reader-differential.py`, `tools/turtle-reader-differential.py`), 9,248 exports and 1,299 round trips through the store (https://github.com/danbri/factoidal/issues/867) |
| 2026-10-13 | the strict `l4factoidal parse FILE --out nquads` peaked at 33 to 35 bytes per input byte (400,000 N-Triples: 1,186 MB; Serd 2 MB, Oxigraph 23 MB) | the whole file as one `String`, the N-Triples `List Char` of the document, the whole dataset and the whole N-Quads `String` before the first line was written | `StrictFeed.lean` (section 3b): 64 KiB chunks, each chunk's lines written and dropped; 24 to 26 MB at every size; the count keeps the set of distinct triples only. Byte identity: `tools/strict-parse-differential.sh` (3b.4); Turtle chunk equality proved (`drainRun_eq`) |
| 2026-09-02/03 | UK Parliament pack 6,134 s | scanner reversed the whole candidate at every line end; a 134 MB, 4,211-line statement group | seven-character `head` + proof; pack 254 s |
| open | 22.9 s user + 21.7 s system and 5.39 GB resident to parse 134 MB (measured 2026-09-03) | `List Char` representation: about 16 bytes and one allocation per character, built twice (scanner `currentRev`, then `text.toList` for the grammar) | a `String`/`ByteArray`-position lexer with its own equality proof against 2.1 |
| 2026-10-10 | `l4factoidal query` and `parse` peak at 35 bytes of resident memory per input byte (256 MB for 6.76 MB of `gene.ttl`; F*: 28 MB) | `parseTurtle`'s whole-document `text.toList` | `parseTurtleText`: the scanner walk over the `String` (2.2, item 5). Query peak 257.7 to 192.7 MB at 80,000 paragraphs, 37.0 to 26.0 bytes per input byte. Byte identity MEASURED, not proved |
| 2026-09-04 | named-graph IBK4 pack quadratic; 553 MB over 194 graphs killed by the operating system after 1 h 57 min | `NQuadsFast.addQuadFast` read the graph with `getElem?` and inserted it back, so `Std.HashMap.insert` copied the whole bucket map of that graph per quad | `Std.HashMap.modify`, which consumes the map; proofs restated through `getElem?_modify`. 104 MB over 50 graphs: 268.73 s to 103.12 s (`2026-09-04-ibk4-named-graph-packing-scale.md`) |
| 2026-09-04 | IBK4 pack held a whole-file `String.toList` | `quadArtifacts` took the source as one `String` | `PackStream.quadIngestFeed` streams the N-Quads grammar in 65,536-byte chunks; byte identity by `NQuadsFold.streamConsume11_eq_batch`. 104 MB over 50 graphs: peak memory 2,531,999,744 to 1,127,907,328 bytes |
| 2026-09-05 | the same whole-file `String.toList` for a TURTLE source into IBK4 | nothing called `TurtleChunkFold`; the quad route needs a `Dataset` and the fold hands back statements | `PackStream.QuadStream` carries the Turtle chunk fold beside the N-Quads stream, `quadStreamDataset` closes either. 104,179,872-byte Turtle source: peak resident set 2,788,786,176 to 1,253,408,768 bytes (26.8 to 12.0 bytes per source byte), generation byte-identical. Byte identity MEASURED, not proved — see 2.3 |
| open | peak IBK4 memory is still about ten times the source | one block per predicate over the whole source, so every row and every encoded block is live at the manifest | several blocks per predicate, which changes the emitted block set and needs a wire-version decision (`2026-09-04-ibk4-named-graph-packing-scale.md`) |
| open | multi-megabyte literals cost seconds each in the packer | every literal goes through the term codec, PTD1 pages, TLI1 keys and Merkle leaves | large-literal policy (corpus ladder, `docs/20260902-persisted-query-ladder.md`) |

## 3. The other syntaxes, briefly

| Syntax | Reference | Other executions | Agreement |
| --- | --- | --- | --- |
| N-Triples | `NTriples.lean` `parseNTriples` | `StrictFeed.lean` `LineFeed` with `tripleReader` (the command line's `parse FILE`, section 3b) | W3C suite; `NTriplesRoundTrip.lean`; `parseLinesAcc_eq_foldLines`; the chunk boundary by `tools/strict-parse-differential.sh` (3b.4) |
| N-Quads | `NQuads.lean` `parseNQuads` | `NQuadsFast.lean` `parseNQuadsFast` (bucketed accumulator; the WASM `datasetOpen` path); `NQuadsStreaming.lean` (chunk-boundary fold), `NQuadsFold.lean` (the generic consumer the IBK4 shard packer streams through); `StrictFeed.lean` `LineFeed` with `quadReader` (the command line's `parse FILE`, section 3b; `LineFeed.run_quad11_eq_batch`) | `parseNQuadsFast_eq_parseNQuads` proved 2026-09-02 (`NQuadsFastTheorems.lean`); the streaming module carries its own chunk-boundary theorem |
| TriG | `TriG.lean` `parseTriG` (shares the Turtle productions; the default graph is the unlabelled block) | `TriGChunkFold.lean` (the shard packers' chunk walk, section 3e; read by `l4sbm11-pack` since 2026-10-14, section 3f) | W3C suites; chunk cuts, brace balance and block labels PROVED in `TriGChunkFoldTheorems.lean`; agreement with `parseTriG` MEASURED (section 3e), open: https://github.com/danbri/factoidal/issues/836 |
| RDF/XML | `RdfXml.lean` `parseRdfXml` (the element tree, then the walk) | `parseRdfXmlStream` (the children of `rdf:RDF` walked as they are read; every caller runs it, section 3c) | W3C suite; `RdfXmlTheorems.lean` (blank-node label spaces disjoint by construction; the scope after a property element equals the scope before it, `propertyElt_scope`, section 3c.7); `parseRdfXml_eq_stream` (`@[csimp]`) |

### 3e. TriG chunk walk (https://github.com/danbri/factoidal/issues/769)

`parseTriG` starts with `text.toList`, and `l4block-shard-pack` read the whole
TriG file, so an IBK4 or IBK5 pack held about 24 bytes of character list per
source byte beside the dataset. `Syntax/TriGChunkFold.lean` gives TriG the
walk Turtle has. The scanner is `TurtleStatementScan`'s with the block depth
added: in normal lexical mode a `{` at depth 0 ends the block header and a `}`
at depth 1 ends the block's last statement. A local-name escape (`ex:a\'b`)
is skipped, because the Turtle scanner reads `\'` as the start of a string.
Each unit is read by the landed grammar functions: a top-level statement by
`readTriGStatement`, a header by `readLabelOrSubject` after the directives,
a statement in a block by `readStatement` with the two refusals of
`readGraphBody`. One `TurtleState` runs through all units in source order.

**RDF 1.2 annotation blocks (2026-10-14,
https://github.com/danbri/factoidal/issues/837 item 5).** An annotation block
`{| ... |}` after an object belongs to its statement (RDF 1.2 TriG, section 3).
The first scanner read its braces as graph block braces. The W3C test run
through the store (`tests/sbm11/w3c_roundtrip.sh`) found the fault: with the
old scanner `l4sbm11-pack` refused 21 RDF 1.2 TriG documents (15 of 26
evaluation tests and 6 of 24 syntax tests) that `parseTriG` reads. The
scanner now holds a `{` read at depth 0 back for one character (`heldOpen`).
`{|` is part of the statement. Any other `{` opens a graph block. Inside a graph
block a `{` is part of the statement. A `}` read right after a `|` closes an
annotation and not the graph block (`afterBar`; `|` occurs nowhere else in the
TriG grammar outside IRIREFs, strings and comments, where the scanner is not in
the normal mode). At the end of the input a held `{` opens a graph block
(`closeInput`). After the change all 50 documents pass, in the store and in
memory. `#guard`s cut nine annotation documents at every position and compare
the quad count with `parseTriG` in RDF 1.2 mode.

PROVED (`TriGChunkFoldTheorems.lean`; axioms `propext`, `Classical.choice`,
`Quot.sound` only): `feed_split` (two chunks in sequence give the result of
their concatenation, every state, every cut); `feed_inv` (the block flag is the
scanner's brace depth at every chunk boundary, nothing pending, and a held `{`
is outside a block: `WellHeld`); `finish_unterminated` (input ending in a block
is refused); `finish_held` (input ending right after a held `{` is refused);
`consumeBlock_graphs`, `applyEvent_stmt_graphs`, `applyEvent_close_graphs`
(inside a block every step call carries the block's label);
`applyEvent_stmt_label`. The change needed a new invariant (`WellHeld`) and the
proofs of the split and the block flag over a scanner step that can hold a
character: they go through `TriGScan.Splits`, a property of a scanner step that
composes (`Splits.comp`).

NOT PROVED: that the walk returns `parseTriG`'s quads. Open obligation and
two known differences of the pack bytes: https://github.com/danbri/factoidal/issues/836.

MEASURED 2026-10-14 (`tests/trig-pack/compare_w3c.sh`): 717 pack cases (every
`.trig` file of the W3C RDF 1.1 and 1.2 suites, ibk4 on the 1.1 files and ibk5
on both): 484 have the same generation hash on the whole-source route,
65,536-byte chunks and 7-byte chunks; 231 are refused by all three; 1 file
(2 cases) differs because the whole-source route publishes the default graph
first (expected failure, issue 836). Generated corpus
(`tests/trig-pack/gen_trig.py`, 60 graphs, one block each): 20,000,000 bytes
(786,419 quads): the same hash on the three routes for ibk4 and ibk5
(ibk4 `a1ff6602bf7a7801ac40de40512f190a54dfd25b0eb65bf4a4456ae6ae112926`,
ibk5 `423aff97de8041b5335d1812a50de171d9b3428ea040806d6d3fc7b81ad55027`,
sha256 of the sorted per-file sha256 list). 100,003,254 bytes (3,831,393
quads): the whole-source route has 4,688 files and the chunk route 4,922,
because publication rule 4 (`maxCarriedRows` = 1,048,576) runs only while
streaming; the chunk route's block files equal those of the N-Quads
streaming route on the same quads (`l4factoidal parse --out nquads`, packed
with `--batch-bytes 2000000000`): `45f061ccb16877fbca83302ef71a1b50e10f840ae5f7791f0c5ffa3739305d02`
(sha256 of the sorted file hashes, manifest excluded).

Peak RSS, 100,003,254 bytes, ibk4, `tests/trig-pack/peak_rss.py`: chunk route
391,692,288 bytes (3.92 bytes per source byte, 209 s); whole-source route
7,169,929,216 bytes (71.7 bytes per source byte, 422 s). Scaling row
`pack-trig-memory` in `tests/stack/lean_scaling.sh` (4 MB to 16 MB: 11.9 bytes
per byte on the chunk route, 70.7 whole-source; bound 20).

Shared lexical pieces: `Lexing.lean` (the N-Triples string body and escape
table the Turtle `decodeEscape` mirrors), `IriResolve.lean` (RFC 3986),
`IriScan.lean`, the `Locality*.lean` family (chunk-locality lemmas used by
the N-Quads streaming proofs).

### 3f. The source layer: one reader interface for every syntax (2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/837. Owner, 2026-10-14,
verbatim: "SMB11 should store rdf graphs regardless of source formats - this is
why we have reflected w3c rdf core concepts into Lean. I don't see any reason
for the format to be made so explicit for internal data manipulation- file
formats are for exchange and publishing".

**Before.** Each consumer of a document chose its own syntax modules.
`Storage/PackStream.lean` had a second enumeration of formats (`PackSyntax`,
four of the six syntaxes), three step functions (`ingestStep`, `quadPubStep`,
`trigPubStep`) and a stream type with one case for each of N-Quads, Turtle and
TriG (`QuadStream`). The SBM11 packer read N-Triples and N-Quads only. The
packers for IBK4 and IBK5 read an `.nt` file with the Turtle grammar. The wasm
parse op called each parser by name. `tests/sbm11/storage_layering.py` reported
31 uses of `L4Factoidal.Syntax` (import lines and names in code) under
`L4Factoidal/Storage/`, in `PackStream.lean` and `BrowserLogTests.lean`. It
reports 0 now.

**After.** `L4Factoidal/RDF/Source.lean` has two functions for a document:

| Function | Meaning | Used by |
| --- | --- | --- |
| `Source.parseDocument extra format mode base text` | the whole text becomes a `Dataset` | the wasm parse op (`Wasm/Ops/Parse.lean`), `l4source-convert`, the buffered pack route |
| `Source.Reader` / `Source.ByteReader` (`init`, `feed`, `finish`) | the text arrives in chunks; each quad goes to a consumer `Step α` when its statement is complete | the shard packers (IBK2 to IBK5), `l4sbm11-pack`, `l4sbm11 canon`, `l4sbm11-dict-pack`, the strict route of `l4factoidal parse FILE` |

`RdfFormat` (`RDF/Format.lean`) is the only table of formats. Each format has
one reader:

| Format | Reader | Memory |
| --- | --- | --- |
| N-Triples | `StrictFeed.LineFeed` with `tripleReader`; a graph name is an error (`expected '.' terminator`) | one chunk and one partial line |
| N-Quads | `StrictFeed.LineFeed` with `quadReader` | one chunk and one partial line |
| Turtle | `TurtleChunkFold` (section 2.2) | one chunk and one unfinished statement |
| TriG | `TriGChunkFold` (section 3e) | one chunk and one unfinished unit |
| RDF/XML | `Reader.whole`: keeps the chunks, parses their join at the end | the document (https://github.com/danbri/factoidal/issues/838) |
| JSON-LD | `Reader.whole` with the parser that `SourceJsonLd.lean` supplies | the document (https://github.com/danbri/factoidal/issues/839) |

JSON-LD stays out of the core wasm: `Source.Extra.jsonld` holds the parser, and
a tool that reads JSON-LD passes `Source.withJsonLd`.

**Two readers moved onto the layer (2026-10-14, item 7 of
https://github.com/danbri/factoidal/issues/837).** `l4sbm11-dict-pack` (packer
phases 1 and 2) read N-Triples and N-Quads with `NQuadsFold`; `l4factoidal parse
FILE` (the strict route, section 3b) chose the syntax modules itself, with a
`match` on the format label in `Wasm/Cli.lean`. Both now take an `RdfFormat` and
read through `Source.Reader` or `Source.ByteReader`. `l4sbm11-dict-pack` shares
`Sbm11Pack.readCfg`, `planRanges` and `streamRange` with `l4sbm11-pack`, takes
`--format` and `--base`, and has no default syntax. The strict `parse` keeps its
labels (`turtle` is still the default of that command) and reads RDF 1.1 for
N-Triples, N-Quads and Turtle as before. Output for a valid input did not change:

- the dictionary files `dict.gdv1` and `dict.gdx1` of the old and the new
  `l4sbm11-dict-pack` are byte-identical on the olympics source and on the
  generated sets, and the new `l4sbm11-dict-pack` writes the dictionary files of
  `l4sbm11-pack` for the 19 fixtures D1 to D4 in every syntax that writes them
  (`tests/sbm11/syntax_independence.sh`);
- `l4factoidal parse FILE --format F --out nquads` of the old and the new build
  give the same bytes and the same exit status for the fixtures D1, D2, D3 and D4
  in every syntax (D4 has triple terms and exits 1 in both, because the command
  reads RDF 1.1), and `tools/strict-parse-differential.sh` agrees on its 21,012
  cases with 0 differences;
- the new `parse` gives the same N-Quads for one dataset in every syntax
  (`syntax_independence.sh`, D1 and D2; D3 by RDFC-1.0 canonical N-Quads).

`tests/sbm11/storage_layering.py` counts only `L4Factoidal/Storage/` (and, since
2026-10-15, `RDF/QuadSource.lean`). The two
tools are in `Harness/` and `Wasm/`, where a format table is allowed but not
wanted: neither has one.

**The pack entry takes quads (2026-10-15).** The entry of phase 1 of `l4sbm11-pack`
was a file path and a byte range, read through `Source.ByteReader`. It is now a
producer of RDF quads (`L4Factoidal/RDF/QuadSource.lean`, `Sbm11Pack.packQuads`), and the
source layer is the file producer (`Sbm11Pack.fileRangeSource`). A `Dataset` in memory,
an array of quads and an HDT file are other producers. `--via-dataset` reads a whole
document with `Source.parseDocument` and packs the `Dataset`; its generation is
byte-identical to the one of the chunk reader for the 33 fixtures of
`tests/sbm11/quad_source.sh`. Record: section 11.4 of
`2026-10-11-shardborough-vs-qlever.md`; tracking
https://github.com/danbri/factoidal/issues/866.

**Blank node labels.** A blank node label is local to one document (RDF 1.1
Concepts, section 3.4). Turtle and TriG mint a label for each `[]`, collection
cell and property list: `anon`, then one more underscore than the longest run of
underscores in the document, then a counter. A reader that sees one chunk does
not know that run, so `Source.Prepass` reads the source once before the first
chunk and `Reader.init` takes the prefix. RDF/XML mints `b<N>`. JSON-LD mints
`_jld_anon`, then the fewest underscores for which no label of the document
begins with the prefix, then a counter (section 3h). A test with explicit labels
that equal the labels a reader would mint (`tests/sbm11/syntax/bnode_collide.*`)
expects five distinct blank nodes. All four syntaxes read five. Until
2026-10-14 JSON-LD read three
(https://github.com/danbri/factoidal/issues/840).

**Theorems** (`RDF/SourceTheorems.lean`; axioms `propext`, `Classical.choice`,
`Quot.sound` only):

- `whole_readAll`, `rdfxml_readAll`, `jsonld_readAll`: a whole reader gives
  `parseDocument` of the joined chunks, for every list of chunks.
- `nquads11_readAll_eq_batch`, `nquads11_readAll_eq_parseNQuadsFast`: in RDF 1.1
  mode a chunked N-Quads read that succeeds gives the line walk of the joined
  text (`NQuadsFold.streamConsume11_eq_batch`, through
  `StrictFeed.LineFeed.run_quad11_eq_batch`) and the dataset of
  `parseNQuadsFast`.
- `turtleStep_collect`: the Turtle consumer with the consumer that collects
  triples is `prependReverse`, the accumulator step of `parseTurtle`
  (`parseTurtle_eq_fold`). This replaces `PackStream.ingestStep_eq_prependReverse`.
- `prepass_chunks`: the pre-pass over any cut of the text gives
  `freshBnodePrefix` of the whole text.

Not proved, each with an open issue and an expected-failure test: the Turtle
chunk walk, the N-Triples chunk boundary, N-Quads in RDF 1.2 mode and the UTF-8
chunk decoding (https://github.com/danbri/factoidal/issues/826, rows SF-1 to
SF-4 of `tests/known-defects/run.sh`); the TriG chunk walk
(https://github.com/danbri/factoidal/issues/836, `tests/trig-pack/order_xfail.sh`).
`Source.lean` has `#guard`s that cut a document at every position for N-Triples,
N-Quads (RDF 1.1 and 1.2), Turtle, TriG and RDF/XML.

**Measured against the old packers.** `tools/pack-differential.sh` packed every
`.ttl`, `.nt`, `.nq` and `.trig` file of the W3C RDF 1.1 and 1.2 suites with the
`l4block-shard-pack` of commit 1986fdf4 and with the new one, in `ibk3` (Turtle
and N-Triples files), `ibk4` and `ibk5`, on the chunk route and the
whole-source route (`L4_PACK_BUFFERED=1`): 8,662 cases. 8,586 agree: 6,367 are packed by both with the same generation hash, and 2,219 are refused by both. 76 differ, all by design.

- In 72 cases (21 files) the old packer accepted the file and the new packer refuses it. Each file is a W3C `rdft:TestNTriplesNegativeSyntax` test (14 files of RDF 1.1 and 7 of RDF 1.2). The old packer read an `.nt` file with the Turtle grammar. The new packer reads it as N-Triples.
- In 4 cases (2 files, `ibk5` only) the old packer refused the file and the new packer accepts it. The files are the RDF 1.2 `rdft:TestNTriplesPositiveC14N` tests `extra_whitespace-03` and `extra_whitespace-04`, which have white space between a literal and its language tag or datatype. The Turtle reader of the old packer answered `expected '.' after triple`.
- No case has a different hash.

The run was repeated after the repair below. It gave the same 76 lines. The old and the new `l4sbm11-pack` give the same generation, file for file, for the generated datasets `multi.nt` and `multi.nq` of 88,000 quads (`tests/sbm11/syntax/gen_multi.py`).

**A cost found on the way: `readTriple12`.** `readTriple12`, the RDF 1.2
statement reader of N-Triples, gave `readObject12` a fuel of `r5.length + 1`
(the number of characters left in the input) for each statement. The N-Quads
reader replaced that count with `lineFuel` on 2026-09-05 (the "RDF 1.2 object
fuel" note in `Syntax/NQuads.lean`, now in `Syntax/NTriples.lean`). The
N-Triples reader kept the old count. A pack of N-Triples text through the
source layer took 2,996 ms of phase 1 for 8.3 MB. The same quads as N-Quads text
took 477 ms (`l4sbm11-pack`, 4 workers, 88,000 quads, 2026-10-14). After the
repair the N-Triples text takes 272 ms. The batch parser `parseNTriples` in RDF
1.2 mode walked the rest of the whole document for each statement, so its time
was quadratic in the document. After the repair `l4source-convert --from
ntriples` reads 8.3 MB of N-Triples text in 1.7 s. A statement
never spans a raw line break (`skipWs` skips space and tab only, and a literal
escapes its line breaks), so the characters up to the next line break bound the
nesting depth of a triple term. No document that parsed before is refused now.
The scaling row `sbm11-pack-nt-vs-nq` (N-Triples text takes at most 2.0 times the
CPU time of N-Quads text) is the gate.

**Costs open.** RDF/XML and JSON-LD hold the document (issues 838 and 839, rows
`sbm11-pack-rdfxml-memory` and `sbm11-pack-jsonld-memory`). The JSON-LD reader
uses native stack in proportion to the number of elements: documents of 25,000
to 100,000 elements overflow a stack of 512 KB, and parse under the 1 GB stack
of a native process (https://github.com/danbri/factoidal/issues/844, row
`JLD-STACK` of `tests/known-defects/run.sh`). The other syntaxes pack under a
512 KB stack: the canary of `tests/stack/run.sh` packs 600,001 N-Triples
statements (57.8 MB; `sbm11-perm`: 103 pass, 0 fail out of 103 on 2026-10-14),
and generated sources of Turtle (40 MB), TriG (40 MB) and RDF/XML (11 MB) pack
in an ad hoc run with `LEAN_STACK_SIZE_KB=512`. Turtle and TriG
phase 1 runs in one worker, whatever `--workers` says (https://github.com/danbri/factoidal/issues/842, rows
`sbm11-pack-ttl-workers` and `sbm11-pack-trig-workers`). The Lean RDF/XML and
JSON-LD writers take time quadratic in the dataset: `l4source-convert` writes
8.3 MB of N-Triples text in 22 s (RDF/XML) and 44 s (JSON-LD), and 4 times the data takes 15 and
24 times as long (https://github.com/danbri/factoidal/issues/845 and
https://github.com/danbri/factoidal/issues/712, rows `rdfxml-write` and
`jsonld-write` of `tests/stack/lean_scaling.sh`). The cost of each syntax in a pack is in
`skills/shardborough-storage/SKILL.md`, section "The source layer".

### 3g. The serialiser layer: one writer interface for every syntax (2026-10-14)

Tracking: https://github.com/danbri/factoidal/issues/837 item 6. The source layer
(section 3f) turns a document into quads. `L4Factoidal/RDF/Sink.lean` is the
other half: it turns quads into a document. A store gives its quads to a writer
and does not know the syntax in which they are written. A tool at the edge names
the format (`RdfFormat`) once. The rule of the source layer holds here: no file
under `L4Factoidal/Storage/` imports an `L4Factoidal.Syntax` module.

`Sink` has two functions for a document, as `Source` has:

| Function | Meaning | Used by |
| --- | --- | --- |
| `Sink.serializeDataset extra format version dataset` | the whole `Dataset` becomes the text, by the library serialisers (`Dataset.toNQuads`, `Graph.toNTriples`, `turtleOfGraphAuto`, `StoreEndpoint.datasetToTrig`, `graphToRdfXml`, `fromRdf`) | `l4source-convert` (its output is byte-identical to the output before the change, for 24 conversions); `l4factoidal parse --out F` for `ntriples`, `trig`, `rdfxml` and `jsonld` (below) |
| `Sink.Writer` (`init`, `push`, `finish`) | the quads arrive one at a time in the order the caller chooses; each call returns the text that quad completes | `l4sbm11 export` |

The JSON-LD writer is in `SinkJsonLd.lean` (`Sink.withJsonLd`), as the JSON-LD
reader is in `SourceJsonLd.lean`.

**What the stream writer holds.**

| Format | Writer | Holds |
| --- | --- | --- |
| N-Triples, N-Quads | one line for each quad | one quad |
| Turtle | `bodyPush`: one statement for each subject, `;` between predicates, `,` between objects | the triples of one subject |
| TriG | the same statements inside a block; a new block opens each time the graph of the next quad is not the open graph | the triples of one subject and the open graph name |
| RDF/XML, JSON-LD | the library writers take a whole graph or dataset | the dataset |

**TriG blocks in SPO order.** The export reads the SPO permutation. A graph
whose subjects interleave with the subjects of other graphs is written in several
blocks, one for each run of that graph. The TriG grammar allows it, and a reader
merges the blocks of one name into one graph. The W3C tests
`alternating_iri_graphs` and `alternating_bnode_graphs` alternate the blocks of two
graphs, and the Lean TriG readers pass them. The writer does not sort the quads
into graphs: that needs the dataset in memory.

**Syntaxes with no graph name.** N-Triples, Turtle and RDF/XML cannot name a
graph. `Sink.GraphChoice` says what the writer does with a quad in a named graph:
`refuse` (an error, the default), `defaultOnly`, `union` (a triple that repeats
the one before it is written once; the SPO order puts every repeat next to its
original) or `named g`. `l4sbm11 export` checks the generation before it writes a
byte, so a refused export leaves no partial file.

**Prefixes.** The stream writers for Turtle and TriG write every IRI in full,
`a` for `rdf:type`, and numbers and booleans in short form, unless the caller
gives a prefix table (`Options.prefixes`). The batch writer `turtleOfGraphAuto`
derives its prefixes from the whole graph, which a stream cannot.

**Checks.** `tests/sbm11/export_roundtrip.sh` (53 pass, 0 fail, 0 expected-fail,
out of 53, 2026-10-14): for each of the fixtures D1 to D4 of `tests/sbm11/syntax/`, pack,
export in each syntax that can write it, pack the export, and compare the data
files byte for byte (D3, which has blank nodes: RDFC-1.0 canonical N-Quads of the
dump). The RDF/XML export of D1 was an expected failure until 2026-10-14: the
export was correct, and the RDF/XML reader applied the `xml:lang` of a property
element to the property elements that follow it, so `"Alice"` read back as
`"Alice"@en` (https://github.com/danbri/factoidal/issues/841, repaired in
section 3c.7). The round trip of the generated set of 12,000 triples through
RDF/XML is a case now. Memory: rows
`sbm11-export-*-memory` of `tests/stack/lean_scaling.py`; the numbers are in
`2026-10-11-shardborough-vs-qlever.md` section 11.2.

**The command line writes the same syntaxes (2026-10-15).** Tracking:
https://github.com/danbri/factoidal/issues/853. `l4factoidal parse FILE --out F`
writes the dataset of FILE in the syntax F. F is `nquads`, `ntriples`, `turtle`,
`trig`, `rdfxml` or `jsonld`. `RDF.formatOfLabel` reads the label, so `Wasm/Cli.lean`
has no table of syntax names. The CI step "Known defects" of
`danbri/factoidal-builds` installs `l4factoidal` and no other program that writes
JSON-LD. The row `JLD-WSTACK` of `tests/known-defects/run.sh` needs a JSON-LD
writer, so the verb has one now. Four labels go to the serialiser layer. Two keep
their older writers.

| F | Writer | Notes |
| --- | --- | --- |
| `ntriples`, `trig`, `rdfxml`, `jsonld` | `Sink.serializeDataset` with `Sink.withJsonLd`, version `rdf12`: the call that `l4source-convert` makes | New. The verb holds the whole dataset in memory. |
| `nquads` | `Dataset.toCanonicalNQuads` | The bytes are the same as before. This is the canonical form of RDF 1.2 N-Quads: language tags in lower case, and the canonical escapes. `Dataset.toNQuads`, which `Sink` calls, keeps the case of a tag and escapes fewer characters. D1 has `"Hallo"@de-DE`, so the two forms differ on D1. |
| `turtle` | `Ops.serializeTurtleTextOf` | The bytes are the same as before. It writes the normal form of the dataset (a repeated triple once, tags in lower case) with prefixes from the whole graph. A triple term is written as `<<( s p o )>>`; until 2026-10-15 it refused a dataset with a triple term (https://github.com/danbri/factoidal/issues/870). |

**Named graphs.** N-Triples, Turtle and RDF/XML have no graph name. The batch
writer of `Sink` writes the triples of the default graph and of all the named
graphs as one graph (`Sink.flatten`). `--out turtle` did the same before this
change. The verb follows the batch writer. It prints a notice on standard error
that gives the number of named graphs. The stream writer of `Sink` refuses such a
dataset by default (`GraphChoice.refuse`). `l4sbm11 export` uses the stream writer
and has `--graph` to choose. `parse` has no `--graph` option.

**Errors.** A writer can refuse a dataset. RDF/XML and JSON-LD have no form for an
RDF 1.2 triple term. The verb then prints the error, writes nothing to standard
output, and exits with 1. An unknown label is a usage error (exit 2). The verb
finds it before it reads the input.

**Row `JLD-WSTACK`.** Until 2026-10-15 the row used `l4sbm11-pack` and `l4sbm11
export`. Both routes call `Sink.jsonLdWriter`, which is `JSONLD.FromRdf.fromRdf` and
`jcsDocument`. Measured under `LEAN_STACK_SIZE_KB=512`, one node with N references:
both routes exit 0 for N = 5,000, 10,000 and 12,000, and both abort with "Stack
overflow" for N = 15,000 and 20,000. The other `--out` writers (`nquads`,
`ntriples`, `trig`, `rdfxml`) run at 30,000 references under the same stack. The
row keeps the sizes 5,000 (control) and 20,000 (probe).

**Checks (2026-10-15).**

- `Wasm/cli-smoke.sh`: 106 pass, 0 fail, 0 xfail (out of 106); 83 pass, 0 fail
  before. The 23 new cases write D1 and D2 in each syntax and read the document
  back with the reader of the same syntax. They also check the notice, the canonical
  form of `nquads`, a triple term of D4 (written as N-Triples, refused by RDF/XML
  and JSON-LD), and the usage errors.
- Same bytes as before for `--out nquads` and `--out turtle`. The old build (commit
  457d8127) and the new build ran on the same inputs; stdout, stderr and the exit
  code were compared. The 31 files of `tests/sbm11/syntax` (D1 to D4 and
  `bnode_collide`): 62 runs, 59 identical, 3 identical on stdout and exit code with
  the new notice on stderr (D2 written as Turtle), 0 different. The same 31 files
  from standard input: 62 runs, 0 different. The W3C RDF 1.1 and RDF 1.2 test files
  of Turtle, N-Triples, N-Quads, TriG and RDF/XML (1,447 files): 2,894 runs, 2,667
  identical (1,700 with exit 0 and 967 with the same error), 227 identical on stdout
  and exit code with the notice on stderr only, 0 different.
- `tests/known-defects/run.sh` in the CI layout (a directory with `factoidal`,
  `owl_runner`, `l4factoidal` and `l4w3c` only): 24 XFAIL, 0 XPASS, 0 ERROR (out of
  24). The line of the row: `XFAIL #853 JSON-LD export of 20,000 references
  overflows a 512 KB stack  5,000 references write under 512 KB; 20,000: exit 134,
  Stack overflow`. The row reads ERROR with an `l4factoidal` that has no `--out
  jsonld`, and XPASS when the probe write passes. Before this change the same
  layout gave 23 XFAIL, 0 XPASS, 1 ERROR.
- Other gates of this change (2026-10-15): `lake build` 1,716 jobs;
  `tools/lean-unbuilt-modules.py --gate` 790 modules, 0 not reached;
  `tools/lean-tail-recursion-audit.py --gate` pass; `tools/lean-hygiene-audit.py`
  clean; `tests/sbm11/run.sh` 2,265 pass, 0 fail, 30 expected-fail (out of 2,295);
  `tests/stack/run.sh --canary` 109 pass, 0 fail (out of 109);
  `tools/strict-parse-differential.sh` with the old build as OLD: 21,012 agree, 0
  differ (out of 21,012). The change is in `Wasm/Cli.lean`, the root of
  `l4factoidal` only, so the WebAssembly module was not rebuilt.

**The batch Turtle writer takes no stack frame for each triple (2026-10-15).** Tracking:
https://github.com/danbri/factoidal/issues/863. The batch Turtle writer is
`turtleOfGraphAuto` and `turtleOfGraphOpts` in `Syntax/TurtleSerialize.lean`. These
programs call it: `l4factoidal parse --out turtle`, `l4source-convert`, the wasm
operations `serializeTurtle`, `serializeTurtleWith`, `datasetSerialize` and
`datasetSerializeWith` (so the npm package), the GET of the Graph Store service, the
Solid server and the RML Turtle target. The stream writer of this section
(`Sink.Writer`) does not derive prefixes and does not call it.

Before this change the writer overflowed a 512 KB stack at 2,711 triples. The wasm
module in Node overflowed at 100,000 triples, on the default stack and under
`--stack-size=512`. The two shapes are one subject with N objects, and N subjects.

*Cause.* The writer chooses its prefix table from the namespaces of the graph. It
sorts one namespace string for each IRI occurrence, then counts the runs of equal
strings with `countRuns`. `countRuns` continued with the result of its recursive
call, so it took one stack frame for each occurrence: about 64 bytes (524,288 bytes
for 8,133 occurrences, three for each triple of the two shapes). The allow list of
`tools/lean-tail-recursion-allow.txt` held a line for it with no reason, from the
first baseline. The gate passes such a line.

*Repair.* `countRuns` stays as the specification. `countRunsLoop` keeps the run in
progress and the finished runs in its arguments and calls itself in tail position.
`countRunsFast` starts it. `countRunsLoop_eq` states that the loop equals the
specification for every state, `countRunsFast_eq` follows, and the `csimp` theorem
`countRuns_eq_countRunsFast` makes the compiler run the loop wherever the source says
`countRuns`. The three theorems depend on `propext` and `Quot.sound` only. The
emitted C of `countRunsLoop` has two `goto _start` and no call of itself, and
`turtleOfGraphOpts` calls `countRunsFast`. The audit lists `countRuns` as `replaced`,
and its line is out of the allow list.

*The rest of the writer.* The module header (`Stack use`) lists what the writer
calls and why none of it takes a frame for each triple. The measurements below
cover it. Three recursions of the module still took a frame for each step of
something other than the triples when this change landed: `tsTermToTurtle` for each
level of RDF 1.2 triple-term nesting in one object, `tsUserUsed` for each prefix of the
caller's table that some IRI uses, and `assignLabelsAvoiding` for each numbered prefix
(at most nine). The first two are loops since issue 864 (the next paragraph);
`assignLabelsAvoiding` has a bound.

| Turtle writer, 512 KB | before (c48a4b70) | after |
|---|---|---|
| `l4factoidal parse --out turtle`, one subject with N objects | 2,710 triples ran, 2,711 overflowed | 100,000 ran (2.87 s, 297 MB); 400,000 ran at 256 KB (12.2 s, 1.13 GB) |
| the same, N subjects | 2,710 ran, 2,711 overflowed | 100,000 ran (1.88 s, 297 MB); 400,000 ran at 256 KB (8.74 s, 1.13 GB) |
| `serializeTurtle`, 100,000 triples, Node default stack | overflow | runs: 3.9 s (one subject with N objects) and 4.2 s (N subjects) |
| the same, Node `--stack-size=512` | overflow | runs: 3.7 s and 4.5 s |
| `tests/stack/run.sh --canary` | 121 pass, 0 fail (out of 121); 8 of the 12 new rows are expected failures | 121 pass, 0 fail (out of 121); 5 expected failures, none for issue 863 |

The old binary on the default stack needed 2.89 s and 296 MB for the first shape. The
loop costs no time and no memory that this measurement can see. Other shapes, all under
`LEAN_STACK_SIZE_KB=512` and with the same bytes as the old binary on the default
stack: 100,000 distinct namespaces (3.5 s, 354 MB), 100,000 blank-node subjects, graphs
of 30,000 and 300,000 triples with ties in the namespace counts (so that `ns1:` to
`ns5:` go to namespaces of equal count), and the whole of `gene.ttl` (205,530
paragraphs; 16.2 MB of Turtle; 24.9 s and 674 MB on the default stack).

*Rows.* `tests/stack/run.sh` has four rows for each shape: `turtle-write-one-node` and
`turtle-write-subjects` (the operation `serializeTurtle`, in the native, native
canary, wasm canary and wasm routes) and `turtle-write-cli-one-node` and
`turtle-write-cli-subjects` (the command line, in the native route and the native
canary; the row reads the Turtle back and counts 100,000 triples). The commit before the
repair added the rows as expected failures that name issue 863; the repair flips them to
assertions.

*Same bytes.* The old binaries (commit c48a4b70) were copied aside before the change.
Standard output, standard error and exit code were compared with the new ones.

| Input | Runs | Identical | Different |
|---|---:|---:|---:|
| `l4factoidal parse --out turtle`: the W3C RDF 1.1 and RDF 1.2 Turtle, TriG and N-Triples files (1,215 files; the RDF 1.2 files again with `turtle12`, `trig12`, `nt12`) | 1,535 | 1,535 (770 with exit 0, 930,299 bytes; 765 the same error) | 0 |
| the same command: the W3C N-Quads, RDF/XML, rdf-mt and rdf-semantics files (861 files) | 1,075 | 1,075 (728 with exit 0, 252,146 bytes; 347 the same error) | 0 |
| the same command: `tests/sbm11/syntax` (27 files) | 27 | 27 (23 with exit 0; 4 the same error) | 0 |
| the same command: 13 large inputs (60,055,276 bytes of Turtle), old on the default stack, new on the default stack and at 512 KB | 13 and 13 | 26 | 0 |
| `l4sbm11 export --format turtle`, with and without `--graph all`: the W3C Turtle, TriG and N-Triples files, packed by the old packer (842 of 1,215 files pack) | 1,684 | 1,684 (1,506 with exit 0, 3,766,283 bytes; 178 the same error) | 0 |
| the same command: `tests/sbm11/syntax` (27 files) | 54 | 54 | 0 |
| the same command: the 13 large inputs | 26 | 26 (258,720,306 bytes) | 0 |

The large inputs are the two 100,000-triple shapes, a file of 100,000 literals, graphs of 30,000 and
300,000 triples with the eight well-known prefixes, with three of them and with two, a graph of 50,000
triples with none, the 40,000-paragraph slice of `gene.ttl` that the row `TTL-SER-725` uses, three
more files of `examples/wikidata/subsets/lifesci-kgx/data` and the whole of `gene.ttl`.

*Known-defects row `TTL-SER-725`.* The F\* writer has the same defect (`count_runs`) and is not
changed. The row ran the F\* writer at 8192 KB and the Lean writer at the 1 GB default stack of a
Lean program, which compares two stack sizes. The Lean run is now pinned at 512 KB, and the detail
text says "Stack overflow in count_runs at 8192 KB; Lean serialises the same input correctly at
512 KB". The Lean run fails with ERROR when the writer overflows again.

*Checks (2026-10-15).*

- `lake build` (default targets): 1,716 jobs, exit 0.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of 1,381 lines,
  4 marked `(a) PENDING`, 504 marked `UNTRIAGED`). `python3
  tools/lean-unbuilt-modules.py --gate`: exit 0, 790 modules, 0 not reached.
  `tools/lean-hygiene-audit.py --build-log`: clean. `tools/test_lean_tail_recursion_audit.py`:
  12 pass, 0 fail (out of 12).
- `tests/sbm11/run.sh`: 2,265 pass, 0 fail, 30 expected-fail (out of 2,295).
- `tests/stack/run.sh --canary` (private `STACK_FIXTURES`, with a wasm module built from
  this tree): 121 pass, 0 fail (out of 121); 5 expected failures (issues 816 and 817), none for
  issue 863. The canary control passed.
- `formal/lean4/Wasm/cli-smoke.sh`: 106 pass, 0 fail, 0 xfail (out of 106).
  `formal/lean4/Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out of 366).
- `npm test` in `npm/factoidal`: 442 pass, 0 fail, 1 skipped (out of 443). `node --test
  tests/hub/*_test.mjs`: 447 pass, 0 fail (out of 447).
- `tests/known-defects/run.sh` in the CI layout (one directory with `factoidal`,
  `owl_runner`, `l4factoidal` and `l4w3c`): 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

**The batch Turtle writer with a large prefix table and a deeply nested triple term (2026-10-15).**
Tracking: https://github.com/danbri/factoidal/issues/864. Found by the repair of issue 863.
The same writer (`turtleOfGraphOpts`, `Syntax/TurtleSerialize.lean`) took one stack frame for
each used prefix of the caller's table and one for each nesting level of a triple term, and four
scans of it were quadratic. The caller's table comes from the options of `serializeTurtleWith` and
`datasetSerializeWith`, and from the prefixes that `datasetOpen` recorded for `datasetSerialize`.

*Before this change* (commit 6607b7f5, native, 512 KB): a table of 8,127 used prefixes ran and 8,128
overflowed in `tsUserUsed` (gdb names it). A triple term nested 300,000 deep overflowed.
User CPU time of `serializeTurtleWith` with a table of 8,000, 16,000 and 32,000 prefixes, every one
used: 2.36 s, 12.1 s and 56.7 s (ratios 5.1 and 4.7 for the two doublings). `datasetOpen` of a
Turtle document with 16,000, 32,000 and 64,000 `@prefix` lines: 1.24 s, 7.15 s and 33.0 s. The
Turtle text of a triple term nested 25,000, 50,000 and 100,000 deep, by the batch writer and the
stream writer: 0.50 s, 1.76 s and 10.2 s of CPU time; at 300,000 deep about 121 s.

*Causes.*

1. `tsUserUsed` continued with `(ns, label) :: tsUserUsed ...` (one frame for each pair it kept),
   scanned the list of the namespaces seen for each pair, and scanned the IRIs of the graph for
   each pair (`tsAnyIriUsesNs`).
2. `tsFindPrefix` scanned the table for each IRI occurrence of the document: `P * n` comparisons,
   3 * 10^10 for 100,000 prefixes and 100,000 triples. This one showed only when the first repair
   let the row run: the 100,000-prefix row did not finish after `tsUserUsed` alone.
3. `freshTopSpec` (a filter in `turtleOfGraphOpts`) compared each namespace of the graph with each
   covered row also when the budget of numbered prefixes was 0, which is the case once the caller's
   rows and the well-known rows are 8 or more.
4. `declarationOrderPrefixes` (`Wasm/Ops/Parse.lean`) scanned a list of the labels seen for each
   prefix of the document: 6.3 s for 32,000 prefixes. The Turtle reader alone (`l4factoidal parse`)
   takes 0.8 s for the same document. `datasetOpen` runs it, and so does every parse that reports
   the prefixes of the document.
5. `tsTermToTurtle` built the text of a triple term as `opening ++ text of the object ++ closer`, one
   frame and one copy of the text built so far for each nesting level: a stack overflow and time
   quadratic in the depth.

*Repair.* Each specification stays in the source as it was. A fast form is proved equal to it for
every input, and a `csimp` theorem makes the compiler run the fast form wherever the source says
the specification. The theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

| Specification | Fast form | Theorems |
|---|---|---|
| `tsUserUsed` | `tsUserUsedFast`: a tail loop (`tsUserUsedLoop`) with a hash set of the namespaces seen, and a hash set of the namespaces that some IRI lies under (`usedNsLoop`) | `tsUserUsedLoop_eq`, `tsUserUsedFast_eq`, `tsUserUsed_eq_fast` |
| `tsTermToTurtle` | `tsTermToTurtleFast`: a loop (`tsTermToTurtleLoop`) with a counter of the open triple terms; it appends the opening of each, and the closers at the leaf | `tsTermToTurtleLoop_eq`, `tsTermToTurtleFast_eq`, `tsTermToTurtle_eq_fast` |
| `turtleOfGraph` (it scans the table with `tsFindPrefix`) | `turtleOfGraphFast`: `Abbreviator` is the scan for a table of at most 64 rows for each distinct length of a namespace, and `PrefixIndex` above | `PrefixIndex.find_eq`, `Abbreviator.run_ofTable`, `turtleOfGraphFast_eq`, `turtleOfGraph_eq_fast` |
| `freshTopSpec` | `freshTopFast`: no filter when the budget is 0 | `freshTopFast_eq`, `freshTopSpec_eq_fast` |
| `declarationOrderPrefixes` | `declarationOrderPrefixesFast`: a hash set for the labels seen | `declarationOrderPrefixesLoop_eq`, `declarationOrderPrefixes_eq_fast` |

`PrefixIndex` stores, for each namespace of the table, its first row and the rank of that row,
and the distinct lengths of the namespaces. A lookup for an IRI of `L` characters takes, for each
length `l < L`, the row of the namespace `take l iri`, and keeps the row of least rank.
`PrefixIndex.find_eq` states that this is the row `List.find?` finds, which is the FIRST row of
the table whose namespace is a proper prefix of the IRI; a longer namespace in a later row does
not win. Its proof has five parts (`skills/lean4-proof-patterns/SKILL.md`, section 9b).

| Turtle writer | before (6607b7f5) | after |
|---|---|---|
| `serializeTurtleWith`, 100,000 prefixes, 100,000 triples, 512 KB | overflow from 8,128 prefixes | runs: 4.7 s to 6.5 s, 546 MB |
| `datasetOpen` of 100,000 `@prefix` lines, then `datasetSerialize`, 512 KB | overflow | runs: 7.3 s to 7.5 s, 735 MB |
| `datasetOpen` of the triples, then `datasetSerializeWith` with 100,000 prefixes, 512 KB | overflow | runs: 4.3 s to 5.1 s, 525 MB |
| the same three in Node, default stack and `--stack-size=512` | overflow | run: 5.9 s, 7.9 s, 5.9 s and 6.7 s, 7.7 s, 6.2 s |
| a triple term nested 300,000 deep, both writers | overflow at 512 KB; about 121 s at the default stack | runs at 512 KB and at 64 KB: 0.8 s |
| user CPU of `serializeTurtleWith`, 8,000, 16,000, 32,000 prefixes | 2.36 s, 12.1 s, 56.7 s | 0.24 s, 0.49 s, 1.0 s |
| user CPU of `datasetOpen`, 16,000, 32,000, 64,000 `@prefix` lines | 1.24 s, 7.15 s, 33.0 s | 0.43 s, 0.87 s, 1.76 s |
| CPU of the nested term, 25,000, 50,000, 100,000 levels | 0.50 s, 1.76 s, 10.2 s | 0.061 s, 0.116 s, 0.241 s |
| `tests/stack/run.sh --canary` | 131 pass, 0 fail (out of 131); 15 expected failures, 10 for issue 864 | 135 pass, 0 fail (out of 135); 5 expected failures, none for issue 864 |

*A cost paid on the way.* The first version of `Abbreviator` was a definition that returned a
closure built from a `let`. The compiler gives such a definition the arity of all its arrows, so
every call of the closure ran the `let` again and built the index for each IRI: 16 s for a table of
1,000 rows, 63 s for 2,000. `Abbreviator` is a value now. Record:
`skills/lean4-performance/SKILL.md`, "A function that returns a function runs its `let` again".

*Rows.* `tests/stack/run.sh`: `turtle-write-prefixes` (the operation `serializeTurtleWith`),
`turtle-write-prefixes-handle` (`datasetOpen` of a Turtle document with 100,000 `@prefix` lines,
then `datasetSerialize`) and `turtle-write-prefixes-with` (`datasetOpen` of the same triples as
N-Quads, then `datasetSerializeWith` with 100,000 prefixes in the options), each in the native,
native canary, wasm canary and wasm routes; `turtle-triple-term` (`l4source-convert --nest-check
300000`) in the native route and the native canary. A row also counts the `@prefix` lines of the
output. The term of `turtle-triple-term` is built in memory by a loop: the Turtle reader took a
frame for each nesting level (class (b) in the allow list), so no text could carry the term (the reader
reads such a text since issue 865: the row `turtle-read-triple-term`, in the paragraph below), and the
wasm module has no operation that builds one. The harness writes the term with the batch writer
and with the stream writer, and compares both with the text that a loop builds (5,400,063 bytes).
`tests/stack/lean_scaling.py`: `turtle-prefixes`, `turtle-prefixes-open` and `turtle-nest-time`,
measured at n, 2n and 4n. The commit before the repair added the rows as expected failures that
name issue 864 (10 of the 131 rows of `tests/stack/run.sh --canary`, and the 3 scaling rows); the
repair flips them to assertions.

*Same bytes.* The old binaries (commit 6607b7f5, the repair of issue 863) were copied aside
before the change. Standard output, standard error and exit code were compared with the new
ones.

| Input | Runs | Identical | Different |
|---|---:|---:|---:|
| `l4factoidal parse --out turtle`: the W3C RDF 1.1 and RDF 1.2 Turtle, TriG and N-Triples files (1,215 files; the RDF 1.2 files again with `turtle12`, `trig12`, `nt12`) | 1,535 | 1,535 (770 with exit 0, 930,299 bytes; 765 the same error) | 0 |
| the same command: the W3C N-Quads, RDF/XML, rdf-mt and rdf-semantics files (861 files) | 1,075 | 1,075 (728 with exit 0, 252,146 bytes; 347 the same error) | 0 |
| the same command: `tests/sbm11/syntax` (27 files) | 27 | 27 (23 with exit 0; 4 the same error) | 0 |
| the same command: 13 large inputs (67,609,181 bytes of Turtle), old on the default stack, new on the default stack and at 512 KB | 13 and 13 | 26 | 0 |
| `l4sbm11 export --format turtle` (the stream writer, which runs `tsTermToTurtle`), with and without `--graph all`: the W3C Turtle, TriG and N-Triples files, packed by the old packer (842 of 1,215 files pack) | 1,684 | 1,684 (1,506 with exit 0, 3,766,283 bytes; 178 the same error) | 0 |
| the same command: `tests/sbm11/syntax` | 54 | 54 | 0 |
| the same command: the 13 large inputs | 26 | 26 (317,197,922 bytes) | 0 |
| `parseToDatasetJson` (which reports the prefixes of the document, so `declarationOrderPrefixes`) and `datasetOpen` + `datasetSerialize` with `turtle` on the 1,215 W3C files | 2,430 | 2,430 (440 with a non-empty prefix table; 3,769,361 bytes) | 0 |
| 3,000 random cases of `tools/turtle-writer-differential.py` (seeds 101 and 102): `datasetOpen` of N-Triples 1.2 with triple terms nested up to 5 deep, or of Turtle with prefixes bound twice; then `datasetSerialize`, `datasetSerializeWith` with a random table of 0 to 200 rows (the same namespace in two rows, namespaces inside one another, the empty namespace, non-ASCII, labels equal to the derived ones) and with `literalShorthand` false; `serializeTurtleWith`; `serializeTurtle`. In 1,521 of the cases the table has 1,100 to 2,100 more rows, every one used, which the writer indexes | 3,568 | 3,568 (913,592,880 bytes) | 0 |

The 13 large inputs are the two 100,000-triple shapes, a file of 100,000 literals, graphs of
30,000 and 300,000 triples whose five namespaces have equal counts (so that `ns1:` to `ns5:` go
to namespaces of equal count) with three of the well-known prefixes, the same with all eight, a
graph of 50,000 triples with none, the 40,000-paragraph slice of `gene.ttl` that the row
`TTL-SER-725` uses, three more files of `examples/wikidata/subsets/lifesci-kgx/data` and the whole
of `gene.ttl`. Earlier revisions of the generator ran 7,200 more cases with 0 differences.

*Checks (2026-10-15).*

- `lake build` (default targets): 1,716 jobs, exit 0.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of 1,379 lines, 4 marked
  `(a) PENDING`, 504 marked `UNTRIAGED`; the audit lists `tsUserUsed` and `tsTermToTurtle` as
  `replaced`, and the lines of both are out of the allow list). `python3
  tools/lean-unbuilt-modules.py --gate`: exit 0, 790 modules, 0 not reached.
  `tools/lean-hygiene-audit.py --build-log`: clean (1,517 `#print axioms` outputs).
  `tools/test_lean_tail_recursion_audit.py`: 12 pass, 0 fail (out of 12).
- `tests/sbm11/run.sh`: 2,265 pass, 0 fail, 30 expected-fail (out of 2,295).
- `tests/stack/run.sh --canary` (private `STACK_FIXTURES`, with a wasm module built from this
  tree): 135 pass, 0 fail (out of 135); 5 expected failures (issues 816 and 817), none for
  issue 864. Before the change, on commit 6607b7f5 with the new rows: 131 pass, 0 fail (out of
  131); 15 expected failures, 10 of them for issue 864. The canary control passed. The rows of
  100,000 prefixes ran in 4.6 s, 7.2 s and 5.1 s (native), 5.9 s, 7.9 s and 5.9 s (wasm) and
  6.7 s, 7.7 s and 6.2 s (wasm under `--stack-size=512`); the triple term nested 300,000 deep in
  0.8 s.
- `tests/stack/lean_scaling.py --only turtle-prefixes,turtle-prefixes-open,turtle-nest-time,
  turtle-serialize`: 4 pass, 0 fail, 0 expected-fail (out of 4). Two runs of the three new rows
  gave ratios of 1.9 to 2.2 for each doubling (bound 3.0).
- `formal/lean4/Wasm/cli-smoke.sh`: 106 pass, 0 fail, 0 xfail (out of 106).
  `formal/lean4/Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out of 366).
- `npm test` in `npm/factoidal`: 442 pass, 0 fail, 1 skipped (out of 443). `node --test
  tests/hub/*_test.mjs`: 447 pass, 0 fail (out of 447).
- `tests/known-defects/run.sh` in the CI layout (one directory with `factoidal`,
  `owl_runner`, `l4factoidal` and `l4w3c`): 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

**The Turtle reader with a deeply nested triple term and a large prefix table, and the stream writer's table (2026-10-15).**
Tracking: https://github.com/danbri/factoidal/issues/865. Found by the repair of issue 864, whose
row `turtle-triple-term` built the term in memory because the reader could not read a text of that
nesting. Three inputs that a caller sizes reach code that took a stack frame, or a scan of a list, for
each step: the nesting of a triple term (2 frames for each level), the number of `@prefix` directives of a
document (a scan of the bindings for each prefixed name), and the number of `--prefix` arguments of
`l4sbm11 export` (a scan of the table for each IRI, and a quadratic append in the option parser).

*Before this change* (commit 3e832dfe, native): `l4factoidal parse` with the format `turtle12` read a
triple term nested 2,536 deep under `LEAN_STACK_SIZE_KB=512` and overflowed at 2,537; Node overflowed on
300,000 levels with the default stack and with `--stack-size=512`. At the default native stack the reader
was linear (20,000 levels: 0.04 s for the count) and the answer of `parseToDatasetJson` was not: 0.04 s,
0.12 s and 0.41 s of CPU time for 5,000, 10,000 and 20,000 levels written as canonical N-Quads
(`Term.toCanonicalNTriples` copied the text of the levels below at each level), and no result in 120 s
for 300,000. CPU time of `l4factoidal parse` of a document with n `@prefix` lines and n triples of three
prefixed names: 2.59 s, 16.4 s and 78.8 s for n = 16,000, 32,000 and 64,000 (ratios 6.3 and 4.8).
`l4sbm11 export --format turtle --verify none` with n `--prefix` arguments, every one used, over n
statements: 0.252 s, 0.828 s and 3.41 s for n = 4,000, 8,000 and 16,000 (ratios 3.3 and 4.1).

*Causes.*

1. `readTtObject` and `readTripleTerm` (the mutual pair of [32] and [30]) called each other, one frame each
   for a nesting level.
2. `Term.toCanonicalNTriples` built `"<<( " ++ s ++ " <p> " ++ text of the object ++ " )>>"`: a frame and a
   copy of the text so far for each level. It is the text of the term in the N-Quads that every parse
   operation answers (`Dataset.toCanonicalNQuads`).
3. `TurtleState.lookupPrefix` was `List.find?` over the bindings in force, newest first: a name under the
   first prefix declared of n took n comparisons.
4. `Sink.bodyPush` and `Sink.trigSwitch` shortened each IRI by a scan of the prefix table
   (`tsAbbreviateIri`); the writer held the table as a list.
5. `Sbm11Export.parseOpts` appended each `--prefix` to the end of the list of the others
   (`o.prefixes ++ [x]`): n squared / 2 list cells for n arguments: 0.73 s of the 3.4 s at 16,000 arguments (one statement in the generation: 0.23 s, 0.73 s, 3.1 s for 8,000, 16,000, 32,000 arguments; after: 0.022 s, 0.078 s, 0.19 s).

*Repair.* Each specification stays in the source as it was; the fast form is proved equal for every input
and the compiler runs it wherever the source says the specification. The theorems depend on `propext`,
`Classical.choice` and `Quot.sound` only.

| Specification | Fast form | Theorems |
|---|---|---|
| `readTripleTerm`, `readTtObject` (Turtle.lean) | `readTripleTermLoop`, `readTtObjectLoop`: `readTripleTermDown` keeps the open triple terms in a list and goes to the object by a tail call; `closeTripleTerms` closes them | `readTripleTermDown_eq`, `readTripleTerm_eq_loop`, `readTtObject_eq_loop` |
| `Term.toCanonicalNTriples` (NTriples.lean) | `Term.toCanonicalNTriplesFast`: a loop with a counter of the open triple terms (as `tsTermToTurtleLoop`) | `Term.toCanonicalNTriplesLoop_eq`, `Term.toCanonicalNTriplesFast_eq`, `Term.toCanonicalNTriples_eq_fast` |
| `TurtleState.lookupPrefix` | `lookupPrefixIndexed`: a lookup in `prefixIndex`, a `Std.TreeMap` that every state carries with the proof `prefixIndex_ok`; `bindPrefix` adds a binding | `lookupPrefixIndexed_eq`, `lookupPrefix_eq_indexed`, `lookupPrefix_bindPrefix` |
| `Sink.bodyPush`, `Sink.trigSwitch` (table) | `bodyPushBy`, `trigSwitchBy` (an `Abbreviator` the writer holds, built once by `Writer.init`) | `bodyPushBy_ofTable`, `trigSwitchBy_ofTable` |
| `Opts.prefixes` (append) | `prefixesRev` and one `reverse` | none: the order of the arguments is the order of the output (the row and 14,463 comparisons) |

`Sink` has no `csimp` theorem for the pair `bodyPush`/`bodyPushBy`: the fast form takes the
`Abbreviator`, which is data that the writer holds, and a theorem `bodyPush = fun table => bodyPushBy
(Abbreviator.ofTable table)` would make every call build the index again (the cost paid in 864). The
stream writer calls the fast form directly.

| Time and stack | before (3e832dfe) | after |
|---|---|---|
| `parseToDatasetJson` of a triple term nested 300,000 deep (a 4.2 MB Turtle text; the answer holds 16.2 MB of N-Quads), native, 512 KB | overflow (2,536 levels ran, 2,537 overflowed in `l4factoidal parse`) | runs: 1.3 s; 0.74 s at the default stack (before: no result in 120 s) |
| the same in Node, default stack and `--stack-size=512` | overflow | runs: 1.9 s and 1.6 s |
| CPU of `l4factoidal parse --out nquads`, 5,000, 10,000, 20,000 levels | 0.04 s, 0.12 s, 0.41 s | not measured at these sizes; 300,000 levels in 1.3 s |
| CPU of `l4factoidal parse`, 16,000, 32,000, 64,000 prefixes | 2.59 s, 16.4 s, 78.8 s | 0.29 s, 0.58 s, 1.11 s |
| CPU of `l4sbm11 export`, 4,000, 8,000, 16,000 prefixes | 0.252 s, 0.828 s, 3.41 s | 0.057 s, 0.071 s, 0.154 s |
| CPU of `l4sbm11 export`, one statement, 8,000, 16,000, 32,000 arguments | 0.23 s, 0.73 s, 3.1 s | 0.022 s, 0.078 s, 0.19 s |
| `tests/stack/run.sh --canary` | 138 pass, 0 fail (out of 138); 8 expected failures, 3 for issue 865 | 139 pass, 0 fail (out of 139); 5 expected failures, none for issue 865 |

The other modes of reading a document with 64,000 prefixes (`--lenient`, `--out turtle`, and TriG with
one graph block for each triple) cost 1.0 s, 2.0 s and 1.1 s of user CPU time, four times the time at
16,000 for four times the size. The lenient reader keeps the state from before a statement, which is
why the index is a tree and not a hash table (`skills/lean4-performance/SKILL.md`).

*Rows.* `tests/stack/run.sh`: `turtle-read-triple-term` (the operation `parseToDatasetJson`, format
`turtle12`, one triple whose object is a triple term nested 300,000 deep) in the native, native canary,
wasm canary and wasm routes. The row checks the answer: `"count":1` and 300,000 openings of a triple
term in the N-Quads. `tests/stack/lean_scaling.py`: `turtle-read-prefixes` and
`sbm11-export-prefixes-time`, measured at n, 2n and 4n. The commit before the repair (236220ad) added the
rows as expected failures that name issue 865 (3 of the 138 rows of `tests/stack/run.sh --canary`, and the 2
scaling rows); the repair flips them to assertions.

*Same bytes.* The old binaries (commit 3e832dfe, the repair of issue 864) were copied aside before the
change. Standard output, standard error and exit code of the commands, and the output files of the
exports, were compared with the new ones.

| Input | Runs | Identical | Different |
|---|---:|---:|---:|
| `l4factoidal parse` with no `--out` (the count), `--out nquads` and `--out turtle`: the W3C RDF 1.1 and RDF 1.2 Turtle, TriG and N-Triples files (1,215 files; the RDF 1.2 files again with `turtle12`, `trig12`, `nt12`) | 4,605 | 4,605 (2,622 with exit 0; 1,983 the same error) | 0 |
| the same three: the W3C N-Quads, RDF/XML, rdf-mt and rdf-semantics files (861 files) | 3,225 | 3,225 (2,404 with exit 0; 821 the same error) | 0 |
| the same three: `tests/sbm11/syntax` (27 files) | 81 | 81 (69 with exit 0; 12 the same error) | 0 |
| `tools/turtle-reader-differential.py`, seeds 11, 12, 13, 4,000 documents each, Turtle and TriG in the RDF 1.2 mode, 40 percent damaged: the count, `--out nquads`, `--out turtle`, `--lenient` | 48,000 | 48,000 (20,209 with exit 0; 27,791 the same error) | 0 |
| `parseToDatasetJson` and `datasetOpen` + `datasetSerialize` with `turtle`, on the W3C files and `tests/sbm11/syntax` (2,637 files) | 5,274 | 5,274 (890 with a non-empty prefix table; 5,046,719 bytes) | 0 |
| `l4sbm11 export --format turtle` and `--format trig`, with no prefix and with tables of 7, 208 and 307 rows (a label bound twice in one of them; all three below the threshold of the index, so the writer scans), the W3C files packed by the old packer | 14,463 | 14,463 (14,065 with exit 0; 398 the same error; 93,857,258 bytes) | 0 |
| the same command on 800 random N-Quads datasets whose IRIs lie under 3 to 1,200 namespaces, with tables of 0, 5, 80 and 1,200 prefixes (the tables above 64 rows for each distinct length are indexed) | 6,400 | 6,400 (126,725,909 bytes) | 0 |
| 3,000 random cases of `tools/turtle-writer-differential.py` (seeds 101 and 102; the writer of the batch operations) | 3,568 | 3,568 (913,592,880 bytes) | 0 |
| `tests/sbm11/w3c_roundtrip.sh`: store and parser outcome and detail of each test | 1,299 | 1,299 (1,281 pass, 18 expected-fail) | 0 |
| `tests/trig-pack/compare_w3c.sh` | 717 | 717 (484 equal hashes, 2 expected, 231 refused) | 0 |

*Checks (2026-10-15).*

- `lake build` (default targets): 1,716 jobs, exit 0. A second build after the last edit of a
  docstring: the 960 C files and the six binaries that the checks use have the same hashes as before.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of 1,376 lines, 4 marked
  `(a) PENDING`, 502 marked `UNTRIAGED`; the audit lists `readTripleTerm`, `readTtObject` and
  `Term.toCanonicalNTriples` as `replaced`, and their three lines are out of the allow list). The C of
  `readTripleTermDown` and of `closeTripleTerms` has one `goto _start` each and no call of itself.
  `python3 tools/lean-unbuilt-modules.py --gate`: exit 0, 790 modules, 0 not reached.
  `tools/lean-hygiene-audit.py --build-log`: clean (1,527 `#print axioms` outputs).
  `tools/test_lean_tail_recursion_audit.py`: 12 pass, 0 fail (out of 12).
- `tests/sbm11/run.sh`: 2,265 pass, 0 fail, 30 expected-fail (out of 2,295). `tests/sbm11/census.sh`,
  `tests/delta-log/run.sh` (46 pass, 0 fail) and `tests/sbm11/threads.sh` (all answers identical): exit 0.
- `tests/stack/run.sh --canary` (private `STACK_FIXTURES`, with a wasm module built from this tree):
  139 pass, 0 fail (out of 139); 5 expected failures (issues 816 and 817), none for issue 865. The
  canary control passed. `turtle-read-triple-term`: 1.05 s native, 1.7 s wasm canary, 1.6 s wasm.
- `tests/stack/lean_scaling.py --only` the two new rows and the rows `turtle-prefixes`,
  `turtle-prefixes-open`, `turtle-nest-time`, `turtle-object-list`, `trig-parse`, `trig-big-graph`,
  `turtle-serialize`, `sbm11-export-ttl-memory`, `sbm11-export-trig-memory`, `sbm11-pack-ttl-memory`,
  `sbm11-pack-trig-memory` and `query-vs-parse`: 14 pass, 0 fail, 0 expected-fail (out of 14). The first run had
  `query-vs-parse` at 2.3 times the CPU time of `parse` (bound 2.0) at a load average of 10.6; at a load
  average of 3.3 it gave 1.4, and the binary before the change 1.6.
- `formal/lean4/Wasm/cli-smoke.sh`: 106 pass, 0 fail, 0 xfail (out of 106).
  `formal/lean4/Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out of 366).
- `npm test` in `npm/factoidal`: 442 pass, 0 fail, 1 skipped (out of 443). `node --test
  tests/hub/*_test.mjs`: 447 pass, 0 fail (out of 447).
- `tests/known-defects/run.sh` in the CI layout (one directory with `factoidal`,
  `owl_runner`, `l4factoidal` and `l4w3c`): 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

**The N-Triples and N-Quads 1.2 readers, the hash and the join key of a term, the N-Triples text of a term and the language tags of a term, with a deeply nested triple term (2026-10-15).**
Tracking: https://github.com/danbri/factoidal/issues/867. The report of issue 865 named three functions that
a triple term nested deep still reached after the Turtle reader became a loop. A row added in this change for the
reader of a file found a fourth, `Term.lowerTags`.

*Before this change* (commit 724fdd79, native, `LEAN_STACK_SIZE_KB=512`): `parseToDatasetJson` with the format
`nt12` or `nq12` read a triple term nested 4,510 deep and overflowed at 4,511 (`readObject12`). With `trig12` and
the term in a graph block 10,152 levels ran and 10,153 overflowed; gdb names the derived hash of a term,
`instHashableTerm.hash`, in the first frames. `Term.joinKey` is computed first for the same key and recurses in the same way.
`l4factoidal parse --out nt` wrote 10,151 levels and overflowed at 10,152 (`Term.toNTriples`). The wasm module
overflowed its call stack on each of the four operations at 300,000 levels, in Node with the default stack and with
`--stack-size=512`. `l4factoidal parse FILE --format nt12|nq12`, which reads a file in 64 KiB chunks (the reader
that the shard packers use), overflowed too. At the default stack the batch readers ran 300,000 levels in 2.0 s,
2.0 s and 1.7 s, and the text of the term did not: 86.6 s for `parse --out nt`, 90.7 s for the answer of a CONSTRUCT
query, CPU time of 0.280 s, 1.23 s and 8.58 s for 25,000, 50,000 and 100,000 levels (ratios 4.4 and 7.0).

*Causes.*

1. `readObject12` (the object reader of N-Triples and N-Quads in the RDF 1.2 mode) called itself once for each
   level: a native frame for each.
2. The hash that `deriving Hashable` made for `Term` mixes the hash of the object last: a frame for each level.
   A dataset keys each triple by `(subject, predicate, Term.joinKey object)` in a hash map (`FastGraph`,
   `tripleKey`), so every parse of a dataset hashes the term.
3. `Term.joinKey` wraps `Term.joinKey` of the object: a frame for each level.
4. `Term.toNTriples` built `"<<( " ++ s ++ " <p> " ++ text of the object ++ " )>>"`: a frame and a copy of the
   text so far for each level. `Graph.toNTriples`, `Dataset.toNQuads`, the stream writers and the answer of a
   CONSTRUCT or DESCRIBE query write the term with it.
5. `Term.lowerTags` wraps `Term.lowerTags` of the object: a frame for each level. The count consumer of the
   streamed reader (`countQuad`) and `normalizeDataset` apply it to every term.

*Repair.* Each specification stays in the source as it was. A loop is proved equal to it and the compiler runs the
loop. The theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

| Specification | Fast form | Theorems |
|---|---|---|
| `readObject12` (NTriples.lean) | `readObject12Loop`: `readObject12Down` reads the subject and the predicate of a level, puts them on a list (`OpenTerms12`) and goes to the object by a tail call, one unit of fuel for a level as the specification takes; `closeObject12` closes the open levels | `readObject12Down_eq` (every list of open levels, every fuel), `closeObject12_error`, `_nil`, `_cons`, `readObject12_open`, `readObject12_eq_loop` (`@[csimp]`) |
| `Term.toNTriples` (NTriples.lean) | `Term.toNTriplesFast`: a loop with the text so far and a counter of the open levels, as `Term.toCanonicalNTriplesLoop`; the helpers `closersStr`, `appendClosers` and `tripleTermOpen` moved above the specification | `Term.toNTriplesLoop_eq` (the text so far, the specification and the closers; the error of RDF 1.1 mode for a triple term), `toNTriplesClose_eq`, `Term.toNTriplesFast_eq`, `Term.toNTriples_eq_fast` (`@[csimp]`) |
| `Term.joinKey` (Core.lean) | `Term.joinKeyFast`: the subject and the predicate of each open level on a list, `wrapTripleTerms` at the end | `Term.joinKeyLoop_eq`, `Term.joinKey_eq_fast` (`@[csimp]`) |
| `Term.lowerTags` (DatasetNormalize.lean) | `Term.lowerTagsFast`: the same shape with `wrapTripleTerms` | `Term.lowerTagsLoop_eq`, `Term.lowerTags_eq_fast` (`@[csimp]`) |
| the hash of a term (`instHashableTerm.hash`, Core.lean) | `Term.hashFast`: the part of each level that does not depend on its object (`hashTripleOpen`) goes on a list, and `hashClose` mixes the parts into the hash of the innermost term, innermost first | `hash_iri`, `hash_bnode`, `hash_literal` and `hash_tripleTerm` (each by `rfl`: the equations of the derived function), `Term.hashDown_eq`, `Term.hashFast_eq` |

The hash is an instance and not a `@[csimp]` theorem. `Term.hash_eq_fast : @instHashableTerm.hash = @Term.hashFast`
as a `@[csimp]` theorem elaborated and the build passed, and the emitted C of `FastGraph` still called
`instHashableTerm_hash`, while the same `tripleKey` called `Term_joinKeyFast` (the replacement of `Term.joinKey`): the
compiler inlines an instance before it replaces the constants of a `@[csimp]` theorem. The audit could not see it:
its class `replaced` is read from the theorem and not from the callers. `instHashableTermLoop` (priority `high`)
is the `Hashable Term` of every module after `Core.lean`, and so of the hash of a `Triple`; the derived instance
stays as the specification and `Term.hashFast_eq` is stated against it. After the change 12 C files call
`Term_hashFast` and none outside `Core.c` names `instHashableTerm_hash`. Every hash value is the value the derived
function gave, so a hash map lists its keys in the order it did before.

| Time and stack, 300,000 levels | before (724fdd79) | after |
|---|---|---|
| `parseToDatasetJson`, format `nt12`, `nq12`, native | overflow under 512 KB (4,510 levels ran); 2.0 s at the default stack | 1.3 s and 1.5 s at the default stack; runs under 512 KB |
| the same in Node | overflow, with the default stack and with `--stack-size=512` | 1.8 s and 2.0 s with the default stack; 2.3 s and 2.2 s at `--stack-size=512` |
| `parseToDatasetJson`, format `trig12`, the term in a graph block | overflow under 512 KB (10,152 levels ran); 1.7 s at the default stack | 1.6 s at the default stack; runs under 512 KB; Node 2.1 s and 1.9 s |
| `queryDataset` CONSTRUCT over the term | overflow under 512 KB; 90.7 s at the default stack | 1.4 s at the default stack; runs under 512 KB; Node 2.0 s and 2.3 s |
| `l4factoidal parse FILE.ttl --format turtle12 --out nt` | overflow under 512 KB (10,151 levels ran); 86.6 s at the default stack | 0.57 s at the default stack; 0.80 s under 512 KB; the output equals the fixture byte for byte |
| `l4factoidal parse FILE --format nt12`, `nq12` (the reader of a file) | overflow under 512 KB (in `readObject12`); 9.8 s and 9.9 s at the default stack | 8.5 s and 9.2 s at the default stack; 9.1 s and 9.8 s under 512 KB |
| `ntriples-nest-time`, 25,000, 50,000, 100,000 levels (CPU) | 0.280 s, 1.23 s, 8.58 s (ratios 4.4 and 7.0) | 0.048 s, 0.091 s, 0.208 s (ratios 1.9 and 2.3) |
| `datasetOpen` of the Turtle text, then a CONSTRUCT through the handle (probe, not a row) | overflow under 512 KB; 198 s at the default stack | 1.4 s under 512 KB; 2.2 s at the default stack |
| `tests/stack/run.sh --canary` | 155 pass, 0 fail (out of 155) with 16 of the new rows; 18 expected failures, 13 for issue 867 | 161 pass, 0 fail (out of 161); 5 expected failures (issues 816 and 817), none for issue 867 |

The time of the file reader (8 to 10 s for one line of 7.2 MB) is the same before and after the repair. The batch
reader reads the same line in 1 to 2 s.

*Rows.* `tests/stack/run.sh`: `ntriples-read-triple-term`, `nquads-read-triple-term` and `trig-read-triple-term`
(the operation `parseToDatasetJson`, formats `nt12`, `nq12`, `trig12`, one triple whose object is a triple term
nested 300,000 deep) and `construct-triple-term` (the operation `queryDataset`, a CONSTRUCT query over the same
term) in the native, native canary, wasm canary and wasm routes; `ntriples-write-triple-term` (`l4factoidal parse
FILE.ttl --format turtle12 --out nt`, compared byte for byte with a fixture) and `ntriples-read-cli-triple-term` and
`nquads-read-cli-triple-term` (`l4factoidal parse FILE --format nt12|nq12`, the reader of a file) in the native
route and the native canary. The rows of the operations check the answer: `"count":1` and 300,000 openings of a
triple term. `tests/stack/lean_scaling.py`: `ntriples-nest-time`, measured at n, 2n and 4n. The commit before the
repair added the rows as expected failures that name issue 867 (15 rows of `tests/stack/run.sh --canary` and the
scaling row); the repair flips them to assertions.

*Guards.* `L4Factoidal/Syntax/NestedTermTests.lean` pins results that the specifications gave before the change,
recorded from the library of commit 724fdd79 by a program that called the functions directly: `readObject12` on 38
texts at 8 fuels (the message and the offset of each error, such as "triple-term nesting too deep" at the offset
of the next object); the five readers and writers on 31 documents, in RDF 1.2 and RDF 1.1 mode; `Term.toNTriples`,
the hash, the join key and the hash of the join key on 14 terms. A guard that compares a specification with its
`@[csimp]` replacement compares the replacement with itself, so the deep guards compare with texts and values built
another way (a repeated string, a repeated `mixHash`), and the loop of the hash is compared with the derived
instance, a different function.

*Same bytes.* The old binaries (commit 724fdd79, the repair of issue 865) were copied aside before the
change. Standard output, standard error and exit code of the commands, and the answers of the operations, were
compared with the new ones. Issue 866 changed `l4sbm11` and `l4sbm11-pack`; the last row compares the merged
tree's two binaries again. The other binaries of the merged tree are the same files as the ones compared.

| Input | Runs | Identical | Different |
|---|---:|---:|---:|
| `l4factoidal parse` with no `--out` (the count), `--out nquads`, `ntriples`, `turtle` and `trig`: the W3C Turtle, TriG, N-Triples, N-Quads, RDF/XML, rdf-mt and rdf-semantics files, `tests/sbm11/syntax` and `tests/rdf-mt-generated` (2,733 files, each in the formats of its extension, the RDF 1.2 formats too) | 26,205 | 26,205 (18,488 with exit 0, 23,201,218 bytes of output; 7,717 the same error) | 0 |
| `l4wasm-cli`: `parseToDatasetJson`, `datasetOpen` then `datasetSerialize` with `nquads` and with `turtle`, and for N-Triples and N-Quads text `queryDataset` with a CONSTRUCT and with a SELECT query, on the same files (2,717 files) | 12,170 | 12,170 | 0 |
| `tools/ntriples-reader-differential.py`, seeds 21, 22, 23, 4,000 documents each, N-Triples and N-Quads in the RDF 1.2 mode, 40 percent damaged: the count, `--out nquads`, `ntriples`, `turtle`, `trig`, `--lenient`, and the RDF 1.1 reader | 84,000 | 84,000 (46,969 with exit 0; 37,031 the same error) | 0 |
| `tools/turtle-reader-differential.py`, seeds 11, 12, 13, 4,000 documents each (Turtle and TriG, four ways to read) | 48,000 | 48,000 (20,209 with exit 0; 27,791 the same error) | 0 |
| `tools/turtle-writer-differential.py`, seeds 101 and 102, 1,500 cases each | 3,568 | 3,568 (913,592,880 bytes) | 0 |
| `l4sbm11 export` as N-Quads, N-Triples, Turtle and TriG of 2,312 generations that the old `l4sbm11-pack` made from the W3C files and `tests/sbm11/syntax` | 9,248 | 9,248 | 0 |
| `tests/sbm11/w3c_roundtrip.sh`: store and parser outcome and detail of each test | 1,299 | 1,299 (1,281 pass, 18 expected-fail) | 0 |
| `tests/trig-pack/compare_w3c.sh`, old against new | 717 | 717 (484 equal hashes, 2 expected, 231 refused) | 0 |
| the same two checks, `l4sbm11` and `l4sbm11-pack` of the merged tree | 1,299 and 9,248 | 1,299 and 9,248 | 0 |

A parse of 480,000 triples (`gen_multi.py`, 45.9 MB of N-Triples, 55.5 MB of N-Quads), minimum CPU time of 5 runs
of `l4factoidal parse`: 4.60 s before and 4.39 s after for N-Triples, 6.12 s and 6.33 s for N-Quads. The hash of
every term in the key of a hash map is now a call of `Term.hashFast`, and the time did not change by more than the
noise.

*Checks (2026-10-15).*

- `lake build` (default targets) on the tree after the rebase on issue 866: 1,725 jobs, exit 0. A build after the
  last edit of a docstring: the 965 C files (one hash over all of them) and the six binaries that the checks use
  are the same as before.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of 1,372 lines, 4 marked `(a) PENDING`,
  502 marked `UNTRIAGED`; the audit lists `readObject12`, `Term.toNTriples`, `Term.joinKey` and `Term.lowerTags` as
  `replaced`, and their four lines are out of the allow list; the line of the derived hash is marked `(s)`). The C of
  `readObject12Down`, `closeObject12`, `Term.toNTriplesLoop`, `Term.joinKeyLoop`, `Term.lowerTagsLoop`,
  `wrapTripleTerms`, `Term.hashDown` and `hashClose` has one `goto _start` each and no call of itself.
  `python3 tools/lean-unbuilt-modules.py --gate`: exit 0, 794 modules, 0 not reached.
  `tools/lean-hygiene-audit.py --build-log`: clean (6,185 `#print axioms` outputs in the logs of the builds of this
  change). `tools/test_lean_tail_recursion_audit.py`: 12 pass, 0 fail (out of 12).
- `tests/sbm11/run.sh`: 2,823 pass, 0 fail, 30 expected-fail (out of 2,853); 555 of them are the quad-source tests
  of issue 866. `tests/sbm11/census.sh`, `tests/delta-log/run.sh` (46 pass, 0 fail) and `tests/sbm11/threads.sh`
  (all answers identical): exit 0.
- `tests/stack/run.sh --canary` (private `STACK_FIXTURES`, with a wasm module built from this tree): 161 pass,
  0 fail (out of 161); 5 expected failures (issues 816 and 817), none for issue 867. The canary control passed.
- `tests/stack/lean_scaling.py --only` the new row and `rdfs-closure-wideflat`, `rdfs-closure-dense`,
  `rdfs-closure-tree`, `trig-parse`, `trig-big-graph`, `turtle-object-list`, `turtle-serialize`, `rdfc-person`,
  `count-distinct`, `select-star`, `sparql-update-insert`, `query-vs-parse`, `sbm11-export-nq-time`,
  `sbm11-dump-time`, `turtle-nest-time`, `turtle-read-prefixes` and `owlrl-closure-cl`: 18 pass, 0 fail,
  0 expected-fail (out of 18).
- `formal/lean4/Wasm/cli-smoke.sh`: 106 pass, 0 fail, 0 xfail (out of 106).
  `formal/lean4/Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out of 366).
- `npm test` in `npm/factoidal`: 442 pass, 0 fail, 1 skipped (out of 443). `node --test
  tests/hub/*_test.mjs`: 447 pass, 0 fail (out of 447).
- `tests/known-defects/run.sh` in the CI layout (one directory with `factoidal`, `owl_runner`, `l4factoidal` and
  `l4w3c`): 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

**The serialising operations read triple terms (2026-10-15).** Tracking:
https://github.com/danbri/factoidal/issues/870. `serializeNQuads`, `serializeTurtle` and
`serializeTurtleWith` read their N-Quads argument with `parseNQuadsFast nq`. The default
mode of that function is RDF 1.1, and the RDF 1.1 reader refuses `<<(`. So the three
operations answered "invalid character in IRIREF (offset N)" for any triple term.
`l4factoidal parse FILE --out turtle` did the same: it reads the canonical N-Quads of its
dataset the same way, through `Ops.serializeTurtleTextOf`, which `serializeTurtleTextOf_eq`
ties to `serializeTurtle`. The operations that read RDF 1.2 (`parseToDatasetJson` with a
`*12` tag, `queryDataset`, `updateDataset`) and the other `--out` writers were not
affected. Of the 16 pairs of reader and writer that can hold a triple term (N-Triples 1.2,
N-Quads 1.2, Turtle 1.2 and TriG 1.2, each written as N-Quads, N-Triples, Turtle and TriG),
12 passed and the 4 with `--out turtle` failed. The cases of `Wasm/cli-smoke.sh` and
`Wasm/native-smoke.sh` were expected failures that name the issue, in the commit before the
repair.

The RDF 1.2 reader is not a superset of the RDF 1.1 reader. Each row was measured with
`parseToDatasetJson`, tags `nquads` and `nq12`:

| Text | RDF 1.1 reader | RDF 1.2 reader |
| --- | --- | --- |
| `<<( s p o )>>` as an object | refuses | reads |
| `"x" @en`, `"1" ^^ <dt>` (white space before `@` or `^^`) | refuses | reads |
| `"x"@en--ltr` | reads the language tag `en--ltr`, no direction | reads the language tag `en` and the direction `ltr` |
| `"x"@abcdefghijk` (a subtag of 11 characters), `"x"@en-` | reads | refuses |
| `"x"@en--xyz`, `"x"@en--LTR` | reads | refuses |

So the three operations read the text as RDF 1.2 and, when the RDF 1.2 reader refuses it,
as RDF 1.1: `parseNQuadsFast12Or11` in `L4Factoidal/RDF/DatasetNormalize.lean`. A text that
either reader accepts is accepted (`parseNQuadsFast12Or11_accepts_rdf11`). A text that both
refuse gets the error of the RDF 1.1 reader, the error these operations gave before
(`parseNQuadsFast12Or11_error`). The RDF 1.2 reader goes first. It reads a text of RDF 1.1
syntax in one pass, and a dataset that passes `roundTripSafe .rdf12` takes the
normalisation with no text round trip. `datasetForOps12Or11` is `datasetForOps` for these two
readers. `datasetForOps12Or11_eq` proves it equal to the text round trip of
`parseNQuadsFast12Or11` for every dataset, so `serializeTurtleTextOf_eq` still holds. A dataset
that passes the RDF 1.1 check gets the dataset that `datasetForOps .rdf11` gave
(`roundTripSafe_rdf11_rdf12`, `datasetForOps12Or11_of_safe11`). The theorems depend on
`propext`, `Classical.choice` and `Quot.sound` only (`#print axioms` in
`DatasetNormalizeTests.lean`).

*Same output as before, and what changed (2026-10-15).* The old build (commit e98ec076) and
the new build ran on the same inputs; the standard output, the standard error and the exit
status were compared.

| Input | Runs | Identical | Changed |
| --- | ---: | ---: | ---: |
| `l4factoidal parse FILE --out turtle`: the 5,997 N-Triples, N-Quads, Turtle and TriG files under `third_party/testing` and `tests`, each in the RDF 1.1 and the RDF 1.2 mode | 11,994 | 11,712 (8,749 with exit 0; 2,963 the same error) | 282 |
| `l4wasm-cli callseq`: `serializeNQuads`, `serializeTurtle` and `serializeTurtleWith` on the 2,017 N-Triples and N-Quads files as they are (one file that is not UTF-8 is skipped) | 6,048 | 5,706 (5,292 ok; 414 the same error) | 342 |
| the same three operations on the canonical N-Quads of each of the 4,658 files that the RDF 1.2 reader reads | 13,974 | 13,128 | 846 |

Each changed run was an error before and exit 0 (ok) now. The 282 changed runs of the command
line are 282 RDF 1.2 files; the old error was "invalid character in IRIREF" in all 282, and the
Turtle text now reads back with the RDF 1.2 Turtle reader as the same set of quads as the
N-Triples text of the dataset, 282 of 282. The 342 changed runs of the operations are 114
files: 110 with a triple term (the old error "invalid character in IRIREF") and 4 with white
space before `@` or `^^` (the old error "expected '.' terminator"). The 846 are 282 files, the
same 282 as the command line's; `serializeTurtle` on the canonical text is the output of
`parse FILE --out turtle` for 282 of 282, byte for byte. The 2,963 runs of the command line that
still exit 1 fail at the read of the file: `--out nquads` fails on the same 2,963. Time of
the operations, 120,000 quads (11.2 MB) of RDF 1.1 syntax, minimum user CPU time of 5 runs: 1.87 s
before and 1.79 s after for `serializeNQuads`, 3.50 s and 3.52 s for `serializeTurtle`; the peak
resident set is 624 MB in both.

*Checks (2026-10-15).*

- `formal/lean4/Wasm/cli-smoke.sh`: 130 pass, 0 fail, 0 xfail (out of 130); before the repair 126 pass,
  0 fail, 4 xfail (out of 130). The new cases: D4 read in four syntaxes (N-Triples 1.2, N-Quads 1.2,
  Turtle 1.2, TriG 1.2) and written in four (N-Quads, N-Triples, Turtle, TriG), 16 pairs, each read back to
  the same 5 quads (3 with a triple term, one nested two deep, one with a base direction); a triple term
  in a named graph through N-Quads 1.2 to N-Quads and TriG. `formal/lean4/Wasm/native-smoke.sh`: 369
  pass, 0 fail, 0 xfail (out of 369); before the repair 366 pass, 0 fail, 3 xfail (out of 369): the
  three operations on a triple term one level deep, one nested two deep, and a base direction.
- Build-time `#guard`s: `Wasm/Ops/Parse.lean` (the three operations on a triple term, on white space
  before `@`, on a tag that only the RDF 1.1 reader reads, on a text that both refuse) and
  `RDF/DatasetNormalizeTests.lean` (`datasetForOps12Or11` and `parseNQuadsFast12Or11` on the same
  cases, with `dsLongTag` for the second reader and `dsIriSpace` for the error).
- `npm test` in `npm/factoidal`: 443 pass, 0 fail, 1 skipped (out of 444); the new test of
  `serialize(..., {format: 'turtle', inputFormat: 'nt12'})` fails against the wasm module of the old
  build with "invalid character in IRIREF (offset 29)". `node --test tests/hub/*_test.mjs`: 447 pass,
  0 fail (out of 447).
- `lake build` (default targets): 1,725 jobs, exit 0. `python3 tools/lean-unbuilt-modules.py --gate`: exit
  0, 794 modules, 0 not reached. `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of
  1,372 lines, 4 marked `(a) PENDING`, 502 marked `UNTRIAGED`). `tools/lean-hygiene-audit.py --build-log`:
  clean (1,661 `#print axioms` outputs in the logs of the builds of this change).
- `tests/sbm11/run.sh`: 2,823 pass, 0 fail, 30 expected-fail (out of 2,853). `tests/sbm11/census.sh`,
  `tests/delta-log/run.sh` (46 pass, 0 fail) and `tests/sbm11/threads.sh` (all answers identical): exit 0.
  `tests/stack/run.sh --canary` with a wasm module built from this tree: 161 pass, 0 fail (out of 161).
  `tests/known-defects/run.sh`: 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

**Costs open.** The RDF/XML and JSON-LD writers keep the dataset
(https://github.com/danbri/factoidal/issues/846 and
https://github.com/danbri/factoidal/issues/847) and take time quadratic in the
dataset (https://github.com/danbri/factoidal/issues/845 and
https://github.com/danbri/factoidal/issues/712). The JSON-LD writer uses native
stack in proportion to the number of elements: one node with 20,000 references
overflows a 512 KB stack (https://github.com/danbri/factoidal/issues/853, row
`JLD-WSTACK` of `tests/known-defects/run.sh`, which writes through `l4factoidal
parse --out jsonld`). The stream writers (N-Triples,
N-Quads, Turtle, TriG) and the RDF/XML export of 100,000 references run under a
512 KB stack; the case `sbm11-export` of `tests/stack/run.sh` exports 600,001
quads with a 300,000-byte literal in three syntaxes under that stack. The batch
Turtle writer writes 100,000 triples in two shapes under that stack too (the
paragraph on https://github.com/danbri/factoidal/issues/863 above), and a table of 100,000
prefixes and a triple term nested 300,000 deep (the paragraph on
https://github.com/danbri/factoidal/issues/864 above). No theorem relates the stream
writers to the batch writers: the round trip through the store is their check
(https://github.com/danbri/factoidal/issues/852, probes SK-1 and SK-2 of
`tests/known-defects/run.sh`, which turn the run red when a theorem of the
expected name is added).

## 3a. Recovery (lenient) mode

Issue: https://github.com/danbri/factoidal/issues/716. Owner, 2026-10-10,
verbatim: "#716 is important for building validators and for streaming huge
datasets through a parser".

Landed 2026-10-10 on `claude/wt-lenient-parse`. Before it, every Lean parser
in sections 2 and 3 stopped at the first error; the F\* npm entry's
`parseDocument` recovered per statement but reported only the first error.

### 3a.1 The diagnostic

`Syntax/Diagnostics.lean`. A `Diagnostic` has a class, the grammar's
message, an `offset` (0-based, Unicode scalar values from the start of the
document: the strict `ParseError.pos`), a `line` (1-based; a line ends at
LINE FEED, so CR LF is one line end and a lone CR is not one) and a `column`
(1-based, Unicode scalar values). The line convention is the one of the
strict error envelope (`Wasm/Ops/Parse.lean`, `lineColumnOfOffset`) and of
the F\* entry, so the first diagnostic of a lenient parse names the line and
column a strict parse names.

`DiagnosticClass` has 16 constructors; `tag` gives the stable JSON name:
`undefined-prefix`, `relative-iri`, `bad-iri`, `bad-escape`,
`unterminated-string`, `bad-literal`, `bad-blank-node`, `bad-prefixed-name`,
`bad-directive`, `bad-graph-name`, `rdf12-syntax`, `unclosed-group`,
`nesting-limit`, `unexpected-token`, `internal`, `too-many-errors`. The class
is decided from the grammar's message (`classifyParseMessage`), so the strict
parsers, their messages and their theorems are unchanged; a `#guard` pins the
class of every message literal in `Lexing`, `NTriples`, `NQuads`, `Turtle`
and `TriG`. "expected prefixed name" is `unexpected-token`: the Turtle readers
fall back to a prefixed name for any token they cannot read otherwise, so the
message reports a missing term.

`LenientOptions.maxErrors = some m`: the error after the `m`-th is reported
as one `too-many-errors` diagnostic (its position, the next error's message)
and the parse stops.

### 3a.2 Executions and synchronisation

| Syntax | Reference lenient | Streaming lenient | Synchronisation |
| --- | --- | --- | --- |
| N-Triples, N-Quads | `NQuadsLenient.lean`: `foldLinesLenient` (one walk, statement reader as a parameter), `parseNTriplesLenient`, `parseNQuadsLenient`, `parseNQuadsFastLenient` | `LenientStream` (cuts after the last line feed with `splitCompleteLines`, as `feedChunkC`; keeps the partial line last character first, section 3b.8) | the end of the line on which the failing statement started (`skipToEol`, `skipEol`) |
| Turtle | `TurtleLenient.lean`: `parseStatementsLenient`, `parseTurtleLenient(WithPrefixes)` | `TurtleChunkLenientState` (the `TurtleChunkFold` walk; each scanner candidate is walked by `parseStatementsLenient`) | the first `TurtleStatementScan` cut at or after the error offset, found by a fresh scanner run from the start of the failing statement (`turtleResync`) |
| TriG | `parseTriGStatementsLenient` (the `FastDataset` accumulator of the strict walk), `parseTriGLenient(WithPrefixes)` | none (as for strict TriG, section 3) | strict `readTriGStatement` first; a failing graph block is read again by `readTriGBlockRecover`, which resumes inside the body at a scanner cut or a normal-mode `}` at or after the error; any other failure resumes as Turtle |

Each lenient walk has the strict walk's branches and differs only in the
error arm. The `TurtleState` after a failing statement is the one before it,
so a prefix whose `@prefix` failed stays undefined and each later use of it
gets its own `undefined-prefix` diagnostic. A statement that starts with a
directive keyword is reported with the directive reader's own error
(`directiveError`; `readStatement` swallows it and reports "expected
subject"). `VERSION` in an RDF 1.1 document is `rdf12-syntax`.

Line state (`LinePos`) changes only at a line feed. The N-Triples and N-Quads
walks advance it only over the characters `skipEol` consumes (no token,
white space run or comment of those grammars holds a raw line break), so line
tracking costs a constant per line; the Turtle walks advance it over each
statement. Diagnostics go to a caller-supplied consumer (`report`); the
streaming states hand each chunk's diagnostics out with `takeDiags`, so
nothing accumulates them across chunks.

`LenientFeed.lean` is the byte-chunk driver the CLI runs: UTF-8 decoding
across reads (`Utf8Stream`), the streaming walk, and for Turtle the
generated blank-node prefix from a first pass (`LenientPrepass`), as the
shard packer does.

### 3a.3 Theorems

All proved, axioms `propext`, `Classical.choice`, `Quot.sound` only:

- `NQuadsLenientTheorems.lean`: `foldLinesLenient_quad_of_ok` and
  `_triple_of_ok` (strict success ⇒ the lenient walk gives the strict result
  and reports nothing, for every triple consumer and every diagnostic
  consumer); `foldLinesLenient_rel` (a step-wise consumer relation is
  preserved); `parseNTriplesLenient_of_ok`, `parseNQuadsLenient_of_ok`,
  `parseNQuadsFastLenient_of_ok` (`parseX s = .ok d → parseXLenient s =
  (d, [])`); `parseNQuadsFastLenient_eq` (indexed accumulator = reference
  accumulator, lenient mode); the converse
  `parseNTriples_ok_of_lenient_quiet` and `parseNQuads_ok_of_lenient_quiet`
  (no diagnostic ⇒ the strict parser accepts).
- `TurtleLenientTheorems.lean`: `parseStatementsLenient_of_ok`,
  `parseTriGStatementsLenient_of_ok`, `parseTurtleLenient_of_ok`,
  `parseTurtleLenientWithPrefixes_of_ok`, `parseTriGLenient_of_ok`,
  `parseTriGLenientWithPrefixes_of_ok`; the converse
  `parseTurtle_ok_of_lenient_quiet` and `parseTriG_ok_of_lenient_quiet`
  (through `TurtleLenientRun.Grew`: a recovered TriG graph block that changed
  the error count or the stop flag added a diagnostic).

So for all four syntaxes the lenient parse reports nothing exactly when the
strict parser accepts, and then returns the strict result; every document
the strict parser refuses gets at least one diagnostic. None of the
hypotheses mentions a lenient walk (anti-pattern 29).

Not proved: streaming lenient = reference lenient. The differential checks
are (1) `#guard`s at every two-way split and with one-character chunks
(`NQuadsLenient.lean`: 5 documents; `TurtleLenient.lean`: 7 documents;
`LenientFeed.lean`: every byte-chunk size from 1 to 12 over documents with
two-byte characters), comparing triples and diagnostics whole, and (2) the
W3C gate below, which runs the streaming walk over 5-character chunks on every
Turtle, N-Triples and N-Quads test file. The strict Turtle streaming walk has
no chunk-boundary theorem either (2.3). One case where the two can differ: a
candidate that the scanner cuts at a `PREFIX`/`BASE` line end while the
grammar reads past it (the same case where strict streaming and strict
reference differ).

### 3a.4 Gates

`lake exe l4w3c --lenient <manifests>` (`Harness/LenientRun.lean`): a positive
syntax or evaluation test passes when the lenient parse reports no
diagnostic and returns the strict result; a negative syntax test passes when
it reports at least one diagnostic; for Turtle, N-Triples and N-Quads the
streaming walk over 5-character chunks must agree with the reference walk.
2026-10-10, `l4w3c --quiet --lenient`: RDF 1.1 Turtle 313 pass, 0 fail (out
of 313); N-Triples 70 pass, 0 fail (out of 70); N-Quads 87 pass, 0 fail (out
of 87); TriG 357 pass, 0 fail (out of 357); RDF 1.2 Turtle syntax 74 pass, 0
fail (out of 74) and eval 32 pass, 0 fail (out of 32); N-Triples syntax 29
pass, 0 fail (out of 29); N-Quads syntax 27 pass, 0 fail (out of 27); TriG
syntax 35 pass, 0 fail (out of 35) and eval 26 pass, 0 fail (out of 26).
TOTAL 1050 pass, 0 fail (out of 1050), of which 358 are negative syntax
tests. (With the two RDF 1.2 c14n manifests added to the same run, their 82
tests are `skip`: they are not syntax tests.) The same after the merge with
`c8dbe2ab`.

The strict suites (`l4w3c --quiet`, the same manifests plus the RDF 1.2
N-Triples and N-Quads c14n manifests) are unchanged: 1132 pass, 0 fail (out
of 1132) before and after, line for line. `Wasm/native-smoke.sh`: 288 pass,
0 fail (out of 288), six of them new `parseDocument` checks (282 pass, 0 fail
(out of 282) at the branch point). After the merge with `c8dbe2ab`, the same
numbers, and `tests/stack/lean_scaling.sh` 12 pass, 0 fail (out of 12).

### 3a.5 Surfaces

- Dispatch op `parseDocument(text, formatTag, baseIRI, optionsJson)`
  (`Wasm/Ops/Lenient.lean`), `{"lenient":true,"maxErrors":n}`: the F\*
  entry's envelope plus `diagnostics: [{message, offset, line, column,
  class}]`; not lenient = `parseToDatasetJson`. RDF/XML and JSON-LD parse
  strictly, as in the F\* entry.
- npm: `l4-core.js` wires `parseDocument`, so `capabilities().parseDiagnostics`
  is `true` and `parse(text, {lenient: true, maxErrors})` returns a Dataset
  with `diagnostics`.
- CLI: `l4factoidal parse --lenient FILE [--format F] [--base IRI]
  [--max-errors N] [--out nquads]` streams the file in 65,536-byte chunks and
  writes each diagnostic as one JSON line to stderr before reading the next
  chunk; exit status 1 when any diagnostic was written. TriG and stdin are
  read whole.

### 3a.6 Scaling and the strict path's speed

`tests/stack/lenient_scaling.sh 250000 1000 "nquads turtle"` (2026-10-10, this
branch merged with `c8dbe2ab`, on a shared 4-CPU host; CPU time is user +
system seconds, memory is the peak resident set from `/usr/bin/time -v`). One
malformed statement every 1,000, five kinds in rotation; every run reported
exactly one diagnostic per malformed statement and kept every other
statement. Streaming path: `l4factoidal parse --lenient FILE`.

| Syntax | Statements | Bytes | CPU s | Peak RSS KiB | Diagnostics |
| --- | ---: | ---: | ---: | ---: | ---: |
| N-Quads | 250,000 | 25,111,204 | 3.87 | 27,196 | 250 |
| N-Quads | 500,000 | 50,412,081 | 7.78 | 26,880 | 500 |
| N-Quads | 1,000,000 | 101,292,441 | 13.98 | 27,172 | 1,000 |
| N-Quads | 2,000,000 | 204,219,345 | 28.56 | 27,308 | 2,000 |
| Turtle | 250,000 | 21,186,597 | 4.88 | 23,196 | 250 |
| Turtle | 500,000 | 42,562,799 | 10.29 | 23,284 | 500 |
| Turtle | 1,000,000 | 85,593,803 | 19.85 | 23,092 | 1,000 |
| Turtle | 2,000,000 | 172,821,992 | 45.29 | 21,616 | 2,000 |

Time doubles with the input (ratios N-Quads 2.01, 1.80, 2.04; Turtle 2.11,
1.93, 2.28) and peak memory does not move (N-Quads 26.9 to 27.3 MB from 25 MB
to 204 MB; Turtle 21.6 to 23.3 MB from 21 MB to 173 MB). The script checks
the counts, time(2x) at most 2.6 times max(time(x), 1 s), and peak(8n) at
most 1.25 times peak(n) plus 64 MiB: 16 pass, 0 fail (out of 16). A run of
the same script before the merge (pre-merge binary, more load on the host)
gave N-Quads 3.21, 6.46, 13.26 and 27.54 s at 41.5 to 41.8 MB and Turtle
5.10, 9.47, 18.82 and 37.67 s at 35.6 to 37.7 MB, also 16 pass, 0 fail (out
of 16). The Turtle times include the blank-node pre-pass, a first read of
the whole file.
For comparison, the strict reference parse of 101,331,473 bytes of N-Quads
through `l4factoidal parse` (which builds the whole `List Char`, the whole
dataset and its canonical N-Quads) used 8,278,248 KiB.

The strict parsers are not changed by this work (the lenient walks are new
functions beside them). Measured anyway, `l4factoidal parse FILE --format F`
under `/usr/bin/time -v`, runs interleaved, user CPU seconds:

| Input | Before | After | Change |
| --- | --- | --- | --- |
| N-Quads, 101,331,473 bytes (1,000,000 quads), branch point `fefe9088` vs this branch before the merge | 28.47, 28.40 | 28.58, 29.01 | +1.3 % |
| the same, `core-split` `c8dbe2ab` vs this branch merged with it | 14.82, 15.35 | 14.20, 15.05 | -3.0 % |
| Turtle, 103,052,745 bytes (1,800,000 triples), `c8dbe2ab` vs merged | 17.78, 17.69 | 16.94, 17.41 | -3.2 % |

Peak memory is the same before and after in each pair (8.28 GB, 3.89 GB and
3.95 GB; the drop between the first and second pair is `c8dbe2ab`'s change to
`parse`, which no longer writes the dataset as N-Quads text). The differences
are within the run-to-run spread on a host shared with other builds. The
`c8dbe2ab` binary was built in another worktree at `cd56fe9a`, which
differs from `c8dbe2ab` only in `CLAUDE.md`.

TriG has a chunk walk for the shard packer only (section 3e); `l4factoidal parse --lenient` reads a TriG
file whole and runs the reference walk, whose memory grows with the input.
After the 2026-10-10 repair of the strict TriG reader (linear; it was
quadratic, `docs/designissues/2026-10-10-lean-vs-fstar-performance.md`) the
lenient TriG walk, which runs that reader, is linear too: 25,000, 50,000,
100,000 and 200,000 statements (10 per graph block, one bad in 500;
1,681,242 to 13,822,892 bytes) took 0.72, 1.32, 2.77 and 5.43 s of CPU and
141, 265, 513 and 987 MB peak.

## 3b. The strict command line reads a file in chunks (2026-10-13)

Issue: https://github.com/danbri/factoidal/issues/813 (key result of
objective O2 of https://github.com/danbri/factoidal/issues/768). Before this
change `l4factoidal parse FILE [--out nquads]` read the whole file into one
`String` and gave it to `Ops.parseTextToDataset`; the state-of-the-art table
(`2026-10-12-sota-reference.md`) measured 33 to 35 bytes of peak resident
memory per input byte, where the streaming reader of the same binary
(`--lenient`) held 24 MB at every size.

### 3b.1 Where the memory and the time went (before)

`l4query-phases FILE --parse-cli --format F --stop-after PHASE` runs the
phases of the old `parseCmd` one at a time (`Harness/QueryPhases.lean`) and
prints the resident set after each. Native binary of `d371f1d9`, load
average 8 on 4 CPUs, one run per phase. Time is milliseconds since the
process started; RSS and peak in MB.

N-Triples, 100,000 triples, 8,077,780 bytes (`nt-100000.nt` of
`tools/sota-bench.py`):

| Phase | What it holds | ms | RSS after | Peak so far |
| --- | --- | ---: | ---: | ---: |
| start | the process | 0 | 12.6 | 12.6 |
| read | the file as one `String` | 34 to 69 | 29.0 | 29.0 |
| chars (alone) | the whole document as a `List Char` | 952 | 264.6 | 303.9 |
| parse | `parseNTriples`: the `List Char` plus the graph | 605 to 644 | 264.6 | 303.9 |
| normalize (count) | `normalizeDataset`, the set of distinct triples | 825 | 61.4 | 303.9 |
| nquads (`--out`) | `Dataset.toCanonicalNQuads`, one 8 MB `String` | 692 | 59.2 | 304.1 |
| output | written | 692 | 42.9 | 304.1 |

Turtle, 20,000 paragraphs of `gene.ttl`, 87,468 triples, 1,706,149 bytes:

| Phase | What it holds | ms | RSS after | Peak so far |
| --- | --- | ---: | ---: | ---: |
| start | the process | 0 | 12.5 | 12.5 |
| read | the file as one `String` | 5 | 16.6 | 16.6 |
| chars (alone; the Turtle path does not build it) | `List Char` | 58 | 65.9 | 74.2 |
| parse | `parseTurtleText` (the scanner walk over the `String`): the graph | 369 to 391 | 37.4 | 37.4 |
| normalize (count) | the set of distinct triples | 553 | 48.1 | 49.6 |
| nquads (`--out`) | the 11.4 MB N-Quads `String` | 405 | 68.1 | 68.1 |
| output | written | 406 | 43.6 | 68.1 |

So for N-Triples (and N-Quads) the peak was the document's `List Char`:
256 MB of 304 MB, 32 bytes per input byte, and 0.9 s of the time (most of it
system time to fault in the pages). For Turtle the peak was the dataset and
the output `String` together. The count added the set of distinct triples to
the dataset.

### 3b.2 The chunked execution

`L4Factoidal/Syntax/StrictFeed.lean`, called by `streamStrictFile` in
`Wasm/Cli.lean`. The file is read in 65,536-byte chunks (`forChunks`), each
decoded by `Utf8Stream`:

| Syntax | Walk | `--out nquads` | Count |
| --- | --- | --- | --- |
| N-Triples | `LineFeed` with `tripleReader`: the complete lines of each chunk (`splitCompleteLines`) through `foldLines`, the five branches of `parseLinesAcc` with the reader as a parameter; the partial last line and the absolute offset are carried | each chunk's triples are written (`chunkText`) and dropped | `countQuad` into a `FastDataset`: the step of `normalizeDataset` (language tags in lower case, §3.3; one entry per distinct triple, §3) |
| N-Quads | `LineFeed` with `quadReader` | `addQuadFast` into a `FastDataset` (the accumulator of `parseNQuadsFast`), written at the end: the canonical form groups the quads by graph and keeps each quad once, so the set is needed | the same set, then `normalizeDataset` |
| Turtle | a pre-pass (`TurtlePrepass`: the generated blank-node prefix and `hasDoubleLt` of the whole file), then the scanner walk of `parseTurtleWalk` one character at a time (`turtleFeed`) | after each chunk the walk's accumulator is written and emptied | `countQuad` per chunk |

The text, the `List Char` of the document, the dataset (except where the
output needs the set) and the output `String` are never built. What a run
keeps between chunks: the walk's state (prefixes, base, the unfinished line or
candidate, the offset), the UTF-8 decoder's last bytes, and the consumer's
state.

The whole-file path (`strictWhole`, which is the code before the change) is
used when a streamed run cannot give today's answer by itself:

- standard input (`-` or no file) and every other syntax (TriG, RDF/XML,
  JSON-LD) and `--out turtle`: as before;
- a Turtle document that contains `<<` (as in `parseTurtleText`);
- a Turtle document the walk refuses: the file is read whole and given to
  `Ops.parseTextToDataset`, so every Turtle error is `parseTurtle`'s, as
  `parseTurtleText_error` states for the in-memory path. When `parseTurtle`
  accepts a document the walk refused (a `PREFIX` directive cut at a line end,
  2.3), the lines already written are the walk's first triples; the command
  line checks that they are the first triples of the reference graph
  (`StrictFeed.walkPrefix`) and writes the rest, or reports an internal error
  (exit 1);
- bytes that are not UTF-8: `readInput` reports them as before.

The N-Triples and N-Quads errors are the line walk's own: the same reader on
the same line, with the absolute offset. On an error the lines of the chunks
before it are already on standard output (a streamed parse writes each chunk
before it reads the next); the message, the offset and the exit status are
the ones before the change.

### 3b.3 Theorems

All in `StrictFeed.lean` and `TurtleChunkFold.lean`; axioms `propext`,
`Classical.choice`, `Quot.sound` at most.

- `foldLines_quadReader`: `foldLines (quadReader mode)` is
  `foldQuadLinesAcc mode`, so `LineFeed.feed_quad11` is one step of
  `NQuadsFold.feedChunkC` and `LineFeed.run_quad11_eq_batch` holds: a chunked
  N-Quads (RDF 1.1) run that succeeds gives the whole document's fold, from
  `streamConsume11_eq_batch` (section 3). The N-Quads output is that fold with
  `addQuadFast`, which is `parseNQuadsFast`.
- `parseLinesAcc_eq_foldLines`, `parseNTriples_eq_foldLines`: the N-Triples
  reference is `foldLines (tripleReader mode)` with a list consumer.
- `turtleFeedChunks_eq`, `turtleFeed_eq_walkChars`, `walkChars_eq_foldl`:
  the characters of the decoded chunks go through the walk's step in order;
  the chunking does not enter.
- `TurtleChunkFold.walk_drain`, `finish_drain` (from `consumeText_map`,
  `consumeCandidates_map`, `feedChar_map`, `finish_map`, `walkChars_map`: the
  walk passes its accumulator only to `step`, so a map that commutes with
  `step` commutes with the walk) and `StrictFeed.drainRun_eq`: emptying the
  accumulator after each chunk and writing what it held writes exactly the
  triples of the walk of the concatenated chunks, in order, and fails exactly
  when that walk fails.
- `TurtlePrepass.feedText_chunks`: the pre-pass over chunks gives
  `freshBnodePrefixText` and `hasDoubleLt` of the concatenation.
- `normalizeDataset_default`, `toCanonicalNQuads_default`, `chunkText_eq`:
  the count and the written text are the ones of the whole-file path for a
  dataset with one default graph.
- `isIri_eq_isIriFast` (`NTriples.lean`, `@[csimp]`): section 3b.5.

Not proved, four equalities, tracked by
https://github.com/danbri/factoidal/issues/826 with one expected failure
each in `tests/known-defects/run.sh` (rows SF-1 to SF-4: XFAIL while no
theorem of the name exists under `formal/lean4`, XPASS, which fails the
suite, when one lands). SF-1, `walkAll_init_eq_parseTurtleWalk`: that
`walkAll` (the walk `drainRun_eq` speaks of) from the
initial state is `parseTurtleWalk`. `TurtleChunkFold.walkChars` writes out the
fold of `parseTurtleWalk` with the same step text, but `rfl` does not close the
equation, because the two `match` expressions elaborate to different auxiliary
matchers; `#guard`s in `StrictFeed.lean` compare them on accepted and refused
documents. SF-2, `LineFeed.run_triple_eq_batch`: the N-Triples chunk boundary
(a line walk over the lines of each chunk equals the walk over the whole text,
errors included; the N-Quads RDF 1.1 success direction is
`streamConsume11_eq_batch`). SF-3, `LineFeed.run_quad12_eq_batch`: the N-Quads
RDF 1.2 case. Not proved either, and inside SF-2 and SF-3 as stated in the
issue: the N-Triples and N-Quads error at a chunk boundary. SF-4,
`Utf8Stream.feedChunks_eq_fromUTF8`: that the Utf8Stream decoding of the
chunks concatenates to the text `readInput` reads. The Turtle walk itself
against `parseTurtle` is the chunk-boundary half of 2.3, also not proved. The
check for all of these is `tools/strict-parse-differential.sh` (3b.4).

### 3b.4 The differential check

`tools/strict-parse-differential.sh OLD NEW` runs `parse FILE --format F
--out nquads` and `parse FILE --format F` (the count) on every `.nt`, `.nq`
and `.ttl` file of the W3C RDF 1.1 and 1.2 suites (RDF/XML excluded; the RDF
1.2 files also in the RDF 1.2 mode), with and without `--base`, by the binary
before the change (OLD, `d371f1d9`) and after it (NEW). NEW runs three times
per case, with the built-in 65,536-byte chunks and with
`L4_STRICT_CHUNK_BYTES=7` and `=1`, so in the small W3C files every line and
statement boundary also falls across a chunk boundary. It then runs
generated files of several chunks each, which put errors and directives past
the first chunks (N-Quads over 50 graphs with repeated quads and language
tags in two cases, and with a malformed line at line 120,000; a malformed
Turtle statement, and a `PREFIX` directive whose IRI is on the next line,
in the middle of 20,000 gene.ttl paragraphs and at the start; an unterminated
N-Triples string at line 50,000). A case agrees when the exit status and
standard error are the same and, when OLD succeeds, standard output is the
same byte for byte.

Result, 2026-10-13, OLD `d371f1d9` against the final binary of this change:
21,012 agree, 0 differ (out of 21,012 cases: 6,992 W3C cases at each of the
three chunk sizes, and 36 generated; OLD succeeded in 14,562 and refused in
6,450). The W3C files are smaller than one 65,536-byte chunk, so the 7-byte and
1-byte runs and the generated files are the ones that cross chunk
boundaries.

The largest inputs of the state-of-the-art table, compared by hand the same
way (both outputs and the count): `nt-400000.nt`, `mixed-nt-400000.nt`,
`gene-80000.ttl`, `ttlrich-400000.ttl`: 8 of 8 the same.

### 3b.5 After: memory and time, and the speed repair

`tools/sota-bench.py`, same host, median of 3 runs, load average 6 to 7 on 4
CPUs (the parse rows) and 28 to 31 (the count rows, measured again after the
repair of 3b.6); wall time (CPU time), peak resident set. Serd 0.32.2 and
Oxigraph 0.5.11 from the same run as the parse rows.

| Row | Before (`e3c3aa01`, SOTA record) | After | Serd | Oxigraph | After / fastest reference: time; memory above process start |
| --- | --- | --- | --- | --- | --- |
| N-Triples 100,000, `--out nquads` | 0.91 s (0.85 s), 306 MB | 0.50 s (0.41 s), 24.3 MB | 0.16 s (0.09 s), 1.9 MB | 0.19 s (0.13 s), 23.2 MB | 3.1; 4.8 |
| N-Triples 400,000, `--out nquads` | 2.97 s (2.80 s), 1,186 MB | 1.95 s (1.75 s), 24.2 MB | 0.44 s (0.28 s), 1.9 MB | 0.65 s (0.50 s), 23.2 MB | 4.4; 4.7 |
| N-Triples mixed terms 400,000 | 3.52 s (3.29 s), 1,177 MB | 2.25 s (2.05 s), 24.1 MB | 0.47 s (0.33 s), 1.9 MB | 0.74 s (0.56 s), 23.2 MB | 4.8; 4.6 |
| Turtle gene.ttl 20,000 paragraphs (87,468 triples) | 0.54 s (0.48 s), 71 MB | 0.41 s (0.29 s), 25.6 MB | 0.12 s (0.06 s), 2.0 MB | 0.18 s (0.12 s), 23.4 MB | 3.6; 6.1 |
| Turtle gene.ttl 80,000 paragraphs (346,100 triples) | 1.95 s (1.71 s), 243 MB | 1.44 s (1.17 s), 25.6 MB | 0.48 s (0.27 s), 2.0 MB | 0.73 s (0.46 s), 23.3 MB | 3.0; 6.1 |
| Turtle, predicate and object lists, 457,136 triples | 3.01 s (2.82 s), 227 MB | 1.84 s (1.61 s), 25.6 MB | 0.56 s (0.32 s), 2.1 MB | 0.88 s (0.68 s), 23.4 MB | 3.3; 6.1 |
| Count, N-Triples 400,000 | 5.13 s (5.07 s), 1,186 MB | 5.66 s (3.28 s), 226 MB (load 31) | — | — | Jena `riot --count` 4.31 s (3.68 s), 224 MB: 1.3; 1.0 (peak resident set ratio) |
| Count, gene.ttl 80,000 paragraphs | 2.93 s (2.82 s), 163 MB | 3.98 s (2.32 s), 163 MB (load 29) | — | — | Jena 4.38 s (4.73 s), 298 MB: 0.91; 0.55 (peak resident set ratio) |

Memory above process start uses the recorded starts of the SOTA record
(Lean 19.5 MB, Serd 1.8 MB; a reference under 1 MB above its start counts as
1 MB), the rule of `tests/perf/sota_gate.sh`. So the two rows of issue 813's
expected failures, N-Triples 400,000 and gene.ttl 80,000, are now within 10
times the fastest reference in time (4.4 and 3.0) and in memory above process
start (4.7 and 6.1), and the gate's expected-failure marks are removed. The
count holds the set: 226 MB for 400,000 distinct triples, as much as Jena.
The streaming reader of the same binary (`--lenient`, which counts repeats)
holds 24 MB.

The time per triple. Callgrind on the streamed parse of 20,000 N-Triples
lines found `RDF.isIri` at 27 percent of the instructions: it builds
`s.toList` to look for one `:`. `NTriples.isIriFast` reads the string in place
(`String.contains`), and the `@[csimp]` theorem `isIri_eq_isIriFast` makes the
compiler call it in every parser: 1,030.5 to 774.6 million instructions for
the 20,000 lines (-24.8 percent), 183.1 to 152.1 million for 2,000 gene.ttl
paragraphs (-17 percent; 38 million of each are the process start). What the
774.6 million (38,700 per triple) are spent on: `readIriRef` 49 percent
(`iriNextStep`, one character of an IRI, 24), the chunk's `List Char`
(`String.toList`, `lean_string_data`) 15, allocation and release about 25.

### 3b.6 A cost paid during the work

The first count build took 9.16 s of CPU for 400,000 N-Triples lines and
0.97 s for 100,000. Two references kept the count's `FastDataset` shared
while the walk updated it, so `addQuadFast` copied its hash map at the first
quad of every 64 KiB chunk: `LineFeed.feed` read `st.pos` after the walk, and
the command line's chunk loop named the old line state `lf` in its error
branch, so the compiler emitted `lean_inc(lf)` before the call. After both
repairs: 2.86 s and 0.62 s of CPU at load 17. The skill
`lean4-performance` already named the first form (`feedChunkC`, 2026-10-12);
it now names both.

### 3b.7 Gates (2026-10-13, this change)

- `l4w3c` RDF 1.1: 1041 pass, 0 fail (out of 1041) before and after; RDF
  1.2: 1358 pass, 0 fail (out of 1358) before and after. The scoreboard rows
  of `l4w3c-rdf11`, `l4w3c-rdf12` and `l4turtle-probe`
  (`tools/lean-scoreboard.sh --only ...`) are identical before and after, logs
  line for line (the probe's one failure, `test-38.ttl`, is there before and
  after).
- `tools/strict-parse-differential.sh`: 21,012 agree, 0 differ (out of
  21,012) (3b.4).
- `tests/stack/lean_scaling.sh`: 27 pass, 0 fail, 3 expected-fail (out of 30),
  with the three new rows `parse-nt-memory`, `parse-ttl-memory` and
  `count-nt-memory`; those rows measured through `/usr/bin/time` after the
  harness defect of 3b.6 was found: 0.2, 0.0 and 6.2 bytes of peak resident
  set per input byte (bounds 1, 1, 12); on the binary before, 37.1, 30.2 and
  37.5, so they fail there.
- `tests/stack/lenient_scaling.sh`: 16 pass, 0 fail (out of 16).
- `tests/stack/run.sh --canary`: 87 pass, 0 fail (out of 87) with
  `STACK_TIMEOUT=300`. With the default cap of 120 s, at load average 20 to
  40, the `wasm manifest` case was killed at the cap once (86 pass, 1 fail
  (out of 87)); in the rerun it took 72.6 s and `native manifest` 115.1 s.
- `Wasm/cli-smoke.sh`: 83 pass, 0 fail (out of 83). `Wasm/native-smoke.sh`:
  353 pass, 0 fail, 2 expected failures (out of 355).
- `tests/perf/sota_gate.sh` (load average 14 to 41): the 36 rows of the parse
  and count workloads pass in the full run; issue 813's two expected-failure
  rows are plain assertions now. See the SOTA record, section 8, for the
  other rows.
- `tools/lean-tail-recursion-audit.py --gate`: pass, with one new allow line
  (`StrictFeed.drainRun`, a specification of the command line's loop used by
  `drainRun_eq` only). `tools/lean-hygiene-audit.py --build-log`: clean
  (partial def 163, baseline 163; every `#print axioms` line `propext`,
  `Classical.choice`, `Quot.sound` at most). Full `lake build`: exit 0
  (1635 jobs). WebAssembly module rebuilt (`NTriples.lean` changed); `npm
  test`: 413 pass, 0 fail, 1 skipped (out of 414).

### 3b.8 One line longer than a chunk (2026-10-15)

Tracking: https://github.com/danbri/factoidal/issues/869. `l4factoidal parse FILE` of a file of
N-Triples or N-Quads took time quadratic in the length of its longest line. The rows
`ntriples-long-line` and `nquads-long-line` of `tests/stack/lean_scaling.py` were expected failures that name
the issue, in the commit before the repair.

**Before.** One line of n bytes (a string literal), `parse FILE --format ntriples`, user CPU time of one run
(the rows of the harness take the minimum of 3 runs: 0.380 s, 2.40 s and 10.3 s at 2, 4 and 8 MB; N-Quads
0.375 s, 2.09 s and 10.6 s):

| n | 1 MB | 2 MB | 4 MB | 8 MB | 16 MB | 32 MB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| before, user CPU | 0.12 s | 0.41 s | 2.46 s | 11.28 s | 45.74 s (load average 11) | not run |
| after, user CPU | 0.05 s | 0.18 s | 0.32 s | 0.58 s | 1.00 s | 2.04 s |
| peak resident set, before and after | 55 MB | 86 MB | 149 MB | 276 MB | 531 MB | 1,030 MB (after) |

**Profile.** `perf record -F 1000` of `parse` of the 4 MB line (3,584 samples): `List.reverseAux` 55.6 percent, the
kernel's `clear_page_erms` (the pages of the copies) 21.0 percent, `splitCompleteLinesTRGo` 17.6 percent; every other
symbol is under 1 percent. A profile with call graphs (`--call-graph dwarf`, 2 MB line) puts all three under
`StrictFeed.LineFeed.feed`: `List.appendTR` and its `List.reverseAux` (the `carry ++ chunk`), and
`splitCompleteLinesTR`, which reverses the whole buffer and scans it from the end for a line break
(`perf` of this container: `/usr/bin/perf` asks for a package of the running kernel;
`/usr/lib/linux-tools/6.8.0-146-generic/perf` runs.)

**Cause.** `LineFeed` kept the partial last line as a list in order. `LineFeed.feed` built `carry ++ chunk` for every
chunk and cut it with `splitCompleteLines`. For a line of n bytes in chunks of 65,536 bytes there are k = n / 65,536
chunks, and at chunk j the partial line holds (j - 1) chunks. `carry ++ chunk` copies it (`List.appendTR` reverses it
twice), and `splitCompleteLines` (the `@[csimp]` replacement `splitCompleteLinesTR`) reverses the buffer and scans
it. That is about 3 walks of the partial line per chunk, 1.5 n squared over 65,536 list-cell steps in all: 1.46 billion
for n = 8,000,000, which at 7.7 ns a step is the 11.28 s measured. The guards at chunk sizes 1 to 14 and the
differential at chunk sizes 1 and 7 compare answers over short lines; no row had a line longer than a chunk.

**Repair.** `LineFeed.carryRev` holds the partial line last character first. `LineFeed.feed` cuts the new chunk alone
with `splitCompleteLines chunk`. When the chunk has no line break, its characters go in front of `carryRev` with
`List.reverseAux`: the work is the length of the chunk. Otherwise the complete lines are `carryRev.reverseAux cut`
(the partial line, once, in order, followed by the chunk up to its last line break), and the rest of the chunk
is the new partial line. The partial line is read once, when its line is complete, so each character is copied a
constant number of times.

**Theorems** (axioms: `propext`, `Classical.choice`, `Quot.sound`; `splitCompleteLines_append_of_noNl` uses `propext`
only):

- `splitCompleteLines_append_of_noNl` (`NQuadsLenient.lean`, which the two readers import): a partial line with no
  line break in front of a chunk is cut at the last line break of the chunk, when the chunk has one.
- In `StrictFeed.lean`, `LineFeed.feed_eq_feedSpec`: `feed` is equal to `feedSpec`, the old definition (`splitCompleteLines (carry ++
  chunk)`), on every state whose partial line holds no line break (`LineFeed.CarryOk`); `LineFeed.feed_carryOk`: `feed`
  keeps it so. Every state that `feed` can produce from `{ acc := init }` has the property.
- `LineFeed.feed_quad11`, `foldlM_quad11` and `LineFeed.run_quad11_eq_batch` carry the hypothesis `CarryOk` through the
  chunks. The statement of `run_quad11_eq_batch` is the one it had: a chunked N-Quads (RDF 1.1) run that succeeds gives
  the fold of the whole document. `NQuadsFold.lean` and `SourceTheorems.lean` did not change.
- In `NQuadsLenient.lean`, `LenientStream.feed_eq_feedSpec`: the lenient feed is the walk of the whole lines of `carry ++
  chunk` (`feedSpec`, the old definition) on a state whose partial line holds no line break (`LenientStream.CarryOk`).

**The lenient reader.** `l4factoidal parse FILE --lenient` (`LenientStream`, `NQuadsLenient.lean`) had the same walk of
`carry ++ chunk`, and the same cost: the harness rows `ntriples-lenient-long-line` and `nquads-lenient-long-line`
(the files of the strict rows) read 0.524 s, 2.40 s and 11.6 s of user CPU at 2, 4 and 8 MB for N-Triples (ratios 4.6
and 4.8) and 0.467 s, 2.69 s and 11.4 s for N-Quads (5.8 and 4.2), load average 7.8; they were expected failures that
name the issue, in their own commit before the repair. `LenientStream.carryRev` holds the partial line last character
first, `feed` cuts the new chunk alone, as `LineFeed.feed` does. After the repair: 0.139 s, 0.292 s and 0.566 s
(ratios 2.1 and 1.9) and 0.148 s, 0.271 s and 0.562 s (1.8 and 2.1), load average 8.5; one run of `--lenient` on one
line of 2, 4, 8 and 16 MB reads 0.15 s, 0.32 s, 0.54 s and 1.11 s (before: 0.44 s, 2.47 s, 10.94 s at 2, 4 and 8 MB).
The Turtle and TriG readers were linear in the length of one statement when measured (one Turtle statement of 8 MB:
0.30 s, 0.60 s, 1.21 s at 2, 4 and 8 MB; one TriG graph block: 0.13 s, 0.25 s, 0.53 s).

**Same quads as before.**

The old build (the build before the repairs of this section) and the new build ran on the same inputs; the standard
output, the standard error and the exit status were compared.

| Input | Runs | Agree | Differ |
| --- | ---: | ---: | ---: |
| `tools/strict-parse-differential.sh`: the W3C RDF 1.1 and 1.2 files and the 36 generated files of 3b.4 (count and `--out nquads`, with and without `--base`; the new build at chunk sizes 65,536, 7 and 1) | 21,012 | 21,012 | 0 |
| the same script, the seven new generated files with a line longer than a chunk (3b.8) | 42 | 42 | 0 |
| `parse FILE` (the count) and `parse FILE --out nquads` over the 5,997 N-Triples, N-Quads, Turtle and TriG files under `third_party/testing` and `tests`, each in the RDF 1.1 and the RDF 1.2 mode | 23,988 | 23,988 | 0 |
| the same files, the new build at chunk size 7 (`--out nquads`) and at chunk size 1 (the count) | 23,988 | 23,312 | 0 (676 more: the old build exits non-zero, the exit status and the standard error are the same, and the standard output of the new build holds the lines written before the error, which the script does not compare) |
| `parse FILE --lenient` and `--lenient --max-errors 3`, with and without `--out nquads`, over ten generated files (150,000 N-Quads lines with errors spread through them, 100,000 N-Triples lines, the seven files with a line longer than a chunk): stdout, the diagnostics on stderr (message, offset, line, column, class), exit status | 40 | 40 | 0 |
| `tools/ntriples-reader-differential.py`, seeds 21, 22 and 23 (N-Triples and N-Quads of RDF 1.2, 40 percent damaged, seven ways to read and write a document): 2,500 documents each at 65,536-byte chunks, and 800 each with `L4_STRICT_CHUNK_BYTES=1` and with `=7`; the build of the strict repair | 86,100 | 86,100 | 0 |
| the same script, seed 31, 2,500 documents, the final build (the lenient reader too) | 17,500 | 17,500 | 0 |

The seven new files: a literal of 150,000 characters between short lines; one of 100,000 two-byte characters (a
chunk boundary then falls between the two bytes of a character); an error on the line after a long line (the
offset counts the long line); an unterminated string inside a long line; a long last line with no line break; the
same with CR LF; and N-Quads with a graph name and a blank-node graph name.

*Checks (2026-10-15).*

- `tests/stack/lean_scaling.py --only` the four long-line rows, `parse-nt-memory`, `count-nt-memory`,
  `parse-ttl-memory`, `sbm11-pack-nt-vs-nq`, `query-vs-parse`, `ntriples-nest-time` and `turtle-read-prefixes`: 11 pass,
  0 fail, 0 expected-fail (out of 11). The long-line rows, user CPU at 2, 4 and 8 MB: N-Triples 0.135 s, 0.247 s,
  0.519 s (ratios 1.8 and 2.1 per doubling; 3.8 for 4x input), N-Quads 0.134 s, 0.256 s, 0.548 s (1.9 and 2.1; 4.1),
  lenient N-Triples 0.129 s, 0.263 s, 0.518 s (2.0 and 2.0; 4.0), lenient N-Quads 0.141 s, 0.330 s, 0.578 s (2.3 and
  1.8; 4.1). Before the repairs the four rows were expected failures (ratios 6.3 and 4.3, 5.6 and 5.1, 4.6 and 4.8,
  5.8 and 4.2). The memory rows read 0.0, 6.3 and 0.0 bytes of peak resident set per input byte (bounds 1, 12, 1), as
  before. `tests/stack/lenient_scaling.sh`: 16 pass, 0 fail (out of 16).
- Build-time `#guard`s in `StrictFeed.lean`: N-Quads (RDF 1.1) at chunk sizes 1 to 16 against the fold of the whole
  document, one line of 600 characters in pieces of 1 to 89 characters, and the state after a chunk with no line break
  and after a chunk with one (`carryRev`, `pos`, `CarryOk`). In `NQuadsLenient.lean`: the existing guards at every
  two-way split and at one-character chunks, and new ones for a literal of 400 characters, a line with an error, and
  an unterminated literal of 300 characters with no line break after it, in pieces of 1 to 89 characters (the
  diagnostics with offset, line and column are compared), and for the state after two chunks.
- On the tree merged with origin/main at 91926d7a (the work of https://github.com/danbri/factoidal/issues/871, which
  changes `XML/Parser.lean`, in the WebAssembly compile set): `lake build` (default targets) 1,726 jobs, exit 0; the WebAssembly module rebuilt;
  `python3 tools/lean-csimp-reach.py --gate --cross-check`: exit 0 (163 `@[csimp]` theorems, all found in the table of
  Lean; 56 findings: 0 new, 28 allowed, 28 suppressed; 558 calls of a replacement in the emitted C);
  `tools/lean-tail-recursion-audit.py --gate`: exit 0 (allow list of 1,371 lines);
  `tools/lean-unbuilt-modules.py --gate`: exit 0, 795 modules, 0 not reached; `tools/lean-hygiene-audit.py
  --build-log`: clean (1,566 `#print axioms` outputs); `tools/test_lean_tail_recursion_audit.py`: 12 pass, 0 fail
  (out of 12); `tools/test_lean_csimp_reach.py`: 33 pass, 0 fail (out of 33).
- `Wasm/cli-smoke.sh`: 130 pass, 0 fail, 0 xfail (out of 130). `Wasm/native-smoke.sh`: 369 pass, 0 fail, 0 xfail
  (out of 369). `npm test` in `npm/factoidal`: 443 pass, 0 fail, 1 skipped (out of 444). `node --test
  tests/hub/*_test.mjs`: 447 pass, 0 fail (out of 447).
- `tests/stack/run.sh --canary` with the WebAssembly module built from this tree: 165 pass, 0 fail (out of 165); the
  new row `xml-markup-chain-top` passes in the four routes (native 2,635 ms; native under 512 KB; wasm canary 2,906 ms;
  wasm 2,824 ms). `tests/sbm11/run.sh`: 2,823 pass, 0 fail, 30 expected-fail (out of 2,853). `tests/sbm11/census.sh`,
  `tests/sbm11/threads.sh` (all answers identical) and `tests/delta-log/run.sh` (46 pass, 0 fail): exit 0.
  `tests/known-defects/run.sh`: 24 XFAIL, 0 XPASS, 0 ERROR (out of 24).

## 3c. RDF/XML: where the time and the memory went, and the repair (2026-10-13)

Issues: https://github.com/danbri/factoidal/issues/814 (time: 13 to 15 times
Oxigraph's) and https://github.com/danbri/factoidal/issues/771 (memory: 48 to
49 bytes of resident memory per input byte). Branch `claude/wt-rdfxml-speed`
of `danbri/factoidal-core`, base `e9590cde`, merged with `main` `80dc8ffc`.
`RdfXml.lean` is a grammar walk over an XML element tree: `XML.parseXML`
(`XML/Parser.lean`) reads the document into the tree of XML 1.0, and
`processDocument` walks the tree with the productions of RDF 1.1 XML Syntax
section 7.

### 3c.1 Before: measurement

Binary of `e9590cde`; inputs: the generated files of `tools/sota-bench.py`
(one `rdf:Description` with one property element per triple) and the Cell
Ontology (`third_party/ontologies/cl-basic/cl-basic.owl`, 9,557,097 bytes).

Callgrind (`valgrind --tool=callgrind l4factoidal parse FILE --format rdfxml
--out nquads`), inclusive instructions:

| Input | Total | XML parse (`XML.parseXML`) | Grammar (`processDocument`) | N-Quads output | Largest single cost |
| --- | ---: | ---: | ---: | ---: | --- |
| 25,000 triples, 3,277,910 bytes | 10,663 M | 26 % | 72 % | under 2 % | `XML.splitQName` 53 %: 1,125,011 calls, about 5,000 instructions each (`String.toList` 1,910, two `String.ofList`); 975,008 of the calls from `findNsAttr`, which resolved every attribute name of an element for each of about 20 lookups per element |
| first 1,001,141 bytes of the Cell Ontology (8,014 triples) | 1,833 M | 42 % | 42 % | 12 % | `splitQName` 25 %; `lean_list_to_array` 8.5 % (the document as a `List Char`, then an array) |

Phases (`l4query-phases FILE --rdfxml-op [--stop-after PHASE]`,
`Harness/QueryPhases.lean`; one process per phase for the peak; load 5 to 9;
time in seconds since process start, memory in MB):

| Input | read | chars (alone) | xml (characters and tree) | grammar | nquads |
| --- | --- | --- | --- | --- | --- |
| 100,000 triples, 13,177,910 bytes | 0.05 s, 39 MB | peak 633 MB | 2.34 s, peak 678 MB | 5.77 s (3.37 s for the phase) | 5.87 s |
| Cell Ontology | 0.03 s, 31 MB | — | 1.30 s, peak 482 MB | 2.30 s | 2.63 s |

So the memory was the document characters: `parseXMLNotes` turned the
`String` into a `List Char` (24 bytes per character), into an array to read
the declaration, through the line-end rewrite of XML 1.0 section 2.11 into a
second `List Char`, and into the `Array Char` the parser reads (8 bytes per
character): 633 MB for 13 MB of text before the first element was read. The
tree added 45 MB. The time was the name resolution of the grammar.

### 3c.2 The repairs

Each fast form is proved equal to the readable definition and registered with
`@[csimp]`, so every caller (the command line, the wasm module, the W3C and
OWL runners) runs it; `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound` only.

| Function | Fast form | Theorem |
| --- | --- | --- |
| `XML.splitQName` (`XML/Namespaces.lean`) | one `String.foldl` pass with the prefix, the local part and the colon count | `splitQName_eq_fast` |
| `XML.documentChars` (the head of `parseXMLNotes`, now its own definition) | `stringChars`: one array from the `String` (capacity: the byte count), no `List Char`; the section 2.11 rewrite runs only when the text holds a character it rewrites (`isLineEndChar`) | `documentChars_eq_fast`, `normalizeLineEndingsFor_of_clean` |
| `XML.sub` | the characters pushed onto one string (`Array.foldl` with bounds) | `sub_eq_fast` |
| `XML.normalizeAttrLiteralWs` | the string itself when it holds no tab, line feed or carriage return | `normalizeAttrLiteralWs_eq_fast` |
| `RdfXml.findNsAttr` | an attribute's name is split and its prefix looked up only when the name ends with the wanted local part, which every match does | `findNsAttr_eq_fast`, `XML.endsWith_of_resolveAttributeName` |
| `XML.scanWhile` | `@[specialize]`: no closure call per character | — (compiler attribute) |
| `RdfXml.parseRdfXml` | `parseRdfXmlStream`, 3c.3 | `parseRdfXml_eq_stream` |

`parseRdfXml` also computes the walk's fuel (`text.length + 2`) before the
XML parse, so the document `String` is released while the characters are
read.

### 3c.3 The children of `rdf:RDF` walked as they are read

`nodeElementList` takes the children of `rdf:RDF` one at a time and never
looks at one again (`nodeElementList_eq_fold`: it is a left fold of
`WalkSt.step`). `parseChildrenFold` is `XML.parseChildren` with the same
branches and calls in the same order, but it hands each child to a step
function instead of putting it on a list; `parseRootFold` reads the document
element's start tag like `XML.parseElement` and, when the element is
`rdf:RDF` ([7.2.8]), its children through `parseChildrenFold` with
`WalkSt.step`. Every other document element ([7.2.2] doc: one node element)
is read by `parseElement` and walked by `processDocument` as before.
`XML.parseXMLNotes` is split into `documentPrologue` (declaration,
section 4.3.3, `Misc*`, `[28] doctypedecl`) and `documentEpilog` (`Misc*` and
the end of the text), which both paths call.

Theorems (`Syntax/RdfXml.lean`, section "`parseRdfXml` without the element
tree of the document element"):

- `parseChildrenFold_eq`: from the fold of the children already read,
  `parseChildrenFold` gives the fold of every child `parseChildren` reads,
  with the same flags, notes, position and error;
- `parseRootFold_eq`: the same for the document element (`rootResult`);
- `processDocument_rootResult`: the walk of a streamed document element is
  `processDocument` of that element;
- `parseRdfXml_eq_stream` (`@[csimp]`): `parseRdfXml = parseRdfXmlStream` on
  every text and base, errors included (an XML error still wins over an
  RDF/XML error found earlier in the document).

No element tree of the document is built: each child of `rdf:RDF` is freed
after its step. The characters (8 bytes each) are still read into one array.
Build-time guards (`RdfXmlTests.lean`) reach each branch: comments,
processing instructions and text between node elements, an empty `rdf:RDF`,
a node element as document element, a markup entity whose replacement text
is a node element, an XML error after an RDF/XML error, content after the
document element.

### 3c.4 After

Callgrind, the same commands: 25,000 triples 10,663 M to 3,400 M instructions
(-68 percent); the first 1,001,141 bytes of the Cell Ontology 1,833 M to 943 M
(-49 percent).

Phases of the final binary (`l4query-phases FILE --rdfxml-op --stream`: the
`stream` phase is `parseRdfXml` as compiled, characters, XML and grammar
together); one process per phase for the peak; load 1.5 to 2; the harness
holds the document `String` throughout, which the command line releases:

| Input | read | chars (alone) | stream | nquads |
| --- | --- | --- | --- | --- |
| 100,000 triples | 0.04 s, 39 MB | peak 144 MB | 2.04 s, peak 158 MB | 2.09 s, peak 178 MB |
| Cell Ontology | 0.04 s, 31 MB | peak 107 MB | 0.85 s, peak 127 MB | 1.21 s, peak 147 MB |

The command line (`tools/sota-bench.py --workloads
parse-rdfxml,parse-rdfxml-real`, 15:30 UTC, load 1.4 to 1.8, median of 3 to 5
runs; wall time (CPU time), peak resident set in MiB; Oxigraph 0.5.11, Jena
6.2.0, from the same run):

| Row | Before (`e3c3aa01`, SOTA record) | After | Oxigraph | Jena `riot` | After / Oxigraph: time; peak resident set |
| --- | --- | --- | --- | --- | --- |
| 25,000 triples | 1.47 s (1.44 s), 151 MB | 0.45 s (0.40 s), 65 MB | 0.11 s (0.08 s), 19 MB | 1.47 s (3.19 s), 154 MB | 4.3; 3.4 |
| 50,000 triples | 2.70 s (2.61 s), 281 MB | 0.84 s (0.79 s), 101 MB | 0.18 s (0.16 s), 19 MB | 1.69 s (3.87 s), 191 MB | 4.7; 5.3 |
| 100,000 triples | 5.33 s (5.12 s), 671 MB | 2.23 s (2.12 s), 181 MB | 0.36 s (0.33 s), 19 MB | 2.16 s (5.08 s), 240 MB | 6.2; 9.5 |
| Cell Ontology | 2.46 s (2.38 s), 479 MB | 1.09 s (1.02 s), 148 MB | 0.27 s (0.21 s), 19 MB | 1.64 s (3.99 s), 143 MB | 4.0; 7.7 |

The three runs of the 100,000 row took 1.92 to 2.43 s with 0.35 to 0.90 s of
system time (the kernel clears the 2 MB pages of about 180 MB); separate runs
at load 5 took 1.66 s (1.58 s user, 0.04 s system). The peak is 14.4 bytes
per input byte at 100,000 triples (48 to 49 before) and 16.3 for the Cell
Ontology with `--out nquads` (52.6 before). The expected-failure mark of
`tests/perf/sota_gate.sh` for `parse-rdfxml` 100,000 (issue 814) is removed:
the gate reported UNEXPECTED PASS (time ratio 5.3, memory ratio 7.9 against
the recorded Oxigraph row).

### 3c.5 Costs still open

| Cost | Cause | Where it is tracked |
| --- | --- | --- |
| 8 bytes of resident memory per document character: 105 MB of the 181 MB at 100,000 triples, 76 MB of the Cell Ontology's 148 MB; the row `cl-basic-parse-memory` of `tests/stack/owl_real_gate.sh` (at most 15 bytes per input byte) stays an expected failure at 15.7 | the XML layer reads an `Array Char` (one boxed `Char` per cell); every production of `XML/Parser.lean` and its theorems are stated over it. The repair is a reader over byte positions of the UTF-8 text | https://github.com/danbri/factoidal/issues/771 (open) |
| `RDF.isIri` runs its `List Char` form in `RdfXml.lean`: 10.5 percent of the instructions at 25,000 triples | the `@[csimp]` `isIri_eq_isIriFast` is in `NTriples.lean`, which `RdfXml.lean` does not import | profile only |
| `resolveIri` parses the base and the reference again for each `rdf:about` and `rdf:resource`: 21.9 percent | `RdfXml.resolveRef` calls `resolveIri st.base r` | profile only (the row is within 10 times Oxigraph) |
| `splitQNameFast` 14.9 percent | one structure per character in the fold; called for each element name, each declaration and each attribute that passes the suffix test | profile only |
| one `ElemNote` (about 56 bytes) per element is kept until the end of the stream | `parseChildrenFold` threads the parser's notes as `parseChildren` does, which the equality theorem needs | part of https://github.com/danbri/factoidal/issues/771 |

### 3c.6 Gates (2026-10-13, this change)

Before is the binary of `main` `80dc8ffc` (built in a separate worktree),
after is this branch merged with it.

- `tools/lean-scoreboard.sh --only l4w3c-rdf11,l4w3c-rdf12,l4rdfxml-probe,l4xmlconf`:
  rows and logs identical before and after, line for line. `l4w3c` RDF 1.1:
  1041 pass, 0 fail (out of 1041), of which RDF/XML 166 pass, 0 fail (out of
  166); RDF 1.2: 1358 pass, 0 fail (out of 1358), of which RDF/XML 31 pass, 0
  fail (out of 31); the RDF/XML probe 132, 41 and 132 pass, 0 fail; XML 1.0
  conformance (`l4xmlconf`): 1861 pass, 0 fail, 345 out of profile (out of
  2206).
- The other runners that read RDF/XML (`l4owl-probe-rl`, `-species`,
  `-fs-input`, `l4grddl`, `l4rif`): rows identical; the logs differ only in
  their `wall_ms` fields.
- Differential, `l4factoidal parse FILE --format rdfxml --out nquads`, with no
  base and with the base `http://example.org/dir/doc.rdf`, on the 308 `.rdf`,
  `.owl` and `.rdfxml` files under `third_party/testing` (the XML suite
  excluded) and `third_party/ontologies`: 616 of 616 runs identical in
  standard output, standard error and exit status. The Gene Ontology basic
  release of issue 771 (118,080,840 bytes, SHA-256 `13a907d2…50d9`): 1,283,913
  statements with both binaries; count path 54.4 s and 5,036 MB before, 22.2
  s and 1,904 MB after (load 9: the WebAssembly build ran beside it).
- `tests/stack/owl_real_gate.sh --only cl-basic-parse-memory,ro-parse`: 0
  pass, 0 fail, 2 expected-fail (out of 2): `cl-basic-parse-memory` 143 MB, 15.7
  bytes per byte against the bound 15 (https://github.com/danbri/factoidal/issues/771);
  `ro-parse` 11,703 triples (https://github.com/danbri/factoidal/issues/329).
- `tests/perf/sota_gate.sh`: 79 pass, 0 fail (out of 79), no expected failure
  left; before the mark was removed the `parse-rdfxml` 100,000 row reported
  UNEXPECTED PASS.
- `tests/stack/lean_scaling.sh`: 38 pass, 0 fail, 1 expected-fail (out of 39),
  with two new rows: `parse-rdfxml` (12,500 to 50,000 triples, 0.199 to 0.951
  s of CPU, ratio 4.8 for 4 times the input, bound 9) and
  `parse-rdfxml-memory` (25,000 to 100,000 triples: 12.5 bytes of peak
  resident set per input byte, bound 16; 55.1 on the binary of `main`, which
  fails the row).
- `tests/stack/run.sh --canary`: 97 pass, 0 fail (out of 97).
- `Wasm/cli-smoke.sh`: 83 pass, 0 fail, 0 xfail (out of 83).
  `Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out of 366).
- `tools/lean-tail-recursion-audit.py --gate`: pass. `tools/lean-unbuilt-modules.py
  --gate`: 768 of 768 modules reached. `tools/lean-hygiene-audit.py
  --build-log`: clean (partial def 163, baseline 163; every `#print axioms`
  `propext`, `Classical.choice`, `Quot.sound` at most). Full `lake build`: exit
  0 (1665 jobs). WebAssembly module rebuilt; `npm test`: 418 pass, 0 fail, 1
  skipped (out of 419).

### 3c.7 The scope of a property element (2026-10-14)

An `xml:lang` attribute applies to the element that carries it and to the
content of that element. It does not apply to the elements after it (XML 1.0
section 2.12). `xml:base`, `xmlns` declarations, `its:dir` and `rdf:version`
follow the same rule (XML Base section 3, Namespaces in XML section 6.1,
RDF 1.2 XML Syntax).

**The defect** (https://github.com/danbri/factoidal/issues/841).
`<ex:p xml:lang="fr">a</ex:p><ex:q>b</ex:q>` gave `"b"@fr`. `propertyElt`
returned the state of the property element, and `propertyEltList` gave that
state to the next property element. The state held the base IRI, the
namespace bindings, the language, the base direction and the version switch
that the first element had set. `nodeElement` restored the scope of its caller.
The property element paths did not: the branches for literal content, empty
elements, `rdf:resource`, `rdf:nodeID`, `rdf:parseType="Literal"` and
`"Collection"` returned the state as it was, and the branches for `"Resource"`
and `"Triple"` called `restoreScope` with the state of the property element as
the parent, which kept the scope of the property element. The header of the
module described the intent (`restoreScope`). The F\* parser has the same defect.

**The effect.** The Lean RDF/XML writer writes the properties of a subject in
key order. A literal that follows a language-tagged literal of the same subject
read back with that language. The RDF/XML export of the generated set of 12,000
triples (`gen_multi.py`, 1,500 subjects) read back with 3,000 quads that differ
from the pack of the N-Triples text (the `name` and the `note` of each subject).
The RDF/XML files of the repository show it too. Of 318 files (the XML
conformance suite excluded), 13 read differently after the repair: 12
third-party documents with 404 statements (Pizza, SKOS, BFO, RO, the Cell
Ontology and the RML ontologies), and `lang_scope.rdf`. In each of the 404
statements the only change is a language tag. RO has 11,705 triples where it
had 11,703 (rdflib 7.6.0 reads 11,705), and the Cell Ontology has 78,835 where
it had 78,833 (rdflib 78,835): a plain literal had become equal to a tagged
one. `xml:base` had the same effect on IRIs (`scope_paths.rdf`).

**The repair.** `closePropertyScope parent child` is `restoreScope` with the
`rdf:li` counter of the child. `propertyElt` applies it to the result of every
path (`closePropertyElt`). The state after a property element has the base,
namespace bindings, language, direction and version switch of the node element
that holds it. The `rdf:li` counter, the blank node counter, the `rdf:ID` keys
and the first error flow out. No other function changed.

**Theorems** (`RdfXmlTheorems.lean`; axioms `propext`, `Classical.choice`,
`Quot.sound`). `propertyElt_scope`: for every fuel, state, subject and node, the
XML scope of the state after `propertyElt` equals the XML scope before it,
whichever production reads the element and whether it finds an error.
`propertyEltList_scope`: the same for a list of property elements. The scope is
five fields (`SameXmlScope`).

**Tests.** 23 build-time guards in `RdfXmlTests.lean` (section "A property
element's scope closes with it"): one or two for each path of `propertyEltBody`,
and for `xml:base`, `xmlns`, `its:dir`, `rdf:version` and the `rdf:li` counter.
22 of them fail on the parser of 2026-10-13; the 23rd is the control of the
`xmlns` guard. File level: `tests/sbm11/syntax_independence.sh` cases
`lang-scope rdfxml` (an expected failure until 2026-10-14) and `scope-paths
rdfxml`; `tests/sbm11/export_roundtrip.sh` (the RDF/XML export of D1 and of the
generated set); `tests/stack/owl_real_gate.py` row `ro-parse` (an expected
failure until 2026-10-14, now a pass).

**What stays open.** The F\* parser (`Parser.RDFXML.fst`, `restore_scope st2 ...`
with the state of the property element) is not repaired:
https://github.com/danbri/factoidal/issues/329 and the row `RDFXML-LANG-SCOPE` of
`tests/known-defects/run.sh` (XFAIL). The Lean parser is the oracle of that row.

### 3h. JSON-LD: the labels of generated blank nodes (2026-10-14)

A blank node label is local to one document (RDF 1.1 Concepts, section 3.4).
The conversion of JSON-LD to RDF makes a blank node for each node object that has
no `@id`, for each cell of a list and for each compound literal. A label that the
document writes (`@id`, `@type`, the name of a graph) goes through the conversion
unchanged. A label that the conversion makes must never equal a label that the
document writes.

**The defect** (https://github.com/danbri/factoidal/issues/840). `freshBnode`
made the labels `_jld_anon0`, `_jld_anon1` and so on for every document. A
document that wrote `_:_jld_anon0` and held a node object with no `@id` got one
blank node where it has two. `tests/sbm11/syntax/bnode_collide.jsonld` has five
nodes and gave three blank nodes: `_jld_anon0` held the properties of the written
node and of the first generated node, and `_jld_anon1` the same for the second.
A document that wrote `_:_jld_anon0` and a list of one item got one blank node
for the node and for the cell of the list. Turtle, TriG and RDF/XML read five
blank nodes from their versions of the first document.

**The choice.** Two repairs were possible.

1. An issuer map, as in the Node Map Generation algorithm of the JSON-LD 1.1 API:
   every blank node identifier of the document gets a new label from one counter.
2. A prefix that the conversion chooses from the document, as the Turtle reader
   does (`freshBnodePrefix`).

The second was chosen. The first changes the label of every blank node that a
document writes. The second changes a label only in a document that writes a
label which begins with `_jld_anon`. The repository has 2,484 JSON-LD files
(`third_party`, `tests`, `examples`, `docs` and `formal`; 2,234 of them parse).
118 of them contain a string that begins with `_:`. One of them writes a label
that begins with `_jld_anon`: `bnode_collide.jsonld`. The build before this change
and the new build gave the same N-Quads text, the same stderr and the same exit
status for `l4factoidal parse FILE --format jsonld --out nquads` on 2,483 of the
2,484 files, and a different text for that file only. A label that an
author writes stays in the output, and `freshBnode_injective` keeps its meaning
for a fixed prefix.

**The scheme.** `generatedPrefix root` is `_jld_anon` followed by k underscores,
where `root` is the expanded document. k is the largest value of `anonNeed s` for
all keys and string values `s` of `root`. `anonNeed s` is 0 when `s` does not
begin with `_:_jld_anon`. Otherwise it is 1 plus the number of underscores that
follow those 11 characters. A document that writes no label which begins with
`_jld_anon` gets k = 0 and the labels `_jld_anon0`, `_jld_anon1` and so on, as
before. A written label `_jld_anon__0` gives k = 3 and the generated labels
`_jld_anon___0` and so on. The prefix is computed once for each document by one
pass over the tree (`maxNeed`). The depth of its recursion is the nesting of the
document. The three functions of the pass are in the allow list of the
tail-recursion audit, class (b). The prefix is the field `labelPrefix` of
`RdfAcc` and does not change during the walk. A string value that is not an `@id`
and begins with `_:_jld_anon` also counts: it makes the prefix longer than it
needs to be and has no other effect.

**Theorems** (`JSONLD/Theorems.lean`; axioms `propext`, `Classical.choice`,
`Quot.sound` only).

- `need_le_maxNeed`: for every key and string value `s` of a tree,
  `anonNeed s ≤ maxNeed root 0`.
- `generated_ne_written`: let `s` be a key or a string value of `root` that is a
  blank node identifier (`_:` and a label). The label that `stripBnodePrefix`
  reads from `s` is not the label that `freshBnode (generatedPrefix root) n`
  makes, for every counter value `n`.
- `idToSubject_ne_generated` and `typeTerm_ne_generated`: the same for the labels
  that `idToSubject` (the `@id` of a node object and of a graph) and `typeTerm`
  (a blank node identifier in `@type`) give.
- `freshBnode_injective`: for a fixed prefix, two counter values give two labels.

`idToSubject` and `typeTerm` are the only functions of `JSONLD/ToRdf.lean` that
read a label from the document, and `freshBnode` is the only one that makes a
label. That is a fact about the source and not a theorem. The guards below check
it for each way that the conversion makes a label.

**Tests.** 11 build-time guards in `JSONLD/Tests.lean` (section "Blank node
labels that the document writes"). Eight give the blank node labels of one
document: the collide document, a list of two cells with no written label, two
labels that only resemble the generated ones (they must not change anything),
`_jld_anon__0`, a list cell, a blank node in `@type`, a blank node as the name of
a graph and a compound literal. Three give `generatedPrefix` of one document.
Six of the eight label guards fail on the converter before this change and the
two others are controls. File level: `tests/sbm11/syntax_independence.sh`, case
`bnode-collide jsonld` (an expected failure until 2026-10-14, now an assertion:
five distinct blank node subjects in each of Turtle, TriG, RDF/XML and JSON-LD),
and `npm/factoidal/test/parse-scope-and-labels.test.js` (the wasm module, two
JSON-LD cases).

**What stays open.** The F\* converter (`Parser.JSONLD.fst`, `jld_fresh_bnode`) has
the same defect and is not repaired: row `JSONLD-BNODE-COLLIDE` of
`tests/known-defects/run.sh` (XFAIL; the Lean CLI is the oracle) and
https://github.com/danbri/factoidal/issues/840.

**Cost.** The pass adds no measurable time or memory. The test: `l4factoidal
parse FILE --format jsonld --out nquads` on a generated file of 60,000 node
objects (11.9 MB, 420,000 quads), nine runs of each build in turn, on one
machine. The median is 3.02 s before and 2.95 s after (minimum 2.70 s and
2.46 s). The peak resident set is 293 to 299 MB for both builds. The two outputs
are byte-identical.

**Gates (2026-10-14, this change).** The counts are as labelled by each runner.
The commit before this change is the RDF/XML scope repair of section 3c.7.

- `lake build` (default targets): exit 0, 1,700 jobs, before and after.
  `tools/lean-tail-recursion-audit.py --gate`: pass; three rows are added to the
  allow list (1,374 to 1,377 lines). `tools/lean-unbuilt-modules.py --gate`: 781
  modules, 0 not reached.
- `tools/lean-scoreboard.sh`, 57 runner runs: the 182 rows are identical before
  and after. JSON-LD toRdf 467 pass, 0 fail (out of 467); expand 385 pass, 0 fail
  (out of 385); compact 245 pass, 0 fail, 1 other (out of 246); flatten 58 pass,
  0 fail (out of 58); fromRdf 53 pass, 0 fail, 1 other (out of 54); html 50 pass,
  0 fail (out of 50); framing 91 pass, 0 fail, 1 other (out of 92).
- `tests/sbm11/syntax_independence.sh`: 97 pass, 0 fail, 1 expected-fail (out of
  98) before; 98 pass, 0 fail, 0 expected-fail (out of 98) after.
  `tests/sbm11/run.sh`: 2,190 pass, 0 fail, 23 expected-fail (out of 2,213)
  before; 2,191 pass, 0 fail, 22 expected-fail (out of 2,213) after.
- `tests/stack/run.sh --canary`: 109 pass, 0 fail (out of 109), before and after.
- Wasm module rebuilt. `Wasm/native-smoke.sh`: 366 pass, 0 fail, 0 xfail (out
  of 366), before and after. `npm test`: 437 pass, 0 fail, 1 skipped (out of 438)
  before; 442 pass, 0 fail, 1 skipped (out of 443) after. `tests/hub`: 447 pass,
  0 fail, before and after.
- `tests/known-defects/run.sh` (Lean CLI of this build): 23 XFAIL, 0 XPASS, 0
  ERROR before; 24 XFAIL, 0 XPASS, 0 ERROR after.

### 3i. The RDF/XML writer's time and the JSON-LD stack (2026-10-18)

Issues: https://github.com/danbri/factoidal/issues/845 (the RDF/XML writer is
quadratic), https://github.com/danbri/factoidal/issues/853 (the JSON-LD writer's
native stack grows with the elements) and
https://github.com/danbri/factoidal/issues/844 (the JSON-LD reader's native stack
grows with the elements). Owner goal of 2026-10-12, verbatim: "OKRs addresses
successfully especially perf and scaling should approach SOTA".

**Method.** Time: `l4source-convert multi.nt out --from nquads --to rdfxml` on the
datasets of `tests/sbm11/syntax/gen_multi.py` (8 triples for each subject); the
`write-ms` field the tool prints. Stack: `l4factoidal parse` under
`LEAN_STACK_SIZE_KB=512` with `LEAN_MAIN_USE_THREAD` unset (the knob of
`tests/stack/run.sh`); for each overflow, `gdb` stopped at the SIGSEGV of the guard
page and the 400 innermost frames were counted by function name. Base: e185eb00.

**RDF/XML writer, before and after** (`write-ms`, same machine, same files):

| subjects | triples | before | after |
| ---: | ---: | ---: | ---: |
| 2,000 | 16,000 | 731 | 91 |
| 4,000 | 32,000 | 2,581 | 224 |
| 8,000 | 64,000 | 10,488 | 440 |
| 16,000 | 128,000 | 39,746 | 952 |
| 32,000 | 256,000 | 202,201 | 1,796 |

Cause: `graphToRdfXml` kept the subjects found so far in a list (`acc.contains`,
`acc ++ [k]`) and read the whole graph once for each subject (`g.filter`). Repair:
`subjectGroups` (the subjects in the order of their first triple, each with its
triples in graph order) is the specification, written as the old code computed it;
`subjectGroupsFast` reads the graph once with a hash map from subject key to that
subject's triples (reversed) and the keys in reverse order of first use.
`subjectGroups_eq_fast` (`@[csimp]`) is proved from the invariant `GroupInv`
(`groupInv_step`, `groupInv_foldl`, `mem_subjectOrder`). The output bytes are the
same: `cmp` on the five datasets above, and a differential of the old and the new
`l4source-convert` on 720 W3C files (every `.rdf` of the RDF 1.1 and RDF 1.2
RDF/XML suites, every RDF 1.1 Turtle `.ttl` and N-Triples `.nt`) re-serialised as
RDF/XML: 720 identical (458 written, 262 refused or not parsed, with the same
text), 0 different.

**JSON-LD reader, the frames found** (512 KB stack, before):

| shape | elements | before | frames at the overflow | after |
| --- | ---: | --- | --- | --- |
| one node, n references | 100,000 | overflow | `Json.sizeItems` | runs, 0.64 s |
| one node, n properties | 100,000 | overflow | `Json.sizeFields` | runs, 0.85 s |
| n node objects (hub) | 100,000 | overflow | `Json.sizeItems` | runs, 3.74 s |
| n `@graph` objects | 100,000 | overflow | `Json.sizeItems` | runs, 2.16 s |
| one node, n blank node objects | 100,000 | overflow | `Json.sizeItems` | runs, 1.05 s |
| one `@list` of n strings | 5,000 | overflow | `expandList` | runs at 100,000, 0.74 s |

`datasetOfJson` takes its fuel from `Json.size root`, and `sizeItems` added the
size of the rest of the list after its recursive call. `sizeAcc` adds into an
accumulator (`sizeAcc_eq : sizeAcc j n = n + size j`; `size_eq_sizeFast`,
`sizeItems_eq_fast`, `sizeFields_eq_fast`, all `@[csimp]`). `expandList` allocated
the cell of the first item, converted the rest, and prepended the first cell's
triples on the way back. `expandListGo` converts the items left to right, keeps the
cells in `pend`, and `listCells` prepends their triples last cell first, which is
the order of the returns of `expandList`. A `csimp` theorem cannot replace a call
inside its own `mutual` block, so the nine functions of the walk are twinned (`W`)
and `expandW_eq` proves all nine equal to the specification at every fuel; every
member of the specification block has a `csimp` theorem, so no compiled code calls
into it (checked with `tools/lean-csimp-reach.py`). Documents with an `@context` go
through `JSONLD.Expand` first, whose frames are tracked by
https://github.com/danbri/factoidal/issues/753; this landing does not change them.

**JSON-LD writer, the frames found** (512 KB stack, `parse FILE.nt --out jsonld`):

| shape | elements | before | frames | after |
| --- | ---: | --- | --- | --- |
| one subject, n IRI objects | 20,000 | overflow | `snocUniqueOv` | runs, 8.5 s |
| one subject, n predicates | 20,000 | overflow | `propAdd` | runs, 3.0 s; 100,000 run in 77 s |
| n subjects | 20,000 | overflow | `insertSortedNode` | runs, 7.3 s |

Each repaired function has a loop form and a `@[csimp]` equality in
`JSONLD/FromRdf.lean`: `snocUniqueStr`, `snocUniqueOv`, `propAdd` (a reversed
accumulator and one `reverseAux`), `ovsRefids`, `propsRefids`, `nodesRefids`,
`mapsRefids` (`filterMap` and `flatMap`), `insertSortedNode` and `sortNodes` (a left
fold from the end), `ovToJson`/`ovListToJson` and `listFrom`/`resolveOv` (twinned
blocks with an accumulator, proved by induction), `buildNamed`. The JCS writer in
`JSONLD/ToRdf.lean`: `jcsInsertSorted`, `jcsSortFields`, and the block
`jcsSerialize`/`jcsSerializeItems`/`jcsSerializeFields`, which now appends each
piece to an accumulator string (`jcsSerW_eq`). The writer's time is still quadratic
in the number of nodes and values: the node map is a list and each triple searches
it (https://github.com/danbri/factoidal/issues/712; rows `jsonld-write` and
`jsonld-write-*-stack` are expected failures of the time bound only). An
`rdf:first`/`rdf:rest` chain of 5,000 cells did not finish in 60 s before or after
(`isCollapsible` walks the chain from every cell, each step a list search; issue
712), so the `listFrom` repair is shown by its theorem and by the W3C suites, not by
a large run.

**Outputs.** A differential of the old and the new `l4factoidal` on 911 W3C JSON-LD
files (every toRdf and expand `-in.jsonld` read to N-Quads, every fromRdf `-in.nq`
written as JSON-LD): 911 identical (715 exit 0), 0 different. The scoreboard rows
are the same numbers before and after (runner logs identical apart from the times):
JSON-LD toRdf 467 pass, 0 fail (out of 467); expand 385 pass, 0 fail (out of 385);
compact 245 pass, 0 fail, 1 other (out of 246); flatten 58 pass, 0 fail (out of 58);
fromRdf 53 pass, 0 fail, 1 other (out of 54); html 50 pass, 0 fail (out of 50);
framing 91 pass, 0 fail, 1 other (out of 92); RDF 1.1 RDF/XML probe 132, 41 and 132
pass, 0 fail; RDF 1.1 RDF/XML (l4w3c) 166 pass, 0 fail (out of 166); RDF 1.2 RDF/XML
eval 31 pass, 0 fail (out of 31).

**Gates added.** `tests/stack/lean_scaling.py`: the row `rdfxml-write` is an
assertion (it was an expected failure for issue 845), and seven rows run at n, 2n
and 4n under a 512 KB stack (`STACK_ROWS`): every run must exit 0, and the time must
stay within 4.5 times (2n) and 9 times (4n) of the time at n. The three writer rows
are expected failures of the time bound (issue 712); an overflow is a failure also
for them. `tests/stack/run.sh`: cases `jsonld-read-fanout` (100,000 references),
`jsonld-read-list` (100,000 items) and `jsonld-write-fanout` (20,000 references),
each checking the count in the answer. The known-defects rows `JLD-STACK` and
`JLD-WSTACK` are removed.

## 4. Rules that follow

1. A new fast path is added beside the reference parser with a theorem or,
   until the theorem lands, a differential tool named in this file.
2. Any per-character or per-line decision in a streaming scanner reads O(1)
   state, never the accumulated text (`skills/lean4-performance`).
3. Fuel is computed once per document or per candidate, never per token
   (`skills/lean4-proof-patterns` section 2 has the theorem shape).
4. Before reading code for a superlinear ingest, run a size ladder without
   the suspect inputs and isolate the region that misbehaves
   (`docs/20260902-persisted-query-ladder.md`, "Where the 6,134 s went").
5. A module under `L4Factoidal/Storage/` names no syntax. It reads a source
   through `RDF/Source.lean` (section 3f). `tests/sbm11/storage_layering.py`
   checks it.
6. When a change moves a syntax to another reader, time the new reader against
   the old route on the same bytes. A pack differential checks bytes only.
   (2026-10-14: the strict N-Triples reader gave the same bytes as the reader
   it replaced and took 2,996 ms of phase 1 against 477 ms for N-Quads text,
   because `readTriple12` computed `r5.length + 1` for each statement. A timing
   of one dataset in every syntax (`tests/sbm11/syntax_bench.sh`) found it.)
