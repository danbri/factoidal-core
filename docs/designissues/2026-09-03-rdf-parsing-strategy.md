# RDF parsing strategy in the Lean tree: layers, entry points, proofs, costs

Status: record of the design as it stands on 2026-09-03 (section 3a, the
lenient mode, added 2026-10-10; section 3c, RDF/XML, added 2026-10-13; section
3f, the source layer, added 2026-10-14), written because the
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
| RDF/XML | `RdfXml.lean` `parseRdfXml` (the element tree, then the walk) | `parseRdfXmlStream` (the children of `rdf:RDF` walked as they are read; every caller runs it, section 3c) | W3C suite; `RdfXmlTheorems.lean` (blank-node label spaces disjoint by construction); `parseRdfXml_eq_stream` (`@[csimp]`) |

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

PROVED (`TriGChunkFoldTheorems.lean`; axioms `propext`, `Classical.choice`,
`Quot.sound` only): `feed_split` (two chunks in sequence give the result of
their concatenation, every state, every cut); `feed_inv` (the block flag is the
scanner's brace depth at every chunk boundary, nothing pending);
`finish_unterminated` (input ending in a block is refused);
`consumeBlock_graphs`, `applyEvent_stmt_graphs`, `applyEvent_close_graphs`
(inside a block every step call carries the block's label);
`applyEvent_stmt_label`.

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
| `Source.Reader` / `Source.ByteReader` (`init`, `feed`, `finish`) | the text arrives in chunks; each quad goes to a consumer `Step α` when its statement is complete | the shard packers (IBK2 to IBK5), `l4sbm11-pack`, `l4sbm11 canon` |

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

**Blank node labels.** A blank node label is local to one document (RDF 1.1
Concepts, section 3.4). Turtle and TriG mint a label for each `[]`, collection
cell and property list: `anon`, then one more underscore than the longest run of
underscores in the document, then a counter. A reader that sees one chunk does
not know that run, so `Source.Prepass` reads the source once before the first
chunk and `Reader.init` takes the prefix. RDF/XML and JSON-LD mint their own
labels (`b<N>`, `_jld_anon<N>`). A test with explicit labels that equal the
minted ones (`tests/sbm11/syntax/bnode_collide.*`) expects five distinct blank
nodes: Turtle, TriG and RDF/XML read five. JSON-LD reads three
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
| N-Triples, N-Quads | `NQuadsLenient.lean`: `foldLinesLenient` (one walk, statement reader as a parameter), `parseNTriplesLenient`, `parseNQuadsLenient`, `parseNQuadsFastLenient` | `LenientStream` (cuts after the last line feed with `splitCompleteLines`, as `feedChunkC`) | the end of the line on which the failing statement started (`skipToEol`, `skipEol`) |
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
| `ro-parse` of `tests/stack/owl_real_gate.sh`: 11,703 triples where rdflib reads 11,705 | an `xml:lang` reaches the next sibling property element; output unchanged by this work | https://github.com/danbri/factoidal/issues/329 |

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
