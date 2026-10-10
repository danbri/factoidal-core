# RDF parsing strategy in the Lean tree: layers, entry points, proofs, costs

Status: record of the design as it stands on 2026-09-03 (section 3a, the
lenient mode, added 2026-10-10), written because the
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
  and the WASM `parse`, `datasetOpen` and `queryDataset` Turtle path
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
  `PackStream.ingestStep_eq_prependReverse` ties the shard packer's step to
  that accumulator. This is the ACCUMULATOR half of the streaming
  agreement, the counterpart of instantiating
  `NQuadsFold.streamConsume11_eq_batch` at the accumulator the batch parser
  uses.
- `TurtleChunkFold.lean` (2026-10-10): `freshBnodePrefixText_eq`,
  `parseTurtleText_error` and `parseTurtleText_eq_of_walk` (section 2.2,
  item 5).
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
| N-Triples | `NTriples.lean` `parseNTriples` | — | W3C suite; `NTriplesRoundTrip.lean` |
| N-Quads | `NQuads.lean` `parseNQuads` | `NQuadsFast.lean` `parseNQuadsFast` (bucketed accumulator; the WASM `datasetOpen` path); `NQuadsStreaming.lean` (chunk-boundary fold), `NQuadsFold.lean` (the generic consumer the IBK4 shard packer streams through) | `parseNQuadsFast_eq_parseNQuads` proved 2026-09-02 (`NQuadsFastTheorems.lean`); the streaming module carries its own chunk-boundary theorem |
| TriG | `TriG.lean` `parseTriG` (shares the Turtle productions; the default graph is the unlabelled block) | none; an IBK4 pack over TriG still buffers the whole source, unlike the Turtle and N-Quads routes (quad-aware layout: `2026-09-02-quad-aware-block-layout.md`) | W3C suites |
| RDF/XML | `RdfXml.lean` | — | W3C suite; `RdfXmlTheorems.lean` (blank-node label spaces disjoint by construction) |

Shared lexical pieces: `Lexing.lean` (the N-Triples string body and escape
table the Turtle `decodeEscape` mirrors), `IriResolve.lean` (RFC 3986),
`IriScan.lean`, the `Locality*.lean` family (chunk-locality lemmas used by
the N-Quads streaming proofs).

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

TriG has no streaming execution; `l4factoidal parse --lenient` reads a TriG
file whole and runs the reference walk, whose memory grows with the input.
After the 2026-10-10 repair of the strict TriG reader (linear; it was
quadratic, `docs/designissues/2026-10-10-lean-vs-fstar-performance.md`) the
lenient TriG walk, which runs that reader, is linear too: 25,000, 50,000,
100,000 and 200,000 statements (10 per graph block, one bad in 500;
1,681,242 to 13,822,892 bytes) took 0.72, 1.32, 2.77 and 5.43 s of CPU and
141, 265, 513 and 987 MB peak.

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
