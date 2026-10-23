/-
L4Factoidal.RDF.Source — the source layer: RDF quads from a document in any
concrete syntax.

Owner, 2026-10-14, verbatim: "SMB11 should store rdf graphs regardless of
source formats - this is why we have reflected w3c rdf core concepts into
Lean. I don't see any reason for the format to be made so explicit for
internal data manipulation- file formats are for exchange and publishing".
Tracking: https://github.com/danbri/factoidal/issues/837.

A store takes RDF terms, triples and quads (the abstract syntax of RDF 1.1 and
RDF 1.2 Concepts, `L4Factoidal.RDF`) and does not know in which concrete
syntax they were written. This module is the one place that turns a document
into quads. A module under `L4Factoidal/Storage/` imports this module and no
`L4Factoidal.Syntax` module (`tests/sbm11/run.sh` part (m) checks it). A tool
at the edge chooses a format by name (`RdfFormat`, `formatOfLabel`,
`formatOfExtension`) and gives it to `Reader.init`.

## Two meanings of "read a document"

* The batch meaning, `parseDocument`: the whole text is parsed and the answer
  is a `Dataset`. The wasm parse op (`Wasm/Ops/Parse.lean`) uses it.
* The chunk meaning, `Reader`: the text arrives in chunks and every quad goes
  to a consumer `Step α` as soon as its statement is complete, in the order
  the document states the quads. The shard packers use it, so the packer holds
  one chunk, one unfinished statement and the consumer's own accumulator, not
  the document.

## What streams

| format | reader | memory |
|---|---|---|
| N-Triples, N-Quads | `StrictFeed.LineFeed` (line walk) | one chunk and one partial line |
| Turtle | `TurtleChunkFold` | one chunk and one unfinished statement |
| TriG | `TriGChunkFold` | one chunk and one unfinished unit |
| RDF/XML | `RdfXmlChunkFold` | one chunk and one child of `rdf:RDF`; the document when the fall-back rule applies |
| JSON-LD | `JsonLdChunkFold` | one chunk and one top-level node object; the document when the fall-back rule applies |

JSON-LD reads one top-level node object at a time when the document is an
array of node objects, or `{"@context":C,"@graph":[...]}`, and no string of it
mentions `_jld_anon` (`Syntax/JsonLdChunkFold.lean`, the streaming document
form of https://www.w3.org/TR/json-ld11-streaming/,
https://github.com/danbri/factoidal/issues/839). `Prepass` decides this by one
read of the document and `Reader.init` receives its answer as the
generated-prefix argument; any other argument reads the document whole. RDF/XML reads
one child of `rdf:RDF` at a time (`Syntax/RdfXmlChunkFold.lean`,
https://github.com/danbri/factoidal/issues/838); a document that the fold
cannot read item by item (its document element is not `rdf:RDF`, it declares
XML 1.1 or a markup entity, and the other cases of the fall-back rule in that
module) is read whole, by the same parser as before.

## Generated blank-node labels

Turtle and TriG mint a label for each `[]`, each collection cell and each
property list. The label is a prefix and a counter (`Turtle.freshBnodePrefix`).
The prefix has one more consecutive underscore than the longest run of
underscores in the whole document, so a label the document writes
(`_:anon___0`) cannot equal a generated one. A reader that sees one chunk
cannot know that run length, so `Reader.init` takes the prefix as an argument
and `Prepass` computes it by one read of the document before the first chunk
goes to the reader. RDF/XML mints `b<N>` and writes `rdf:nodeID` values as
`n<value>`; these cannot collide. N-Triples and N-Quads mint nothing.
JSON-LD mints `_jld_anon`, the fewest underscores for which no label of the
document begins with the prefix (none when no label begins with `_jld_anon`),
and a counter (`JSONLD/ToRdf.lean`, `generatedPrefix`). A label the document
writes is passed through, and `JSONLD.generated_ne_written` proves that it
cannot equal a generated one (https://github.com/danbri/factoidal/issues/840).

## What is proved and what is measured

`SourceTheorems.lean`. The whole reader (JSON-LD) gives `parseDocument` of
the joined chunks for every split. The RDF/XML reader gives it when the fold
falls back (`rdfxml_readAll_of_notStreamed`); when it reads item by item the
equality is measured, not proved (row RX-1 of `tests/known-defects/run.sh`,
https://github.com/danbri/factoidal/issues/936). The N-Quads reader gives
the batch fold of the joined chunks in RDF 1.1 mode, from
`NQuadsFold.streamConsume11_eq_batch` through `StrictFeed.LineFeed`. Five
statements are not proved. Each has an open issue and an expected-failure row
in `tests/known-defects/run.sh` or `tests/trig-pack/order_xfail.sh`:

* N-Triples, chunked against batch (`LineFeed.run_triple_eq_batch`, row SF-2),
  and N-Quads in RDF 1.2 mode (`LineFeed.run_quad12_eq_batch`, row SF-3):
  https://github.com/danbri/factoidal/issues/826.
* Turtle: the chunk fold against `parseTurtle`. The accumulator half is proved
  (`Syntax.parseTurtle_eq_fold`); the chunk-boundary half is measured
  (`docs/designissues/2026-09-03-rdf-parsing-strategy.md` section 2.3) and is
  row SF-1 of https://github.com/danbri/factoidal/issues/826. The `#guard`s at
  the end of this file cut each document at every position.
* UTF-8: `ByteReader` decodes the chunks with `Utf8Stream`; the decoding of
  byte chunks equal to the decoding of the whole text is row SF-4 of
  https://github.com/danbri/factoidal/issues/826.
* TriG: the chunk fold against `parseTriG`
  (https://github.com/danbri/factoidal/issues/836).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Format
import L4Factoidal.Syntax.Utf8Stream
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.NQuadsFold
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.StrictFeed
import L4Factoidal.Syntax.StrictFeedText
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.TriGChunkFold
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.RdfXmlChunkFold
import L4Factoidal.Syntax.JsonLdChunkFold
import L4Factoidal.Syntax.TurtleSplitScan

namespace L4Factoidal.RDF.Source

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- The RDF version a source is read as: `.rdf11` (RDF 1.1 Concepts and
    Abstract Syntax) or `.rdf12` (RDF 1.2: triple terms, directional language
    strings). It is the `Mode` of the syntax parsers, named here so that a
    module that does not import a syntax module can state it. -/
abbrev RdfVersion := Mode

/-! ## What a format does -/

/-- Whether a format is always read whole. None is: RDF/XML is read one child
    of `rdf:RDF` at a time and JSON-LD one top-level node object at a time, and
    each is read whole only under its fall-back rule (`RdfXmlChunkFold`,
    `JsonLdChunkFold`). -/
def readsWhole : RdfFormat → Bool
  | .jsonld | .nt | .turtle | .nquads | .trig | .rdfxml => false

/-- A line start is a statement boundary: N-Triples and N-Quads. A source in
    one of these can be cut at line starts into byte ranges that are read
    independently. Turtle, TriG, RDF/XML and JSON-LD cannot be cut so. -/
def splitsAtLines : RdfFormat → Bool
  | .nt | .nquads => true
  | .turtle | .trig | .rdfxml | .jsonld => false

/-- Turtle and TriG mint blank-node labels with a document-wide prefix, which
    `Prepass` computes before the first chunk is read. -/
def needsPrepass : RdfFormat → Bool
  | .turtle | .trig | .jsonld => true
  | .nt | .nquads | .rdfxml => false

/-- The formats whose documents can carry a named graph. -/
def hasNamedGraphs : RdfFormat → Bool
  | .nquads | .trig | .jsonld => true
  | .nt | .turtle | .rdfxml => false

/-! ## Parameters of a reader -/

/-- The consumer of a source: one quad at a time, in the order the document
    states them. `none` is the default graph. -/
abbrev Step (α : Type) := α → Triple → Option Subject → α

/-- The consumer that collects triples, newest first, and drops the graph
    name. The shard packer for IBK2 and IBK3 (one graph per block) folds with
    it. -/
def collect : Step (List Triple) := fun acc t _ => t :: acc

/-- The consumer of the named graphs a document declares: the name of a named
    graph that the document states, with or without a triple (RDF 1.1 Concepts
    section 4: a named graph can be empty). A TriG graph block declares its graph,
    and a JSON-LD document declares each named graph of its dataset. N-Triples,
    Turtle and RDF/XML have no named graph, and an N-Quads line states the graph
    of its quad, so these declare none (2026-10-15,
    https://github.com/danbri/factoidal/issues/855). -/
abbrev Decl (α : Type) := α → Subject → α

/-- The consumer that ignores the declarations. The readers without the `D`
    suffix use it, so a consumer of quads only sees what it saw before. -/
def noDecl {α : Type} : Decl α := fun a _ => a

/-- A parser of one whole document. -/
abbrev DocParser := Mode → Option String → String → Except ParseError Dataset

/-- Readers the caller links in. JSON-LD lives outside this module so that a
    build without the JSON-LD library (the core wasm,
    https://github.com/danbri/factoidal/issues/713 stage 4) does not carry
    it: `L4Factoidal/RDF/SourceJsonLd.lean` supplies `withJsonLd`. -/
structure Extra where
  jsonld : Option DocParser := none
  /-- The item reader of JSON-LD (`Syntax/JsonLdChunkFold.lean`). Without it
      JSON-LD is always read whole. -/
  jsonldStream : Option JsonLdChunkFold.Ops := none

/-- The RDF/XML parser as a `DocParser`. RDF/XML has no named graphs. -/
def rdfXmlParser : DocParser := fun _ base text =>
  (RdfXml.parseRdfXml text base).map fun g => { default := g, named := [] }

/-! ## The batch meaning -/

/-- Parse a whole document into a dataset. For N-Triples, Turtle and RDF/XML
    the triples are the default graph. The parser per format is the one the
    wasm parse op has always called, so that op is unchanged. -/
def parseDocument (extra : Extra) (fmt : RdfFormat) (mode : Mode) (base : Option String)
    (text : String) : Except ParseError Dataset :=
  match fmt with
  | .nt => (parseNTriples text mode).map fun g => { default := g, named := [] }
  | .nquads => parseNQuadsFast text mode
  | .turtle => (parseTurtleText text base mode).map fun g => { default := g, named := [] }
  | .trig => parseTriG text base mode
  | .rdfxml => rdfXmlParser mode base text
  | .jsonld =>
      match extra.jsonld with
      | some parse => parse mode base text
      | none => .error ⟨"JSON-LD is not available in this build", 0⟩

/-- `parseDocument`, with the prefixes the document declared (Turtle and TriG:
    the most recent binding first, as the parsers hold them; `[]` for the other
    formats). -/
def parseDocumentWithPrefixes (extra : Extra) (fmt : RdfFormat) (mode : Mode)
    (base : Option String) (text : String) :
    Except ParseError (Dataset × List (String × String)) :=
  match fmt with
  | .turtle =>
      (parseTurtleWithPrefixes text base mode).map fun (g, ps) =>
        (({ default := g, named := [] } : Dataset), ps)
  | .trig => parseTriGWithPrefixes text base mode
  | .nt | .nquads | .rdfxml | .jsonld =>
      (parseDocument extra fmt mode base text).map fun ds => (ds, [])

/-- Fold a dataset through a consumer: the default graph, then each named
    graph in order. -/
def foldDataset {α : Type} (step : Step α) (acc : α) (ds : Dataset) : α :=
  ds.named.foldl (fun a ng => ng.graph.foldl (fun a t => step a t (some ng.name)) a)
    (ds.default.foldl (fun a t => step a t none) acc)

/-- `foldDataset` that also declares each named graph, before its triples: an
    empty named graph reaches the consumer. -/
def foldDatasetD {α : Type} (step : Step α) (decl : Decl α) (acc : α) (ds : Dataset) : α :=
  ds.named.foldl (fun a ng => ng.graph.foldl (fun a t => step a t (some ng.name)) (decl a ng.name))
    (ds.default.foldl (fun a t => step a t none) acc)

@[simp] theorem foldDatasetD_noDecl {α : Type} (step : Step α) (acc : α) :
    foldDatasetD step noDecl acc = foldDataset step acc := rfl

/-! ## The chunk meaning -/

/-- The Turtle chunk fold hands over the triples a statement completed. -/
def turtleStep {α : Type} (step : Step α) (acc : α) (ts : List Triple) : α :=
  ts.foldl (fun a t => step a t none) acc

/-- The TriG chunk fold hands over the triples a unit completed, with the
    graph the unit belongs to; a graph block of a named graph is handed over once
    with no triple when it opens (`TriGChunkFold.applyEvent`), which is its
    declaration. -/
def trigStepD {α : Type} (step : Step α) (decl : Decl α) (acc : α) (g : Option Subject)
    (ts : List Triple) : α :=
  match g, ts with
  | some n, [] => decl acc n
  | _, _ => ts.foldl (fun a t => step a t g) acc

/-- `trigStepD` without declarations. -/
def trigStep {α : Type} (step : Step α) (acc : α) (g : Option Subject) (ts : List Triple) : α :=
  trigStepD step noDecl acc g ts

/-- A reader of one document, generic in the consumer's accumulator `α`.

    `nquads` and `ntriples` are one line walk (`StrictFeed.LineFeed`) with
    two statement readers: `quadReader` reads an optional graph name, and
    `tripleReader` (the reader of `parseNTriples`) reads none, so a statement
    that names a graph is an N-Triples error. -/
inductive Reader (α : Type) where
  | nquads (mode : Mode) (s : StrictFeedText.TextFeed α)
  | ntriples (mode : Mode) (s : StrictFeedText.TextFeed α)
  | turtle (f : TurtleChunkFoldState α)
  | trig (f : TriGChunkFoldState α)
  /-- RDF/XML: one child of `rdf:RDF` at a time (`RdfXmlChunkFold`). -/
  | rdfxml (f : RdfXmlChunkFold.State α)
  /-- JSON-LD: one top-level node object at a time, for a document that the
      `Prepass` found eligible (`JsonLdChunkFold`). -/
  | jsonldItems (f : JsonLdChunkFold.State α)
  /-- JSON-LD (and any whole parser): the chunks, newest first, and the parser that reads
      their join. -/
  | whole (parse : DocParser) (mode : Mode) (base : Option String) (acc : α) (bufRev : List String)

/-- A reader at the start of a document. `bnodePrefix` is used by Turtle and
    TriG (`Prepass`) and ignored by the other formats. The only failure is a
    format whose reader the caller did not link: JSON-LD without
    `Extra.jsonld`. -/
def Reader.init {α : Type} (extra : Extra) (fmt : RdfFormat) (mode : Mode)
    (base : Option String) (bnodePrefix : String) (acc : α) : Except String (Reader α) :=
  match fmt with
  | .nquads => .ok (.nquads mode { acc })
  | .nt => .ok (.ntriples mode { acc })
  | .turtle => .ok (.turtle (TurtleChunkFoldState.init bnodePrefix (fun a _ => a) acc base mode))
  | .trig => .ok (.trig (TriGChunkFoldState.init bnodePrefix acc base mode))
  | .rdfxml => .ok (.rdfxml (RdfXmlChunkFold.State.init base acc))
  | .jsonld =>
      match extra.jsonld with
      | some parse =>
          match extra.jsonldStream with
          | some ops =>
              if bnodePrefix == JsonLdChunkFold.streamPrefix then
                .ok (.jsonldItems (JsonLdChunkFold.State.init ops mode base acc))
              else .ok (.whole parse mode base acc [])
          | none => .ok (.whole parse mode base acc [])
      | none => .error "JSON-LD is not available in this build"

/-- Feed one decoded chunk. The consumer sees every quad of every statement
    the chunk completes, and `decl` every named graph the chunk declares (a TriG
    graph block). A parse error is returned at once. -/
def Reader.feedD {α : Type} (step : Step α) (decl : Decl α) : Reader α → String → Except ParseError (Reader α)
  | .nquads mode s, text =>
      (StrictFeedText.TextFeed.feed true mode step s text).map (.nquads mode)
  | .ntriples mode s, text =>
      (StrictFeedText.TextFeed.feed false mode step s text).map (.ntriples mode)
  | .turtle f, text => (f.feed (turtleStep step) text).map .turtle
  | .trig f, text => (f.feed (trigStepD step decl) text).map .trig
  | .rdfxml f, text => (f.feed (fun a t => step a t none) text).map .rdfxml
  | .jsonldItems f, text => (f.feed step decl text).map .jsonldItems
  | .whole parse mode base acc bufRev, text => .ok (.whole parse mode base acc (text :: bufRev))

/-- `feedD` without declarations. -/
def Reader.feed {α : Type} (step : Step α) (r : Reader α) (text : String) : Except ParseError (Reader α) :=
  r.feedD step noDecl text

/-- End of the document: the unfinished statement is read, and a `whole`
    reader parses the joined chunks and declares each named graph of the
    dataset. -/
def Reader.finishD {α : Type} (step : Step α) (decl : Decl α) : Reader α → Except ParseError α
  | .nquads mode s => StrictFeedText.TextFeed.finish true mode step s
  | .ntriples mode s => StrictFeedText.TextFeed.finish false mode step s
  | .turtle f => f.finish (turtleStep step)
  | .trig f => f.finish (trigStepD step decl)
  | .rdfxml f => f.finish (fun a t => step a t none)
  | .jsonldItems f => f.finish
  | .whole parse mode base acc bufRev =>
      (parse mode base (String.join bufRev.reverse)).map (foldDatasetD step decl acc)

/-- `finishD` without declarations. -/
def Reader.finish {α : Type} (step : Step α) (r : Reader α) : Except ParseError α :=
  r.finishD step noDecl

/-- The accumulator now. -/
def Reader.acc {α : Type} : Reader α → α
  | .nquads _ s => s.acc
  | .ntriples _ s => s.acc
  | .turtle f => f.acc
  | .trig f => f.acc
  | .rdfxml f => f.acc
  | .jsonldItems f => f.acc
  | .whole _ _ _ acc _ => acc

/-- Take the accumulator out, give it to `f`, and put the first result back;
    the second result is returned. The accumulator is taken out of the reader
    by a match, so `f` holds the only reference and can update it in place. A
    streaming caller drains finished work this way after every chunk. -/
def Reader.withAcc {α β : Type} (f : α → α × β) : Reader α → Reader α × β
  | .nquads mode ⟨acc, carryText, pos⟩ =>
      let (acc, b) := f acc
      (.nquads mode ⟨acc, carryText, pos⟩, b)
  | .ntriples mode ⟨acc, carryText, pos⟩ =>
      let (acc, b) := f acc
      (.ntriples mode ⟨acc, carryText, pos⟩, b)
  | .turtle ⟨state, acc, pos, scanner⟩ =>
      let (acc, b) := f acc
      (.turtle ⟨state, acc, pos, scanner⟩, b)
  | .trig ⟨state, acc, pos, block, scanner⟩ =>
      let (acc, b) := f acc
      (.trig ⟨state, acc, pos, block, scanner⟩, b)
  | .rdfxml fs =>
      let (fs, b) := fs.withAcc f
      (.rdfxml fs, b)
  | .jsonldItems fs =>
      let (fs, b) := fs.withAcc f
      (.jsonldItems fs, b)
  | .whole parse mode base acc bufRev =>
      let (acc, b) := f acc
      (.whole parse mode base acc bufRev, b)

/-- Replace the accumulator. -/
def Reader.setAcc {α : Type} (r : Reader α) (a : α) : Reader α :=
  (r.withAcc (fun _ => (a, ()))).1

/-- Feed a list of chunks and finish. -/
def Reader.readAll {α : Type} (step : Step α) (r : Reader α) (chunks : List String) :
    Except ParseError α :=
  match chunks.foldlM (fun r c => r.feed step c) r with
  | .error e => .error e
  | .ok r => r.finish step

/-- `readAll` with the declarations. -/
def Reader.readAllD {α : Type} (step : Step α) (decl : Decl α) (r : Reader α) (chunks : List String) :
    Except ParseError α :=
  match chunks.foldlM (fun r c => r.feedD step decl c) r with
  | .error e => .error e
  | .ok r => r.finishD step decl

/-! ## From bytes -/

/-- Why a read stopped. -/
inductive Failure where
  | utf8 (message : String)
  | parse (error : ParseError)

def Failure.message : Failure → String
  | .utf8 m => s!"UTF-8 error: {m}"
  | .parse e => s!"parse error at {e.pos}: {e.msg}"

/-- A reader that takes bytes: the UTF-8 decoder carries a partial code point
    from one chunk to the next, and the reader takes the decoded text. -/
structure ByteReader (α : Type) where
  utf8 : Utf8Stream
  reader : Reader α

def ByteReader.init {α : Type} (extra : Extra) (fmt : RdfFormat) (mode : Mode)
    (base : Option String) (bnodePrefix : String) (acc : α) : Except String (ByteReader α) :=
  (Reader.init extra fmt mode base bnodePrefix acc).map fun reader => ⟨Utf8Stream.init, reader⟩

def ByteReader.feedD {α : Type} (step : Step α) (decl : Decl α) :
    ByteReader α → ByteArray → Except Failure (ByteReader α)
  | ⟨utf8, reader⟩, bytes =>
      match utf8.feed bytes with
      | .error m => .error (.utf8 m)
      | .ok (text, utf8) =>
          match reader.feedD step decl text with
          | .error e => .error (.parse e)
          | .ok reader => .ok ⟨utf8, reader⟩

def ByteReader.feed {α : Type} (step : Step α) (r : ByteReader α) (bytes : ByteArray) :
    Except Failure (ByteReader α) :=
  r.feedD step noDecl bytes

/-- The end of the bytes: a partial code point is an error. The reader is
    returned, not finished, so that a caller can check the source digest
    between the two. -/
def ByteReader.endBytes {α : Type} (r : ByteReader α) : Except Failure (Reader α) :=
  match r.utf8.finish with
  | .error m => .error (.utf8 m)
  | .ok _ => .ok r.reader

def ByteReader.finishD {α : Type} (step : Step α) (decl : Decl α) (r : ByteReader α) : Except Failure α :=
  match r.endBytes with
  | .error f => .error f
  | .ok reader => (reader.finishD step decl).mapError .parse

def ByteReader.finish {α : Type} (step : Step α) (r : ByteReader α) : Except Failure α :=
  r.finishD step noDecl

/-- `Reader.withAcc`, through the byte layer. -/
def ByteReader.withAcc {α β : Type} (f : α → α × β) : ByteReader α → ByteReader α × β
  | ⟨utf8, reader⟩ =>
      let (reader, b) := reader.withAcc f
      (⟨utf8, reader⟩, b)

def ByteReader.acc {α : Type} (r : ByteReader α) : α := r.reader.acc

/-- Replace the accumulator. -/
def ByteReader.setAcc {α : Type} (r : ByteReader α) (a : α) : ByteReader α :=
  (r.withAcc (fun _ => (a, ()))).1

/-! ## Several readers over one document

N-Triples and N-Quads are cut at line starts (`splitsAtLines`). Turtle and
TriG are cut at dot boundaries that `Syntax.SplitScan` finds in one read of
the bytes (https://github.com/danbri/factoidal/issues/842). The reader of the
range after a split starts with `Reader.resume`: it reads the directive
units before the split for their prefixes and base, keeping nothing, sets
the generated blank-node counter to the count of the scan at the split, and,
in TriG, enters the graph block the split is in. A range that ends at a
split ends with `finishRangeCountD`, which accepts a TriG range that ends
inside a graph block and gives the counter at the end.

Blank nodes. A label the document writes (`_:b`) is kept as written by every
reader, so the same label in two ranges is the same blank node, as in the
single reader (a label is scoped to the document). A generated label is the
prefix of the document and the counter (`TurtleState.freshBnode`). Every
range uses the prefix of the document, and starts with the counter the scan
counted before its start (`SplitScan.Split.counter`); the caller checks that
the counter at the end of each range equals the count at the next split.
When all checks hold, the ranges mint the labels of the single reader; a
caller whose check fails reads the document as one range. The quads of all
the ranges, in range order, are the quads of the single reader; this is
measured by `l4split-diff`, not proved
(https://github.com/danbri/factoidal/issues/944). -/

/-- Whether a syntax is cut at statement boundaries found by
    `Syntax.SplitScan`. -/
def splitsAtStatements : RdfFormat → Bool
  | .turtle | .trig => true
  | _ => false

/-- Start a reader inside its document: read `prelude` (the directive units
    before the start, `SplitScan.Plan.directives`) for its directives only,
    set the generated blank-node counter to `counter`, and in TriG enter the
    graph block named by `header`. A reader of another syntax takes an empty
    prelude, no header and no counter only. -/
def Reader.resume {α : Type} (r : Reader α) (prelude : String) (header : Option String)
    (counter : Option Nat := none) : Except ParseError (Reader α) :=
  match r with
  | .turtle f =>
      match header with
      | some _ => .error ⟨"a Turtle reader has no graph block", 0⟩
      | none => (f.resume prelude counter).map .turtle
  | .trig f => (f.resume prelude header counter).map .trig
  | r => if prelude.isEmpty && header.isNone && counter.isNone then .ok r
         else .error ⟨"only a Turtle or TriG reader starts inside a document", 0⟩

/-- `finishD` for a range that ends at a split: a TriG range can end inside a
    graph block. Gives the generated blank-node counter at the end (`none` for
    a syntax other than Turtle and TriG). -/
def Reader.finishRangeCountD {α : Type} (step : Step α) (decl : Decl α) :
    Reader α → Except ParseError (α × Option Nat)
  | .turtle f => (f.finishCount (turtleStep step)).map fun (a, c) => (a, some c)
  | .trig f => (f.finishOpenCount (trigStepD step decl)).map fun (a, c) => (a, some c)
  | r => (r.finishD step decl).map fun a => (a, none)

def ByteReader.resume {α : Type} (r : ByteReader α) (prelude : String) (header : Option String)
    (counter : Option Nat := none) : Except ParseError (ByteReader α) :=
  (r.reader.resume prelude header counter).map fun reader => { r with reader }

/-- `Reader.finishRangeCountD` through the byte layer. -/
def ByteReader.finishRangeCountD {α : Type} (step : Step α) (decl : Decl α) (r : ByteReader α) :
    Except Failure (α × Option Nat) :=
  match r.endBytes with
  | .error f => .error f
  | .ok reader => (reader.finishRangeCountD step decl).mapError .parse

/-! ## The pre-pass for generated blank-node labels -/

/-- One read of the document before the first chunk goes to a Turtle or TriG
    reader: the longest run of underscores in the text, by the same character
    walk that `Syntax.freshBnodePrefix` uses on a whole text. The pre-pass
    reads bytes (a partial code point is carried), decodes them, and counts
    underscores. It also tells whether the text has `<<`, for a caller that
    must send such a document to the reference parser (`Prepass.hasDoubleLt`). -/
structure Prepass where
  utf8 : Utf8Stream := Utf8Stream.init
  underscores : UnderscoreRun := {}
  /-- `StrictFeed.doubleLtStep` over the text so far: 2 when the text has `<<`
      (`TurtleChunkFold.hasDoubleLt`). -/
  lt : Nat := 0
  /-- A JSON-LD document: the shape and mention probe of `JsonLdChunkFold`
      instead of the two counts above (`Prepass.forFormat`). -/
  jld : Option JsonLdChunkFold.Probe := none

/-- The pre-pass for a source in syntax `fmt`. -/
def Prepass.forFormat (fmt : RdfFormat) : Prepass :=
  { jld := if fmt == .jsonld then some {} else none }

def Prepass.feed (p : Prepass) (bytes : ByteArray) : Except String Prepass :=
  match p.utf8.feed bytes with
  | .error m => .error m
  | .ok (text, utf8) =>
      match p.jld with
      | some probe => .ok { p with utf8, jld := some (probe.feedString text) }
      | none =>
          .ok { p with utf8, underscores := p.underscores.feedChars text.toList,
                       lt := text.foldl StrictFeed.doubleLtStep p.lt }

/-- Whether the whole text has `<<`, the opening of an RDF 1.2 triple term or
    reified triple (`TurtleChunkFold.hasDoubleLt`). `parseTurtleText` reads such a
    document with the reference parser. The command line (`l4factoidal parse`)
    reads it whole for the same reason. -/
def Prepass.hasDoubleLt (p : Prepass) : Bool := p.lt == 2

/-- The generated-label prefix of the whole text, once its bytes are all fed.
    For a JSON-LD pre-pass it is the argument that `Reader.init` reads:
    `JsonLdChunkFold.streamPrefix` when the document is read item by item,
    `""` when it is read whole. -/
def Prepass.finish (p : Prepass) : Except String String :=
  match p.utf8.finish with
  | .error m => .error m
  | .ok _ =>
      match p.jld with
      | some probe => .ok probe.prefixArg
      | none => .ok (freshBnodePrefixOfLongest p.underscores.longest)

/-! ## Build-time checks -/

#guard !readsWhole .jsonld && !readsWhole .rdfxml
#guard !readsWhole .turtle && !readsWhole .trig && !readsWhole .nt && !readsWhole .nquads
#guard splitsAtLines .nt && splitsAtLines .nquads
#guard !splitsAtLines .turtle && !splitsAtLines .trig && !splitsAtLines .rdfxml && !splitsAtLines .jsonld
#guard needsPrepass .turtle && needsPrepass .trig && needsPrepass .jsonld && !needsPrepass .nquads

/-- The quads of a dataset in the order `foldDataset` gives them. -/
private def quadsOf (ds : Dataset) : List (Triple × Option Subject) :=
  (foldDataset (fun (a : List (Triple × Option Subject)) t g => (t, g) :: a) [] ds).reverse

/-- The quads a reader gives for a document cut into two chunks at `cut`. -/
private def readCut (fmt : RdfFormat) (mode : Mode) (doc : String) (cut : Nat) :
    Option (List (Triple × Option Subject)) :=
  let cs := doc.toList
  let chunks := [String.ofList (cs.take cut), String.ofList (cs.drop cut)]
  match Reader.init ({} : Extra) fmt mode none (freshBnodePrefix doc) ([] : List (Triple × Option Subject)) with
  | .error _ => none
  | .ok r =>
      match r.readAll (fun a t g => (t, g) :: a) chunks with
      | .ok quads => some quads.reverse
      | .error _ => none

/-- The reader at every cut position gives the quads of `parseDocument`, in the
    same order. Documents are written so that the dataset order and the
    document order are the same (no graph recurs, no triple repeats). -/
private def cutsAgree (fmt : RdfFormat) (mode : Mode) (doc : String) : Bool :=
  let want := (parseDocument {} fmt mode none doc).toOption.map quadsOf
  want.isSome && (List.range (doc.length + 1)).all fun cut => readCut fmt mode doc cut == want

private def refused (fmt : RdfFormat) (mode : Mode) (doc : String) : Bool :=
  (parseDocument {} fmt mode none doc).toOption.isNone &&
    (List.range (doc.length + 1)).all fun cut => (readCut fmt mode doc cut).isNone

private def ntDoc : String :=
  "<http://e/a> <http://e/p> <http://e/b> .\n# a comment\n<http://e/a> <http://e/q> \"x\"@en .\n_:b1 <http://e/p> \"7\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n"

private def nqDoc : String :=
  ntDoc ++ "<http://e/c> <http://e/p> <http://e/d> <http://e/g1> .\n<http://e/c> <http://e/q> \"y\" <http://e/g1> .\n<http://e/e> <http://e/p> <http://e/f> <http://e/g2> .\n"

private def ttlDoc : String :=
  "@prefix e: <http://e/> .\ne:a e:p e:b , e:c ; e:q \"x\"@en .\ne:d e:p [ e:q e:r ] .\ne:f e:p ( 1 2 ) .\n[] e:p e:z .\n"

private def trigDoc : String :=
  "@prefix e: <http://e/> .\n{ e:a e:p e:b }\ne:g1 { e:c e:p e:d ; e:q \"y\" . e:d e:p [] }\nGRAPH e:g2 { e:e e:p ( 1 2 ) }\n"

private def xmlDoc : String :=
  "<?xml version=\"1.0\"?><rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\"><rdf:Description rdf:about=\"http://e/a\"><e:p rdf:resource=\"http://e/b\"/><e:q>x</e:q></rdf:Description><rdf:Description><e:p>y</e:p></rdf:Description></rdf:RDF>"

#guard cutsAgree .nt .rdf11 ntDoc
#guard cutsAgree .nquads .rdf11 nqDoc
#guard cutsAgree .nquads .rdf12 nqDoc
#guard cutsAgree .turtle .rdf11 ttlDoc
#guard cutsAgree .trig .rdf11 trigDoc
#guard cutsAgree .rdfxml .rdf11 xmlDoc

-- Refusals agree at every cut: a graph name in N-Triples, an unterminated
-- statement, a block that does not close, a document that is not XML.
#guard refused .nt .rdf11 "<http://e/a> <http://e/p> <http://e/b> <http://e/g> .\n"
#guard refused .nquads .rdf11 "<http://e/a> <http://e/p> .\n"
#guard refused .turtle .rdf11 "@prefix e: <http://e/> .\ne:a e:p e:b e:c .\n"
#guard refused .trig .rdf11 "@prefix e: <http://e/> .\ne:g { e:a e:p e:b\n"
#guard refused .rdfxml .rdf11 "<rdf:RDF"

-- N-Triples stays one grammar: N-Quads text with a graph name is refused by
-- `.nt` and read by `.nquads`.
#guard (parseDocument {} .nquads .rdf11 none "<http://e/a> <http://e/p> <http://e/b> <http://e/g> .\n").toOption.isSome

-- A format whose reader the caller did not link is refused at `init`, by name.
#guard (match Reader.init ({} : Extra) .jsonld .rdf11 none "" (0 : Nat) with
        | .error m => m == "JSON-LD is not available in this build"
        | .ok _ => false)

-- The declared named graphs: each graph block of a TriG document, empty or not, at
-- every cut, in the order of `parseDocument`'s named graphs; none for N-Quads, whose
-- named graphs are the graphs of its quads.
private def declCut (fmt : RdfFormat) (doc : String) (cut : Nat) : Option (List Subject) :=
  let cs := doc.toList
  let chunks := [String.ofList (cs.take cut), String.ofList (cs.drop cut)]
  match Reader.init ({} : Extra) fmt .rdf11 none (freshBnodePrefix doc) ([] : List Subject) with
  | .error _ => none
  | .ok r =>
      match r.readAllD (fun a _ _ => a) (fun a n => if a.contains n then a else n :: a) chunks with
      | .ok names => some names.reverse
      | .error _ => none

private def trigEmptyDoc : String :=
  "@prefix e: <http://e/> .\ne:g0 { }\n{ e:a e:p e:b }\ne:g1 { e:c e:p e:d }\nGRAPH _:b { }\n[] { }\n"

#guard (List.range (trigEmptyDoc.length + 1)).all fun cut =>
  declCut .trig trigEmptyDoc cut ==
    (parseDocument {} .trig .rdf11 none trigEmptyDoc).toOption.map fun ds => ds.named.map (·.name)
#guard (parseDocument {} .trig .rdf11 none trigEmptyDoc).toOption.map (fun ds => ds.named.length) == some 4
#guard (List.range (nqDoc.length + 1)).all fun cut => declCut .nquads nqDoc cut == some []

-- Generated labels never equal a written one: the explicit label that a
-- prefix of one underscore less would mint is a different node.
#guard (match parseDocument {} .turtle .rdf11 none "@prefix e: <http://e/> . e:a e:p [] , _:anon__0 ." with
        | .ok ds => (ds.default.map fun t => t.o).eraseDups.length == 2
        | .error _ => false)

-- `Prepass` gives the prefix of the whole text for any cut of its bytes.
#guard (let doc := "a__b ___ c _:anon___0 éé __"
        let bytes := doc.toUTF8
        (List.range (bytes.size + 1)).all fun cut =>
          match (Prepass.feed {} (bytes.extract 0 cut)) with
          | .error _ => false
          | .ok p =>
            match Prepass.feed p (bytes.extract cut bytes.size) with
            | .error _ => false
            | .ok p => p.finish.toOption == some (freshBnodePrefix doc))

end L4Factoidal.RDF.Source
