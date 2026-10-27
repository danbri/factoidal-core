/-
Wasm.Ops.Parse — parseToDatasetJson / serializeNQuads / serializeTurtle.

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  parseToDatasetJson(text, formatTag, baseIRI)
    -> {"ok":true,"count":N,"nquads":"…"} | {"ok":false,"error":"…"}
  serializeNQuads(nquads)
    -> {"ok":true,"nquads":"…"}
  serializeTurtle(nquads)
    -> {"ok":true,"turtle":"…"}

The dataset handle IS the returned N-Quads string, exactly as in the F*
entry.

The N-Quads text of `serializeNQuads`, `serializeTurtle` and `serializeTurtleWith`
is read as RDF 1.2 N-Quads and, when the RDF 1.2 reader refuses it, as RDF 1.1
N-Quads (`RDF.parseNQuadsFast12Or11`,
https://github.com/danbri/factoidal/issues/870). A triple term is accepted, and
so is every text that the RDF 1.1 reader accepted before.

Envelope parity with the F* entry (https://github.com/danbri/factoidal/issues/685),
added after the lines above were written:

  * `parseToDatasetJson` also answers `"prefixes":{label:iri}` (Turtle and TriG;
    `{}` for the other formats), each label once, in declaration order, with its
    latest binding.
  * A parse failure of Turtle, TriG, N-Triples or N-Quads answers
    `{"ok":false,"error":"<msg> at line L, column C","offset":N,"line":L,
    "column":C,"format":"<tag>"}`. The line and the column are 1-based, the
    column counted in Unicode scalar values; `offset` is a count of Unicode
    scalar values from the start of the text (the F* entry counts UTF-8 bytes,
    which the two agree with on ASCII text). RDF/XML and a missing format carry
    the message and `format` only.
  * `serializeTurtleWith(nquads, optionsJson)`, with `{"prefixes":{label:iri},
    "literalShorthand":bool}`.
  * Per-document blank-node scope: the IO entry (`parseToDatasetJsonScoped`,
    which `callIO` serves under the name `parseToDatasetJson`) prefixes every
    blank-node label of a document with `d<N>_`, `N` counting parses in the
    process, as `RDF.Dataset.Merge.rename_dataset_bnodes` does in the F* entry.
    Two documents that both write `_:b0` stay two nodes when their N-Quads are
    concatenated. The pure entry keeps the labels as written, because it has no
    counter. Format tags follow `RDF.Format.fst`'s `format_of_string` table
for the formats the Lean engine parses; a `*12` tag routes to the RDF
1.2 (`Mode.rdf12`) entry points, mirroring `entry_jsoo.ml`'s
consumer-side dispatch.

One table of readers (https://github.com/danbri/factoidal/issues/975, item 2).
The document readers below name a format by its tag (`RDF.formatOfLabel`; the
empty tag is Turtle) and read the document through `readerOf`, the
`RdfReader` of the table `Dataflow.readers` (`L4Factoidal/Dataflow/Reader.lean`).
An `RdfReader` holds its contract as fields: its dataset is the set of the
parse, its scoped dataset satisfies `ReaderContract`, and it fails exactly when
the parser fails. The N-Quads text of a dataset handle is read the same way
(`Dataflow.readNQuadsText`, `readNQuadsText12Or11`).

JSON-LD: the functions that read a document take an `ExtraReader`
(`parseTextToDatasetBy` and the other `…By` forms), which carries the
source-layer readers the build links in. The full dispatch passes
`jsonLdReader` (`Wasm/Ops/ParseJsonLd.lean`, `Source.withJsonLd`: JSON-LD 1.1
through `JSONLD.parseJsonLd` with no document loader), and the core dispatch
(`Wasm/CoreDispatch.lean`) passes a reader that refuses JSON-LD by name. That
parameter is what lets the core wasm link without the JSON-LD library
(https://github.com/danbri/factoidal/issues/713 stage 4). The names without
`By` (`parseTextToDataset`, `parseToDatasetJson`, …) are the JSON-LD-reading
forms and live in `Wasm/Ops/ParseJsonLd.lean`.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note: the umbrella initializer dies under
wasm32).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleChunkFold
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.RDF.Source
import L4Factoidal.Dataflow.Reader
import Std.Data.HashSet
import L4Factoidal.RDF.DatasetMerge
import L4Factoidal.RDF.DocumentScope
import Wasm.Ops.FromDataset
import L4Factoidal.Syntax.LangTagWarnings
import L4Factoidal.RDF.IriSyntax
import Std.Data.HashSet

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Total quad count of a dataset (the F* `dataset_triple_count`).
Not private: `Wasm/Ops/Handles.lean`'s count envelopes use it too. -/
def datasetQuadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (·.graph.length)).foldl (· + ·) 0

/-- Consumer-side RDF 1.2 opt-in, exactly as entry_jsoo.ml: a "*12" tag
selects Mode.rdf12; every other tag keeps the 1.1 path. Returns the mode and
the lower-cased base tag. -/
def resolveModeAndTag (formatTag : String) : Mode × String :=
  let lo := formatTag.toLower
  match lo with
  | "ttl12" | "turtle12"   => (Mode.rdf12, "ttl")
  | "nt12"  | "ntriples12" => (Mode.rdf12, "nt")
  | "nq12"  | "nquads12"   => (Mode.rdf12, "nq")
  | "trig12"               => (Mode.rdf12, "trig")
  | _                      => (Mode.rdf11, lo)

/-- The source-layer readers of a dispatch. `extra` is what the build links
in: `Source.withJsonLd` in the full dispatch (`Wasm/Ops/ParseJsonLd.lean`),
`{}` in the core dispatch, so that the core wasm links without the JSON-LD
library (https://github.com/danbri/factoidal/issues/713 stage 4). `refuse`
gives the error text for a JSON-LD tag when `extra` has no JSON-LD parser;
`none` treats the tag as unknown. Every syntax, JSON-LD included, is read by
the reader of the table `Dataflow.readers extra` (`readerOf`). -/
structure ExtraReader where
  extra : L4Factoidal.RDF.Source.Extra := {}
  refuse : Option (String → String) := none

/-- The reader with no extra syntax: a JSON-LD tag is unknown. -/
def noExtraReader : ExtraReader := {}

/-- **The reader of syntax `fmt` in this dispatch**: the `RdfReader` of the
table `Dataflow.readers`. The document-reading functions below read through it
and through no other parser. -/
def readerOf (extra : ExtraReader) (fmt : RdfFormat) : L4Factoidal.Dataflow.RdfReader :=
  L4Factoidal.Dataflow.readers extra.extra fmt

/-- The format tags of JSON-LD 1.1 (`RDF.Format.fst`'s `format_of_string`). -/
def jsonLdFormatTags : List String := [ "jsonld", "json-ld", "application/ld+json" ]

/-- The format a lower-cased tag names: the labels of `RDF.formatOfLabel`, and
the empty tag, which is Turtle (`RDF.rdfFormatDefault`, the F* entry's default). -/
def formatOfTag (tag : String) : Option RdfFormat :=
  if tag == "" then some rdfFormatDefault else formatOfLabel tag

/-- Parse `text` under `formatTag` into a `Dataset`. Graph-shaped
formats (Turtle, N-Triples, RDF/XML) wrap as the default graph; JSON-LD and a
tag outside the table go to `extra`. The dataset is a set of quads
(`Source.parseDocument`; the answer of `extra` goes through `Dataset.toSet`;
`parseTextToDatasetBy_isSet`).
Not private: `Wasm/Ops/Handles.lean`'s `datasetOpenBy` is the same parse. -/
def parseTextToDatasetReadBy (extra : ExtraReader) (text formatTag baseIRI : String) :
    Except String Dataset :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  let (mode, tag) := resolveModeAndTag formatTag
  let unknown : Except String Dataset := .error s!"unknown format tag '{formatTag}'"
  match formatOfTag tag with
  | none => unknown
  | some fmt =>
      if fmt == .jsonld then
        match extra.extra.jsonld, extra.refuse with
        | some _, _ => ((readerOf extra fmt).dataset { text, mode, base }).mapError (·.msg)
        | none, some refuse => .error (refuse tag)
        | none, none => unknown
      else ((readerOf extra fmt).dataset { text, mode, base }).mapError fmtParseError

/-! ## Every IRI of a dataset is an IRI (https://github.com/danbri/factoidal/issues/1057)

RDF 1.2 Concepts section 3.2: an IRI in an RDF graph is an absolute IRI that
conforms to RFC 3987 section 2.2. The readers check the IRIREF characters; the
N-Triples line loop checks only for a colon, and its round-trip proofs are about
that check. The one engine check is `isAbsoluteIri`, applied to the dataset a
document op reads (`parseTextToDatasetBy`, `parseDocumentOutcomeBy`), the quads a
host supplies (`jsonQuadsLoop`), and the dataset a writer op writes
(`datasetSerialize`), so no writer writes an IRI that no reader reads. Each
distinct IRI is checked once; an IRI in the plain `http(s)` shape
(`isPlainHttpIri`) takes one pass and no table entry. -/

/-- The IRIs of a term (a literal's datatype IRI, the IRIs inside a triple
term), in front of `acc`. -/
def termIrisInto : Term → List String → List String
  | .iri i, acc => i.val :: acc
  | .bnode _, acc => acc
  | .literal l, acc => l.val.datatype.val :: acc
  | .tripleTerm s p o, acc =>
      termIrisInto o (p.val :: (match s with | .iri i => i.val :: acc | .bnode _ => acc))

/-- The IRIs of a triple. -/
def tripleIris (t : Triple) : List String :=
  termIrisInto t.o (t.p.val :: (match t.s with | .iri i => [i.val] | .bnode _ => []))

/-- The IRIs of a quad: its triple's and its graph name's. -/
def quadIris (g : Option Subject) (t : Triple) : List String :=
  match g with
  | some (.iri i) => i.val :: tripleIris t
  | _ => tripleIris t

/-- Every IRI of `t` is in the plain `http(s)` shape (`isPlainHttpIri`), so
each is an absolute IRI. A triple term answers `false` and takes the full
check. The specification of the test `firstInvalidIri?` makes. -/
def tripleAllPlain (t : Triple) : Bool :=
  (match t.s with | .iri i => isPlainHttpIri i.val | .bnode _ => true) &&
  isPlainHttpIri t.p.val &&
  (match t.o with
   | .iri i => isPlainHttpIri i.val
   | .bnode _ => true
   | .literal l => isPlainHttpIri l.val.datatype.val
   | .tripleTerm _ _ _ => false)

/-- `tripleAllPlain` is sound: each IRI of such a triple is plain, so the full
check would accept it, and `firstInvalidIri?` loses nothing when it skips it. -/
theorem tripleAllPlain_sound (t : Triple) (h : tripleAllPlain t = true) :
    ∀ v ∈ tripleIris t, isPlainHttpIri v = true := by
  obtain ⟨s, p, o⟩ := t
  cases s <;> cases o <;>
    simp_all [tripleAllPlain, tripleIris, termIrisInto]

/-- A string that `isPlainHttpIri` accepts. -/
abbrev PlainIri := {v : String // isPlainHttpIri v = true}

theorem isPlainHttpIri_http : isPlainHttpIri "http://" = true := by
  have h7 : ¬ ((⟨7⟩ : String.Pos.Raw) < "http://".rawEndPos) := by
    simp [String.Pos.Raw.lt_iff]; decide
  rw [isPlainHttpIri, plainBytesFrom]
  simp [byteAt, h7, String.Pos.Raw.lt_iff]
  decide

/-- The plain IRI a scan starts from. -/
def PlainIri.start : PlainIri := ⟨"http://", isPlainHttpIri_http⟩

/-- Plain IRIs seen before, one slot for each UTF-8 length modulo 64. The
IRIs of real data repeat (a subject on many lines, a few predicates and
datatypes, class IRIs as objects): a repeat costs one string comparison
(the length, then the bytes) and not a scan. -/
abbrev PlainCache := Array PlainIri

/-- The slot of `v` in a `PlainCache`. -/
@[inline] def plainSlot (v : String) : Nat := v.utf8ByteSize % 64

/-- The empty cache: 64 slots, each `PlainIri.start`. -/
def PlainCache.empty : PlainCache := Array.replicate 64 PlainIri.start

/-- `some c'` when `v` is plain (`isPlainHttpIri`), with `v` in its slot of
`c'`; `none` when it is not. A `v` equal to the IRI of its slot takes no
scan. -/
@[inline] def plainIn (c : PlainCache) (v : String) : Option PlainCache :=
  let k := plainSlot v
  match c[k]? with
  | some x =>
      if x.1 == v then some c
      else if h : isPlainHttpIri v = true then some (c.set! k ⟨v, h⟩) else none
  | none => if isPlainHttpIri v then some c else none

/-- `plainIn` answers `some` exactly for a plain `v`. -/
theorem plainIn_isSome (c : PlainCache) (v : String) :
    (plainIn c v).isSome = isPlainHttpIri v := by
  unfold plainIn
  cases hk : c[plainSlot v]? with
  | none => by_cases hv : isPlainHttpIri v = true <;> simp [hk, hv]
  | some x =>
    simp only [hk]
    by_cases hx : (x.1 == v) = true
    · have e : x.1 = v := beq_iff_eq.mp hx
      rw [if_pos hx, ← e, x.2]; rfl
    · rw [if_neg hx]
      by_cases hv : isPlainHttpIri v = true <;> simp [hv]

theorem plainIn_plain {c c' : PlainCache} {v : String} (h : plainIn c v = some c') :
    isPlainHttpIri v = true := by
  rw [← plainIn_isSome c]; simp [h]

/-- The subject IRI of the triple before, or a new plain one; `none` when
the subject is not plain. A blank-node subject keeps `last`. -/
@[inline] def plainSubject (last : PlainIri) : Subject → Option PlainIri
  | .bnode _ => some last
  | .iri i =>
      if i.val == last.1 then some last
      else if h : isPlainHttpIri i.val = true then some ⟨i.val, h⟩ else none

/-- `some` when every IRI of `t` is plain (the test of `tripleAllPlain`),
with the new subject and cache. -/
@[inline] def plainStep (last : PlainIri) (c : PlainCache) (t : Triple) :
    Option (PlainIri × PlainCache) :=
  match plainSubject last t.s with
  | none => none
  | some s' =>
    match plainIn c t.p.val with
    | none => none
    | some c1 =>
      match t.o with
      | .iri oi => (plainIn c1 oi.val).map (s', ·)
      | .bnode _ => some (s', c1)
      | .literal l => (plainIn c1 l.val.datatype.val).map (s', ·)
      | .tripleTerm _ _ _ => none

theorem plainSubject_sound (last : PlainIri) (s : Subject) (x : PlainIri)
    (h : plainSubject last s = some x) :
    (match s with | .iri i => isPlainHttpIri i.val | .bnode _ => true) = true := by
  cases s with
  | bnode _ => rfl
  | iri i =>
    simp only [plainSubject] at h
    by_cases he : (i.val == last.1) = true
    · have : i.val = last.1 := beq_iff_eq.mp he
      simp [this, last.2]
    · by_cases hv : isPlainHttpIri i.val = true
      · exact hv
      · simp [he, hv] at h

/-- `plainStep` is sound: when it answers `some`, `tripleAllPlain t`, so
each IRI of `t` is plain (`tripleAllPlain_sound`) and an absolute IRI. -/
theorem plainStep_sound (last : PlainIri) (c : PlainCache) (t : Triple) (r : PlainIri × PlainCache)
    (h : plainStep last c t = some r) : tripleAllPlain t = true := by
  obtain ⟨s, p, o⟩ := t
  simp only [plainStep] at h
  cases hs : plainSubject last s with
  | none => simp [hs] at h
  | some s' =>
    have h1 := plainSubject_sound last s s' hs
    cases hc : plainIn c p.val with
    | none => simp [hs, hc] at h
    | some c1 =>
      have h2 := plainIn_plain hc
      cases o with
      | iri oi =>
        cases ho : plainIn c1 oi.val with
        | none => simp [hs, hc, ho] at h
        | some _ =>
          have h3 := plainIn_plain ho
          cases s <;> simp_all [tripleAllPlain]
      | bnode _ => cases s <;> simp_all [tripleAllPlain]
      | literal l =>
        cases ho : plainIn c1 l.val.datatype.val with
        | none => simp [hs, hc, ho] at h
        | some _ =>
          have h3 := plainIn_plain ho
          cases s <;> simp_all [tripleAllPlain]
      | tripleTerm _ _ _ => simp [hs, hc] at h

/-- The full check of the IRIs of `t` that are not plain, each distinct IRI
once (`seen`): `.error v` names the first that is not an absolute IRI. -/
def checkTripleIris (seen : Std.HashSet String) (t : Triple) :
    Except String (Std.HashSet String) :=
  (tripleIris t).foldlM (fun seen v =>
    if isPlainHttpIri v || seen.contains v then .ok seen
    else if isAbsoluteIri v then .ok (seen.insert v) else .error v) seen

/-- The loop of `firstInvalidIri?` over the triples `ts` of a graph, then the
graphs `gs`. A triple whose IRIs are all plain (`plainStep`, sound by
`plainStep_sound`) takes no other test; any other triple takes
`checkTripleIris`. The state is in the arguments, so the loop allocates
nothing for a plain triple whose IRIs it has seen. -/
def scanIris (seen : Std.HashSet String) (last : PlainIri) (c : PlainCache) :
    List Triple → List Graph → Option String
  | [], [] => none
  | [], g :: gs => scanIris seen last c g gs
  | t :: ts, gs =>
    match plainStep last c t with
    | some (s', c') => scanIris seen s' c' ts gs
    | none =>
      -- The cache starts again here: `c` is not used after `plainStep`, so
      -- the compiled `plainIn` updates it in place and does not copy it.
      match checkTripleIris seen t with
      | .error v => some v
      | .ok seen' => scanIris seen' last PlainCache.empty ts gs
termination_by ts gs => (gs.length, ts.length)

/-- The first IRI of `ds` that is not an absolute IRI (`isAbsoluteIri`): the
graph names, then each triple (`scanIris`). -/
def firstInvalidIri? (ds : Dataset) : Option String :=
  match ds.named.find? (fun ng => match ng.name with
      | .iri i => !isAbsoluteIriFast i.val | .bnode _ => false) with
  | some ⟨.iri i, _⟩ => some i.val
  | _ => scanIris {} PlainIri.start PlainCache.empty ds.default
           (ds.named.map (·.graph))

/-- The message for an IRI that is not one. `ErrorModel.classify` gives it the
code `term.invalid-iri`. -/
def invalidIriMessage (v : String) : String :=
  s!"invalid IRI <{v}>: not an absolute IRI (RFC 3987 section 2.2; RDF 1.2 Concepts section 3.2)"

/-- The codepoint offset of `<v>` in `text`, when the document writes it so. -/
def iriOffsetIn (text v : String) : Option Nat :=
  match text.splitOn ("<" ++ v ++ ">") with
  | first :: _ :: _ => some first.length
  | _ => none

/-- Parse `text` under `formatTag` into a `Dataset` (`parseTextToDatasetReadBy`),
and refuse it when an IRI of it is not an absolute IRI. -/
def parseTextToDatasetBy (extra : ExtraReader) (text formatTag baseIRI : String) :
    Except String Dataset :=
  match parseTextToDatasetReadBy extra text formatTag baseIRI with
  | .error e => .error e
  | .ok ds =>
      match firstInvalidIri? ds with
      | some v => .error (invalidIriMessage v)
      | none => .ok ds

/-- `parseToDatasetJson(text, formatTag, baseIRI)`, the pure entry's envelope
(no prefixes, labels as written). -/
def parseToDatasetJsonBy (extra : ExtraReader) (text formatTag baseIRI : String) : String :=
  match parseTextToDatasetBy extra text formatTag baseIRI with
  | .error msg => errJson msg
  | .ok ds =>
      okWith [("count", .number (toString (datasetQuadCount ds))),
              ("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- The N-Quads text of a dataset handle, read as RDF 1.2 N-Quads and, when the
RDF 1.2 reader refuses it, as RDF 1.1 N-Quads, both by the N-Quads reader of
the table (`Dataflow.readNQuadsText`). It is `parseNQuadsFast12Or11`. -/
def readNQuadsText12Or11 (nq : String) : Except ParseError Dataset :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .ok ds => .ok ds
  | .error _ => L4Factoidal.Dataflow.readNQuadsText .rdf11 nq

theorem readNQuadsText12Or11_eq (nq : String) :
    readNQuadsText12Or11 nq = parseNQuadsFast12Or11 nq := by
  cases h : parseNQuadsFast nq .rdf12 <;>
    simp [readNQuadsText12Or11, parseNQuadsFast12Or11, L4Factoidal.Dataflow.readNQuadsText_eq, h]

/-- `serializeNQuads(nquads)` — reparse and re-serialise in canonical
N-Quads form. The text is read as RDF 1.2 N-Quads, and as RDF 1.1 N-Quads when
the RDF 1.2 reader refuses it (`parseNQuadsFast12Or11`,
https://github.com/danbri/factoidal/issues/870). -/
def serializeNQuads (nq : String) : String :=
  match readNQuadsText12Or11 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds   => okWith [("nquads", .string (Dataset.toCanonicalNQuads ds))]

/-- `serializeTurtle(nquads)` — prefix-compacted pretty-print. Named
graphs are flattened into the default graph for this path (the
fidelity-preserving path is serializeNQuads / canonicalizeToNQuads),
mirroring `entry_jsoo.ml`'s `serialize_turtle`. The text is read as in
`serializeNQuads`, so a triple term is written as `<<( ... )>>`. -/
def serializeTurtle (nq : String) : String :=
  match readNQuadsText12Or11 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      let g := ds.default ++ ds.named.flatMap (·.graph)
      okWith [("turtle", .string (turtleOfGraphAuto g))]

/-- The Turtle text `serializeTurtle` would put in its envelope for the
canonical N-Quads of `ds`, or the envelope's error text, computed from the
parsed dataset (`datasetForOps12Or11`, issues 724 and 870). The command line
prints it without the JSON envelope. -/
def serializeTurtleTextOf (ds : Dataset) : Except String String :=
  match datasetForOps12Or11 ds with
  | .error e => .error (fmtParseError e)
  | .ok d => .ok (turtleOfGraphAuto (d.default ++ d.named.flatMap (·.graph)))

/-- `serializeTurtleTextOf` carries exactly the text and the error of the
`serializeTurtle` envelope on the dataset's canonical N-Quads. -/
theorem serializeTurtleTextOf_eq (ds : Dataset) :
    serializeTurtle (Dataset.toCanonicalNQuads ds) =
      match serializeTurtleTextOf ds with
      | .error e => errJson e
      | .ok t => okWith [("turtle", .string t)] := by
  unfold serializeTurtle serializeTurtleTextOf
  rw [datasetForOps12Or11_eq]
  rw [readNQuadsText12Or11_eq]
  cases parseNQuadsFast12Or11 (Dataset.toCanonicalNQuads ds) <;> rfl

/-! ## Positions, prefixes and blank-node scope (issue 685) -/

/-- A parse failure in the shape the envelope reports. `position` is
(offset, line, column) when the failing grammar reports one. -/
structure ParseFailure where
  message  : String
  position : Option (Nat × Nat × Nat) := none

/-- A parsed document and the prefixes it declared: each label once, in
declaration order, with its latest binding. -/
structure ParseOutcome where
  ds       : Dataset
  prefixes : List (String × String)
  /-- The RDF version mode the reader read the document in. -/
  mode     : Mode := .rdf12

/-- 1-based line and 1-based column, counted in Unicode scalar values, of the
character at codepoint `offset` in `text`. An offset past the end gives the
position just after the last character. Port of `position_of_offset`. -/
def lineColumnOfOffset (text : String) (offset : Nat) : Nat × Nat :=
  go (text.toList.take offset) 1 1
where
  go : List Char → Nat → Nat → Nat × Nat
    | [], line, col => (line, col)
    | ch :: rest, line, col =>
        if ch == '\n' then go rest (line + 1) 1 else go rest line (col + 1)

def failureAt (text : String) (e : ParseError) : ParseFailure :=
  let (line, col) := lineColumnOfOffset text e.pos
  { message := e.msg, position := some (e.pos, line, col) }

/-- Keep each label once with its LATEST binding, in the order those latest
bindings were declared. The parsers hold prefixes most recent first and a
re-binding does not remove the older one. Port of
`declaration_order_prefixes`.

This is the SPECIFICATION. It scans the list of the labels seen for each prefix, so a
document of `P` prefixes takes `P * P / 2` string comparisons: 6.3 s for 32,000
prefixes (https://github.com/danbri/factoidal/issues/864). The compiler runs
`declarationOrderPrefixesFast` in its place (`declarationOrderPrefixes_eq_fast`, a
`csimp` theorem), so `parseDocumentOutcomeBy` and `datasetOpen` take linear time. -/
def declarationOrderPrefixes (mostRecentFirst : List (String × String)) :
    List (String × String) :=
  go [] [] mostRecentFirst
where
  go (seen : List String) (acc : List (String × String)) :
      List (String × String) → List (String × String)
    | [] => acc
    | (label, iri) :: rest =>
        if seen.contains label then go seen acc rest
        else go (label :: seen) ((label, iri) :: acc) rest

/-- The loop of `declarationOrderPrefixesFast`: `go` with the labels seen held in a hash
set. -/
def declarationOrderPrefixesLoop (seen : Std.HashSet String) (acc : List (String × String)) :
    List (String × String) → List (String × String)
  | [] => acc
  | (label, iri) :: rest =>
      if seen.contains label then declarationOrderPrefixesLoop seen acc rest
      else declarationOrderPrefixesLoop (seen.insert label) ((label, iri) :: acc) rest

/-- The loop, for every state it can be in: the hash set holds the strings of the
list. -/
theorem declarationOrderPrefixesLoop_eq :
    ∀ (l : List (String × String)) (seenS : Std.HashSet String) (seenL : List String)
      (acc : List (String × String)), (∀ x, seenS.contains x = seenL.contains x) →
      declarationOrderPrefixesLoop seenS acc l = declarationOrderPrefixes.go seenL acc l
  | [], seenS, seenL, acc, _ => by simp [declarationOrderPrefixesLoop, declarationOrderPrefixes.go]
  | (label, iri) :: rest, seenS, seenL, acc, hseen => by
      unfold declarationOrderPrefixesLoop declarationOrderPrefixes.go
      by_cases h : seenL.contains label = true
      · have h' : seenS.contains label = true := by rw [hseen]; exact h
        rw [if_pos h', if_pos h]
        exact declarationOrderPrefixesLoop_eq rest seenS seenL acc hseen
      · have h' : ¬ seenS.contains label = true := by rw [hseen]; exact h
        rw [if_neg h', if_neg h]
        refine declarationOrderPrefixesLoop_eq rest _ _ _ ?_
        intro x
        have hc : (label == x) = (x == label) := by
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
          exact ⟨Eq.symm, Eq.symm⟩
        rw [Std.HashSet.contains_insert, hseen x, List.contains_cons, hc]

/-- `declarationOrderPrefixes` as a loop with a hash set: linear time. -/
def declarationOrderPrefixesFast (mostRecentFirst : List (String × String)) :
    List (String × String) :=
  declarationOrderPrefixesLoop ∅ [] mostRecentFirst

theorem declarationOrderPrefixesFast_eq (mostRecentFirst : List (String × String)) :
    declarationOrderPrefixesFast mostRecentFirst = declarationOrderPrefixes mostRecentFirst := by
  unfold declarationOrderPrefixesFast declarationOrderPrefixes
  exact declarationOrderPrefixesLoop_eq mostRecentFirst ∅ [] [] (fun x => by simp)

/-- Any call of the specification runs the loop. `parseDocumentOutcomeBy` is compiled
after this line. -/
@[csimp] theorem declarationOrderPrefixes_eq_fast :
    @declarationOrderPrefixes = @declarationOrderPrefixesFast := by
  funext l; exact (declarationOrderPrefixesFast_eq l).symm

#print axioms declarationOrderPrefixesLoop_eq
#print axioms declarationOrderPrefixes_eq_fast

/-- `parseTextToDatasetBy`, with the position of a failure and the prefixes of
the document. The two share one dispatch table of formats; only the failure
and the extra result differ. RDF/XML failures carry no position, as in the F*
entry; so does a syntax read by `extra` (JSON-LD), which declares no
prefixes. -/
def parseDocumentOutcomeReadBy (extra : ExtraReader) (text formatTag baseIRI : String) :
    Except ParseFailure ParseOutcome :=
  let base : Option String := if baseIRI == "" then none else some baseIRI
  let (mode, tag) := resolveModeAndTag formatTag
  let noPosition (m : String) : ParseFailure := { message := m }
  let unknown : ParseFailure := noPosition s!"unknown format tag '{formatTag}'"
  match formatOfTag tag with
  | none => .error unknown
  | some fmt =>
      if fmt == .jsonld then
        match extra.extra.jsonld, extra.refuse with
        | some _, _ =>
            match (readerOf extra fmt).run { text, mode, base } with
            | .error e => .error (noPosition e.msg)
            | .ok (ds, _) => .ok { ds := ds, prefixes := [], mode }
        | none, some refuse => .error (noPosition (refuse tag))
        | none, none => .error unknown
      else
        match (readerOf extra fmt).run { text, mode, base } with
        | .error e => .error (if fmt == .rdfxml then noPosition e.msg else failureAt text e)
        | .ok (ds, ps) => .ok { ds := ds, prefixes := declarationOrderPrefixes ps, mode }

/-- `parseDocumentOutcomeReadBy`, refused when an IRI of the dataset is not an
absolute IRI; the failure has the position of `<v>` when the text writes it so. -/
def parseDocumentOutcomeBy (extra : ExtraReader) (text formatTag baseIRI : String) :
    Except ParseFailure ParseOutcome :=
  match parseDocumentOutcomeReadBy extra text formatTag baseIRI with
  | .error f => .error f
  | .ok o =>
      match firstInvalidIri? o.ds with
      | some v =>
          .error (match iriOffsetIn text v with
            | some off => failureAt text ⟨invalidIriMessage v, off⟩
            | none => { message := invalidIriMessage v })
      | none => .ok o

theorem readerDataset_mapError_isSet (r : L4Factoidal.Dataflow.RdfReader)
    (inp : L4Factoidal.Dataflow.ReaderInput) (f : ParseError → String) (ds : Dataset)
    (h : (r.dataset inp).mapError f = .ok ds) : ds.IsSet := by
  unfold L4Factoidal.Dataflow.RdfReader.dataset at h
  cases hr : r.run inp with
  | error e => rw [hr] at h; cases h
  | ok out =>
    rw [hr] at h
    simp only [Except.map, Except.mapError, Except.ok.injEq] at h
    subst h
    exact r.isSet hr

/-- The dataset of `parseTextToDatasetBy` is a set of quads (RDF 1.1 Concepts
section 3: "An RDF graph is a set of RDF triples"): it is the dataset of an
`RdfReader` (`RdfReader.isSet`). -/
theorem parseTextToDatasetReadBy_isSet (extra : ExtraReader) (text formatTag baseIRI : String)
    (ds : Dataset) (h : parseTextToDatasetReadBy extra text formatTag baseIRI = .ok ds) :
    ds.IsSet := by
  unfold parseTextToDatasetReadBy at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · exact readerDataset_mapError_isSet _ _ _ ds h
      · cases h
      · cases h
    · exact readerDataset_mapError_isSet _ _ _ ds h

/-- The dataset of `parseDocumentOutcomeBy`, which `datasetOpen` stores, is a
set of quads: it is the dataset of an `RdfReader`. -/
theorem parseDocumentOutcomeReadBy_isSet (extra : ExtraReader) (text formatTag baseIRI : String)
    (o : ParseOutcome) (h : parseDocumentOutcomeReadBy extra text formatTag baseIRI = .ok o) :
    o.ds.IsSet := by
  unfold parseDocumentOutcomeReadBy at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · split at h
        · cases h
        · next out hr =>
          simp only [Except.ok.injEq] at h
          subst h
          exact (readerOf extra _).isSet hr
      · cases h
      · cases h
    · split at h
      · cases h
      · next out hr =>
        simp only [Except.ok.injEq] at h
        subst h
        exact (readerOf extra _).isSet hr

theorem parseTextToDatasetBy_isSet (extra : ExtraReader) (text formatTag baseIRI : String)
    (ds : Dataset) (h : parseTextToDatasetBy extra text formatTag baseIRI = .ok ds) :
    ds.IsSet := by
  unfold parseTextToDatasetBy at h
  split at h
  · cases h
  · next d hd =>
    split at h
    · cases h
    · cases h
      exact parseTextToDatasetReadBy_isSet extra text formatTag baseIRI _ hd

theorem parseDocumentOutcomeBy_isSet (extra : ExtraReader) (text formatTag baseIRI : String)
    (o : ParseOutcome) (h : parseDocumentOutcomeBy extra text formatTag baseIRI = .ok o) :
    o.ds.IsSet := by
  unfold parseDocumentOutcomeBy at h
  split at h
  · cases h
  · next o0 h0 =>
    split at h
    · cases h
    · cases h
      exact parseDocumentOutcomeReadBy_isSet extra text formatTag baseIRI _ h0

#print axioms parseTextToDatasetBy_isSet
#print axioms parseDocumentOutcomeBy_isSet

-- https://github.com/danbri/factoidal/issues/1057: one IRI check for every
-- syntax. N-Triples keeps a colon-only check in its line loop; the op refuses.
#guard (parseTextToDatasetBy noExtraReader "<a_b:c> <http://a/p> <http://a/o> ." "ntriples" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://www:example.org/> <http://a/p> <http://a/o> ." "nquads" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://a/%zz> <http://a/p> <http://a/o> ." "ntriples12" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://a/s> <http://a/p> \"x\"^^<a_b:c> ." "ntriples" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://a/s> <http://a/p> <http://a/o> <a_b:g> ." "nquads" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://a/s> <http://a/p> <<( <a_b:c> <http://a/p> <http://a/o> )>> ." "ntriples12" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<http://a/s> <http://a/p> <http://a/o> ." "ntriples" "").toOption.isSome
#guard (parseTextToDatasetBy noExtraReader "<a_b:c> <http://a/p> <http://a/o> ." "turtle" "http://ex/").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<:foo> <http://a/p> <http://a/o> ." "turtle" "http://example.org/dir/doc").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "<a/b:c> <http://a/p> <#o> ." "turtle" "http://ex/").toOption.isSome
-- The scan of `firstInvalidIri?` (`scanIris`): a blank-node subject, a subject,
-- predicate and datatype seen in the triple before, a second named graph, and
-- valid IRIs that are not plain.
#guard (parseTextToDatasetBy noExtraReader "_:b <a_b:c> <http://a/o> ." "ntriples" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader "_:b <http://a/p> _:c .\n_:c <http://a/p> \"x\" ." "ntriples" "").toOption.isSome
#guard (parseTextToDatasetBy noExtraReader
  "<http://a/s> <http://a/p> <http://a/o> .\n<http://a/s> <http://a/p> <a_b:c> ." "ntriples" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader
  "<http://a/s> <http://a/p> \"x\" .\n<http://a/s> <http://a/p> \"y\"^^<a_b:c> ." "ntriples" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader
  "<http://a/s> <http://a/p> <http://a/o> <http://a/g> .\n<http://a/s> <a_b:c> <http://a/o> <http://a/h> ." "nquads" "").toOption.isNone
#guard (parseTextToDatasetBy noExtraReader
  "<urn:x:y> <http://a/p?q=1> \"x\"^^<http://a/d%41> .\n<urn:x:y> <http://a:80/p> <http://a/%C3%A9> ." "ntriples" "").toOption.isSome
#guard (match parseTextToDatasetReadBy noExtraReader
    "<http://a/s> <http://a/p> \"x\" .\n<http://a/s> <http://a/p> \"y\"^^<http://a/b#c#d> ." "ntriples" "" with
  | .ok ds => firstInvalidIri? ds == some "http://a/b#c#d"
  | .error _ => false)
#guard (match parseDocumentOutcomeBy noExtraReader "<http://a/s> <http://a/p> <http://a/o> .\n<a_b:c> <http://a/p> <http://a/o> ." "ntriples" "" with
        | .error f => f.position.map (fun (_, line, col) => (line, col)) == some (2, 1) &&
                      (f.message.splitOn "invalid IRI <a_b:c>").length == 2
        | .ok _ => false)

/-- The display tag of an error envelope: the caller's own spelling,
lower-cased, or `turtle` for the empty default. -/
def displayFormatTag (formatTag : String) : String :=
  if formatTag == "" then "turtle" else formatTag.toLower

/-- `{"ok":false,"error":"<msg>[ at line L, column C]","offset"?,"line"?,
"column"?,"format":"<tag>"}`. Shared by `parseToDatasetJson` and `datasetOpen`. -/
def parseFailureEnvelope (formatTag : String) (f : ParseFailure) : String :=
  let fmt := ("format", Json.string (displayFormatTag formatTag))
  match f.position with
  | none =>
      (Json.object [("ok", .bool false), ("error", .string f.message), fmt]).toString
  | some (offset, line, col) =>
      (Json.object
        [ ("ok", .bool false)
        , ("error", .string s!"{f.message} at line {line}, column {col}")
        , ("offset", .number (toString offset))
        , ("line", .number (toString line))
        , ("column", .number (toString col))
        , fmt ]).toString

/-- `{label: iri, …}` in the order given. -/
def prefixesJson (ps : List (String × String)) : Json :=
  .object (ps.map fun (label, iri) => (label, Json.string iri))

/-- Give the dataset a document scope: every blank-node label gets `scope`
in front of it. -/
def scopeBnodes (scope : String) (ds : Dataset) : Dataset :=
  L4Factoidal.RDF.renameDatasetBnodes scope ds

/-- One diagnostic (a recovered error of the lenient parse, or a warning) as an
envelope carries it. -/
def diagnosticJson (d : Diagnostic) : Json :=
  .object
    [ ("message", .string d.message)
    , ("offset", .number (toString d.offset))
    , ("line", .number (toString d.line))
    , ("column", .number (toString d.column))
    , ("class", .string d.cls.tag) ]

/-- The syntax of `formatTag` is of the N-Triples family, so
`Syntax.scanLangTags` finds the position of each language tag. -/
def tagScanFormat (formatTag : String) : Bool :=
  match formatOfTag (resolveModeAndTag formatTag).2 with
  | some .nt | some .nquads | some .turtle | some .trig => true
  | _ => false

/-- The warnings of a document read under `formatTag` into `ds`: one for each
language tag that is not well-formed under BCP 47 (owner decision of
2026-10-24, `Syntax/LangTagWarnings.lean`). -/
def readerWarnings (text formatTag : String) (ds : Dataset) : List Diagnostic :=
  langTagWarnings (tagScanFormat formatTag) text ds

/-- The member `"warnings"` of a successful parse envelope, present only when
there is a warning (so every envelope of a document with no warning is as it
was). -/
def warningsMembers (ws : List Diagnostic) : List (String × Json) :=
  if ws.isEmpty then [] else [("warnings", .array (ws.map diagnosticJson))]

/-- `parseToDatasetJson`, the parity envelope. `scope` is the blank-node label
prefix, or `none` to keep the labels as written. -/
def parseToDatasetJsonWithBy (extra : ExtraReader) (scope : Option String)
    (text formatTag baseIRI : String) : String :=
  match parseDocumentOutcomeBy extra text formatTag baseIRI with
  | .error f => parseFailureEnvelope formatTag f
  | .ok o =>
      let ds := match scope with
        | some pre => scopeBnodes pre o.ds
        | none => o.ds
      okWith ([("count", .number (toString (datasetQuadCount ds))),
              ("nquads", .string (Dataset.toCanonicalNQuads ds)),
              ("prefixes", prefixesJson o.prefixes)] ++
              warningsMembers (readerWarnings text formatTag o.ds))

/-- Parses so far in this process. The scope of the next one is `d<N>_`. -/
initialize documentScopeCounter : IO.Ref Nat ← IO.mkRef 0

/-- The next document scope prefix, `d0_`, `d1_`, … (`RDF.docScope`; two
scope numbers give disjoint labels, `RDF.docLabel_inj`). Never reused. -/
def nextDocumentScope : IO String := do
  let n ← documentScopeCounter.modifyGet fun n => (n, n + 1)
  pure (L4Factoidal.RDF.docScope n)

/-- `parseToDatasetJson` with a fresh blank-node scope per call. `callIO`
serves this entry under the op name `parseToDatasetJson`. -/
def parseToDatasetJsonScopedBy (extra : ExtraReader) (text formatTag baseIRI : String) :
    IO String := do
  let scope ← nextDocumentScope
  pure (parseToDatasetJsonWithBy extra (some scope) text formatTag baseIRI)

/-! ## `serializeTurtleWith` -/

/-- Options of `serializeTurtleWith` and `datasetSerializeWith`: `""` or
`{"prefixes":{label:iri},"literalShorthand":bool}`. `prefixes` maps each label
(the key, without a colon) to its namespace; the renderer wants
(namespace, `label:`) pairs, so this transposes and appends the colon. A
`prefixes` member that is absent keeps `defaultPrefixes`; one entry whose value
is not a string is skipped. `literalShorthand` absent, or not a boolean, is
`true`. -/
def turtleOptionsOfJson (defaultPrefixes : PrefixTable) (optionsJson : String) :
    Except String TurtleRenderOptions :=
  if optionsJson == "" then .ok { prefixes := defaultPrefixes }
  else
    match parseJson optionsJson with
    | .error _ => .error "invalid optionsJson (not valid JSON)"
    | .ok root =>
        let prefixes := match root.field? "prefixes" with
          | some (.object fields) =>
              fields.filterMap fun (label, v) => match v with
                | .string iri => some (iri, label ++ ":")
                | _ => none
          | _ => defaultPrefixes
        let shorthand := match root.field? "literalShorthand" with
          | some (.bool b) => b
          | _ => true
        .ok { prefixes := prefixes, literalShorthand := shorthand }

/-- The graph the pretty-print path renders: named graphs are flattened into
the default graph (the fidelity-preserving path is `serializeNQuads`). -/
def flattenedGraph (ds : Dataset) : Graph :=
  ds.default ++ ds.named.flatMap (·.graph)

/-- `serializeTurtleWith(nquads, optionsJson)`. The text is read as in
`serializeNQuads`. -/
def serializeTurtleWith (nq optionsJson : String) : String :=
  match readNQuadsText12Or11 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      match turtleOptionsOfJson [] optionsJson with
      | .error msg => errJson msg
      | .ok opts => okWith [("turtle", .string (turtleOfGraphOpts opts (flattenedGraph ds)))]

/-- The op names this module adds to the pure dispatch. -/
def parityOpNames : List String := [ "serializeTurtleWith" ]

/-- Serve one of `parityOpNames`, or `none`. -/
def callParity (op : String) (args : List String) : Option String :=
  match op, args with
  | "serializeTurtleWith", [a, b] => some (serializeTurtleWith a b)
  | "serializeTurtleWith", _ =>
      some (errJson s!"serializeTurtleWith expects 2 arguments, got {args.length}")
  | _, _ => none

/-! ## Build-time checks -/

-- Lines are 1-based, columns are 1-based and count Unicode scalar values.
#guard lineColumnOfOffset "" 0 == (1, 1)
#guard lineColumnOfOffset "abc" 0 == (1, 1)
#guard lineColumnOfOffset "abc" 2 == (1, 3)
#guard lineColumnOfOffset "ab\ncd" 3 == (2, 1)
#guard lineColumnOfOffset "ab\ncd" 4 == (2, 2)
-- A multi-byte character is one column.
#guard lineColumnOfOffset "\u00e9\u00e9x" 2 == (1, 3)
#guard lineColumnOfOffset "\u00e9\n\u00e9x" 3 == (2, 2)
-- An offset past the end is the position after the last character.
#guard lineColumnOfOffset "ab\ncd" 99 == (2, 3)

-- Each label once, its latest binding, in the order those bindings were made.
#guard declarationOrderPrefixes [] == []
#guard declarationOrderPrefixes [("a", "3"), ("b", "2"), ("a", "1")] == [("b", "2"), ("a", "3")]
#guard declarationOrderPrefixes [("b", "2"), ("a", "1")] == [("a", "1"), ("b", "2")]

-- The caller's `prefixes` replace the defaults; an absent one keeps them.
#guard (match turtleOptionsOfJson [("http://d/", "d:")] "" with
        | .ok o => o.prefixes == [("http://d/", "d:")] && o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [("http://d/", "d:")] "{}" with
        | .ok o => o.prefixes == [("http://d/", "d:")] && o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [("http://d/", "d:")]
          "{\"prefixes\":{\"x\":\"http://x/\",\"n\":3},\"literalShorthand\":false}" with
        | .ok o => o.prefixes == [("http://x/", "x:")] && !o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [] "{\"literalShorthand\":\"no\"}" with
        | .ok o => o.literalShorthand
        | .error _ => false)
#guard (match turtleOptionsOfJson [] "{" with
        | .error m => m == "invalid optionsJson (not valid JSON)"
        | .ok _ => false)

-- The N-Quads text of the serialising ops is read as RDF 1.2 and, when that reader
-- refuses it, as RDF 1.1 (issue 870). A triple term one level deep, one nested two
-- deep, and a base direction; the document is canonical, so `serializeNQuads` gives
-- it back.
private def tripleTermDoc : String :=
  "<http://e/a> <http://e/p> <<( <http://e/b> <http://e/q> \"x\"@en--ltr )>> .\n" ++
  "<http://e/c> <http://e/p> <<( <http://e/b> <http://e/q> <<( <http://e/d> <http://e/q> <http://e/f> )>> )>> .\n"
#guard serializeNQuads tripleTermDoc == okWith [("nquads", .string tripleTermDoc)]
#guard ((serializeTurtle tripleTermDoc).splitOn "<<(").length == 4
#guard ((serializeTurtleWith tripleTermDoc "").splitOn "<<(").length == 4
-- White space before `@` is RDF 1.2 syntax.
#guard serializeNQuads "<http://e/a> <http://e/p> \"x\" @en .\n" ==
  okWith [("nquads", .string "<http://e/a> <http://e/p> \"x\"@en .\n")]
-- A language tag that only the RDF 1.1 reader reads: the second reader is reached.
private def longTagDoc : String := "<http://e/a> <http://e/p> \"x\"@abcdefghijk .\n"
#guard (parseNQuadsFast longTagDoc .rdf12).toOption.isNone
#guard serializeNQuads longTagDoc == okWith [("nquads", .string longTagDoc)]
#guard ((serializeTurtle longTagDoc).splitOn "@abcdefghijk").length == 2
-- Both readers refuse: the error is the RDF 1.1 reader's, as before.
private def badDoc : String := "<http://e/a> <http://e/p> .\n"
#guard serializeNQuads badDoc ==
  (match parseNQuadsFast badDoc with
   | .error e => errJson (fmtParseError e)
   | .ok _ => "")
#guard (parseNQuadsFast badDoc .rdf12).toOption.isNone

end L4Wasm.Ops
