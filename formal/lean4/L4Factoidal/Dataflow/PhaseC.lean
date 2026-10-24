/-
L4Factoidal.Dataflow.PhaseC — the reader and writer stages of the system, one
for each concrete syntax (https://github.com/danbri/factoidal/issues/975,
phase C).

## Readers

`readerStage extra fmt mode base n` is the batch reader of one syntax: parse
the whole text (`Source.parseDocument`), then give its blank nodes the
document scope `n` (`Dataset.scopeDocument`). `ReaderContract` states, for a
successful run, with `raw` the list that the parser of the syntax gives
(`parseDocumentRaw`) and `ds` its set:

* the set: `SetOf ds raw`, and `ds.den = raw.den`;
* the scope: `out = ds.scopeDocument n`, `out.InScope n`, `out.IsSet`;
* the meaning: `out.den = raw.den.rename (docLabel n)` (exact image) and
  `DatasetDen.Iso raw.den out.den`;
* RDF 1.2 terms: `eraseLabels out = eraseLabels ds`. The scope step changes
  blank-node labels only. Every IRI, every literal (lexical form, datatype,
  language tag, base direction) and every triple term, nested ones included,
  is kept (`eraseLabels_scopeDocument`, from `Term.renameBnodes`, which
  recurses into `Term.tripleTerm`).

The outcomes stay distinct: the run fails exactly when the parser of the
syntax fails, with its message (`readerStage_error`,
`readerStage_error_of_raw`), and succeeds exactly when it succeeds
(`readerStage_ok_of_raw`). `readerStage_eq_scoped` proves that the run is
`scopedParseStage` on `(fmt, text)`.

One stage value for each syntax: `ntriplesReader`, `nquadsReader`,
`turtleReader`, `trigReader`, `rdfxmlReader`, `jsonldReader`
(`Source.withJsonLd`), and `rdfJsonReader` (RDF/JSON, the W3C Note, read by
`RdfJson.parseRdfJson`; `RdfJsonContract`).

What is not proved: that the parser reads the grammar of its syntax. The W3C
syntax suites test it (the registry names them).

## Streaming readers

* `streamSetStage`: the consumer of the streamed N-Triples and Turtle output
  (`l4factoidal parse --out nquads`). For the triples the reader hands it,
  chunk by chunk, it writes the default graph of `Dataset.toSet` of all of
  them, in order, with no repeat (`runChunks_eq_toSet`,
  `runChunks_keyNodup`). That the reader hands the triples of the batch parse
  for every cut of the text is not proved: rows SF-1 (Turtle) and SF-2
  (N-Triples) of `tests/known-defects/run.sh`,
  https://github.com/danbri/factoidal/issues/826.
* `nquads11StreamStage`: the N-Quads chunk reader in RDF 1.1 mode. A
  successful run gives the dataset of the batch parser for the joined chunks
  (`nquads11_readAll_eq_parseNQuadsFast`), so the batch reader on the joined
  text gives its scoped form (`nquads11Stream_reader`). RDF 1.2 mode is row
  SF-3.

## Writers

`writerProjection fmt` is the part of a dataset that the syntax `fmt` can
state:

* N-Triples, Turtle, RDF/XML (no graph name): the union of all the graphs as
  the default graph, no graph name (`writerProjection_triples_den`:
  `unionAllDen`). The empty-named-graph registry and the graph of each
  triple are lost.
* N-Quads (no statement without a triple): every named graph that has a
  triple; an empty named graph is lost (`writerProjection_nquads_den`:
  `dropEmptyDen`).
* TriG, JSON-LD: the dataset.

`writerDomain fmt v` is the set of datasets the writer accepts and is meant to
keep: RDF/XML and JSON-LD have no triple term (the writers refuse one with an
error); JSON-LD has no directional language string (finding: the writer
accepts one and drops its base direction,
https://github.com/danbri/factoidal/issues/984); with N-Triples and N-Quads
every IRI and language tag must be in the lexical space of its grammar
production (IRIREF, LANGTAG). Blank-node labels need no condition
(https://github.com/danbri/factoidal/issues/986): the writers of the N-Triples
family write `Dataset.relabelForWrite` (`RDF/WriterLabels.lean`), which keeps
each BLANK_NODE_LABEL and gives every other label a fresh BLANK_NODE_LABEL,
the same for each occurrence, that no other blank node of the document has (a
blank-node label is local to its document, RDF 1.1 Concepts section 3.4). A
language tag outside LANGTAG (RDF 1.2: subtags of 1 to 8 characters) has no
valid rewrite, and the writers refuse it with an error that names the tag
(`langTagWritable`, `langTagError`). An IRI outside IRIREF is written as it is
(outside the domain; `iriPrintSafe`).

`WriterRoundTrip fmt v` is the round-trip property: on the domain, a
successful write parses back to a dataset whose denotation is isomorphic to
the projection's. Proved for N-Triples and N-Quads, RDF 1.1 and RDF 1.2 modes
(`writerRoundTrip_nt`, `writerRoundTrip_nquads`; the isomorphism is the
relabelling `Dataset.writeLabelMap`, injective on the blank nodes of the
dataset, `writeLabelMap_injOn`; the identity when every label is a
BLANK_NODE_LABEL). Stated, not proved, for Turtle, TriG, RDF/XML and JSON-LD.
`PhaseCTests.lean` tests the property on seeded datasets for every writer, by
the stream writers too.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Instances
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.RDF.SourceTheorems
import L4Factoidal.RDF.StreamSet
import L4Factoidal.RDF.SinkJsonLd
import L4Factoidal.Syntax.RdfJson
import L4Factoidal.Syntax.NTriplesRoundTrip
import L4Factoidal.Syntax.NTriplesDocRoundTrip
import L4Factoidal.Syntax.NQuadsDocRoundTrip
import L4Factoidal.Syntax.NQuadsFastTheorems
import L4Factoidal.Syntax.SyntaxTheorems

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.Syntax

/-! ## Blank-node labels only -/

/-- The dataset with every blank-node label replaced by the empty label: what
is left when the labels are ignored. -/
def eraseLabels (ds : Dataset) : Dataset := ds.renameBnodes (fun _ => "")

/-- **The document scope changes blank-node labels only.** IRIs, literals and
triple terms (nested ones too) are kept. -/
theorem eraseLabels_scopeDocument (n : Nat) (ds : Dataset) :
    eraseLabels (ds.scopeDocument n) = eraseLabels ds := by
  unfold eraseLabels Dataset.scopeDocument
  rw [Dataset.renameBnodes_comp]
  rfl

/-- A triple term stays a triple term under a relabelling: its predicate is
kept, and its subject and object are relabelled. -/
theorem renameBnodes_tripleTerm (f : BNodeId → BNodeId) (s : Subject) (p : WfIri) (o : Term) :
    (Term.tripleTerm s p o).renameBnodes f = .tripleTerm (s.renameBnodes f) p (o.renameBnodes f) :=
  rfl

/-! ## The batch reader of one syntax -/

/-- The contract of the reader of syntax `fmt` with the document scope `n`. -/
def ReaderContract (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode) (base : Option String)
    (n : Nat) (text : String) (out : Dataset) : Prop :=
  ∃ raw ds, parseDocumentRaw extra fmt mode base text = .ok raw ∧ SetOf ds raw ∧
    ds.den = raw.den ∧ out = ds.scopeDocument n ∧ out.IsSet ∧ out.InScope n ∧
    out.den = raw.den.rename (docLabel n) ∧ DatasetDen.Iso raw.den out.den ∧
    eraseLabels out = eraseLabels ds

/-- Parse the whole text of syntax `fmt`, then scope its blank nodes by `n`. -/
def readerStage (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode) (base : Option String)
    (n : Nat) : Stage String String Dataset where
  run text :=
    match parseDocument extra fmt mode base text with
    | .ok ds => .ok (ds.scopeDocument n)
    | .error e => .error e.msg
  contract := ReaderContract extra fmt mode base n
  sound := by
    intro text out h
    split at h
    · next ds hp =>
      injection h with h
      subst h
      obtain ⟨raw, hr, hs⟩ := parseDocument_set extra fmt mode base text ds hp
      have hden := SetOf.den_eq hs
      refine ⟨raw, ds, hr, hs, hden, rfl, Dataset.scopeDocument_isSet n hs.isSet,
        ds.scopeDocument_inScope n, ?_, ?_, eraseLabels_scopeDocument n ds⟩
      · rw [← hden]
        exact Dataset.den_renameBnodes (docLabel n) ds
      · rw [← hden]
        exact ds.den_iso_scopeDocument n
    · cases h

/-- `parseDocument` fails exactly when the parser of the syntax fails, with the
same error. -/
theorem parseDocument_error_iff (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode)
    (base : Option String) (text : String) (e : ParseError) :
    parseDocument extra fmt mode base text = .error e ↔
      parseDocumentRaw extra fmt mode base text = .error e := by
  unfold parseDocument
  split
  · exact Iff.rfl
  · cases parseDocumentRaw extra fmt mode base text with
    | error e' => simp [Except.map]
    | ok raw => simp [Except.map]

/-- **An error of the reader is an error of the parser**, with its message. -/
theorem readerStage_error {extra : Extra} {fmt : RdfFormat} {mode : Syntax.Mode}
    {base : Option String} {n : Nat} {text m : String}
    (h : (readerStage extra fmt mode base n).run text = .error m) :
    ∃ e, parseDocumentRaw extra fmt mode base text = .error e ∧ e.msg = m := by
  dsimp only [readerStage] at h
  split at h
  · cases h
  · next e hp =>
    injection h with h
    exact ⟨e, (parseDocument_error_iff extra fmt mode base text e).mp hp, h⟩

/-- **An error of the parser is an error of the reader**, with its message. -/
theorem readerStage_error_of_raw {extra : Extra} {fmt : RdfFormat} {mode : Syntax.Mode}
    {base : Option String} {n : Nat} {text : String} {e : ParseError}
    (h : parseDocumentRaw extra fmt mode base text = .error e) :
    (readerStage extra fmt mode base n).run text = .error e.msg := by
  have hp := (parseDocument_error_iff extra fmt mode base text e).mpr h
  simp only [readerStage, hp]

/-- **A success of the parser is a success of the reader.** -/
theorem readerStage_ok_of_raw {extra : Extra} {fmt : RdfFormat} {mode : Syntax.Mode}
    {base : Option String} {n : Nat} {text : String} {raw : Dataset}
    (h : parseDocumentRaw extra fmt mode base text = .ok raw) :
    ∃ out, (readerStage extra fmt mode base n).run text = .ok out := by
  cases hp : parseDocument extra fmt mode base text with
  | ok ds => exact ⟨ds.scopeDocument n, by simp only [readerStage, hp]⟩
  | error e =>
    have he := (parseDocument_error_iff extra fmt mode base text e).mp hp
    rw [h] at he
    cases he

/-- The reader is `scopedParseStage` on the pair of the syntax and the text. -/
theorem readerStage_eq_scoped (extra : Extra) (fmt : RdfFormat) (mode : Syntax.Mode)
    (base : Option String) (n : Nat) (text : String) :
    (readerStage extra fmt mode base n).run text = (scopedParseStage extra mode base n).run (fmt, text) := by
  simp only [readerStage, scopedParseStage, Stage.weaken, Stage.comp, parseStage, scopeStage,
    Stage.ofFun]
  cases parseDocument extra fmt mode base text <;> rfl

/-! ### One reader for each syntax -/

/-- N-Triples (RDF 1.1 N-Triples; RDF 1.2 mode reads triple terms). -/
def ntriplesReader (mode : Syntax.Mode) (n : Nat) : Stage String String Dataset :=
  readerStage {} .nt mode none n

/-- N-Quads. -/
def nquadsReader (mode : Syntax.Mode) (n : Nat) : Stage String String Dataset :=
  readerStage {} .nquads mode none n

/-- Turtle, with the base IRI of the document. -/
def turtleReader (mode : Syntax.Mode) (base : Option String) (n : Nat) : Stage String String Dataset :=
  readerStage {} .turtle mode base n

/-- TriG, with the base IRI of the document. -/
def trigReader (mode : Syntax.Mode) (base : Option String) (n : Nat) : Stage String String Dataset :=
  readerStage {} .trig mode base n

/-- RDF/XML, with the base IRI of the document. -/
def rdfxmlReader (mode : Syntax.Mode) (base : Option String) (n : Nat) : Stage String String Dataset :=
  readerStage {} .rdfxml mode base n

/-- JSON-LD (JSON-LD 1.1 API section 8.4, Deserialize JSON-LD to RDF), with
the JSON-LD library linked in. -/
def jsonldReader (mode : Syntax.Mode) (base : Option String) (n : Nat) : Stage String String Dataset :=
  readerStage Source.withJsonLd .jsonld mode base n

/-! ### RDF/JSON -/

/-- The contract of the RDF/JSON reader: `g` is the graph the parser gives,
the output is its set as the default graph, scoped by `n`. -/
def RdfJsonContract (n : Nat) (text : String) (out : Dataset) : Prop :=
  ∃ g, RdfJson.parseRdfJson text = .ok g ∧
    out = (({ default := g, named := [] } : Dataset).toSet).scopeDocument n ∧ out.IsSet ∧
    out.InScope n ∧ out.den = ({ default := g, named := [] } : Dataset).den.rename (docLabel n) ∧
    DatasetDen.Iso ({ default := g, named := [] } : Dataset).den out.den

/-- RDF/JSON (W3C Note, RDF 1.1 JSON Alternate Serialization): triples only. -/
def rdfJsonReader (n : Nat) : Stage String String Dataset where
  run text :=
    match RdfJson.parseRdfJson text with
    | .ok g => .ok ((({ default := g, named := [] } : Dataset).toSet).scopeDocument n)
    | .error e => .error e
  contract := RdfJsonContract n
  sound := by
    intro text out h
    split at h
    · next g hp =>
      injection h with h
      subst h
      have hden := Dataset.den_toSet ({ default := g, named := [] } : Dataset)
      refine ⟨g, hp, rfl, Dataset.scopeDocument_isSet n (Dataset.toSet_isSet _),
        Dataset.scopeDocument_inScope n _, ?_, ?_⟩
      · rw [← hden]
        exact Dataset.den_renameBnodes (docLabel n) _
      · rw [← hden]
        exact Dataset.den_iso_scopeDocument n _
    · cases h

/-! ## Streaming readers -/

/-- The streamed output of the dedup consumer is the default graph of the set
of all the triples handed to it, and has no repeat. -/
def StreamSetContract (chunks : List (List Triple)) (out : Graph) : Prop :=
  out = (Dataset.toSet { default := chunks.flatten, named := [] }).default ∧ out.KeyNodup

/-- The consumer of the streamed N-Triples and Turtle output: the triples it
writes, over all the chunks. -/
def streamSetStage : Stage String (List (List Triple)) Graph :=
  Stage.ofFun (fun chunks => (runChunks chunks).2) StreamSetContract
    (fun chunks => ⟨runChunks_eq_toSet chunks, runChunks_keyNodup chunks⟩)

/-- The N-Quads chunk reader (RDF 1.1 mode), with the consumer of
`parseNQuadsFast`. -/
def nquads11StreamRun (chunks : List String) : Except String Dataset :=
  match (Reader.nquads .rdf11 { acc := ({} : FastDataset) }).readAll addQuadFast chunks with
  | .ok fd => .ok fd.toDataset
  | .error e => .error e.msg

/-- The streamed N-Quads read gives the batch parse of the joined chunks. -/
def NQuadsStreamContract (chunks : List String) (out : Dataset) : Prop :=
  parseDocumentRaw {} .nquads .rdf11 none (String.join chunks) = .ok out

def nquads11StreamStage : Stage String (List String) Dataset where
  run := nquads11StreamRun
  contract := NQuadsStreamContract
  sound := by
    intro chunks out h
    unfold nquads11StreamRun at h
    split at h
    · next fd hr =>
      injection h with h
      subst h
      exact nquads11_readAll_eq_parseNQuadsFast chunks fd hr
    · cases h

/-- **Streamed, then scoped, is the batch reader.** A successful streamed
N-Quads read, scoped by `n`, is the output of the batch N-Quads reader on the
joined text. -/
theorem nquads11Stream_reader {chunks : List String} {out : Dataset}
    (h : nquads11StreamStage.run chunks = .ok out) (n : Nat) :
    (nquadsReader .rdf11 n).run (String.join chunks) = .ok (out.scopeDocument n) := by
  have hc : parseDocumentRaw {} .nquads .rdf11 none (String.join chunks) = .ok out :=
    nquads11StreamStage.sound chunks out h
  have hp : parseDocument {} .nquads .rdf11 none (String.join chunks) = .ok out := hc
  simp only [nquadsReader, readerStage, hp]

/-! ## Writers: the representable domain and the projection -/

/-- The part of a dataset the syntax `fmt` can state. -/
def writerProjection : RdfFormat → Dataset → Dataset
  | .nt | .turtle | .rdfxml => fun ds => { default := Sink.flatten ds, named := [] }
  | .nquads => fun ds => { ds with named := ds.named.filter (fun ng => !ng.graph.isEmpty) }
  | .trig | .jsonld => fun ds => ds

/-- The union of all the graphs as the default graph; no graph name. -/
def unionAllDen (d : DatasetDen) : DatasetDen where
  graph gn t := gn = none ∧ ∃ g0, d.graph g0 t
  names _ := False
  graph_key := by
    rintro gn t u h ⟨hg, g0, hm⟩
    exact ⟨hg, g0, d.graph_key g0 t u h hm⟩
  named_mem := by
    rintro n t ⟨hg, -⟩
    cases hg

/-- The graph names that have a triple; the graphs are kept. -/
def dropEmptyDen (d : DatasetDen) : DatasetDen where
  graph := d.graph
  names n := ∃ t, d.graph (some n) t
  graph_key := d.graph_key
  named_mem := fun _ t h => ⟨t, h⟩

theorem mem_flatten_iff (ds : Dataset) (t : Triple) :
    (Sink.flatten ds).mem t = true ↔ ∃ g0, ds.memQuad t g0 := by
  rw [Graph.mem_iff_key]
  constructor
  · rintro ⟨u, hu, hk⟩
    rw [Sink.flatten, List.mem_append] at hu
    rcases hu with hu | hu
    · exact ⟨none, (Graph.mem_iff_key t _).mpr ⟨u, hu, hk⟩⟩
    · obtain ⟨ng, hng, hu⟩ := List.mem_flatMap.mp hu
      exact ⟨some ng.name, ng, hng, rfl, (Graph.mem_iff_key t _).mpr ⟨u, hu, hk⟩⟩
  · rintro ⟨g0, hm⟩
    cases g0 with
    | none =>
      obtain ⟨u, hu, hk⟩ := (Graph.mem_iff_key t _).mp hm
      exact ⟨u, by rw [Sink.flatten, List.mem_append]; exact Or.inl hu, hk⟩
    | some n =>
      obtain ⟨ng, hng, -, hm⟩ := hm
      obtain ⟨u, hu, hk⟩ := (Graph.mem_iff_key t _).mp hm
      exact ⟨u, by
        rw [Sink.flatten, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨ng, hng, hu⟩), hk⟩

/-- **The projection of a triples-only syntax** (N-Triples, Turtle, RDF/XML)
denotes the union of all the graphs as the default graph, with no graph name. -/
theorem writerProjection_triples_den (fmt : RdfFormat)
    (hf : fmt = .nt ∨ fmt = .turtle ∨ fmt = .rdfxml) (ds : Dataset) :
    (writerProjection fmt ds).den = unionAllDen ds.den := by
  have e : writerProjection fmt ds = { default := Sink.flatten ds, named := [] } := by
    rcases hf with rfl | rfl | rfl <;> rfl
  rw [e]
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show (Sink.flatten ds).mem t = true ↔ (none = none ∧ ∃ g0, ds.memQuad t g0)
      rw [mem_flatten_iff]
      exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
    | some n =>
      show (∃ ng ∈ ([] : List NamedGraph), _) ↔ _
      constructor
      · rintro ⟨_, h, -⟩
        cases h
      · rintro ⟨h, -⟩
        cases h
  · intro m
    show m ∈ ([] : List NamedGraph).map (·.name) ↔ False
    simp

/-- **The projection of N-Quads** keeps every graph and drops the names of the
empty named graphs. -/
theorem writerProjection_nquads_den (ds : Dataset) :
    (writerProjection .nquads ds).den = dropEmptyDen ds.den := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none => exact Iff.rfl
    | some n =>
      show (∃ ng ∈ ds.named.filter (fun ng => !ng.graph.isEmpty), ng.name = n ∧ ng.graph.mem t = true) ↔
        (∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true)
      constructor
      · rintro ⟨ng, hng, hn, hm⟩
        exact ⟨ng, (List.mem_filter.mp hng).1, hn, hm⟩
      · rintro ⟨ng, hng, hn, hm⟩
        refine ⟨ng, List.mem_filter.mpr ⟨hng, ?_⟩, hn, hm⟩
        cases hg : ng.graph with
        | nil => rw [hg] at hm; cases hm
        | cons _ _ => rfl
  · intro m
    show m ∈ (ds.named.filter (fun ng => !ng.graph.isEmpty)).map (·.name) ↔
      ∃ t, ∃ ng ∈ ds.named, ng.name = m ∧ ng.graph.mem t = true
    constructor
    · intro h
      obtain ⟨ng, hng, hn⟩ := List.mem_map.mp h
      obtain ⟨hng, hne⟩ := List.mem_filter.mp hng
      cases hg : ng.graph with
      | nil => rw [hg] at hne; cases hne
      | cons t _ =>
        refine ⟨t, ng, hng, hn, ?_⟩
        rw [hg, Graph.mem_iff_key]
        exact ⟨t, List.mem_cons_self, rfl⟩
    · rintro ⟨t, ng, hng, hn, hm⟩
      refine List.mem_map.mpr ⟨ng, List.mem_filter.mpr ⟨hng, ?_⟩, hn⟩
      cases hg : ng.graph with
      | nil => rw [hg] at hm; cases hm
      | cons _ _ => rfl

/-- **TriG and JSON-LD** state every dataset: no projection. -/
theorem writerProjection_dataset (fmt : RdfFormat) (hf : fmt = .trig ∨ fmt = .jsonld) (ds : Dataset) :
    writerProjection fmt ds = ds := by
  rcases hf with rfl | rfl <;> rfl

/-- A term with a triple term in it. -/
def Term.hasTripleTermB : Term → Bool
  | .tripleTerm _ _ _ => true
  | _ => false

/-- A literal with a base direction (RDF 1.2 directional language string). -/
def Term.hasDirectionB : Term → Bool
  | .literal l => l.val.direction.isSome
  | _ => false

/-- The datasets the writer of `fmt` accepts and is meant to keep. RDF/XML and
JSON-LD: no triple term. JSON-LD: no directional language string (the writer
accepts one and drops the direction, https://github.com/danbri/factoidal/issues/984).
N-Triples: every IRI and language tag in the lexical space of its N-Triples
production (`NTriplesRoundTrip.Triple.ntSafe`: IRIREF [8], LANGTAG [144s]); any
blank-node label, as the writer relabels (`Dataset.relabelForWrite`,
https://github.com/danbri/factoidal/issues/986). N-Quads: the same for each
written quad and its graph label (`NQuadsRoundTrip.Quad.ntSafe`). -/
def writerDomain (fmt : RdfFormat) (ds : Dataset) : Bool :=
  let ts := Sink.flatten ds
  match fmt with
  | .rdfxml => ts.all fun t => !Term.hasTripleTermB t.o
  | .jsonld => ts.all fun t => !Term.hasTripleTermB t.o && !Term.hasDirectionB t.o
  | .nt => ts.all NTriplesRoundTrip.Triple.ntSafe
  | .nquads => (NQuadsRoundTrip.quadsOf ds).all NQuadsRoundTrip.Quad.ntSafe
  | .turtle | .trig => true

/-- **The round-trip property of the writer of `fmt`** (proved for N-Triples and
N-Quads, `writerRoundTrip_nt` and `writerRoundTrip_nquads`): a
set in the domain that the writer writes parses back to a dataset whose
denotation is isomorphic to the projection's. -/
def WriterRoundTrip (fmt : RdfFormat) (v : Syntax.Mode) : Prop :=
  ∀ ds : Dataset, ds.IsSet → writerDomain fmt ds = true → ∀ text,
    Sink.serializeDataset Sink.withJsonLd fmt v ds = .ok text →
    ∃ back, parseDocument Source.withJsonLd fmt v none text = .ok back ∧
      DatasetDen.Iso back.den (writerProjection fmt ds).den

/-! ### The writer stages of N-Triples and N-Quads: proved -/

/-- The contract of the writer of `fmt` on a dataset and its text: on the
domain, the text parses back to a dataset whose denotation is isomorphic to the
projection's. -/
def WriterContract (fmt : RdfFormat) (v : Syntax.Mode) (ds : Dataset) (text : String) : Prop :=
  writerDomain fmt ds = true → ∃ back, parseDocument Source.withJsonLd fmt v none text = .ok back ∧
    DatasetDen.Iso back.den (writerProjection fmt ds).den

/-! ### Relabelling before the write -/

theorem flatten_renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) :
    Sink.flatten (ds.renameBnodes f) = (Sink.flatten ds).map (Triple.renameBnodes f) := by
  simp [Sink.flatten, Dataset.renameBnodes, Graph.renameBnodes, List.map_append, List.map_flatMap,
    List.flatMap_map]

/-- A map injective on the blank nodes of `ds` is injective on the blank nodes
of a dataset whose blank nodes occur in `ds`. -/
theorem injectiveOnBnodes_mono {f : BNodeId → BNodeId} {ds ds2 : Dataset}
    (hsub : ∀ b, ds2.BnodeOccurs b → ds.BnodeOccurs b) (h : ds.InjectiveOnBnodes f) :
    ds2.InjectiveOnBnodes f := by
  rw [Dataset.injectiveOnBnodes_iff] at h ⊢
  exact fun a c ha hc he => h a c (hsub a ha) (hsub c hc) he

theorem bnodeOccurs_of_flatten {ds : Dataset} {b : BNodeId}
    (h : ({ default := Sink.flatten ds, named := [] } : Dataset).BnodeOccurs b) : ds.BnodeOccurs b := by
  rcases h with ⟨t, ht, hb⟩ | ⟨ng, hng, -⟩
  · rw [Sink.flatten, List.mem_append] at ht
    rcases ht with ht | ht
    · exact Or.inl ⟨t, ht, hb⟩
    · obtain ⟨ng, hng, ht⟩ := List.mem_flatMap.mp ht
      exact Or.inr ⟨ng, hng, Or.inr ⟨t, ht, hb⟩⟩
  · cases hng

theorem bnodeOccurs_of_nquadsProjection {ds : Dataset} {b : BNodeId}
    (h : (writerProjection .nquads ds).BnodeOccurs b) : ds.BnodeOccurs b := by
  rcases h with h | ⟨ng, hng, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨ng, (List.mem_filter.mp hng).1, hb⟩

/-- The N-Quads projection of the relabelled dataset is the relabelled
projection. -/
theorem writerProjection_nquads_renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) :
    writerProjection .nquads (ds.renameBnodes f) = (writerProjection .nquads ds).renameBnodes f := by
  simp [writerProjection, Dataset.renameBnodes, Graph.renameBnodes, List.filter_map,
    Function.comp_def, List.isEmpty_map]

/-- **The N-Triples writer keeps its contract**, RDF 1.1 and RDF 1.2 modes.
The writer writes `ds.relabelForWrite` (`RDF/WriterLabels.lean`), whose
blank-node labels are BLANK_NODE_LABELs, so its triples are in
`Triple.ntLex` (`Triple.ntLex_renameBnodes`). The parser gives back the
written list of triples, in order (`parseNTriples_toNTriples`), so the parsed
dataset is the set of the relabelled projection's quads
(`Dataset.den_toSet`). The relabelling is injective on the blank nodes of the
dataset (`writeLabelMap_injOn`), so the isomorphism is the relabelling
(`Dataset.den_iso_renameBnodes`). -/
theorem writerContract_nt (v : Syntax.Mode) (ds : Dataset) (text : String)
    (hser : Sink.serializeDataset Sink.withJsonLd .nt v ds = .ok text) : WriterContract .nt v ds text := by
  intro hdom
  have hall : (Sink.flatten ds.relabelForWrite).all NTriplesRoundTrip.Triple.ntLex = true := by
    rw [relabelForWrite_eq, flatten_renameBnodes, List.all_map]
    apply List.all_eq_true.mpr
    intro t ht
    exact NTriplesRoundTrip.Triple.ntLex_renameBnodes (writeLabelMap_valid ds) (List.all_eq_true.mp hdom t ht)
  have hg : parseNTriples text v = .ok (Sink.flatten ds.relabelForWrite) :=
    NTriplesRoundTrip.parseNTriples_toNTriples v (Sink.flatten ds.relabelForWrite) hall text hser
  refine ⟨({ default := Sink.flatten ds.relabelForWrite, named := [] } : Dataset).toSet, ?_, ?_⟩
  · simp [parseDocument, parseDocumentRaw, givesSet, hg, Except.map]
  · rw [Dataset.den_toSet]
    have e : ({ default := Sink.flatten ds.relabelForWrite, named := [] } : Dataset) =
        (writerProjection .nt ds).renameBnodes ds.writeLabelMap := by
      rw [relabelForWrite_eq, flatten_renameBnodes]
      rfl
    rw [e]
    exact (Dataset.den_iso_renameBnodes (injectiveOnBnodes_mono (fun _ hb => bnodeOccurs_of_flatten hb)
      (writeLabelMap_injOn ds))).symm

/-- **The N-Quads writer keeps its contract**, RDF 1.1 and RDF 1.2 modes. The
writer writes `ds.relabelForWrite`, whose quads are in `Quad.ntLex`
(`Quad.ntLex_renameBnodes`). The parser adds the written quads in order
(`parseNQuads_toNQuads`); the dataset it gives has the quads of the relabelled
dataset, up to RDF term equality (`addAll_quadsOf_memQuad`), and the names of
the graphs that have a triple (`addAll_quadsOf_names`): the denotation of the
relabelled projection (`writerProjection_nquads_den`,
`writerProjection_nquads_renameBnodes`). The isomorphism is the relabelling. -/
theorem writerContract_nquads (v : Syntax.Mode) (ds : Dataset) (text : String)
    (hser : Sink.serializeDataset Sink.withJsonLd .nquads v ds = .ok text) :
    WriterContract .nquads v ds text := by
  intro hdom
  have hall : (NQuadsRoundTrip.quadsOf ds.relabelForWrite).all NQuadsRoundTrip.Quad.ntLex = true := by
    rw [relabelForWrite_eq, NQuadsRoundTrip.quadsOf_renameBnodes, List.all_map]
    apply List.all_eq_true.mpr
    intro q hq
    exact NQuadsRoundTrip.Quad.ntLex_renameBnodes (writeLabelMap_valid ds) (List.all_eq_true.mp hdom q hq)
  have hp : parseNQuads text v =
      .ok (NQuadsRoundTrip.addAll Dataset.empty (NQuadsRoundTrip.quadsOf ds.relabelForWrite)) :=
    NQuadsRoundTrip.parseNQuads_toNQuads v ds.relabelForWrite hall text hser
  refine ⟨NQuadsRoundTrip.addAll Dataset.empty (NQuadsRoundTrip.quadsOf ds.relabelForWrite), ?_, ?_⟩
  · show parseNQuadsFast text v = _
    rw [parseNQuadsFast_eq_parseNQuads, hp]
  · have hden : (NQuadsRoundTrip.addAll Dataset.empty (NQuadsRoundTrip.quadsOf ds.relabelForWrite)).den =
        (writerProjection .nquads ds.relabelForWrite).den := by
      rw [writerProjection_nquads_den]
      apply DatasetDen.ext
      · intro gn t
        exact NQuadsRoundTrip.addAll_quadsOf_memQuad ds.relabelForWrite t gn
      · intro m
        exact NQuadsRoundTrip.addAll_quadsOf_names ds.relabelForWrite m
    rw [hden, relabelForWrite_eq, writerProjection_nquads_renameBnodes]
    exact (Dataset.den_iso_renameBnodes (injectiveOnBnodes_mono (fun _ hb => bnodeOccurs_of_nquadsProjection hb)
      (writeLabelMap_injOn ds))).symm

/-- The N-Triples writer as a stage. -/
def ntriplesWriter (v : Syntax.Mode) : Stage String Dataset String where
  run := Sink.serializeDataset Sink.withJsonLd .nt v
  contract := WriterContract .nt v
  sound := writerContract_nt v

/-- The N-Quads writer as a stage. -/
def nquadsWriter (v : Syntax.Mode) : Stage String Dataset String where
  run := Sink.serializeDataset Sink.withJsonLd .nquads v
  contract := WriterContract .nquads v
  sound := writerContract_nquads v

/-- `WriterRoundTrip .nt v`, both modes. The hypothesis `ds.IsSet` is not
used: a list with a repeat round trips too. -/
theorem writerRoundTrip_nt (v : Syntax.Mode) : WriterRoundTrip .nt v :=
  fun ds _ hdom text hser => writerContract_nt v ds text hser hdom

/-- `WriterRoundTrip .nquads v`, both modes. -/
theorem writerRoundTrip_nquads (v : Syntax.Mode) : WriterRoundTrip .nquads v :=
  fun ds _ hdom text hser => writerContract_nquads v ds text hser hdom

/-- The executable check of `WriterRoundTrip` on one dataset, for the tests:
`Dataset.isomorphic?` (the blank-node bijection search of `RDF/Isomorphism.lean`)
in place of `DatasetDen.Iso`. `none`: the writer refused the dataset. -/
def writerRoundTripB (fmt : RdfFormat) (v : Syntax.Mode) (ds : Dataset) : Option Bool :=
  match Sink.serializeDataset Sink.withJsonLd fmt v ds with
  | .error _ => none
  | .ok text =>
    match parseDocument Source.withJsonLd fmt v none text with
    | .error _ => some false
    | .ok back => some (Dataset.isomorphic? back (writerProjection fmt ds).toSet)

/-- The same check through the stream writer (`Sink.streamDataset`, the union
of the graphs for a syntax with no graph name). -/
def streamRoundTripB (fmt : RdfFormat) (v : Syntax.Mode) (ds : Dataset) : Option Bool :=
  match Sink.streamDataset Sink.withJsonLd fmt { version := v, graphs := .union } ds with
  | .error _ => none
  | .ok text =>
    match parseDocument Source.withJsonLd fmt v none text with
    | .error _ => some false
    | .ok back => some (Dataset.isomorphic? back (writerProjection fmt ds).toSet)

/-- The RDF/JSON round trip on one graph. -/
def rdfJsonRoundTripB (g : Graph) : Option Bool :=
  match RdfJson.graphToRdfJson g with
  | .error _ => none
  | .ok text =>
    match RdfJson.parseRdfJson text with
    | .error _ => some false
    | .ok back => some (Dataset.isomorphic? ({ default := back, named := [] } : Dataset).toSet
        ({ default := g, named := [] } : Dataset).toSet)

#print axioms eraseLabels_scopeDocument
#print axioms readerStage
#print axioms readerStage_error
#print axioms readerStage_error_of_raw
#print axioms readerStage_ok_of_raw
#print axioms readerStage_eq_scoped
#print axioms rdfJsonReader
#print axioms streamSetStage
#print axioms nquads11StreamStage
#print axioms nquads11Stream_reader
#print axioms writerProjection_triples_den
#print axioms writerProjection_nquads_den
#print axioms flatten_renameBnodes
#print axioms writerProjection_nquads_renameBnodes
#print axioms writerContract_nt
#print axioms writerContract_nquads
#print axioms ntriplesWriter
#print axioms nquadsWriter
#print axioms writerRoundTrip_nt
#print axioms writerRoundTrip_nquads

end L4Factoidal.Dataflow
