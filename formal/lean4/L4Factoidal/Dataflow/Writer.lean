/-
L4Factoidal.Dataflow.Writer — the interface type of an RDF writer
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, the writer kind).

## The contract

A writer turns a dataset into the text of one syntax. Its contract is a round
trip: on its declared domain, the text that a successful write gives is read
back, by the `RdfReader` of the same syntax, as a dataset whose denotation is
isomorphic (`DatasetDen.Iso`, a blank-node relabelling) to the writer's
projection of the input (`RoundTripOn`). The projection is the part of the
dataset that the syntax can state (`writerProjection`: a syntax with no graph
name writes the union of the graphs; N-Quads loses an empty named graph).

## The interface type

`RdfWriter` holds the syntax, the write function (`run`), the declared domain
(`domain`), the projection, and `assumed_roundTrip` (the name of the assumed claim, or
`none`) and `roundTrip` (the proof when nothing is assumed).

* `assumed_roundTrip = none`: `roundTrip` is a proof of the claim. The N-Triples and N-Quads
  writers carry `writerContractW_nt` and `writerContractW_nquads`
  (RDF 1.1 and RDF 1.2).
* `assumed_roundTrip = some name`: no proof exists. `name` is the declaration of the
  claim as a `Prop` (`TurtleWriterRoundTrip` and the others below). The
  assumption is named, listed (`assumedWriters`) and checked by the tests; a
  theorem that needs the round trip of such a writer takes the named `Prop` as
  a hypothesis (`RdfWriter.claim_of_assumption`). It is never an `axiom`.

So a writer cannot be added to the table without stating its contract, and the
contract is either a proof or a name on a list.

`writers sx rx` is the table, one writer for each syntax. Every wasm and
command-line path that writes RDF/S syntaxes takes its writer from this
table. `sx` is the writer-side library set (`Sink.Extra`, JSON-LD) and `rx` the
reader-side one (`Source.Extra`): a build without the JSON-LD library passes
`{}`. `canonicalNQuadsRdfWriter` is the canonical N-Quads writer of the dataset
handles (`Dataset.toCanonicalNQuads`).

This module does not import the JSON-LD library, so the core wasm module can
import it.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Reader
import L4Factoidal.RDF.Sink
import L4Factoidal.RDF.SourceTheorems
import L4Factoidal.Syntax.NTriplesRoundTrip
import L4Factoidal.Syntax.NTriplesDocRoundTrip
import L4Factoidal.Syntax.NQuadsDocRoundTrip
import L4Factoidal.Syntax.NQuadsFastTheorems
import L4Factoidal.Syntax.SyntaxTheorems
import L4Factoidal.RDF.DatasetNormalize

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.Syntax

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

/-- The contract of the writer of `fmt` on a dataset and its text, with the
reader-side libraries `rx`: on the domain, the text parses back to a dataset
whose denotation is isomorphic to the projection's. -/
def WriterContractW (rx : Source.Extra) (fmt : RdfFormat) (v : Syntax.Mode) (ds : Dataset)
    (text : String) : Prop :=
  writerDomain fmt ds = true → ∃ back, parseDocument rx fmt v none text = .ok back ∧
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
theorem writerContractW_nt (sx : Sink.Extra) (rx : Source.Extra) (v : Syntax.Mode) (ds : Dataset) (text : String)
    (hser : Sink.serializeDataset sx .nt v ds = .ok text) : WriterContractW rx .nt v ds text := by
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
theorem writerContractW_nquads (sx : Sink.Extra) (rx : Source.Extra) (v : Syntax.Mode) (ds : Dataset) (text : String)
    (hser : Sink.serializeDataset sx .nquads v ds = .ok text) :
    WriterContractW rx .nquads v ds text := by
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


/-! ## The interface type -/

/-- The text of `fmt` for a dataset, with the Turtle options: the Turtle writer
checks the language tags, relabels the blank nodes and renders with `opts`
(`turtleOfGraphOpts`); every other syntax is `Sink.serializeDataset` and
ignores `opts`. -/
def serializeWith (sx : Sink.Extra) (fmt : RdfFormat) (opts : TurtleRenderOptions)
    (v : Syntax.Mode) (ds : Dataset) : Except String String :=
  match fmt with
  | .turtle => do
      Sink.checkLangTags v ds
      pure (turtleOfGraphOpts opts (Sink.flatten ds.relabelForWrite))
  | _ => Sink.serializeDataset sx fmt v ds

/-- With the default options it is `Sink.serializeDataset`. -/
theorem serializeWith_default (sx : Sink.Extra) (fmt : RdfFormat) (v : Syntax.Mode) (ds : Dataset) :
    serializeWith sx fmt {} v ds = Sink.serializeDataset sx fmt v ds := by
  cases fmt <;> rfl

/-- The dataset that the canonical N-Quads writer of a dataset handle writes: a
language tag outside LANGTAG is an error that names the tag, and a blank-node
label outside BLANK_NODE_LABEL gets a fresh valid label
(https://github.com/danbri/factoidal/issues/986). -/
def writeInput (v : Syntax.Mode) (ds : Dataset) : Except String Dataset :=
  match Sink.checkLangTags v ds with
  | .error e => .error e
  | .ok () => .ok ds.relabelForWrite

/-- The text of the canonical N-Quads writer of a dataset handle. -/
def canonicalNQuadsRun (v : Syntax.Mode) (_opts : TurtleRenderOptions) (ds : Dataset) :
    Except String String :=
  (writeInput v ds).map Dataset.toCanonicalNQuads

/-- The domain of the canonical N-Quads writer: the check of
`parseNQuadsFast_toCanonicalNQuads`, on the relabelled dataset. -/
def canonicalNQuadsDomain (v : Syntax.Mode) (ds : Dataset) : Bool :=
  roundTripSafe v ds.relabelForWrite

/-- **The round-trip claim** of a writer: for a set in the domain that the
writer writes with any options, the reader `readers rx fmt` reads the text back
to a dataset whose denotation is isomorphic to the projection's. -/
def RoundTripOn (rx : Source.Extra) (fmt : RdfFormat) (domain : Syntax.Mode → Dataset → Bool)
    (projection : Dataset → Dataset)
    (run : Syntax.Mode → TurtleRenderOptions → Dataset → Except String String)
    (v : Syntax.Mode) : Prop :=
  ∀ (opts : TurtleRenderOptions) (ds : Dataset), ds.IsSet → domain v ds = true → ∀ text,
    run v opts ds = .ok text →
    ∃ back, (readers rx fmt).dataset { text, mode := v } = .ok back ∧
      DatasetDen.Iso back.den (projection ds).den

/-- **A writer of one RDF syntax, with its contract as fields.** -/
structure RdfWriter where
  /-- The writer-side libraries linked in (`Sink.withJsonLd` for JSON-LD). -/
  extra : Sink.Extra
  /-- The reader-side libraries of the matching reader. -/
  readExtra : Source.Extra
  /-- The syntax. -/
  fmt : RdfFormat
  /-- Write a dataset in an RDF version mode; the options are the Turtle ones
  and the other syntaxes ignore them. -/
  run : Syntax.Mode → TurtleRenderOptions → Dataset → Except String String
  /-- The datasets that the writer is meant to keep. -/
  domain : Syntax.Mode → Dataset → Bool
  /-- The part of a dataset that the syntax can state. -/
  projection : Dataset → Dataset
  /-- The name of the `Prop` that is assumed as the round trip with the
  matching reader, or `none` when the round trip is proved (`roundTrip`). An
  unproved contract field of an interface type is named `assumed_<what>`
  (`foundation/README.md`); the gate counts it. -/
  assumed_roundTrip : Option Lean.Name
  /-- The round trip with the matching reader, in each mode: proved when
  nothing is assumed. -/
  roundTrip : ∀ v, assumed_roundTrip = none →
    RoundTripOn readExtra fmt domain projection run v

namespace RdfWriter

/-- The round-trip claim of the writer in mode `v`. -/
def Claim (w : RdfWriter) (v : Syntax.Mode) : Prop :=
  RoundTripOn w.readExtra w.fmt w.domain w.projection w.run v

/-- The name of the assumed claim; `none` for a proved one. -/
def assumption? (w : RdfWriter) (_v : Syntax.Mode) : Option Lean.Name := w.assumed_roundTrip

/-- A writer that assumes nothing has the claim, by its proof. -/
theorem claim_of_proved (w : RdfWriter) (v : Syntax.Mode) (h : w.assumption? v = none) :
    w.Claim v :=
  w.roundTrip v h

/-- A successful write of a set in the domain, read by the matching reader. -/
theorem roundTrip_of_claim (w : RdfWriter) {v : Syntax.Mode} (hc : w.Claim v)
    (opts : TurtleRenderOptions) (ds : Dataset) (hs : ds.IsSet) (hd : w.domain v ds = true)
    (text : String) (hr : w.run v opts ds = .ok text) :
    ∃ back, (readers w.readExtra w.fmt).dataset { text, mode := v } = .ok back ∧
      DatasetDen.Iso back.den (w.projection ds).den :=
  hc opts ds hs hd text hr

end RdfWriter

/-! ## The named assumptions

Each is the round-trip claim of one writer, written out. None has a proof:
the Turtle and TriG writers, the RDF/XML writer, the JSON-LD writer and the
canonical N-Quads writer are tested on seeded datasets
(`Dataflow/PhaseCTests.lean`) and on the W3C syntax suites. -/

/-- Assumed: the Turtle writer, with any options, writes a text that the Turtle
reader reads back to the union of the graphs, up to a blank-node relabelling.
Component fact that exists: the projection (`writerProjection_triples_den`). -/
def TurtleWriterRoundTrip (rx : Source.Extra) (v : Syntax.Mode) : Prop :=
  RoundTripOn rx .turtle (fun _ => writerDomain .turtle) (writerProjection .turtle)
    (fun v opts ds => do
      Sink.checkLangTags v ds
      pure (turtleOfGraphOpts opts (Sink.flatten ds.relabelForWrite))) v

/-- Assumed: the TriG writer, for the whole dataset. -/
def TrigWriterRoundTrip (sx : Sink.Extra) (rx : Source.Extra) (v : Syntax.Mode) : Prop :=
  RoundTripOn rx .trig (fun _ => writerDomain .trig) (writerProjection .trig)
    (fun v _ ds => Sink.serializeDataset sx .trig v ds) v

/-- Assumed: the RDF/XML writer, on datasets with no triple term. -/
def RdfXmlWriterRoundTrip (sx : Sink.Extra) (rx : Source.Extra) (v : Syntax.Mode) : Prop :=
  RoundTripOn rx .rdfxml (fun _ => writerDomain .rdfxml) (writerProjection .rdfxml)
    (fun v _ ds => Sink.serializeDataset sx .rdfxml v ds) v

/-- Assumed: the JSON-LD writer, on datasets with no triple term and no
directional language string. -/
def JsonLdWriterRoundTrip (sx : Sink.Extra) (rx : Source.Extra) (v : Syntax.Mode) : Prop :=
  RoundTripOn rx .jsonld (fun _ => writerDomain .jsonld) (writerProjection .jsonld)
    (fun v _ ds => Sink.serializeDataset sx .jsonld v ds) v

/-- Assumed: the canonical N-Quads writer of the dataset handles, on the
datasets of `canonicalNQuadsDomain`. Component fact that exists:
`parseNQuadsFast_toCanonicalNQuads` (the parse of the text is
`normalizeDataset`); its denotation is not yet related to the projection. -/
def CanonicalNQuadsWriterRoundTrip (rx : Source.Extra) (v : Syntax.Mode) : Prop :=
  RoundTripOn rx .nquads canonicalNQuadsDomain (writerProjection .nquads) canonicalNQuadsRun v

/-! ## The writers -/

/-- The N-Triples writer: the round trip is proved (`writerContractW_nt`). -/
def ntRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .nt
  run v opts ds := serializeWith sx .nt opts v ds
  domain _ := writerDomain .nt
  projection := writerProjection .nt
  assumed_roundTrip := none
  roundTrip v _ := by
    intro opts ds _ hd text hr
    obtain ⟨back, hb, hi⟩ := writerContractW_nt sx rx v ds text hr hd
    exact ⟨back, by rw [readers_dataset]; exact hb, hi⟩

/-- The N-Quads writer: the round trip is proved (`writerContractW_nquads`). -/
def nquadsRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .nquads
  run v opts ds := serializeWith sx .nquads opts v ds
  domain _ := writerDomain .nquads
  projection := writerProjection .nquads
  assumed_roundTrip := none
  roundTrip v _ := by
    intro opts ds _ hd text hr
    obtain ⟨back, hb, hi⟩ := writerContractW_nquads sx rx v ds text hr hd
    exact ⟨back, by rw [readers_dataset]; exact hb, hi⟩

/-- The Turtle writer: the round trip is the assumption `TurtleWriterRoundTrip`. -/
def turtleRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .turtle
  run v opts ds := serializeWith sx .turtle opts v ds
  domain _ := writerDomain .turtle
  projection := writerProjection .turtle
  assumed_roundTrip := some ``TurtleWriterRoundTrip
  roundTrip _ h := by cases h

/-- The TriG writer: the round trip is the assumption `TrigWriterRoundTrip`. -/
def trigRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .trig
  run v opts ds := serializeWith sx .trig opts v ds
  domain _ := writerDomain .trig
  projection := writerProjection .trig
  assumed_roundTrip := some ``TrigWriterRoundTrip
  roundTrip _ h := by cases h

/-- The RDF/XML writer: the round trip is the assumption `RdfXmlWriterRoundTrip`. -/
def rdfxmlRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .rdfxml
  run v opts ds := serializeWith sx .rdfxml opts v ds
  domain _ := writerDomain .rdfxml
  projection := writerProjection .rdfxml
  assumed_roundTrip := some ``RdfXmlWriterRoundTrip
  roundTrip _ h := by cases h

/-- The JSON-LD writer: the round trip is the assumption `JsonLdWriterRoundTrip`.
With `sx = {}` (no JSON-LD library) every write is an error. -/
def jsonldRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .jsonld
  run v opts ds := serializeWith sx .jsonld opts v ds
  domain _ := writerDomain .jsonld
  projection := writerProjection .jsonld
  assumed_roundTrip := some ``JsonLdWriterRoundTrip
  roundTrip _ h := by cases h

/-- The canonical N-Quads writer of the dataset handles: the round trip is the
assumption `CanonicalNQuadsWriterRoundTrip`. -/
def canonicalNQuadsRdfWriter (sx : Sink.Extra) (rx : Source.Extra) : RdfWriter where
  extra := sx
  readExtra := rx
  fmt := .nquads
  run := canonicalNQuadsRun
  domain := canonicalNQuadsDomain
  projection := writerProjection .nquads
  assumed_roundTrip := some ``CanonicalNQuadsWriterRoundTrip
  roundTrip _ h := by cases h

/-- **The writers, one for each syntax.** Every wasm path that writes an RDF
syntax takes its writer from this table. -/
def writers (sx : Sink.Extra) (rx : Source.Extra) : RdfFormat → RdfWriter
  | .nt => ntRdfWriter sx rx
  | .nquads => nquadsRdfWriter sx rx
  | .turtle => turtleRdfWriter sx rx
  | .trig => trigRdfWriter sx rx
  | .rdfxml => rdfxmlRdfWriter sx rx
  | .jsonld => jsonldRdfWriter sx rx

theorem writers_fmt (sx : Sink.Extra) (rx : Source.Extra) (fmt : RdfFormat) :
    (writers sx rx fmt).fmt = fmt := by
  cases fmt <;> rfl

/-- The text of the table's writer with the default options is the text of
`Sink.serializeDataset`. -/
theorem writers_run_default (sx : Sink.Extra) (rx : Source.Extra) (fmt : RdfFormat)
    (v : Syntax.Mode) (ds : Dataset) :
    (writers sx rx fmt).run v {} ds = Sink.serializeDataset sx fmt v ds := by
  have h := serializeWith_default sx fmt v ds
  cases fmt <;> exact h

/-! ### One named writer for each syntax (the registry names them) -/

def ntriplesDocumentWriter : RdfWriter := writers {} {} .nt
def nquadsDocumentWriter : RdfWriter := writers {} {} .nquads
def turtleDocumentWriter : RdfWriter := writers {} {} .turtle
def trigDocumentWriter : RdfWriter := writers {} {} .trig
def rdfxmlDocumentWriter : RdfWriter := writers {} {} .rdfxml
def canonicalNQuadsDocumentWriter : RdfWriter := canonicalNQuadsRdfWriter {} {}

/-- The syntaxes of the table. -/
def allFormats : List RdfFormat := [.nt, .nquads, .turtle, .trig, .rdfxml, .jsonld]

/-- **The named assumptions of the writers**: the writers of the table and the
canonical N-Quads writer whose round trip is assumed in the mode RDF 1.1, with
the name of the assumption. `assumedWriters12` is the same list for RDF 1.2;
the tests pin both. The list may only shrink. -/
def assumedWritersIn (v : Syntax.Mode) : List (RdfFormat × Lean.Name) :=
  ((allFormats.map (writers {} {})) ++ [canonicalNQuadsRdfWriter {} {}]).filterMap fun w =>
    (w.assumption? v).map fun n => (w.fmt, n)

def assumedWriters : List (RdfFormat × Lean.Name) := assumedWritersIn .rdf11

def assumedWriters12 : List (RdfFormat × Lean.Name) := assumedWritersIn .rdf12

#print axioms serializeWith_default
#print axioms writers_run_default
#print axioms writerContractW_nt
#print axioms writerContractW_nquads
#print axioms ntRdfWriter
#print axioms nquadsRdfWriter
#print axioms RdfWriter.claim_of_proved
#print axioms RdfWriter.roundTrip_of_claim
#print axioms writerProjection_triples_den
#print axioms writerProjection_nquads_den

end L4Factoidal.Dataflow
