/-
L4Factoidal.Dataflow.PhaseD — query, update, reasoning and validation as
stages (https://github.com/danbri/factoidal/issues/975, phase D).

Each stage's `sound` is an existing theorem or a short composition of
existing theorems. New proofs in this phase: `SPARQL/UpdateDenotation.lean`
(the update effect on `DatasetDen`) and `mem_select` (graph selection).

## Stages

| stage | in → out | contract | from |
|---|---|---|---|
| `updateStage` | `Dataset × Update` → `Dataset` | `UpdateContract`: on a set, the result is a set and each operation has its SPARQL 1.1 Update effect on `DatasetDen` (`OpsDen`) | `applyUpdateIn_den`, `applyUpdateIn_isSet` |
| `selectStage` | `Dataset` → `Graph` | `SelectContract`: the graph holds the triples of the selected graphs of the denotation | `mem_select` |
| `rdfsSelectStage` | `Dataset` → `Graph` | the closure is RDFS-entailed by the selected graph | `fullClosure_entails` |
| `rhoDfSelectStage` | `Dataset` → `Graph` | ρdf soundness; ρdf completeness when the closure is closed and in the fragment | `closure_rhoDfEntails`, `closure_rhoDf_iff` |
| `simpleEntailsSelectStage` | `Dataset × Graph` → `Bool` | true iff simple entailment (RDF 1.1 Semantics section 5.2), and iff the model-theoretic form for triple-term-free graphs | `simpleEntails_iff_spec`, `simpleEntails_iff_mt` |
| `owlRlSelectStage` | `Dataset` → `Graph` | every output triple is derivable by the OWL 2 RL/RDF rules and true in every interpretation that meets the row conditions | `closure_sound`, `rl_derives_holds` |
| `rifSelectStage` | `Dataset` → `Facts` | the closure keeps every input fact | `RIF.closure_extensive` |
| `shaclStage` | `Graph × Graph` → `ValidationReport` | a conforming report implies SHACL Core conformance of every focus node | `validateWithSparql_sound_core` |
| `bgpSelectStage`, `bgpAskStage` | `Graph` → `SolutionSeq`, `Bool` | each solution instantiates the pattern into the graph | `evalBgp_instantiates_into_graph` |
| `documentToRdfsBgp` | `Document` → `SolutionSeq` | the composed path (below) | `documentToRdfsBgp_sound` |

## Which graph a reasoner reads

RDF 1.1 Semantics defines entailment between graphs, not datasets. A reasoner
stage reads one graph: `GraphSelection` is an explicit parameter that names the
default graph (`default := true`), named graphs (`named`), or both; the stage
reads the UNION of the selected graphs (`Dataset.select`). Union, not merge:
RDF 1.1 Concepts section 4 says "Blank nodes can be shared between graphs in
an RDF dataset", so the graphs of one dataset have one blank-node scope.
`mem_select` states the selected graph on the denotation: a triple is in it
exactly when the denotation holds it in a selected graph. A selected name that
the dataset does not hold, or an empty named graph, adds no triple.

## Completeness: where proved, where missing

* Simple entailment: proved both ways (`simpleEntailsSelectStage`).
* ρdf (the six-rule `RDFS.closure`): proved when the closure is ρdf-closed and
  in the ρdf model fragment (`rhoDfSelectStage`).
* Full RDFS (`RDFS.fullClosure`): soundness only. Completeness is missing; it
  is false without the axiomatic triples (finding C-1,
  `rdfsEntails_subclassSelfLoop_iri`). The negative W3C rdf-mt tests are
  evidence, not proof.
* OWL 2 RL: soundness only. `owlRl_complete_ground` is conditional on a
  Derives-closed closure, which is the open obligation `closureFix_saturated`
  (https://github.com/danbri/factoidal/issues/756); not stated here.
* RIF: extensivity only; per-round licensing (`step_licensed`) is a
  provenance property, not truth. No RIF-BLD model theory, no proof of the
  RDF-to-RIF mapping (`factsOfTriple`).
* SPARQL BGP: soundness only; completeness is the named gap
  `EvalBgpCompleteAt`. So an ASK answer `false` is not proved to mean
  "not entailed".

## The composed path

`documentToRdfsBgp` is `decodeStage`, `parseStage`, `selectStage sel`,
`rdfsClosureStage`, `bgpSelectStage q`. `documentToRdfsBgp_sound`: a successful
run gives the UTF-8 text and the format of the document, the raw parse and its
denotation, the selected graph on that denotation, the closure with
`RdfsEntails` from the selected graph, and for each solution: the pattern
instantiated by it is in the closure (RDF term equality), and, when the
instance and the closure are `TripleExact` / `GraphExact` (no case-folded
language tag in play), the instance is RDFS-entailed by the selected graph.

Premises: `hcmps` (the container membership IRIs are `rdf:_n` IRIs); the
exactness conditions of the last clause. No IO assumption.

Only tested, not proved, on this path: the grammar conformance of the parser
(W3C RDF syntax suites); the step from a SPARQL query string to the `Bgp`
(the stage takes the pattern); the SPARQL algebra beyond a BGP (W3C SPARQL 1.1
and 1.2 suites).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Instances
import L4Factoidal.SPARQL.UpdateDenotation
import L4Factoidal.SPARQL.EntailmentRegimeRdfs
import L4Factoidal.RDF.EntailmentSimpleRefinement
import L4Factoidal.OWL.RLSemantics
import L4Factoidal.RIF.EngineTheorems
import L4Factoidal.RIF.RdfMapping
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.SHACL.SparqlTheorems

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.Source
open L4Factoidal.SPARQL

/-! ## SPARQL Update -/

/-- On a set, the result is a set, and the request has the effect `OpsDen`
states on the denotation: the operations in order, each with its SPARQL 1.1
Update effect (`OpDen`). The input is a value and is not changed; the result is
a new value. -/
def UpdateContract (env : EvalEnv) (inp : Dataset × Update) (out : Dataset) : Prop :=
  inp.1.IsSet → out.IsSet ∧ OpsDen env (requestPrefix inp.1) 0 inp.1 inp.2.ops out

def updateStage (env : EvalEnv) : Stage String (Dataset × Update) Dataset where
  run inp :=
    match applyUpdateIn env inp.1 inp.2 with
    | .ok ds => .ok ds
    | .error e => .error (toString e)
  contract := UpdateContract env
  sound := by
    rintro ⟨ds, u⟩ out h hs
    revert h
    show (match applyUpdateIn env ds u with
      | .ok ds => (.ok ds : Except String Dataset) | .error e => .error (toString e)) = .ok out → _
    cases hu : applyUpdateIn env ds u with
    | error e => intro h; cases h
    | ok ds' =>
      intro h
      injection h with h
      subst h
      exact applyUpdateIn_den env u hs hu

/-! ## Graph selection -/

/-- The graphs a reasoner reads: the default graph when `default`, and the
named graphs whose names are in `named`. -/
structure GraphSelection where
  default : Bool := false
  named : List Subject := []
  deriving Repr, Inhabited

/-- The union of the selected graphs (one blank-node scope: RDF 1.1 Concepts
section 4). -/
def _root_.L4Factoidal.RDF.Dataset.select (sel : GraphSelection) (ds : Dataset) : Graph :=
  (if sel.default then ds.default else []) ++
    (ds.named.filter (fun ng => sel.named.contains ng.name)).flatMap (·.graph)

/-- The selected graphs on the denotation. -/
def GraphSelection.Holds (sel : GraphSelection) (d : DatasetDen) (t : Triple) : Prop :=
  (sel.default = true ∧ d.graph none t) ∨ ∃ n ∈ sel.named, d.graph (some n) t

/-- **The selected graph on the denotation.** -/
theorem mem_select (sel : GraphSelection) (ds : Dataset) (t : Triple) :
    (ds.select sel).mem t = true ↔ sel.Holds ds.den t := by
  rw [Graph.mem_iff_key]
  unfold Dataset.select GraphSelection.Holds
  constructor
  · rintro ⟨u, hu, e⟩
    rcases List.mem_append.mp hu with hu | hu
    · cases hd : sel.default
      · simp [hd] at hu
      · simp only [hd, if_true] at hu
        exact Or.inl ⟨rfl, (Graph.mem_iff_key t ds.default).mpr ⟨u, hu, e⟩⟩
    · obtain ⟨ng, hng, hu⟩ := List.mem_flatMap.mp hu
      obtain ⟨hng, hc⟩ := List.mem_filter.mp hng
      exact Or.inr ⟨ng.name, List.contains_iff_mem.mp hc, ng, hng, rfl,
        (Graph.mem_iff_key t ng.graph).mpr ⟨u, hu, e⟩⟩
  · rintro (⟨hd, hm⟩ | ⟨n, hn, ng, hng, hname, hm⟩)
    · obtain ⟨u, hu, e⟩ := (Graph.mem_iff_key t ds.default).mp hm
      exact ⟨u, List.mem_append.mpr (Or.inl (by simp only [hd, if_true]; exact hu)), e⟩
    · obtain ⟨u, hu, e⟩ := (Graph.mem_iff_key t ng.graph).mp hm
      refine ⟨u, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨ng, ?_, hu⟩)), e⟩
      exact List.mem_filter.mpr ⟨hng, List.contains_iff_mem.mpr (hname ▸ hn)⟩

/-- The output is the union of the selected graphs, and it holds exactly the
triples of the selected graphs of the denotation. -/
def SelectContract (sel : GraphSelection) (ds : Dataset) (g : Graph) : Prop :=
  g = ds.select sel ∧ ∀ t, g.mem t = true ↔ sel.Holds ds.den t

def selectStage (sel : GraphSelection) : Stage String Dataset Graph :=
  Stage.ofFun (Dataset.select sel) (SelectContract sel) (fun ds => ⟨rfl, mem_select sel ds⟩)

/-! ## Reasoners over a selection -/

/-- RDFS closure (RDF 1.1 Semantics section 9, the `fullClosure` regime) of
the selected graphs. -/
def rdfsSelectStage (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (sel : GraphSelection) : Stage String Dataset Graph :=
  (selectStage sel).comp (rdfsClosureStage D cmps hcmps)

/-- **RDFS over a dataset, soundness.** -/
theorem rdfsSelect_sound (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    (sel : GraphSelection) {ds : Dataset} {c : Graph}
    (h : (rdfsSelectStage D cmps hcmps sel).run ds = .ok c) :
    RdfsEntails (fun x => x ∈ D) (ds.select sel) c ∧
      ∀ t, (ds.select sel).mem t = true ↔ sel.Holds ds.den t := by
  obtain ⟨g, ⟨hg, hmem⟩, he⟩ := (rdfsSelectStage D cmps hcmps sel).sound ds c h
  subst hg
  exact ⟨he, hmem⟩

/-- ρdf (the six-rule closure `RDFS.closure`): the closure is ρdf-entailed by
the input, and when it is ρdf-closed and in the ρdf model fragment it decides
ρdf entailment of every triple-term-free graph by simple entailment. -/
def RhoDfContract (g c : Graph) : Prop :=
  RhoDfEntails g c ∧ (RhoDfClosed c → RhoDfModelFragGraph c →
    ∀ e, GraphTtFree e → (RhoDfEntails g e ↔ SimpleEntailmentSpec c e))

def rhoDfClosureStage (fuel : Nat) : Stage String Graph Graph :=
  Stage.ofFun (fun g => RDFS.closure g fuel) RhoDfContract
    (fun g => ⟨closure_rhoDfEntails g fuel, fun hc hf _ he => closure_rhoDf_iff fuel hc hf he⟩)

def rhoDfSelectStage (fuel : Nat) (sel : GraphSelection) : Stage String Dataset Graph :=
  (selectStage sel).comp (rhoDfClosureStage fuel)

/-- Simple entailment (RDF 1.1 Semantics section 5.2) of `h` by the selected
graphs: the answer is `true` exactly when `SimpleEntails`, and, for graphs
without triple terms, exactly when the model-theoretic form holds. -/
def SimpleContract (sel : GraphSelection) (inp : Dataset × Graph) (b : Bool) : Prop :=
  (b = true ↔ SimpleEntails (inp.1.select sel) inp.2) ∧
    (GraphTtFree (inp.1.select sel) → GraphTtFree inp.2 →
      (b = true ↔ SimpleEntailsMt (inp.1.select sel) inp.2))

def simpleEntailsSelectStage (sel : GraphSelection) : Stage String (Dataset × Graph) Bool :=
  Stage.ofFun (fun p => simpleEntails (p.1.select sel) p.2) (SimpleContract sel)
    (fun _ => ⟨SimpleRefinement.simpleEntails_iff_spec _ _,
      fun ha hb => (SimpleRefinement.simpleEntails_iff_spec _ _).trans (simpleEntails_iff_mt ha hb)⟩)

open L4Factoidal.OWL.RL in
/-- OWL 2 RL: every output triple is derivable by the OWL 2 RL/RDF rules
(`Derives`) from the input, and, for an input without the reserved helper
IRIs, true in every interpretation that meets the row conditions, under the
premise assignment extended at the comprehension witnesses. -/
def RlContract (g c : Graph) : Prop :=
  ∀ t ∈ c, Derives g t ∧ (RlReservedFree g → ∀ (i : Interp), RlConditions i →
    ∀ A : BnodeAssignment i.idom, HoldsAll i A g → TripleHolds i (rlExtend i A) t)

open L4Factoidal.OWL.RL in
def owlRlClosureStage : Stage String Graph Graph :=
  Stage.ofFun closureFix RlContract (fun g _ ht =>
    ⟨closure_sound _ g ht, fun hres _ hc _ hA => rl_derives_holds hc hres hA (closure_sound _ g ht)⟩)

def owlRlSelectStage (sel : GraphSelection) : Stage String Dataset Graph :=
  (selectStage sel).comp owlRlClosureStage

/-- RIF: the forward-chaining closure keeps every input fact. -/
def RifContract (facts out : RIF.Facts) : Prop := ∀ f ∈ facts, f ∈ out

def rifClosureStage (rules : List RIF.Rule) (rounds : Nat) : Stage String RIF.Facts RIF.Facts :=
  Stage.ofFun (fun fs => (RIF.closure rules fs rounds).1) RifContract
    (fun fs f hf => RIF.closure_extensive rules rounds fs f hf)

/-- The RIF facts of the selected graphs (`RIF.RdfMapping.factsOfTriple`; the
mapping has no proved contract), then the RIF closure. -/
def rifSelectStage (sel : GraphSelection) (rules : List RIF.Rule) (rounds : Nat) :
    Stage String Dataset RIF.Facts :=
  ((selectStage sel).comp
    (Stage.ofFun (fun g => g.flatMap RIF.RdfMapping.factsOfTriple)
      (fun g fs => fs = g.flatMap RIF.RdfMapping.factsOfTriple) (fun _ => rfl))).comp
    (rifClosureStage rules rounds)

/-! ## SHACL validation -/

open L4Factoidal.SHACL in
/-- The configuration `validateFull` evaluates with (SHACL 1.2 node
expressions read from the shapes graph). -/
def shaclCfg (cfg : ValidationConfig) (data shapesRaw : Graph) : ValidationConfig :=
  { cfg with evalExpr := nodeExprEvaluator shapesRaw data }

open L4Factoidal.SHACL in
/-- A conforming report implies SHACL Core conformance (SHACL section 3.4,
`Spec.GraphConforms`) of every focus node of every shape of the decoded shapes
graph; when the validation ran (no failure), conformance is also the
SHACL-SPARQL conditions (`validateWithSparql_conforms_iff`). -/
def ShaclContract (cfg : ValidationConfig) (inp : Graph × Graph) (r : ValidationReport) : Prop :=
  r.conforms = true →
    Spec.GraphConforms ((shaclCfg cfg inp.1 inp.2).envFor inp.1 (decodeShapesGraph inp.2).shapes)
      inp.1 (decodeShapesGraph inp.2)

open L4Factoidal.SHACL in
/-- `(data graph, shapes graph)` to the report, as `l4shacl` runs it
(`Harness/ShaclProbe.lean`): the shapes graph is decoded, a shapes graph with
unsupported features is refused, and `validateFull` validates. -/
def shaclStage (cfg : ValidationConfig) : Stage String (Graph × Graph) ValidationReport where
  run inp :=
    let sg := decodeShapesGraph inp.2
    if sg.unsupported.isEmpty then .ok (validateFull inp.1 inp.2 sg cfg)
    else .error ("unsupported: " ++ String.intercalate ", " sg.unsupported)
  contract := ShaclContract cfg
  sound := by
    rintro ⟨data, shapes⟩ r h hc
    dsimp only at h
    split at h
    · injection h with h
      subst h
      unfold validateFull at hc
      split at hc
      · simp at hc
      · exact validateWithSparql_sound_core data shapes _ _ hc
    · cases h

/-- SHACL over a dataset: the data graph and the shapes graph are selections. -/
def shaclSelectStage (cfg : L4Factoidal.SHACL.ValidationConfig) (dataSel shapesSel : GraphSelection) :
    Stage String Dataset L4Factoidal.SHACL.ValidationReport :=
  (Stage.ofFun (fun ds => (ds.select dataSel, ds.select shapesSel))
    (fun ds p => p = (ds.select dataSel, ds.select shapesSel)) (fun _ => rfl)).comp (shaclStage cfg)

/-! ## SPARQL basic graph patterns -/

/-- Each solution instantiates the pattern into the graph (RDF term
equality). -/
def BgpContract (q : Bgp) (g : Graph) (sols : SolutionSeq) : Prop :=
  ∀ mu ∈ sols, ∀ t ∈ instBgp q mu, g.mem t = true

def bgpSelectStage (q : Bgp) : Stage String Graph SolutionSeq :=
  Stage.ofFun (evalBgp q) (BgpContract q) (fun g _ hmu => evalBgp_instantiates_into_graph q g hmu)

/-- ASK of a basic graph pattern: `true` implies a solution that instantiates
the pattern into the graph. `false` is not proved to mean "no such solution"
(`EvalBgpCompleteAt` is a named gap). -/
def AskContract (q : Bgp) (g : Graph) (b : Bool) : Prop :=
  b = true → ∃ mu ∈ evalBgp q g, ∀ t ∈ instBgp q mu, g.mem t = true

def bgpAskStage (q : Bgp) : Stage String Graph Bool :=
  Stage.ofFun (fun g => !(evalBgp q g).isEmpty) (AskContract q) (fun g h => by
    have hne : evalBgp q g ≠ [] := by
      intro e
      simp [e] at h
    obtain ⟨mu, hm⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨mu, hm, evalBgp_instantiates_into_graph q g hm⟩)

/-! ## The composed path: document → parse → RDFS closure → BGP -/

/-- Document bytes, then the parser, then the selection, then the RDFS
closure, then the basic graph pattern. -/
def documentToRdfsBgp (extra : Extra) (mode : Syntax.Mode) (base : Option String)
    (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) (sel : GraphSelection)
    (q : Bgp) : Stage String Document SolutionSeq :=
  ((((decodeStage.comp (parseStage extra mode base)).comp (selectStage sel)).comp
    (rdfsClosureStage D cmps hcmps)).comp (bgpSelectStage q))

/-- An RDFS-entailed graph entails each of its exact sub-instances. -/
theorem rdfsEntails_of_mem {D : DatatypeSet} {g c e : Graph} (h : RdfsEntails D g c)
    (hex : GraphExact c) (he : ∀ t ∈ e, TripleExact t ∧ c.mem t = true) : RdfsEntails D g e := by
  intro i hc hs
  obtain ⟨a, ha⟩ := h i hc hs
  refine ⟨a, fun t ht => ?_⟩
  obtain ⟨hte, hm⟩ := he t ht
  obtain ⟨u, hu, hue⟩ := exists_of_graphMem hm
  have e : u = t := tripleExact_eqb_eq (hex u hu) hte hue
  exact e ▸ ha u hu

/-- **The composed path, soundness.** A successful run of `documentToRdfsBgp`
on a document `d` gives:

1. the format of the document's media type (or extension) and its UTF-8 text;
2. the raw parse of the text, and a set dataset `ds` with its denotation;
3. the selected graph, on that denotation (`mem_select`);
4. the closure `c`, RDFS-entailed by the selected graph (`fullClosure_entails`);
5. for each solution `mu`: the pattern instantiated by `mu` is in `c`
   (`evalBgp_instantiates_into_graph`), and, when the instance and `c` are exact,
   the instance is RDFS-entailed by the selected graph.

Premise: `hcmps`. No IO assumption. Only tested: the parser's grammar
conformance, the SPARQL query text to `q`, the SPARQL algebra beyond a BGP. -/
theorem documentToRdfsBgp_sound (extra : Extra) (mode : Syntax.Mode) (base : Option String)
    (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) (sel : GraphSelection)
    (q : Bgp) {d : Document} {sols : SolutionSeq}
    (h : (documentToRdfsBgp extra mode base D cmps hcmps sel q).run d = .ok sols) :
    ∃ (f : RdfFormat) (text : String) (raw ds : Dataset) (c : Graph),
      formatOfDocument d.mediaType d.source = some f ∧ text.toUTF8 = d.bytes ∧
      parseDocumentRaw extra f mode base text = .ok raw ∧ ds.IsSet ∧ ds.den = raw.den ∧
      (∀ t, (ds.select sel).mem t = true ↔ sel.Holds raw.den t) ∧
      RdfsEntails (fun x => x ∈ D) (ds.select sel) c ∧
      ∀ mu ∈ sols, (∀ t ∈ instBgp q mu, c.mem t = true) ∧
        (GraphExact c → (∀ t ∈ instBgp q mu, TripleExact t) →
          RdfsEntails (fun x => x ∈ D) (ds.select sel) (instBgp q mu)) := by
  obtain ⟨c, ⟨g, ⟨ds, ⟨⟨f, text⟩, ⟨hf, hutf⟩, ⟨raw, hraw, _, hset, hden⟩⟩, ⟨hg, hmem⟩⟩, hent⟩,
      hbgp⟩ := (documentToRdfsBgp extra mode base D cmps hcmps sel q).sound d sols h
  subst hg
  refine ⟨f, text, raw, ds, c, hf, hutf, hraw, hset, hden, ?_, hent, ?_⟩
  · intro t; rw [← hden]; exact hmem t
  · intro mu hmu
    refine ⟨hbgp mu hmu, fun hex hte => rdfsEntails_of_mem hent hex
      (fun t ht => ⟨hte t ht, hbgp mu hmu t ht⟩)⟩

#print axioms updateStage
#print axioms mem_select
#print axioms rdfsSelect_sound
#print axioms rhoDfClosureStage
#print axioms simpleEntailsSelectStage
#print axioms owlRlClosureStage
#print axioms rifClosureStage
#print axioms shaclStage
#print axioms bgpSelectStage
#print axioms bgpAskStage
#print axioms documentToRdfsBgp_sound

end L4Factoidal.Dataflow
