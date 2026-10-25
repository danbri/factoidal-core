/-
L4Factoidal.Dataflow.EndToEnd — the end-to-end theorem over the interface
types (https://github.com/danbri/factoidal/issues/975, "Architecture
acceptance", item 5): document text → `RdfReader` → `LawfulDataset` →
`LawfulEvaluator` → `Answer`.

## The pipeline

`pipeline r ev inp env q`:

1. `r.certified inp`: the reader `r : RdfReader` reads the document text
   `inp` (the decoded text, its RDF mode, its base IRI) to a dataset with its
   set proof, or stops with the parse error;
2. `loadStore c`: the lawful store of the dataset, `LawfulDataset.ofCertified
   c` (the record the wasm query ops build, `queryParsedCertified`), for every
   dataset the reader accepts. Its law is proved
   (`LawfulDataset.ofCertified_proved`), so it carries no named assumption.
   A graph name is an IRI or a blank node (RDF 1.1 Concepts section 4); the
   record names its backends by the graph name itself, so a blank-node graph
   name has its own backend, `GRAPH ?g` binds `?g` to the blank node, and no
   IRI can share the name (`NamedRel`, `Dataset.IsSet.names`). Until
   2026-10-25 the record spelled a graph name as a string; a blank-node graph
   name then gave no store and the reference evaluator answered;
3. `ev.run`: the evaluator `ev : LawfulEvaluator` evaluates the parsed query
   `q` over the dataset and the store's backend, with an environment whose
   dataset is the read dataset (SPARQL 1.1 section 18.6).

## The theorem

`pipeline_sound`: when the reader accepts the document (`r.run inp = .ok
out`), the pipeline answers `ev.run x` for the input `x = pipelineInput env c
q`, and

* (reader) the parse of the document succeeds with a raw dataset `raw`, the
  read dataset is the set of quads of `raw`, and its denotation is
  `raw.den` (`RdfReader.set`, `SetOf.den_eq`);
* (store) the pipeline loads a store for every accepted document, the store
  has the denotation of the read dataset and a proved law
  (`LawfulDataset.Proved`: no named assumption), and the evaluator input
  carries its backend (`x.backend = some (loadStore c).backend`);
* (evaluator) the answer satisfies `EvalContract x`: it is the answer of the
  foundation's SPARQL 1.1 evaluation over the read dataset (`referenceAnswer`:
  `evalSelect`, `evalAsk`, `evalConstruct`, `evalDescribe`), OR, for SELECT and
  ASK on the backend path, the foundation's solution-modifier layer over a
  WHERE answer that SPARQL 1.1 allows (`Allowed`, section 18.5, up to multiset
  equality). The second disjunct is NOT claimed equal to the first: the tree
  has no theorem that two `Allowed` answers of one pattern are one multiset
  (`Dataflow/Evaluator.lean`, "Not claimed").

Premises, and only these:

* `hev : ev.AssumptionHolds`: the named assumption of the evaluator, the field
  `LawfulEvaluator.assumed_contractOn` (`foundation/assumptions.txt`). For
  `shippedEvaluator` it follows from the two named statements
  `BackendOutsideFragmentAgrees` and `SelectFastPathAgrees`
  (`shippedEvaluator_assumptionHolds`, used by `shipped_pipeline_sound`).
* `h : r.run inp = .ok out`: the reader accepts the document. This is the
  case split of the pipeline (on a parse error the pipeline answers the error,
  `pipeline_error`), not an assumption.

The reader `RdfReader` has no assumption field (every reader law is proved).
The store of the pipeline is `ofCertified`, whose law is proved for every graph
name (no `AssumptionName` is used). `pipeline_sound_proved` drops `hev` for
the inputs outside `ev.assumed_contractOn`; that premise names the domain of
the assumption, it does not restate the conclusion.

Anti-pattern 29 check: the conclusion is `pipeline … = .ok (ev.run x) ∧
(reader facts) ∧ (store facts) ∧ EvalContract x (ev.run x)`. No premise
contains `pipeline`, `ReaderContract`, `SetOf`, `den` or `LawfulDataset`.
`hev` contains `EvalContract`, but only on the inputs in
`ev.assumed_contractOn`; that restriction is the named assumption of item 2,
which item 5 admits as a premise. On the other inputs the conclusion comes
from the field `ev.sound` and from `EvalInput.Wf`, which this module proves
(`pipelineInput_wf`, from `LawfulDataset.backendReads_ofCertified`, which has
no premise on the graph names).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Dataflow.Store
import L4Factoidal.Dataflow.Evaluator
import L4Factoidal.Dataflow.Compose
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.RDF.Source

/-! ## The join of the store and the evaluator -/

/-- **The backend of the lawful store of a certified dataset reads the
dataset** (`BackendReads`, the premise of `EvalInput.Wf`), for IRI and
blank-node graph names alike. -/
theorem LawfulDataset.backendReads_ofCertified (c : CertifiedDataset) :
    BackendReads (LawfulDataset.ofCertified c).backend c.val := by
  rw [LawfulDataset.ofCertified_backend]
  exact backendReads_indexed c.val c.property

/-! ## The pipeline -/

/-- The lawful store of a read dataset. -/
def loadStore (c : CertifiedDataset) : LawfulDataset := LawfulDataset.ofCertified c

/-- The evaluator input of the pipeline: the environment reads the read
dataset (section 18.6), and the backend is the store's. -/
def pipelineInput (env : EvalEnv) (c : CertifiedDataset) (q : Query) : EvalInput :=
  { env := { env with dataset := some c.val }, ds := c.val,
    backend := some (loadStore c).backend, query := q }

/-- **The pipeline**: read, load, evaluate. -/
def pipeline (r : RdfReader) (ev : LawfulEvaluator) (inp : ReaderInput) (env : EvalEnv)
    (q : Query) : Except Syntax.ParseError Answer :=
  (r.certified inp).map fun c => ev.run (pipelineInput env c q)

/-- The store of the pipeline has the read dataset's denotation and a proved
law, for every graph name. -/
theorem loadStore_spec (c : CertifiedDataset) :
    (loadStore c).den = c.val.den ∧ (loadStore c).Proved :=
  ⟨LawfulDataset.ofCertified_den c, LawfulDataset.ofCertified_proved c⟩

/-- The pipeline input is well formed. -/
theorem pipelineInput_wf (env : EvalEnv) (c : CertifiedDataset) (q : Query) :
    (pipelineInput env c q).Wf where
  envDataset := rfl
  isSet := c.property
  backendReads := by
    intro dsb h
    simp only [pipelineInput, Option.some.injEq] at h
    subst h
    exact LawfulDataset.backendReads_ofCertified c

theorem certified_of_run {r : RdfReader} {inp : ReaderInput} {out : Dataset × PrefixList}
    (h : r.run inp = .ok out) : r.certified inp = .ok ⟨out.1, r.isSet h⟩ := by
  unfold RdfReader.certified
  split
  · next out' h' =>
    rw [h] at h'
    cases h'
    rfl
  · next e h' => rw [h] at h'; cases h'

/-- On a parse error the pipeline answers the error of the parser. -/
theorem pipeline_error (r : RdfReader) (ev : LawfulEvaluator) (inp : ReaderInput)
    (env : EvalEnv) (q : Query) (e : Syntax.ParseError)
    (h : parseDocumentRaw r.extra r.fmt inp.mode inp.base inp.text = .error e) :
    pipeline r ev inp env q = .error e := by
  have hr := (r.fails inp e).mpr h
  unfold pipeline RdfReader.certified
  split
  · next out h' => rw [hr] at h'; cases h'
  · next e' h' => rw [hr] at h'; cases h'; rfl

/-! ## The reader as a source -/

/-- The pipeline input is the query input of `Compose.lean` over the store of
the read dataset: the read dataset is already in the order of its backend. -/
theorem pipelineInput_eq (env : EvalEnv) (c : CertifiedDataset) (q : Query) :
    pipelineInput env c q = queryInput env (loadStore c) c.val q := by
  unfold pipelineInput queryInput loadStore
  rw [Sourced.ofCertified_align c]

/-- **The reader as a source** (source (a) of the composition table,
`docs/2026-10-25-composition.md`): the output of an accepted document. -/
def readerSource (r : RdfReader) {inp : ReaderInput} {out : Dataset × PrefixList}
    (h : r.run inp = .ok out) : Sourced :=
  Sourced.ofCertified ⟨out.1, r.isSet h⟩

/-- **Source theorem (a), the reader**: the record of an accepted document has
the denotation of the parse (`raw.den`) and no named assumption. -/
theorem readerSource_spec (r : RdfReader) {inp : ReaderInput} {out : Dataset × PrefixList}
    (h : r.run inp = .ok out) :
    (∃ raw, parseDocumentRaw r.extra r.fmt inp.mode inp.base inp.text = .ok raw ∧
      SetOf out.1 raw ∧ (readerSource r h).den = raw.den) ∧
    (readerSource r h).assumptions = [] := by
  obtain ⟨raw, hraw, hs⟩ := r.set inp out h
  exact ⟨⟨raw, hraw, hs, SetOf.den_eq hs⟩, rfl⟩

/-! ## The end-to-end theorem -/

/-- **End to end (issue 975, item 5).** Document text → `RdfReader` →
`LawfulDataset` → `LawfulEvaluator` → `Answer`. When the reader accepts the
document, the pipeline answers `ev.run x`; the read dataset is the set of the
parse with the parse's denotation; the pipeline loads a store for every graph
name, with that denotation and a proved law, and the evaluator input carries
its backend; and the answer satisfies the evaluator contract against the
foundation's SPARQL 1.1 semantics (`EvalContract`: the reference answer, or
for SELECT and ASK with no FROM clause the modifier layer over a WHERE
answer that `Allowed` admits and that is the reference WHERE answer up to the
order of the solutions); when the solution modifiers do not read the order
(`OrderFree`), the answer is the reference answer up to the order of the rows
(`AnswerAgrees`).

Since 2026-10-25 this is a corollary: the reader source theorem
(`readerSource_spec`) and the query theorem over any lawful record
(`query_sound`, `Dataflow/Compose.lean`), joined by `pipelineInput_eq`.

Premises: `hev`, the named assumption of the evaluator
(`LawfulEvaluator.assumed_contractOn`), and `h`, the case "the reader
accepts". The reader and the store add no named assumption. -/
theorem pipeline_sound (r : RdfReader) (ev : LawfulEvaluator) (hev : ev.AssumptionHolds)
    (inp : ReaderInput) (env : EvalEnv) (q : Query) {out : Dataset × PrefixList}
    (h : r.run inp = .ok out) :
    let c : CertifiedDataset := ⟨out.1, r.isSet h⟩
    let x := pipelineInput env c q
    pipeline r ev inp env q = .ok (ev.run x) ∧
      (∃ raw, parseDocumentRaw r.extra r.fmt inp.mode inp.base inp.text = .ok raw ∧
        SetOf out.1 raw ∧ out.1.den = raw.den) ∧
      ((loadStore c).den = out.1.den ∧ (loadStore c).Proved ∧
        x.backend = some (loadStore c).backend) ∧
      EvalContract x (ev.run x) ∧ (OrderFree q → AnswerAgrees (ev.run x) (referenceAnswer x)) := by
  intro c x
  obtain ⟨⟨raw, hraw, hs, hden⟩, hpr⟩ := readerSource_spec r h
  have hq := (readerSource r h).query_sound ev hev
    (by rw [hpr]; exact Assumed.nil) env q
  refine ⟨?_, ⟨raw, hraw, hs, hden⟩, ⟨rfl, hpr, rfl⟩, ?_⟩
  · unfold pipeline
    rw [certified_of_run h]
    rfl
  · show EvalContract (pipelineInput env c q) (ev.run (pipelineInput env c q)) ∧
      (OrderFree q → AnswerAgrees (ev.run (pipelineInput env c q))
        (referenceAnswer (pipelineInput env c q)))
    rw [pipelineInput_eq]
    exact hq.2

/-- The end-to-end theorem without the evaluator's named assumption, on the
inputs outside `ev.assumed_contractOn`. -/
theorem pipeline_sound_proved (r : RdfReader) (ev : LawfulEvaluator)
    (inp : ReaderInput) (env : EvalEnv) (q : Query) {out : Dataset × PrefixList}
    (h : r.run inp = .ok out)
    (ha : ¬ ev.assumed_contractOn (pipelineInput env ⟨out.1, r.isSet h⟩ q)) :
    EvalContract (pipelineInput env ⟨out.1, r.isSet h⟩ q)
      (ev.run (pipelineInput env ⟨out.1, r.isSet h⟩ q)) :=
  ev.sound _ (pipelineInput_wf env _ q) ha

/-- **End to end for the shipped evaluator** (the wasm query ops): the only
premises are the two named statements of `shippedEvaluator`'s assumption. -/
theorem shipped_pipeline_sound (r : RdfReader) (h1 : BackendOutsideFragmentAgrees)
    (h2 : SelectFastPathAgrees) (inp : ReaderInput) (env : EvalEnv) (q : Query)
    {out : Dataset × PrefixList} (h : r.run inp = .ok out) :
    let c : CertifiedDataset := ⟨out.1, r.isSet h⟩
    let x := pipelineInput env c q
    pipeline r shippedEvaluator inp env q = .ok (shippedEvaluator.run x) ∧
      (∃ raw, parseDocumentRaw r.extra r.fmt inp.mode inp.base inp.text = .ok raw ∧
        SetOf out.1 raw ∧ out.1.den = raw.den) ∧
      ((loadStore c).den = out.1.den ∧ (loadStore c).Proved ∧
        x.backend = some (loadStore c).backend) ∧
      EvalContract x (shippedEvaluator.run x) ∧
      (OrderFree q → AnswerAgrees (shippedEvaluator.run x) (referenceAnswer x)) :=
  pipeline_sound r shippedEvaluator (shippedEvaluator_assumptionHolds h1 h2) inp env q h

/-- The reference path needs no assumption: a CONSTRUCT query through the
pipeline is the foundation's CONSTRUCT answer over the read dataset. -/
theorem shipped_pipeline_construct (r : RdfReader) (inp : ReaderInput) (env : EvalEnv)
    (q : Query) (t : List TriplePattern) (hq : q.form = .construct t)
    {out : Dataset × PrefixList} (h : r.run inp = .ok out) :
    pipeline r shippedEvaluator inp env q =
      .ok (.graph (evalConstruct { env with dataset := some out.1 } out.1 q)) := by
  unfold pipeline
  rw [certified_of_run h]
  show Except.ok (shippedRun _) = _
  rw [shippedRun_of_construct _ t (by exact hq)]
  simp only [referenceAnswer, pipelineInput, hq]

#print axioms LawfulDataset.backendReads_ofCertified
#print axioms loadStore_spec
#print axioms pipelineInput_wf
#print axioms pipeline_error
#print axioms pipelineInput_eq
#print axioms readerSource_spec
#print axioms pipeline_sound
#print axioms pipeline_sound_proved
#print axioms shipped_pipeline_sound
#print axioms shipped_pipeline_construct

/-! ## Tests: the pipeline on documents -/

private def nq : RdfReader := nquadsDocumentReader

private def doc : ReaderInput :=
  { text := "<http://e/s> <http://e/p> <http://e/o> .\n<http://e/s> <http://e/p> \"x\"@EN <http://e/g> .\n" }

private def run? (d : ReaderInput) (s : String) : Option (Except Syntax.ParseError Answer) :=
  match parseSparql s none .v11 with
  | .ok q => some (pipeline nq shippedEvaluator d {} q)
  | .error _ => none

private def rows? : Option (Except Syntax.ParseError Answer) → Option Nat
  | some (.ok (.select _ rs)) => some rs.length
  | _ => none

private def bool? : Option (Except Syntax.ParseError Answer) → Option Bool
  | some (.ok (.ask b)) => some b
  | _ => none

private def bn : ReaderInput := { text := "<http://e/s> <http://e/p> <http://e/o> _:g .\n" }

#guard rows? (run? doc "SELECT * WHERE { ?s ?p ?o }") = some 1
#guard rows? (run? doc "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }") = some 1
-- the upper-case tag of the document is read in lower case (issue 1001)
#guard bool? (run? doc "ASK { GRAPH <http://e/g> { ?s ?p \"x\"@en } }") = some true
#guard bool? (run? doc "ASK { ?s ?p <http://e/nothing> }") = some false
-- a parse error stops the pipeline
#guard (match run? { text := "<http://e/s> <http://e/p> ." } "ASK {}" with
  | some (.error _) => true | _ => false)
-- a blank-node graph name: the pipeline loads a store (issue 975)
#guard (match nq.certified bn with
  | .ok c => match (loadStore c).backend.named.map (·.name) with
    | [Subject.bnode _] => true
    | _ => false
  | .error _ => false)
#guard (match nq.certified doc with
  | .ok c => (loadStore c).backend.named.length == 1 | .error _ => false)
#guard rows? (run? bn "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }") = some 1

/-! ### Blank-node graph names: the backend answers, equal to the reference

`agrees d s`: the document reads, the query parses, the pipeline input has a
store (`backend.isSome`), the backend path answers (`backendSelect?` or
`backendAsk?` is `some`), and the pipeline's answer is `referenceAnswer` of
the same input (`evalSelect`, `evalAsk` over the read dataset), SELECT rows up
to order. -/

/-- A document with a blank-node graph name, an IRI graph name, a default
graph, and the label `g` used both as a graph name and as a subject. -/
private def bnMix : ReaderInput :=
  { text := "<http://e/s> <http://e/p> <http://e/o> _:g .\n" ++
      "<http://e/s> <http://e/p> \"x\" <http://e/h> .\n" ++
      "_:g <http://e/p> <http://e/o2> _:g .\n" ++
      "<http://e/d> <http://e/p> <http://e/o> .\n" ++
      "<http://e/t> <http://e/q> <http://e/o> _:k .\n" }

/-- The same elements with the same multiplicities: equal lengths, and each
element of `a` occurs as often in `b` as in `a`. Loops only (`count`, `all`):
`List.isPerm` reaches `List.erase`, a recursion on the list length
(`tools/lean-tail-recursion-audit.py --gate`). -/
private def sameMultiset {α} [BEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- Two answers agree: the same boolean or graph; for SELECT, the same header
and the same rows up to order (the backend's rows are an answer `Allowed`
admits, `EvalContract`, which fixes the multiset and not the order). -/
private def sameAnswer : Answer → Answer → Bool
  | .select h1 r1, .select h2 r2 => sameMultiset h1 h2 && sameMultiset r1 r2
  | a, b => a == b

private def agrees (d : ReaderInput) (s : String) : Bool :=
  match parseSparql s none .v11, nq.certified d with
  | .ok q, .ok c =>
    let x := pipelineInput {} c q
    let onBackend := match q.form with
      | .select _ => (backendSelect? x).isSome
      | .ask => (backendAsk? x).isSome
      | _ => false
    x.backend.isSome && onBackend &&
      (match pipeline nq shippedEvaluator d {} q with
       | .ok a => sameAnswer a (referenceAnswer x)
       | .error _ => false)
  | _, _ => false

#guard agrees bnMix "SELECT ?g ?s ?o WHERE { GRAPH ?g { ?s <http://e/p> ?o } }"
#guard agrees bnMix "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
#guard agrees bnMix "SELECT ?g WHERE { GRAPH ?g { ?g ?p ?o } }"
#guard agrees bnMix "SELECT ?g WHERE { GRAPH ?g { ?s ?p ?o } } LIMIT 2"
#guard agrees bnMix "SELECT ?g (COUNT(*) AS ?n) WHERE { GRAPH ?g { ?s ?p ?o } } GROUP BY ?g"
#guard agrees bnMix "SELECT * WHERE { GRAPH <http://e/h> { ?s ?p ?o } }"
#guard agrees bnMix "SELECT * WHERE { ?s ?p ?o }"
#guard agrees bnMix "ASK { GRAPH ?g { <http://e/t> ?p ?o } }"
#guard agrees bnMix "ASK { GRAPH <http://e/g> { ?s ?p ?o } }"
-- the GRAPH ?g answer binds a blank node: four rows, two graphs a blank node
#guard rows? (run? bnMix "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }") = some 4
#guard (match run? bnMix "SELECT ?g WHERE { GRAPH ?g { <http://e/t> ?p ?o } }" with
  | some (.ok (.select _ [mu])) => match Binding.lookup "g" mu with
    | some (.bnode _) => true | _ => false
  | _ => false)

end L4Factoidal.Dataflow
