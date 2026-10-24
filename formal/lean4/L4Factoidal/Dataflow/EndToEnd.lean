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
2. `loadStore c`: the lawful store of the dataset. When every graph name is an
   IRI it is `LawfulDataset.ofCertified c` (the record the wasm query ops
   build, `queryParsedCertified`); its law is proved
   (`LawfulDataset.ofCertified_proved`), so it carries no named assumption.
   When a graph name is a blank node there is no store (`none`), and the
   evaluator reads the dataset with the reference evaluator (the backend
   record cannot read a blank-node graph name pair for pair, `NamedRel`);
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
* (store) every store the pipeline loads has the denotation of the read
  dataset and a proved law (`LawfulDataset.Proved`: no named assumption);
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
The store of the pipeline is `ofCertified` with IRI graph names, whose law is
proved (no `AssumptionName` is used). `pipeline_sound_proved` drops `hev` for
the inputs outside `ev.assumed_contractOn`; that premise names the domain of
the assumption, it does not restate the conclusion.

Anti-pattern 29 check: the conclusion is `pipeline … = .ok (ev.run x) ∧
(reader facts) ∧ (store facts) ∧ EvalContract x (ev.run x)`. No premise
contains `pipeline`, `ReaderContract`, `SetOf`, `den` or `LawfulDataset`.
`hev` contains `EvalContract`, but only on the inputs in
`ev.assumed_contractOn`; that restriction is the named assumption of item 2,
which item 5 admits as a premise. On the other inputs the conclusion comes
from the field `ev.sound` and from `EvalInput.Wf`, which this module proves
(`pipelineInput_wf`, from `LawfulDataset.backendReads_ofCertified`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Dataflow.Store
import L4Factoidal.Dataflow.Evaluator
import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.RDF.Source

/-! ## The join of the store and the evaluator -/

/-- **The backend of the lawful store of a certified dataset with IRI graph
names reads the dataset** (`BackendReads`, the premise of `EvalInput.Wf`). -/
theorem LawfulDataset.backendReads_ofCertified (c : CertifiedDataset)
    (hi : Storage.QuadDataset.namesAreIris c.val = true) :
    BackendReads (LawfulDataset.ofCertified c).backend c.val := by
  rw [LawfulDataset.ofCertified_backend]
  exact backendReads_indexed c.val c.property hi

theorem LawfulDataset.ofCertified_den (c : CertifiedDataset) :
    (LawfulDataset.ofCertified c).den = c.val.den := by
  unfold LawfulDataset.ofCertified; split <;> rfl

/-! ## The pipeline -/

/-- The lawful store of a read dataset: `ofCertified` when every graph name is
an IRI, else none. -/
def loadStore (c : CertifiedDataset) : Option LawfulDataset :=
  if Storage.QuadDataset.namesAreIris c.val = true then some (LawfulDataset.ofCertified c) else none

/-- The evaluator input of the pipeline: the environment reads the read
dataset (section 18.6), and the backend is the store's. -/
def pipelineInput (env : EvalEnv) (c : CertifiedDataset) (q : Query) : EvalInput :=
  { env := { env with dataset := some c.val }, ds := c.val,
    backend := (loadStore c).map (·.backend), query := q }

/-- **The pipeline**: read, load, evaluate. -/
def pipeline (r : RdfReader) (ev : LawfulEvaluator) (inp : ReaderInput) (env : EvalEnv)
    (q : Query) : Except Syntax.ParseError Answer :=
  (r.certified inp).map fun c => ev.run (pipelineInput env c q)

/-- The store of the pipeline has the read dataset's denotation and a proved
law. -/
theorem loadStore_spec (c : CertifiedDataset) :
    ∀ L, loadStore c = some L → L.den = c.val.den ∧ L.Proved := by
  intro L h
  unfold loadStore at h
  split at h
  · next hi =>
    cases h
    exact ⟨LawfulDataset.ofCertified_den c, LawfulDataset.ofCertified_proved hi⟩
  · cases h

/-- The pipeline input is well formed. -/
theorem pipelineInput_wf (env : EvalEnv) (c : CertifiedDataset) (q : Query) :
    (pipelineInput env c q).Wf where
  envDataset := rfl
  isSet := c.property
  backendReads := by
    intro dsb h
    simp only [pipelineInput, loadStore] at h
    split at h
    · next hi =>
      cases h
      exact LawfulDataset.backendReads_ofCertified c hi
    · cases h

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

/-! ## The end-to-end theorem -/

/-- **End to end (issue 975, item 5).** Document text → `RdfReader` →
`LawfulDataset` → `LawfulEvaluator` → `Answer`. When the reader accepts the
document, the pipeline answers `ev.run x`; the read dataset is the set of the
parse with the parse's denotation; every loaded store has that denotation and
a proved law; and the answer satisfies the evaluator contract against the
foundation's SPARQL 1.1 semantics (`EvalContract`: the reference answer, or
for SELECT and ASK the modifier layer over a WHERE answer that `Allowed`
admits).

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
      (∀ L, loadStore c = some L → L.den = out.1.den ∧ L.Proved) ∧
      EvalContract x (ev.run x) := by
  intro c x
  obtain ⟨raw, hraw, hs⟩ := r.set inp out h
  refine ⟨?_, ⟨raw, hraw, hs, SetOf.den_eq hs⟩, loadStore_spec c, ?_⟩
  · unfold pipeline
    rw [certified_of_run h]
    rfl
  · exact ev.contract hev x (pipelineInput_wf env c q)

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
      (∀ L, loadStore c = some L → L.den = out.1.den ∧ L.Proved) ∧
      EvalContract x (shippedEvaluator.run x) :=
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
-- a blank-node graph name: no store, the reference evaluator answers
#guard (match nq.certified bn with
  | .ok c => (loadStore c).isNone | .error _ => false)
#guard (match nq.certified doc with
  | .ok c => (loadStore c).isSome | .error _ => false)
#guard rows? (run? bn "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }") = some 1

end L4Factoidal.Dataflow
