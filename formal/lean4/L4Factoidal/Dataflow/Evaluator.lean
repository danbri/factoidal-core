/-
L4Factoidal.Dataflow.Evaluator — the interface type of a SPARQL query
evaluator (https://github.com/danbri/factoidal/issues/975, "Architecture
acceptance", item 2, the query evaluator kind).

## The input and the answer

`EvalInput`: the evaluation environment (`EvalEnv`: extension functions,
SERVICE snapshots, `NOW()`, base IRI, the dataset EXISTS reads), the dataset
(`Dataset`, whose meaning is `Dataset.den : DatasetDen`), an optional
in-memory or store backend of the dataset (`DatasetBackend`), and the parsed
query. `Answer`: the rows of a SELECT (header and solution sequence), the
boolean of an ASK, or the graph of a CONSTRUCT or DESCRIBE.

`EvalInput.Wf`: the environment's dataset is the input dataset (SPARQL 1.1
section 18.6: EXISTS reads the query's dataset), the dataset is a set (so the
value has exactly the membership of its denotation `ds.den`), and a backend,
when there is one, reads the dataset (`BackendReads`: the default backend
reads the default graph, the named backends read the named graphs pair for
pair, with distinct names; `Storage.BackendRefinement.GraphRel` and
`NamedRel`). `EvalInput.wf_indexed`: the indexed backend the wasm query ops
build satisfies it for a set dataset with IRI graph names.

## The contract

`EvalContract inp out` is a disjunction of two statements against the
FOUNDATION (`foundation/manifest.toml`, level 1):

* `out = referenceAnswer inp`: the answer of the foundation's SPARQL 1.1
  evaluation (`SPARQL.Query`: `evalSelect`, `evalAsk`, `evalConstruct`,
  `evalDescribe`, sections 16 and 18);
* or, for SELECT and ASK: there is a WHERE answer `A` that SPARQL 1.1 allows
  (`Storage.Sbm11.IdGroup.Allowed`, section 18.5 up to multiset equality; in
  the manifest) for the WHERE pattern in the default graph, and `out` is the
  foundation's solution-modifier layer over `A` (`modifierLayer`: `selectPost`
  for SELECT, `formHasSolution` for ASK; sections 18.2.4 and 18.2.5).

## The interface type

`LawfulEvaluator`: a run `EvalInput → Answer`, the class of inputs on which
the contract is a NAMED assumption (`assumed_contractOn`, counted by the
assumption ratchet of issue 975 item 4), and `sound`: every well-formed input
outside that class satisfies the contract. So a value of the type cannot exist
without the proof for the inputs it does not name as assumed.
`LawfulEvaluator.AssumptionHolds` is the statement of the assumption, and
`LawfulEvaluator.contract` gives the contract on every well-formed input from
it; a theorem that uses an evaluator on an assumed input takes
`AssumptionHolds` as a hypothesis with that name (the `IOStage.Realised`
style, `Dataflow/Stage.lean`). `provedStage` and `toStage` give the `Stage`
views for composition.

## The shipped evaluator

`shippedRun` is the evaluation of the wasm query ops
(`Wasm/Ops/Query.lean`, `queryParsedDatasetWith`, which now takes a
`LawfulEvaluator` and calls its `run`): SELECT and ASK with no FROM clause go
to the backend runners `runSelectQueryBackendDataset` and
`runAskQueryBackendDataset` when there is a backend; when they answer `none`
(a `text:query` pattern, for example) or there is no backend or a FROM
clause, the reference evaluator answers; CONSTRUCT and DESCRIBE always use the
reference evaluator.

`shippedAssumed`, the inputs on which its contract is assumed: the backend
path is taken (no FROM clause, a backend, no `text:query` pattern) and

* the WHERE pattern, after the blank-node rewrite, is outside
  `Storage.BackendRefinement.NativeFrag` (BIND, LATERAL, property paths,
  SERVICE, sub-SELECT, FILTER or OPTIONAL with a condition that is not
  `backendLocal`, GRAPH with a blank node or literal): `OutsideNativeFrag`;
* or the query is a SELECT and one of the four streaming fast paths of
  `evalSelectBackendDataset` matches (COUNT(*) of one triple pattern, COUNT
  GROUP BY a predicate, COUNT GROUP BY a graph, LIMIT of one triple pattern):
  `SelectFastPath`.

Proved (`shippedEvaluator.sound`): every other well-formed input. Off the
backend path the answer is the reference answer (`shippedRun_of_noBackend`,
`shippedRun_of_from`, `shippedRun_of_construct`, `shippedRun_of_describe`);
on it, for SELECT (plain arm) and ASK over a `NativeFrag` pattern, the answer
is the modifier layer over the backend's WHERE answer, which
`evalPatternBackend_allowed` (PR 52) proves `Allowed`.

Not claimed: that two answers `Allowed` admits for one pattern are one
multiset, so the second disjunct is not proved to give the reference answer;
that the answer depends on `ds.den` only (two set datasets with one
denotation, listed in another order); that the SELECT * header of the backend
path (`collectVarsInOrder`) equals the reference header (`projectedVars`).

## Joining with a store

`BackendReads dsb ds` is the premise a store interface (`LawfulStore`, issue
975 Phase B, branch claude/storecaps-interface-975) discharges: its exact
search laws give `GraphRel` for each graph backend. An end-to-end theorem
(bytes → `RdfReader` → `LawfulStore` → `LawfulEvaluator` → answer, item 5)
then needs only the named assumptions of the three types.

`GraphFixed` (no upper-case letter in a language tag) is no longer a premise
of `GraphRel`: https://github.com/danbri/factoidal/issues/1001 (PR 57) makes it
true of every graph.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.BackendRefinement
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StoreFastPath
open L4Factoidal.Storage.Sbm11.IdGroup (Allowed)
open L4Factoidal.Storage.BackendRefinement (GraphRel NamedRel NativeFrag)

/-! ## The input and the answer -/

/-- The input of an evaluator: the environment, the dataset, an optional
backend of the dataset, the parsed query. -/
structure EvalInput where
  env : EvalEnv
  ds : Dataset
  backend : Option DatasetBackend
  query : Query

/-- The answer of an evaluator. -/
inductive Answer where
  | select (vars : List VarName) (rows : SolutionSeq)
  | ask (b : Bool)
  | graph (g : Graph)
  deriving BEq

/-- The answer has the form of the query. -/
def Answer.formOk : Answer → Query → Bool
  | .select _ _, q => match q.form with | .select _ => true | _ => false
  | .ask _, q => match q.form with | .ask => true | _ => false
  | .graph _, q => match q.form with | .construct _ | .describe _ => true | _ => false

/-- A backend reads a dataset: the default backend the default graph, the
named backends the named graphs pair for pair, with distinct names. -/
structure BackendReads (dsb : DatasetBackend) (ds : Dataset) : Prop where
  default : GraphRel dsb.default ds.default
  named : NamedRel dsb.named ds.named
  namesNodup : (dsb.named.map (·.name)).Nodup

/-- The premises on an input. -/
structure EvalInput.Wf (inp : EvalInput) : Prop where
  /-- EXISTS reads the input dataset (section 18.6). -/
  envDataset : inp.env.dataset = some inp.ds
  /-- The dataset value is a set: its membership is its denotation's. -/
  isSet : inp.ds.IsSet
  /-- A backend, when given, reads the dataset. -/
  backendReads : ∀ dsb, inp.backend = some dsb → BackendReads dsb inp.ds

/-- The indexed backend of a set dataset with IRI graph names reads it. -/
theorem backendReads_indexed (d : Dataset) (hset : d.IsSet)
    (hiri : Storage.QuadDataset.namesAreIris d = true) :
    BackendReads (indexedDatasetBackend d) d := by
  have hi := Storage.BackendRefinement.iris_of_namesAreIris hiri
  refine ⟨Storage.BackendRefinement.graphRel_indexed hset.default, ?_, ?_⟩
  · rw [DatasetRestriction.indexedDatasetBackend_named]
    exact Storage.BackendRefinement.namedRel_indexed d.named hset.graphs hi
  · rw [DatasetRestriction.indexedDatasetBackend_named, List.map_map]
    exact Storage.BackendRefinement.ngKey_nodup d.named hset.names hi

/-- The input the wasm query ops build is well formed. -/
theorem EvalInput.wf_indexed (env : EvalEnv) (d : Dataset) (q : Query) (hset : d.IsSet)
    (hiri : Storage.QuadDataset.namesAreIris d = true)
    (he : env.dataset = some d) :
    EvalInput.Wf { env, ds := d, backend := some (indexedDatasetBackend d), query := q } where
  envDataset := he
  isSet := hset
  backendReads := by
    intro dsb h
    cases h
    exact backendReads_indexed d hset hiri

/-- With no backend, any environment that reads the dataset gives a
well-formed input. -/
theorem EvalInput.wf_none (env : EvalEnv) (d : Dataset) (q : Query) (hset : d.IsSet)
    (he : env.dataset = some d) :
    EvalInput.Wf { env, ds := d, backend := none, query := q } where
  envDataset := he
  isSet := hset
  backendReads := by intro dsb h; cases h

/-! ## The contract -/

/-- The answer of the foundation's SPARQL 1.1 evaluation (`SPARQL.Query`). -/
def referenceAnswer (inp : EvalInput) : Answer :=
  match inp.query.form with
  | .select _ =>
    let r := evalSelect inp.env inp.ds inp.query
    .select r.1 r.2
  | .ask => .ask (evalAsk inp.env inp.ds inp.query)
  | .construct _ => .graph (evalConstruct inp.env inp.ds inp.query)
  | .describe _ => .graph (evalDescribe inp.env inp.ds inp.query)

/-- The query with its WHERE blank nodes rewritten to variables (the first
step of `evalSelect` and of the backend runners). -/
def _root_.L4Factoidal.SPARQL.Query.rewritten (q : Query) : Query :=
  .mk q.form q.dataset q.pattern.rewriteBnodes q.groupBy q.having q.modifier q.postValues q.base

/-- The SELECT header of a set of rows: the projected variables, or for
SELECT * the variables of the rows in order. -/
def selectHeader (sel : SelectClause) (rows : SolutionSeq) : List VarName :=
  match sel with
  | .vars items => selectItemVars items
  | .all => collectVarsInOrder rows

/-- The foundation's solution-modifier layer of a SELECT or ASK query over a
WHERE answer `A` (sections 18.2.4, 18.2.5), in the default graph. -/
def modifierLayer (inp : EvalInput) (A : SolutionSeq) : Option Answer :=
  match inp.query.form with
  | .select sel =>
    let rows := selectPost inp.env inp.ds.default inp.query.rewritten A
    some (.select (selectHeader sel rows) rows)
  | .ask => some (.ask (formHasSolution inp.env inp.ds.default inp.query.rewritten A))
  | _ => none

/-- **The contract of a query evaluator.** The reference answer, or the
modifier layer over a WHERE answer SPARQL 1.1 allows. -/
def EvalContract (inp : EvalInput) (out : Answer) : Prop :=
  out = referenceAnswer inp ∨
    ∃ A, Allowed inp.env inp.ds inp.query.pattern.rewriteBnodes inp.ds.default A ∧
      modifierLayer inp A = some out

/-! ## The interface type -/

/-- **A SPARQL query evaluator, with its contract as fields.** -/
structure LawfulEvaluator where
  /-- Evaluate a parsed query. -/
  run : EvalInput → Answer
  /-- The inputs on which the contract is a named assumption, not a proof. -/
  assumed_contractOn : EvalInput → Prop
  /-- Every well-formed input outside the assumed class satisfies the
  contract. -/
  sound : ∀ inp, inp.Wf → ¬ assumed_contractOn inp → EvalContract inp (run inp)

namespace LawfulEvaluator

/-- The named assumption: the contract holds on the assumed inputs too. A
hypothesis of every theorem that uses the evaluator on such an input. -/
def AssumptionHolds (ev : LawfulEvaluator) : Prop :=
  ∀ inp, inp.Wf → ev.assumed_contractOn inp → EvalContract inp (ev.run inp)

/-- The contract on every well-formed input, under the named assumption. -/
theorem contract (ev : LawfulEvaluator) (h : ev.AssumptionHolds) (inp : EvalInput)
    (hw : inp.Wf) : EvalContract inp (ev.run inp) := by
  by_cases ha : ev.assumed_contractOn inp
  · exact h inp hw ha
  · exact ev.sound inp hw ha

/-- The stage of the evaluator with the proved contract only. -/
def provedStage (ev : LawfulEvaluator) : Stage String EvalInput Answer :=
  Stage.ofFun ev.run (fun inp out => inp.Wf → ¬ ev.assumed_contractOn inp → EvalContract inp out)
    (fun inp => ev.sound inp)

/-- The stage of the evaluator under its named assumption. -/
def toStage (ev : LawfulEvaluator) (h : ev.AssumptionHolds) : Stage String EvalInput Answer :=
  Stage.ofFun ev.run (fun inp out => inp.Wf → EvalContract inp out)
    (fun inp hw => ev.contract h inp hw)

end LawfulEvaluator

/-! ## The shipped evaluator -/

/-- The SELECT answer of the backend path, or `none`. -/
def backendSelect? (inp : EvalInput) : Option SolutionSeq :=
  if inp.query.dataset.isEmpty then inp.backend.bind (runSelectQueryBackendDataset inp.env inp.query)
  else none

/-- The ASK answer of the backend path, or `none`. -/
def backendAsk? (inp : EvalInput) : Option Bool :=
  if inp.query.dataset.isEmpty then inp.backend.bind (runAskQueryBackendDataset inp.env inp.query)
  else none

/-- The evaluation of the wasm query ops. -/
def shippedRun (inp : EvalInput) : Answer :=
  match inp.query.form with
  | .ask =>
    match backendAsk? inp with
    | some b => .ask b
    | none => .ask (evalAsk inp.env inp.ds inp.query)
  | .select sel =>
    match backendSelect? inp with
    | some rows => .select (selectHeader sel rows) rows
    | none =>
      let r := evalSelect inp.env inp.ds inp.query
      .select r.1 r.2
  | .construct _ => .graph (evalConstruct inp.env inp.ds inp.query)
  | .describe _ => .graph (evalDescribe inp.env inp.ds inp.query)

/-- The backend path is taken: no FROM clause, a backend, no `text:query`. -/
def BackendPath (inp : EvalInput) : Prop :=
  inp.query.dataset.isEmpty = true ∧ inp.backend.isSome = true ∧
    inp.query.pattern.mentionsFulltext = false

/-- The WHERE pattern is outside the fragment `evalPatternBackend_allowed`
covers. -/
def OutsideNativeFrag (inp : EvalInput) : Prop :=
  ¬ NativeFrag inp.query.pattern.rewriteBnodes

/-- No streaming fast path of `evalSelectBackendDataset` matches. -/
def PlainSelectArm (q : Query) (dsb : DatasetBackend) : Prop :=
  detectStreamingCountGroupByGraph q = none ∧ detectStreamingCountStar q = none ∧
    resolveStreamingCountGroupByPredicate q dsb.default dsb = none ∧
    detectLimitSingleTpScoped q = none

/-- A SELECT on which a streaming fast path matches. -/
def SelectFastPath (inp : EvalInput) : Prop :=
  (∃ sel, inp.query.form = .select sel) ∧
    ∃ dsb, inp.backend = some dsb ∧ ¬ PlainSelectArm inp.query.rewritten dsb

/-- The inputs on which the shipped evaluator's contract is assumed. -/
def shippedAssumed (inp : EvalInput) : Prop :=
  BackendPath inp ∧ (OutsideNativeFrag inp ∨ SelectFastPath inp)

/-! ### Off the backend path: the reference answer -/

theorem shippedRun_of_noBackend (inp : EvalInput) (h : inp.backend = none) :
    shippedRun inp = referenceAnswer inp := by
  unfold shippedRun referenceAnswer backendSelect? backendAsk?
  rw [h]
  cases inp.query.form <;> simp

theorem shippedRun_of_from (inp : EvalInput) (h : inp.query.dataset.isEmpty = false) :
    shippedRun inp = referenceAnswer inp := by
  unfold shippedRun referenceAnswer backendSelect? backendAsk?
  rw [h]
  cases inp.query.form <;> simp

theorem shippedRun_of_construct (inp : EvalInput) (t : List TriplePattern)
    (h : inp.query.form = .construct t) : shippedRun inp = referenceAnswer inp := by
  unfold shippedRun referenceAnswer
  rw [h]

theorem shippedRun_of_describe (inp : EvalInput) (t : List PatternTerm)
    (h : inp.query.form = .describe t) : shippedRun inp = referenceAnswer inp := by
  unfold shippedRun referenceAnswer
  rw [h]

/-! ### On the backend path -/

theorem rewritten_form (q : Query) : q.rewritten.form = q.form := by
  cases q; rfl

theorem rewritten_pattern (q : Query) : q.rewritten.pattern = q.pattern.rewriteBnodes := by
  cases q; rfl

theorem activeGraph_of {env : EvalEnv} {ds : Dataset} (h : env.dataset = some ds) :
    env.activeGraph = ds.default := by
  simp [EvalEnv.activeGraph, h]

/-- The backend runner's answer to a SELECT unpacks into the path's parts. -/
theorem backendSelect?_some {inp : EvalInput} {rows : SolutionSeq}
    (h : backendSelect? inp = some rows) :
    inp.query.dataset.isEmpty = true ∧ inp.query.pattern.mentionsFulltext = false ∧
      ∃ dsb, inp.backend = some dsb ∧ evalSelectBackendDataset inp.env inp.query.rewritten dsb = some rows := by
  unfold backendSelect? at h
  cases hd : inp.query.dataset.isEmpty
  · rw [hd] at h; simp at h
  · rw [hd] at h
    simp only [↓reduceIte] at h
    cases hb : inp.backend with
    | none => rw [hb] at h; simp at h
    | some dsb =>
      rw [hb] at h
      simp only [Option.bind_some, runSelectQueryBackendDataset] at h
      cases hf : inp.query.pattern.mentionsFulltext
      · rw [hf] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ⟨rfl, rfl, dsb, rfl, h⟩
      · rw [hf] at h; simp at h

theorem backendAsk?_some {inp : EvalInput} {b : Bool} (h : backendAsk? inp = some b) :
    inp.query.dataset.isEmpty = true ∧ inp.query.pattern.mentionsFulltext = false ∧
      ∃ dsb, inp.backend = some dsb ∧ evalAskBackendReference inp.env inp.query.rewritten dsb = some b := by
  unfold backendAsk? at h
  cases hd : inp.query.dataset.isEmpty
  · rw [hd] at h; simp at h
  · rw [hd] at h
    simp only [↓reduceIte] at h
    cases hb : inp.backend with
    | none => rw [hb] at h; simp at h
    | some dsb =>
      rw [hb] at h
      simp only [Option.bind_some, runAskQueryBackendDataset] at h
      cases hf : inp.query.pattern.mentionsFulltext
      · rw [hf] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        rw [evalAskBackend_eq_reference] at h
        exact ⟨rfl, rfl, dsb, rfl, h⟩
      · rw [hf] at h; simp at h

/-- The plain SELECT arm: the modifier layer over the backend's WHERE answer. -/
theorem evalSelectBackendDataset_plain (env : EvalEnv) (q : Query) (dsb : DatasetBackend)
    (sel : SelectClause) (hform : q.form = .select sel) (hp : PlainSelectArm q dsb) :
    evalSelectBackendDataset env q dsb =
      some (selectPost env env.activeGraph q (evalPatternBackend env dsb q.pattern dsb.default)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold evalSelectBackendDataset
  rw [h1]
  simp only
  unfold evalSelectBackendOnGraph
  rw [h2]
  simp only
  rw [h3]
  simp only
  rw [h4]
  simp only
  rw [hform]

/-- The backend ASK: the modifier layer over the backend's WHERE answer. -/
theorem evalAskBackendReference_some {env : EvalEnv} {q : Query} {dsb : DatasetBackend} {b : Bool}
    (h : evalAskBackendReference env q dsb = some b) :
    b = formHasSolution env env.activeGraph q (evalPatternBackend env dsb q.pattern dsb.default) := by
  unfold evalAskBackendReference at h
  split at h
  · simp only at h
    split at h
    · simp at h
    · injection h with h
      exact h.symm
  · simp at h

/-- The WHERE answer of the backend is allowed, for a pattern of the fragment. -/
theorem backendWhere_allowed (inp : EvalInput) (hw : inp.Wf) (dsb : DatasetBackend)
    (hb : inp.backend = some dsb) (hn : NativeFrag inp.query.pattern.rewriteBnodes) :
    Allowed inp.env inp.ds inp.query.pattern.rewriteBnodes inp.ds.default
      (evalPatternBackend inp.env dsb inp.query.rewritten.pattern dsb.default) := by
  have hr := hw.backendReads dsb hb
  rw [rewritten_pattern]
  exact Storage.BackendRefinement.evalPatternBackend_allowed inp.env dsb inp.ds hr.named
    hr.namesNodup _ hn _ _ hr.default

/-- **The shipped evaluator satisfies the contract on every well-formed input
outside `shippedAssumed`.** -/
theorem shippedRun_sound (inp : EvalInput) (hw : inp.Wf) (ha : ¬ shippedAssumed inp) :
    EvalContract inp (shippedRun inp) := by
  have hact := activeGraph_of hw.envDataset
  cases hform : inp.query.form with
  | construct t => exact .inl (shippedRun_of_construct inp t hform)
  | describe t => exact .inl (shippedRun_of_describe inp t hform)
  | ask =>
    cases hk : backendAsk? inp with
    | none =>
      left
      simp only [shippedRun, referenceAnswer, hform, hk]
    | some b =>
      obtain ⟨hd, hf, dsb, hb, he⟩ := backendAsk?_some hk
      have hpath : BackendPath inp := ⟨hd, by rw [hb]; rfl, hf⟩
      have hn : NativeFrag inp.query.pattern.rewriteBnodes := by
        refine Classical.byContradiction fun hn => ha ⟨hpath, .inl hn⟩
      right
      refine ⟨_, backendWhere_allowed inp hw dsb hb hn, ?_⟩
      have hbv := evalAskBackendReference_some he
      rw [hact] at hbv
      simp only [modifierLayer, shippedRun, hform, hk, hbv]
  | select sel =>
    cases hk : backendSelect? inp with
    | none =>
      left
      simp only [shippedRun, referenceAnswer, hform, hk]
    | some rows =>
      obtain ⟨hd, hf, dsb, hb, he⟩ := backendSelect?_some hk
      have hpath : BackendPath inp := ⟨hd, by rw [hb]; rfl, hf⟩
      have hn : NativeFrag inp.query.pattern.rewriteBnodes := by
        refine Classical.byContradiction fun hn => ha ⟨hpath, .inl hn⟩
      have hplain : PlainSelectArm inp.query.rewritten dsb := by
        refine Classical.byContradiction fun hp => ha ⟨hpath, .inr ⟨⟨sel, hform⟩, dsb, hb, hp⟩⟩
      rw [evalSelectBackendDataset_plain inp.env _ dsb sel (by rw [rewritten_form, hform]) hplain,
        hact] at he
      injection he with he
      right
      refine ⟨_, backendWhere_allowed inp hw dsb hb hn, ?_⟩
      simp only [modifierLayer, shippedRun, hform, hk, ← he]

/-- **The shipped evaluator** (the wasm query ops). -/
def shippedEvaluator : LawfulEvaluator where
  run := shippedRun
  assumed_contractOn := shippedAssumed
  sound := shippedRun_sound

theorem shippedEvaluator_run : shippedEvaluator.run = shippedRun := rfl

/-- The named assumption of the shipped evaluator, as two statements: the
contract on the backend path outside `NativeFrag`, and on the SELECT fast
paths. -/
def BackendOutsideFragmentAgrees : Prop :=
  ∀ inp, inp.Wf → BackendPath inp → OutsideNativeFrag inp → EvalContract inp (shippedRun inp)

def SelectFastPathAgrees : Prop :=
  ∀ inp, inp.Wf → BackendPath inp → SelectFastPath inp → EvalContract inp (shippedRun inp)

theorem shippedEvaluator_assumptionHolds (h1 : BackendOutsideFragmentAgrees)
    (h2 : SelectFastPathAgrees) : shippedEvaluator.AssumptionHolds := by
  rintro inp hw ⟨hp, ho | hs⟩
  · exact h1 inp hw hp ho
  · exact h2 inp hw hp hs

#print axioms backendReads_indexed
#print axioms EvalInput.wf_indexed
#print axioms LawfulEvaluator.contract
#print axioms shippedRun_of_noBackend
#print axioms shippedRun_of_from
#print axioms evalSelectBackendDataset_plain
#print axioms evalAskBackendReference_some
#print axioms shippedRun_sound
#print axioms shippedEvaluator
#print axioms shippedEvaluator_assumptionHolds

end L4Factoidal.Dataflow
