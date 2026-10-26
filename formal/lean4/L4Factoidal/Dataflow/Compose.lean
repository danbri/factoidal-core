/-
L4Factoidal.Dataflow.Compose — the query theorem over any lawful dataset
record, and the type of a source of one
(https://github.com/danbri/factoidal/issues/975, owner-approved plan of
2026-10-25: "`query_sound` over any `LawfulStore` ... Then one small theorem
per source that produces a `LawfulStore` with a stated den").

## `query_sound`

`query_sound ev hev S hS ds hset hden env q`: for ANY `LawfulDataset` `S`
(whatever produced it), a set dataset `ds` with `ds.den = S.den`, and a
parsed query `q`, the evaluator `ev` run on `queryInput env S ds q` satisfies
`EvalContract` against the foundation's SPARQL 1.1 semantics over a dataset
whose denotation is `S.den`, with `S.backend` as the backend.

`ds` is a value of the reference evaluator (`referenceAnswer` and the FROM
and CONSTRUCT paths of an evaluator read a `Dataset`, not a `DatasetDen`).
The input carries `alignNamed S.backend ds`: the default graph of `ds`, and
one named graph for each named backend of `S`, in the backend's order, with
the graph of that name in `ds`. `BackendReads` (`Dataflow/Evaluator.lean`)
pairs the backends and the named graphs in list order; `alignNamed` makes the
order of `ds` the order of the backend, and keeps the set property and the
denotation (`alignNamed_isSet`, `alignNamed_den`). For a dataset already in
the backend's order it is the dataset (`alignNamed_self`), so the reader path
is unchanged (`Dataflow/EndToEnd.lean`, `pipeline_sound`).

Premises, and only these:

* `hev : ev.AssumptionHolds`: the evaluator's named assumption
  (`LawfulEvaluator.assumed_contractOn`);
* `hS : Assumed S.assumed_contracts`: the named assumptions of `S`'s law
  (`[]` for a proved record, `LawfulDataset.assumed_of_proved`);
* `hset : ds.IsSet` and `hden : ds.den = S.den`: which dataset value the
  reference evaluator reads.

Anti-pattern 29 check: the conclusion is `x.ds.IsSet ∧ x.ds.den = S.den ∧
x.backend = some S.backend ∧ EvalContract x (ev.run x) ∧ (OrderFree q →
AnswerAgrees (ev.run x) (referenceAnswer x))`. No premise mentions
`AnswerAgrees`; it comes from `EvalContract.agrees`
(`Storage.BackendAgreement.evalPatternBackend_ref`, `selectPost_congr`,
`formHasSolution_congr`). `hden` and `hset`
are about `ds`, not about `x.ds = alignNamed S.backend ds`; the first two
conjuncts are proved (`alignNamed_isSet`, `alignNamed_den`), the third is
`rfl`, and `EvalContract` comes from `ev.contract` and `EvalInput.Wf`, which
this module proves from `S.law` (`backendReads_alignNamed`). `hev` contains
`EvalContract` only on the inputs in `ev.assumed_contractOn`.

## Sources

`Sourced`: a `LawfulDataset` with a set dataset of the same denotation. A
source theorem says "this source yields a `Sourced` whose `den` is X";
`Sourced.query_sound` then gives the evaluator contract over X. The guarantee
of a composed path is the conjunction of the source theorem and
`query_sound`, under the union of the named assumptions:
`Sourced.assumptions` (the record's `assumed_contracts`) and
`ev.AssumptionHolds`. `Dataflow/Sources.lean` has the sources.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Store
import L4Factoidal.Dataflow.Evaluator

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StorePlan (NamedGraphBackend)
open L4Factoidal.Storage.PlannerSoundness (DatasetBackendExact)
open L4Factoidal.Storage.BackendRefinement (GraphRel NamedRel)

/-! ## The named graph of a name -/

/-- The graph of the first named graph of `ds` with the name `n`, or the empty
graph when `ds` has no graph of that name. -/
def namedGraphOf (ds : Dataset) (n : Subject) : Graph :=
  ((ds.named.find? (fun ng => ng.name == n)).map (·.graph)).getD []

theorem eq_of_mem_nodup_map' {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, hf => by
      rw [List.map_cons, List.nodup_cons] at h
      rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
      · rw [ha', hb']
      · subst ha'
        exact absurd (hf ▸ List.mem_map_of_mem hb') h.1
      · subst hb'
        exact absurd (hf.symm ▸ List.mem_map_of_mem ha') h.1
      · exact eq_of_mem_nodup_map' f h.2 ha' hb' hf

/-- The lookup finds a graph of the name, or there is none. -/
theorem namedGraphOf_cases (ds : Dataset) (n : Subject) :
    (∃ ng ∈ ds.named, ng.name = n ∧ namedGraphOf ds n = ng.graph) ∨
      ((∀ ng ∈ ds.named, ng.name ≠ n) ∧ namedGraphOf ds n = []) := by
  unfold namedGraphOf
  cases h : ds.named.find? (fun ng => ng.name == n) with
  | some ng =>
    have hp := _root_.List.find?_some h
    exact Or.inl ⟨ng, List.mem_of_find?_eq_some h, beq_iff_eq.mp hp, rfl⟩
  | none =>
    refine Or.inr ⟨fun ng hng e => ?_, rfl⟩
    have := List.find?_eq_none.mp h ng hng
    exact this (beq_iff_eq.mpr e)

/-- In a dataset with distinct graph names, the lookup of a graph's name is
that graph. -/
theorem namedGraphOf_of_mem {ds : Dataset} (h : ds.names.Nodup) {ng : NamedGraph}
    (hng : ng ∈ ds.named) : namedGraphOf ds ng.name = ng.graph := by
  rcases namedGraphOf_cases ds ng.name with ⟨ng', hng', hn, e⟩ | ⟨hno, _⟩
  · rw [e]
    have : ng' = ng :=
      eq_of_mem_nodup_map' (fun x : NamedGraph => x.name) (l := ds.named) h hng' hng hn
    rw [this]
  · exact absurd rfl (hno ng hng)

theorem namedGraphOf_keyNodup {ds : Dataset} (h : ds.IsSet) (n : Subject) :
    (namedGraphOf ds n).KeyNodup := by
  rcases namedGraphOf_cases ds n with ⟨ng, hng, _, e⟩ | ⟨_, e⟩
  · rw [e]; exact h.graphs ng hng
  · rw [e]; exact Graph.keyNodup_nil

/-! ## The dataset in the order of a backend -/

/-- The dataset `ds` with its named graphs in the order of the named backends
of `dsb`: one named graph per backend, with the backend's name and the graph of
that name in `ds`. -/
def alignNamed (dsb : DatasetBackend) (ds : Dataset) : Dataset :=
  { default := ds.default,
    named := dsb.named.map fun ngb => ⟨ngb.name, namedGraphOf ds ngb.name⟩ }

theorem alignNamed_names (dsb : DatasetBackend) (ds : Dataset) :
    (alignNamed dsb ds).names = dsb.named.map (·.name) := by
  simp only [alignNamed, Dataset.names, List.map_map]
  rfl

theorem alignNamed_isSet {D : DatasetDen} {dsb : DatasetBackend} (hex : DatasetBackendExact D dsb)
    {ds : Dataset} (hset : ds.IsSet) : (alignNamed dsb ds).IsSet where
  default := hset.default
  names := by rw [alignNamed_names]; exact hex.namesNodup
  graphs := by
    intro ng hng
    simp only [alignNamed, List.mem_map] at hng
    obtain ⟨ngb, _, rfl⟩ := hng
    exact namedGraphOf_keyNodup hset ngb.name

theorem alignNamed_den {D : DatasetDen} {dsb : DatasetBackend} (hex : DatasetBackendExact D dsb)
    {ds : Dataset} (hset : ds.IsSet) (hden : ds.den = D) : (alignNamed dsb ds).den = ds.den := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none => exact Iff.rfl
    | some n =>
      show (∃ ng ∈ (alignNamed dsb ds).named, ng.name = n ∧ ng.graph.mem t = true) ↔
        ∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true
      constructor
      · rintro ⟨ng, hng, hn, hm⟩
        simp only [alignNamed, List.mem_map] at hng
        obtain ⟨ngb, _, rfl⟩ := hng
        simp only at hn hm
        subst hn
        rcases namedGraphOf_cases ds ngb.name with ⟨ng', hng', hn', e⟩ | ⟨_, e⟩
        · rw [e] at hm; exact ⟨ng', hng', hn', hm⟩
        · rw [e] at hm; simp [Graph.mem] at hm
      · rintro ⟨ng, hng, hn, hm⟩
        have hnm : ds.den.names n := List.mem_map.mpr ⟨ng, hng, hn⟩
        rw [hden] at hnm
        obtain ⟨ngb, hngb, e⟩ := hex.names n hnm
        refine ⟨⟨ngb.name, namedGraphOf ds ngb.name⟩, ?_, e.symm, ?_⟩
        · simp only [alignNamed, List.mem_map]
          exact ⟨ngb, hngb, rfl⟩
        · show (namedGraphOf ds ngb.name).mem t = true
          rw [← e, ← hn, namedGraphOf_of_mem hset.names hng]
          exact hm
  · intro n
    show n ∈ (alignNamed dsb ds).names ↔ n ∈ ds.names
    rw [alignNamed_names]
    constructor
    · intro h
      obtain ⟨ngb, hngb, rfl⟩ := List.mem_map.mp h
      obtain ⟨m, hm, e, _⟩ := hex.named ngb hngb
      rw [← e]
      show ds.den.names m
      rw [hden]; exact hm
    · intro h
      have hn : D.names n := by rw [← hden]; exact h
      obtain ⟨ngb, hngb, e⟩ := hex.names n hn
      exact List.mem_map.mpr ⟨ngb, hngb, e.symm⟩

theorem namedRel_map (g : Subject → Graph) :
    ∀ (l : List NamedGraphBackend), (∀ ngb ∈ l, GraphRel ngb.backend (g ngb.name)) →
      NamedRel l (l.map fun ngb => ⟨ngb.name, g ngb.name⟩)
  | [], _ => .nil
  | ngb :: rest, h =>
    .cons rfl (h ngb List.mem_cons_self)
      (namedRel_map g rest (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- **The backend of a lawful record reads the aligned dataset**, for every
set dataset with the record's denotation. -/
theorem backendReads_alignNamed {D : DatasetDen} {dsb : DatasetBackend}
    (hex : DatasetBackendExact D dsb) {ds : Dataset} (hset : ds.IsSet) (hden : ds.den = D) :
    BackendReads dsb (alignNamed dsb ds) where
  default := by
    refine ⟨backendExact_congr hex.default (fun t => ?_), hset.default⟩
    rw [← hden]
    exact Dataset.den_default_iff_keyMem t
  named := by
    apply namedRel_map
    intro ngb hngb
    obtain ⟨n, hn, e, hb⟩ := hex.named ngb hngb
    have hn' : ds.den.names n := by rw [hden]; exact hn
    obtain ⟨ng, hng, hname⟩ := List.mem_map.mp hn'
    rw [← e, ← hname, namedGraphOf_of_mem hset.names hng]
    refine ⟨backendExact_congr hb (fun t => ?_), hset.graphs ng hng⟩
    rw [← hden, ← hname]
    exact Dataset.IsSet.graph_iff_keyMem_named hset hng t
  namesNodup := hex.namesNodup

theorem map_align_eq (g : Subject → Graph) :
    ∀ (l : List NamedGraphBackend) (m : List NamedGraph), l.map (·.name) = m.map (·.name) →
      (∀ ng ∈ m, g ng.name = ng.graph) →
      l.map (fun ngb => (⟨ngb.name, g ngb.name⟩ : NamedGraph)) = m
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | b :: bs, ng :: ms, h, hg => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨?_, map_align_eq g bs ms h.2 (fun x hx => hg x (List.mem_cons_of_mem _ hx))⟩
    rw [h.1, hg ng List.mem_cons_self]

/-- A dataset already in the order of the backend is its own alignment. -/
theorem alignNamed_self {dsb : DatasetBackend} {ds : Dataset} (hset : ds.IsSet)
    (h : dsb.named.map (·.name) = ds.names) : alignNamed dsb ds = ds := by
  show (⟨ds.default, _⟩ : Dataset) = ds
  rw [map_align_eq (namedGraphOf ds) dsb.named ds.named h
    (fun ng hng => namedGraphOf_of_mem hset.names hng)]

/-! ## The query input over a lawful record -/

/-- The evaluator input of a query over a lawful record `S`, with the set
dataset `ds` as the reference value: the environment reads the aligned
dataset (section 18.6), and the backend is `S`'s. -/
def queryInput (env : EvalEnv) (S : LawfulDataset) (ds : Dataset) (q : Query) : EvalInput :=
  { env := { env with dataset := some (alignNamed S.backend ds) },
    ds := alignNamed S.backend ds, backend := some S.backend, query := q }

theorem queryInput_wf (env : EvalEnv) (S : LawfulDataset) (hS : Assumed S.assumed_contracts)
    {ds : Dataset} (hset : ds.IsSet) (hden : ds.den = S.den) (q : Query) :
    (queryInput env S ds q).Wf where
  envDataset := rfl
  isSet := alignNamed_isSet (S.law hS) hset
  backendReads := by
    intro dsb h
    simp only [queryInput, Option.some.injEq] at h
    subst h
    exact backendReads_alignNamed (S.law hS) hset hden

/-- **The query theorem over any lawful dataset record** (issue 975,
owner-approved plan, step 1). For every `LawfulDataset` `S`, whatever produced
it, and every set dataset `ds` with `S`'s denotation: the evaluator input has
a set dataset with denotation `S.den` and `S`'s backend, and the evaluator's
answer satisfies the evaluator contract (`EvalContract`: the SPARQL 1.1
reference answer, or for SELECT and ASK with no FROM clause the modifier layer
over a WHERE answer that `Allowed` admits and that is the reference WHERE
answer up to the order of the solutions); when the solution modifiers do not
read the order (`OrderFree`), the answer is the reference answer up to the
order of the rows (`AnswerAgrees`: the same SELECT header and multiset of
rows, the same ASK boolean).

Premises: the evaluator's named assumption `hev`, the record's named
assumptions `hS`, and `hset`, `hden`, which name the reference dataset. -/
theorem query_sound (ev : LawfulEvaluator) (hev : ev.AssumptionHolds) (S : LawfulDataset)
    (hS : Assumed S.assumed_contracts) {ds : Dataset} (hset : ds.IsSet) (hden : ds.den = S.den)
    (env : EvalEnv) (q : Query) :
    let x := queryInput env S ds q
    x.ds.IsSet ∧ x.ds.den = S.den ∧ x.backend = some S.backend ∧ EvalContract x (ev.run x) ∧
      (OrderFree q → AnswerAgrees (ev.run x) (referenceAnswer x)) := by
  intro x
  have hw := queryInput_wf env S hS hset hden q
  have hc := ev.contract hev x hw
  refine ⟨alignNamed_isSet (S.law hS) hset, ?_, rfl, hc, fun hof => hc.agrees hw hof⟩
  show (alignNamed S.backend ds).den = S.den
  rw [alignNamed_den (S.law hS) hset hden, hden]

/-- `query_sound` without the evaluator's named assumption, on the inputs
outside `ev.assumed_contractOn`. -/
theorem query_sound_proved (ev : LawfulEvaluator) (S : LawfulDataset)
    (hS : Assumed S.assumed_contracts) {ds : Dataset} (hset : ds.IsSet) (hden : ds.den = S.den)
    (env : EvalEnv) (q : Query) (ha : ¬ ev.assumed_contractOn (queryInput env S ds q)) :
    EvalContract (queryInput env S ds q) (ev.run (queryInput env S ds q)) :=
  ev.sound _ (queryInput_wf env S hS hset hden q) ha

theorem LawfulDataset.assumed_of_proved {S : LawfulDataset} (h : S.Proved) :
    Assumed S.assumed_contracts := by
  unfold LawfulDataset.Proved at h
  rw [h]; exact Assumed.nil

/-! ## Sources -/

/-- **The output of a source**: a lawful dataset record and a set dataset of
the same denotation (the value the reference evaluator reads). For a record
whose law rests on named assumptions (a disk store), the equation rests on the
same assumptions: the reference value is what the store's search returns. -/
structure Sourced where
  store : LawfulDataset
  ref : Dataset
  isSet : ref.IsSet
  den_eq : Assumed store.assumed_contracts → ref.den = store.den

namespace Sourced

/-- The denotation of a source's output. -/
def den (s : Sourced) : DatasetDen := s.store.den

/-- The named assumptions a source's output rests on. -/
def assumptions (s : Sourced) : List Assumption := s.store.assumed_contracts

/-- The evaluator input of a query over a source's output. -/
def input (s : Sourced) (env : EvalEnv) (q : Query) : EvalInput := queryInput env s.store s.ref q

/-- **A query over a source's output**: the evaluator contract over a dataset
whose denotation is the source's `den`, under the source's named assumptions
and the evaluator's. -/
theorem query_sound (s : Sourced) (ev : LawfulEvaluator) (hev : ev.AssumptionHolds)
    (hs : Assumed s.assumptions) (env : EvalEnv) (q : Query) :
    (s.input env q).ds.den = s.den ∧ EvalContract (s.input env q) (ev.run (s.input env q)) ∧
      (OrderFree q → AnswerAgrees (ev.run (s.input env q)) (referenceAnswer (s.input env q))) :=
  let h := Dataflow.query_sound ev hev s.store hs s.isSet (s.den_eq hs) env q
  ⟨h.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The source of a certified dataset: the indexed record the wasm query ops
build (`LawfulDataset.ofCertified`, proved law). -/
def ofCertified (c : CertifiedDataset) : Sourced where
  store := LawfulDataset.ofCertified c
  ref := c.val
  isSet := c.property
  den_eq := fun _ => rfl

theorem ofCertified_den (c : CertifiedDataset) : (ofCertified c).den = c.val.den := rfl

theorem ofCertified_assumptions (c : CertifiedDataset) : (ofCertified c).assumptions = [] := rfl

/-- The aligned dataset of a certified dataset's own record is the dataset. -/
theorem ofCertified_align (c : CertifiedDataset) :
    alignNamed (LawfulDataset.ofCertified c).backend c.val = c.val := by
  apply alignNamed_self c.property
  rw [LawfulDataset.ofCertified_backend, DatasetRestriction.indexedDatasetBackend_named,
    List.map_map]
  rfl

end Sourced

#print axioms namedGraphOf_of_mem
#print axioms alignNamed_isSet
#print axioms alignNamed_den
#print axioms backendReads_alignNamed
#print axioms alignNamed_self
#print axioms queryInput_wf
#print axioms query_sound
#print axioms query_sound_proved
#print axioms Sourced.query_sound
#print axioms Sourced.ofCertified_align

end L4Factoidal.Dataflow
