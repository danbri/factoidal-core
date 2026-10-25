/-
L4Factoidal.Dataflow.StoreTheorems — the backend evaluator against SPARQL 1.1,
stated over the data-access interface types `LawfulStore` and `LawfulDataset`
(`Dataflow/Store.lean`; https://github.com/danbri/factoidal/issues/975,
item 2).

`Storage/BackendRefinement.lean` proves the evaluator against a backend and a
separate premise `BackendExact gb G` with a list `g` that denotes `G`. Here
the premise is the interface value:

* `LawfulStore.evalBgp_kequiv`: the only premise is `Assumed s.assumed_contracts`
  (for a proved store, `Assumed.nil`). The backend's solutions of a basic
  graph pattern equal the reference's (`evalBgp`, SPARQL 1.1 section 18.3)
  over the rows of the unbounded search, as a multiset up to order and RDF
  term equality (`SolKEquiv`). The unbounded search is a list for the graph:
  `solve_all` and `solveNodupKeys` of the law.
* `LawfulStore.evalBgp_kequiv_of_list`: the same against any list that
  denotes the graph with each triple once.
* `LawfulDataset.where_allowed`: for every pattern of `NativeFrag`, the
  WHERE answer of `evalPatternBackend` over the record is an answer `Allowed`
  admits over the dataset the record enumerates (`reference`). The premises
  besides `Assumed` are about the data, not the store law: every named
  backend has an IRI name (`NamesWf`, the condition the query op already
  checks, `namesAreIris`). The former premise `Fixed` (every row object its
  own join key) is gone: language tags are lower case in every term (issue
  1001, PR 57), so `GraphRel` no longer carries it.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Store
import L4Factoidal.Storage.BackendRefinement

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.BackendRefinement
open L4Factoidal.Storage.PlannerSoundness (DatasetBackendExact)
open L4Factoidal.Storage.Sbm11.IdGroup (Allowed)

namespace LawfulStore

/-- **The backend BGP evaluator over a lawful store is the reference
evaluator over the store's rows.** The only premise is the store's named
assumptions. -/
theorem evalBgp_kequiv (s : LawfulStore) (h : Assumed s.assumed_contracts) (b : Bgp) :
    SolKEquiv (evalBgpBackend b s.backend) (evalBgp b (s.search patternBoundAll)) :=
  evalBgpBackend_kequiv (s.law h) (s.search_nodupKeys h patternBoundAll)
    (fun t => ((s.exact h).solve_all t).symm) b

/-- The same against any list that denotes the store's graph with each triple
once. -/
theorem evalBgp_kequiv_of_list (s : LawfulStore) (h : Assumed s.assumed_contracts) {g : Graph}
    (hg : g.KeyNodup) (hG : ∀ t, s.graph t ↔ KeyMem g t) (b : Bgp) :
    SolKEquiv (evalBgpBackend b s.backend) (evalBgp b g) :=
  evalBgpBackend_kequiv (s.law h) hg hG b

/-- For a proved store the statement has no premise. -/
theorem evalBgp_kequiv_proved (s : LawfulStore) (hp : s.Proved) (b : Bgp) :
    SolKEquiv (evalBgpBackend b s.backend) (evalBgp b (s.search patternBoundAll)) :=
  s.evalBgp_kequiv (assumed_of_proved hp) b

/-- Two lawful stores of one graph give one answer, up to order and RDF term
equality. -/
theorem evalBgp_kequiv_of_graph (s s' : LawfulStore) (h : Assumed s.assumed_contracts)
    (h' : Assumed s'.assumed_contracts) (e : ∀ t, s.graph t ↔ s'.graph t) (b : Bgp) :
    SolKEquiv (evalBgpBackend b s.backend) (evalBgpBackend b s'.backend) :=
  (s.evalBgp_kequiv h b).trans
    (s'.evalBgp_kequiv_of_list h' (s.search_nodupKeys h patternBoundAll)
      (fun t => (e t).symm.trans ((s.exact h).solve_all t).symm) b).symm

/-- The law of a store's arm for the list of its rows. -/
theorem backendExact_rows (s : LawfulStore) (h : Assumed s.assumed_contracts) :
    BackendExact s.backend (KeyMem (s.search patternBoundAll)) :=
  backendExact_congr (s.law h) (fun t => ((s.exact h).solve_all t).symm)

end LawfulStore

namespace LawfulDataset

/-- The dataset the record enumerates: each backend read with the unbounded
search (`materialiseDatasetBackend`, the dataset the delegating arms of the
evaluator read). -/
def reference (L : LawfulDataset) : Dataset := materialiseDatasetBackend L.backend

/-- Every named backend has an IRI name. -/
def NamesWf (L : LawfulDataset) : Prop := ∀ ngb ∈ L.backend.named, isIri ngb.name = true

/-- A backend with a law and fixed rows reads the list of its rows. -/
theorem graphRel_rows {gb : GraphBackend} {G : Triple → Prop} (hx : BackendExact gb G) :
    GraphRel gb (backendSearch gb patternBoundAll) where
  exact := backendExact_congr hx (fun t => by
    rw [backendSearch_exact hx patternBoundAll t]
    exact ⟨fun h => ⟨h, rfl⟩, And.left⟩)
  keyNodup := backendSearch_nodupKeys hx patternBoundAll

theorem namedRel_rows {D : DatasetDen} : ∀ (L : List NamedGraphBackend),
    (∀ ngb ∈ L, ∃ n, BackendExact ngb.backend (D.graph (some n))) →
    (∀ ngb ∈ L, isIri ngb.name = true) →
    NamedRel L (L.filterMap (fun ngb => (wfIriOf? ngb.name).map (fun i =>
      ({ name := .iri i, graph := backendSearch ngb.backend patternBoundAll } : NamedGraph))))
  | [], _, _ => .nil
  | ngb :: rest, hx, hi => by
    have hw : wfIriOf? ngb.name = some ⟨ngb.name, hi ngb List.mem_cons_self⟩ := by
      simp [wfIriOf?, hi ngb List.mem_cons_self]
    rw [List.filterMap_cons, hw]
    obtain ⟨n, hn⟩ := hx ngb List.mem_cons_self
    exact .cons ⟨ngb.name, hi ngb List.mem_cons_self⟩ rfl rfl
      (graphRel_rows hn)
      (namedRel_rows rest (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
        (fun x hx' => hi x (List.mem_cons_of_mem _ hx')))

/-- **The WHERE answer of the backend evaluator over a lawful dataset is an
answer SPARQL 1.1 allows**, for every pattern of `NativeFrag`, over the
dataset the record enumerates. -/
theorem where_allowed (L : LawfulDataset) (h : Assumed L.assumed_contracts) (hiri : L.NamesWf)
    (env : EvalEnv) (p : QueryPattern) (hp : NativeFrag p) :
    Allowed env L.reference p L.reference.default
      (evalPatternBackend env L.backend p L.backend.default) := by
  have hl := L.law h
  have hn : NamedRel L.backend.named L.reference.named :=
    namedRel_rows L.backend.named
      (fun ngb hm => by
        obtain ⟨n, -, -, hx⟩ := hl.named ngb hm
        exact ⟨n, hx⟩)
      hiri
  exact evalPatternBackend_allowed env L.backend L.reference hn hl.namesNodup p hp
    L.backend.default L.reference.default (graphRel_rows hl.default)

end LawfulDataset

/-! ## The stages -/

/-- The contract of the BGP answer over a lawful store: under the store's named
assumptions, the reference's answer over the store's rows, up to order and
RDF term equality. -/
def LawfulBgpContract (b : Bgp) (s : LawfulStore) (r : SolutionSeq) : Prop :=
  Assumed s.assumed_contracts → SolKEquiv r (evalBgp b (s.search patternBoundAll))

/-- A lawful store → the backend's solutions of the basic graph pattern `b`. -/
def lawfulBgpStage (b : Bgp) : Stage String LawfulStore SolutionSeq :=
  Stage.ofFun (fun s => evalBgpBackend b s.backend) (LawfulBgpContract b)
    (fun s h => s.evalBgp_kequiv h b)

/-- The contract of the WHERE answer over a lawful dataset. -/
def LawfulWhereContract (env : EvalEnv) (p : QueryPattern) (L : LawfulDataset) (r : SolutionSeq) :
    Prop :=
  NativeFrag p → Assumed L.assumed_contracts → L.NamesWf →
    Allowed env L.reference p L.reference.default r

/-- A lawful dataset → the WHERE answer of the backend evaluator. -/
def lawfulWhereStage (env : EvalEnv) (p : QueryPattern) : Stage String LawfulDataset SolutionSeq :=
  Stage.ofFun (fun L => evalPatternBackend env L.backend p L.backend.default)
    (LawfulWhereContract env p)
    (fun L hp h hiri => L.where_allowed h hiri env p hp)

#print axioms lawfulBgpStage
#print axioms lawfulWhereStage
#print axioms LawfulStore.evalBgp_kequiv
#print axioms LawfulStore.evalBgp_kequiv_of_list
#print axioms LawfulStore.evalBgp_kequiv_proved
#print axioms LawfulStore.evalBgp_kequiv_of_graph
#print axioms LawfulStore.backendExact_rows
#print axioms LawfulDataset.graphRel_rows
#print axioms LawfulDataset.namedRel_rows
#print axioms LawfulDataset.where_allowed

end L4Factoidal.Dataflow
