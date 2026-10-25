/-
L4Factoidal.Storage.SelectedDataset — a pure model of the dataset that the
reference fallback of `l4sbm11 query` reads, and the theorem that its SELECT
answer is the answer over the whole store
(https://github.com/danbri/factoidal/issues/975, hand-over finding 6).

## The two datasets

* `queryDataset q D` is the RDF dataset of the query (SPARQL 1.1 Query section
  13): with no `FROM` and no `FROM NAMED` clause, the dataset `D` of the store;
  else the default graph is the RDF merge of the `FROM` graphs
  (`SPARQL.fromMerge`, `FromMerge.applyDataset_default_isMergeOf`, issue 979)
  and the named graphs are the `FROM NAMED` graphs. It is `SPARQL.applyDataset`,
  which the harness calls.
* `selectedModel q D` is the read of `Harness.Sbm11Query.selectedDataset`: the
  triples whose predicate the predicate collector names
  (`ShardManifest.queryQuadConstantPredicates?`; every triple when it names
  nothing), in the graphs the graph-name collector names
  (`ShardManifest.queryGraphNames?`; every graph when it names nothing). A
  named graph that the predicate selection empties stays in the model with no
  triple, as the harness keeps it. `den_selectedModel` states the model over
  `RDF.DatasetDen`: a quad is in it exactly when it is in `D`, its graph is
  kept and its triple is kept.

## The theorem

`referenceSelect` is the SELECT arm of `Harness.Sbm11Query.runReference`
(the harness calls it). `referenceSelect_selected`: for a SELECT query over a
store whose graph names are IRIs, the answer over
`queryDataset q (selectedModel q D)` is the answer over `queryDataset q D`, the
same list. With no graph-name selection (`referenceSelect_selectedModel`):

1. with no graph-name selection the model is `mapRestrict keep D`: every graph
   kept, each filtered (`selectedModel_of_graphs_none`);
2. `applyDataset` commutes with `mapRestrict` for a `keep` that respects RDF
   term equality and blank-node relabelling (`applyDataset_mapRestrict`); the
   RDF merge of the filtered `FROM` graphs is the filter of the merge
   (`fromMerge_filter`);
3. `mapRestrict keep d` is a `DatasetRestricted` restriction of `d`
   (`datasetRestricted_mapRestrict`), so the evaluator half of planner
   soundness (`DatasetRestriction.runSelectQueryBackendDataset_restrict`)
   gives the same answer. This needed no premise on empty named graphs after
   `DatasetRestricted` lost its field `noEmpty` (2026-10-24).

With a graph-name selection (`referenceSelect_selectedModel_graphs`; the
collector then requires no dataset clause): a planner-fragment pattern does not
read an active graph that its reads (`graphsReadFrom`) do not name
(`evalPatternBackend_active`, `runSelect_default`), so the default graph that
the model drops can be put back; the rest is a `DatasetRestricted` restriction
with the IRIs of the selection readable.

## Not proved here

* The IO read: that `Harness.Sbm11Query.selectedDataset` returns a dataset
  equal to `selectedModel q G.denote`. It reads the files through `Session`;
  its rows come in scan order, so it is equal to the model only up to the
  order of the triples and of the named graphs.
* The environment: the harness evaluates with `env.dataset = some applied`,
  which differs between the two sides; the theorem takes one `env`. Only
  `EXISTS` reads `env.dataset`, and the collectors refuse an `EXISTS`
  (`Query.patternBoundedReads`, `Expr.backendLocal`), but no theorem shows the
  answer does not read it.
* A store with a graph name that is not an IRI, with a predicate or graph-name
  selection: the harness then runs the reference evaluator `evalSelect`, and no
  restriction theorem covers it (the premise `hI`).
* The relation of `runSelectQueryBackendDataset` to the answers that SPARQL 1.1
  allows (`Sbm11.IdAllowedTheorems.Allowed`, `WhereOk`) and to the id path:
  there is no refinement theorem for the backend evaluator
  (`StoreDataset.evalPatternBackend`, `StorePlan.evalBgpBackend`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PlannerSoundness
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.SPARQL.FromMerge
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Storage.SelectedDataset

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StoreFastPath
open L4Factoidal.SPARQL.DatasetRestriction
open L4Factoidal.Storage.PlannerSoundness

/-! ## 1. The model -/

/-- The triples the predicate collector keeps: those whose predicate it names,
or every triple when it names nothing. -/
def selectKeep (q : Query) : Triple → Bool :=
  match ShardManifest.queryQuadConstantPredicates? q with
  | some ps => keepPred ps
  | none => fun _ => true

/-- One graph name of the collector against the graph position of a quad
(`none` is the default graph). The harness looks up the id of the name's term
and compares ids. -/
def graphNameIs : ShardManifest.GraphName → Option Subject → Bool
  | .defaultGraph, none => true
  | .iri v, some (.iri w) => v.val == w.val
  | .bnode l, some (.bnode b) => l == b
  | _, _ => false

/-- The graphs the graph-name collector keeps: those it names, or every graph
when it names nothing. -/
def graphKept (q : Query) (gn : Option Subject) : Bool :=
  match ShardManifest.queryGraphNames? q with
  | none => true
  | some gs => gs.any fun g => graphNameIs g gn

/-- **The pure model of `Harness.Sbm11Query.selectedDataset`.** The kept
triples of the kept graphs; a kept named graph with no kept triple is in the
dataset with no triple. -/
def selectedModel (q : Query) (D : Dataset) : Dataset :=
  { default := if graphKept q none then D.default.filter (selectKeep q) else []
  , named := (D.named.filter fun ng => graphKept q (some ng.name)).map
      fun ng => { ng with graph := ng.graph.filter (selectKeep q) } }

/-- Every graph kept, each filtered by `keep`. -/
def mapRestrict (keep : Triple → Bool) (d : Dataset) : Dataset :=
  { default := d.default.filter keep
  , named := d.named.map fun ng => { ng with graph := ng.graph.filter keep } }

/-- The RDF dataset of the query (SPARQL 1.1 Query section 13): the store's
dataset with no dataset clause, else the `FROM` merge and the `FROM NAMED`
graphs. -/
def queryDataset (q : Query) (D : Dataset) : Dataset :=
  (applyDataset q.dataset D D.default).1

/-- The query with its dataset clauses removed: the harness evaluates it over
the dataset that `applyDataset` built. -/
def withoutDataset : Query → Query
  | .mk form _ pattern groupBy having modifier postValues base =>
      .mk form [] pattern groupBy having modifier postValues base

/-- **The SELECT arm of the reference fallback** (`Harness.Sbm11Query.runReference`
calls it): the backend evaluator when every graph name is an IRI, the reference
evaluator `evalSelect` otherwise, and when the backend evaluator hands the query
on (`text:query`). -/
def referenceSelect (env : EvalEnv) (q : Query) (applied : Dataset) : SolutionSeq :=
  let stripped := withoutDataset q
  let rows? :=
    if QuadDataset.namesAreIris applied then
      runSelectQueryBackendDataset env stripped (indexedDatasetBackend applied)
    else none
  match rows? with
  | some rows => rows
  | none => (evalSelect env applied stripped).2

theorem withoutDataset_pattern (q : Query) : (withoutDataset q).pattern = q.pattern := by
  cases q; rfl

/-! ## 2. The model with no graph-name selection -/

theorem filter_true (l : List Triple) : l.filter (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons t rest ih => simp [ih]

theorem selectedModel_of_graphs_none {q : Query} (h : ShardManifest.queryGraphNames? q = none)
    (D : Dataset) : selectedModel q D = mapRestrict (selectKeep q) D := by
  have hk : ∀ gn, graphKept q gn = true := by
    intro gn
    simp only [graphKept, h]
  unfold selectedModel mapRestrict
  rw [if_pos (hk none), List.filter_eq_self.mpr (fun (ng : NamedGraph) _ => hk (some ng.name))]

theorem mapRestrict_true (d : Dataset) : mapRestrict (fun _ => true) d = d := by
  obtain ⟨dflt, named⟩ := d
  simp only [mapRestrict, filter_true]
  congr 1
  induction named with
  | nil => rfl
  | cons ng rest ih =>
      simp only [List.map_cons, ih]

/-! ## 3. `mapRestrict` is a restriction -/

theorem lookupGraph_map (keep : Triple → Bool) (n : Iri) :
    ∀ l : List NamedGraph,
      lookupGraph (l.map fun ng => { ng with graph := ng.graph.filter keep }) n
        = (lookupGraph l n).map (fun g => g.filter keep)
  | [] => rfl
  | ng :: rest => by
      simp only [List.map_cons, lookupGraph]
      by_cases h : iriNamed ng.name n = true
      · simp [h]
      · simp only [h, if_false, Bool.false_eq_true]
        exact lookupGraph_map keep n rest

/-- **`mapRestrict keep d` is a restriction of `d`**, with no premise on the
named graphs: a graph that `keep` empties is kept with no triple. -/
theorem datasetRestricted_mapRestrict (keep : Triple → Bool) (d : Dataset) :
    DatasetRestricted keep none d (mapRestrict keep d) :=
  { dflt := rfl
  , named := fun i _ => Or.inl (lookupGraph_map keep i.val d.named)
  , namedList := fun _ => namedRestricted_map keep d.named }

/-- The backend SELECT answers the same over `mapRestrict keep d` as over `d`
for a query in the planner fragment whose patterns `keep` keeps. -/
theorem runSelect_mapRestrict (env : EvalEnv) (q : Query) (keep : Triple → Bool) (d : Dataset)
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hk : PatternKept keep q.pattern.rewriteBnodes) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend (mapRestrict keep d))
      = runSelectQueryBackendDataset env q (indexedDatasetBackend d) :=
  runSelectQueryBackendDataset_restrict env (datasetRestricted_mapRestrict keep d) q hf hk
    (fun _ _ => trivial) (fun _ => rfl)

/-! ## 4. The FROM merge of filtered graphs

`keep` respects RDF term equality (`hkey`) and does not read blank-node labels
(`hren`). `keepPred` does both: it reads the predicate only. -/

section Filter

variable {keep : Triple → Bool}

theorem mem_filter_of_keep (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    {t : Triple} (ht : keep t = true) :
    ∀ g : Graph, Graph.mem t (g.filter keep) = Graph.mem t g
  | [] => rfl
  | u :: rest => by
      have ih := mem_filter_of_keep hkey ht rest
      by_cases hu : keep u = true
      · rw [List.filter_cons, if_pos hu]
        simp only [Graph.mem, ih]
      · have hb : u.eqb t = false := by
          cases he : u.eqb t with
          | false => rfl
          | true =>
              exfalso
              apply hu
              rw [hkey u t ((Triple.eqb_iff_key u t).mp he)]
              exact ht
        rw [List.filter_cons, if_neg hu]
        simp only [Graph.mem, hb, Bool.false_or, ih]

theorem add_filter (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    (t : Triple) (g : Graph) :
    (g.add t).filter keep = if keep t then Graph.add t (g.filter keep) else g.filter keep := by
  by_cases ht : keep t = true
  · rw [if_pos ht]
    simp only [Graph.add, mem_filter_of_keep hkey ht g]
    split
    · rfl
    · rw [List.filter_append]
      simp [ht]
  · rw [if_neg ht]
    simp only [Graph.add]
    split
    · rfl
    · rw [List.filter_append]
      simp [ht]

theorem foldl_add_filter (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u) :
    ∀ (g2 g1 : Graph),
      (g2.foldl (fun (acc : Graph) t => acc.add t) g1).filter keep
        = (g2.filter keep).foldl (fun (acc : Graph) t => acc.add t) (g1.filter keep)
  | [], _ => rfl
  | t :: rest, g1 => by
      rw [List.foldl_cons, foldl_add_filter hkey rest (g1.add t), add_filter hkey t g1]
      by_cases ht : keep t = true
      · rw [if_pos ht, List.filter_cons, if_pos ht, List.foldl_cons]
      · rw [if_neg ht, List.filter_cons, if_neg ht]

theorem union_filter (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    (g1 g2 : Graph) :
    (g1.union g2).filter keep = Graph.union (g1.filter keep) (g2.filter keep) :=
  foldl_add_filter hkey g2 g1

theorem foldl_union_filter (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u) :
    ∀ (gs : List Graph) (g0 : Graph),
      (gs.foldl Graph.union g0).filter keep
        = (gs.map (·.filter keep)).foldl Graph.union (g0.filter keep)
  | [], _ => rfl
  | g :: rest, g0 => by
      rw [List.foldl_cons, foldl_union_filter hkey rest, union_filter hkey, List.map_cons,
        List.foldl_cons]

theorem renameBnodes_filter (hren : ∀ (f : BNodeId → BNodeId) (t : Triple),
      keep (t.renameBnodes f) = keep t)
    (f : BNodeId → BNodeId) (g : Graph) :
    (g.renameBnodes f).filter keep = Graph.renameBnodes f (g.filter keep) := by
  simp only [Graph.renameBnodes, List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp only [Function.comp_apply, hren f t]

theorem scopeFromGraphs_filter (hren : ∀ (f : BNodeId → BNodeId) (t : Triple),
      keep (t.renameBnodes f) = keep t) :
    ∀ (n : Nat) (gs : List Graph),
      scopeFromGraphs n (gs.map (·.filter keep)) = (scopeFromGraphs n gs).map (·.filter keep)
  | _, [] => rfl
  | n, g :: rest => by
      simp only [List.map_cons, scopeFromGraphs, renameBnodes_filter hren,
        scopeFromGraphs_filter hren (n + 1) rest]

/-- **The RDF merge of the filtered graphs is the filter of the merge.** -/
theorem fromMerge_filter (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    (hren : ∀ (f : BNodeId → BNodeId) (t : Triple), keep (t.renameBnodes f) = keep t)
    (gs : List Graph) :
    fromMerge (gs.map (·.filter keep)) = (fromMerge gs).filter keep := by
  simp only [fromMerge, List.length_map]
  rw [foldl_union_filter hkey]
  split
  · rfl
  · rw [scopeFromGraphs_filter hren]
    rfl

end Filter

theorem lookupNamedIri_mapRestrict (keep : Triple → Bool) (d : Dataset) (i : Iri) :
    (mapRestrict keep d).lookupNamedIri i = (d.lookupNamedIri i).map (·.filter keep) := by
  simp only [Dataset.lookupNamedIri]
  split
  · simp only [Dataset.lookupNamed, mapRestrict, List.find?_map]
    have hp : ((fun ng : NamedGraph => ng.name == Subject.iri ⟨i, by assumption⟩) ∘
        fun ng : NamedGraph => { ng with graph := ng.graph.filter keep })
        = fun ng : NamedGraph => ng.name == Subject.iri ⟨i, by assumption⟩ := rfl
    rw [hp]
    cases d.named.find? (fun ng => ng.name == Subject.iri ⟨i, by assumption⟩) <;> rfl
  · rfl

/-- **`applyDataset` commutes with `mapRestrict`** for a `keep` that respects
RDF term equality and blank-node relabelling. -/
theorem applyDataset_mapRestrict {keep : Triple → Bool}
    (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    (hren : ∀ (f : BNodeId → BNodeId) (t : Triple), keep (t.renameBnodes f) = keep t)
    (dcs : List DatasetClause) (d : Dataset) (a a' : Graph) :
    (applyDataset dcs (mapRestrict keep d) a).1 = mapRestrict keep (applyDataset dcs d a').1 := by
  unfold applyDataset
  split
  · rfl
  · simp only [lookupNamedIri_mapRestrict]
    simp only [mapRestrict]
    congr 1
    · rw [← fromMerge_filter hkey hren, List.map_filterMap]
    · rw [List.map_filterMap]
      congr 1
      funext dc
      cases dc with
      | named i =>
          simp only []
          cases h : Dataset.lookupNamedIri i.val d <;> simp
      | default _ => rfl

theorem namesAreIris_mapRestrict (keep : Triple → Bool) (d : Dataset) :
    QuadDataset.namesAreIris (mapRestrict keep d) = QuadDataset.namesAreIris d := by
  simp only [QuadDataset.namesAreIris, mapRestrict, List.all_map]
  rfl

theorem keepPred_key' (P : List WfIri) :
    ∀ t u : Triple, t.key = u.key → keepPred P t = keepPred P u :=
  fun t u e => keepPred_key P t u e

theorem keepPred_rename (P : List WfIri) :
    ∀ (f : BNodeId → BNodeId) (t : Triple), keepPred P (t.renameBnodes f) = keepPred P t :=
  fun _ _ => rfl

/-! ## 5. The answer -/

theorem fulltext_rewriteBnodeTriple (tp : TriplePattern) :
    (rewriteBnodeTriple tp).fulltext?.isSome = tp.fulltext?.isSome := by
  obtain ⟨s, p, o⟩ := tp
  simp only [rewriteBnodeTriple, TriplePattern.fulltext?]
  cases p <;> cases o <;> rfl

theorem bgpHasFulltext_map (b : Bgp) :
    bgpHasFulltext (b.map rewriteBnodeTriple) = bgpHasFulltext b := by
  simp only [bgpHasFulltext, List.any_map, Function.comp_def, fulltext_rewriteBnodeTriple]

theorem mentionsFulltext_rewriteBnodes :
    ∀ p : QueryPattern, p.rewriteBnodes.mentionsFulltext = p.mentionsFulltext
  | .bgp b => by
      simp only [QueryPattern.rewriteBnodes, QueryPattern.mentionsFulltext, bgpHasFulltext_map]
  | .join l r | .union l r | .minus l r | .lateral l r => by
      simp only [QueryPattern.rewriteBnodes, QueryPattern.mentionsFulltext,
        mentionsFulltext_rewriteBnodes l, mentionsFulltext_rewriteBnodes r]
  | .leftJoin l r _ => by
      simp only [QueryPattern.rewriteBnodes, QueryPattern.mentionsFulltext,
        mentionsFulltext_rewriteBnodes l, mentionsFulltext_rewriteBnodes r]
  | .filter _ p | .bind _ _ p | .graph _ p => by
      simp only [QueryPattern.rewriteBnodes, QueryPattern.mentionsFulltext,
        mentionsFulltext_rewriteBnodes p]
  | .values _ _ | .service _ _ _ | .serviceVar _ _ _ | .subSelect _ | .propertyPath _ _ _
  | .empty => by
      simp only [QueryPattern.rewriteBnodes, QueryPattern.mentionsFulltext]

theorem mentionsFulltext_of_plannerFragment :
    ∀ p : QueryPattern, plannerFragment p = true → p.mentionsFulltext = false
  | .bgp b, h => by simpa [plannerFragment, QueryPattern.mentionsFulltext] using h
  | .empty, _ => rfl
  | .join l r, h | .union l r, h | .minus l r, h => by
      simp only [plannerFragment, Bool.and_eq_true] at h
      simp only [QueryPattern.mentionsFulltext, mentionsFulltext_of_plannerFragment l h.1,
        mentionsFulltext_of_plannerFragment r h.2, Bool.or_false]
  | .leftJoin l r _, h => by
      simp only [plannerFragment, Bool.and_eq_true] at h
      simp only [QueryPattern.mentionsFulltext, mentionsFulltext_of_plannerFragment l h.1.2,
        mentionsFulltext_of_plannerFragment r h.2, Bool.or_false]
  | .filter _ p, h | .bind _ _ p, h => by
      simp only [plannerFragment, Bool.and_eq_true] at h
      simp only [QueryPattern.mentionsFulltext, mentionsFulltext_of_plannerFragment p h.2]
  | .graph (.iri _) p, h | .graph (.var _) p, h => by
      simp only [plannerFragment, Bool.and_eq_true] at h
      simp only [QueryPattern.mentionsFulltext, mentionsFulltext_of_plannerFragment p h.2]
  | .graph (.bnode _) _, h | .graph (.literal _) _, h | .graph (.tripleTerm _ _ _) _, h
  | .lateral _ _, h | .values _ _, h | .service _ _ _, h | .serviceVar _ _ _, h
  | .subSelect _, h | .propertyPath _ _ _, h => by simp [plannerFragment] at h

/-- The backend SELECT evaluator answers (it does not hand the query on) for a
SELECT query with no `text:query` pattern. -/
theorem runSelect_isSome (env : EvalEnv) (q : Query) (dsb : DatasetBackend)
    (hft : q.pattern.mentionsFulltext = false) {sel : SelectClause} (hs : q.form = .select sel) :
    (runSelectQueryBackendDataset env q dsb).isSome = true := by
  unfold runSelectQueryBackendDataset
  rw [if_neg (by rw [hft]; exact Bool.false_ne_true)]
  cases q with
  | mk form dcs pattern gb hv md pv bs =>
      simp only [Query.form] at hs
      subst hs
      unfold evalSelectBackendDataset
      split
      · rfl
      · unfold evalSelectBackendOnGraph
        repeat' split
        all_goals simp_all [Query.form]

theorem plannerFragment_of_preds {q : Query} {P : List WfIri}
    (h : ShardManifest.queryQuadConstantPredicates? q = some P) :
    plannerFragment q.pattern.rewriteBnodes = true := by
  simp only [ShardManifest.queryQuadConstantPredicates?] at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    exact hg.2
  · simp at h

/-- **The reference fallback answers over the selected dataset as over the
whole store.** When the graph-name collector names no graph, the SELECT answer
of the reference fallback over the query dataset of `selectedModel q D` is its
answer over the query dataset of `D` (the same list). `hi`: the graph names of
the query dataset are IRIs, or the predicate collector names no predicate (then
the model is `D`). -/
theorem referenceSelect_selectedModel (env : EvalEnv) (q : Query) (D : Dataset)
    {sel : SelectClause} (hs : q.form = .select sel)
    (hg : ShardManifest.queryGraphNames? q = none)
    (hi : QuadDataset.namesAreIris (queryDataset q D) = true ∨
      ShardManifest.queryQuadConstantPredicates? q = none) :
    referenceSelect env q (queryDataset q (selectedModel q D))
      = referenceSelect env q (queryDataset q D) := by
  rw [selectedModel_of_graphs_none hg]
  cases hp : ShardManifest.queryQuadConstantPredicates? q with
  | none =>
      have hk : selectKeep q = fun _ => true := by simp only [selectKeep, hp]
      rw [hk, mapRestrict_true]
  | some P =>
      have hk : selectKeep q = keepPred P := by simp only [selectKeep, hp]
      rw [hk]
      have hI : QuadDataset.namesAreIris (queryDataset q D) = true := by
        rcases hi with h | h
        · exact h
        · rw [hp] at h; cases h
      have hq : queryDataset q (mapRestrict (keepPred P) D)
          = mapRestrict (keepPred P) (queryDataset q D) :=
        applyDataset_mapRestrict (keepPred_key' P) (keepPred_rename P) q.dataset D _ _
      have hf : plannerFragment (withoutDataset q).pattern.rewriteBnodes = true := by
        rw [withoutDataset_pattern]; exact plannerFragment_of_preds hp
      have hkp : PatternKept (keepPred P) (withoutDataset q).pattern.rewriteBnodes := by
        rw [withoutDataset_pattern]; exact patternKept_of_queryPredicates q P hp
      have hsome := runSelect_isSome env (withoutDataset q) (indexedDatasetBackend (queryDataset q D))
        (by rw [withoutDataset_pattern, ← mentionsFulltext_rewriteBnodes]
            exact mentionsFulltext_of_plannerFragment _ (plannerFragment_of_preds hp)) (sel := sel)
        (by cases q; simpa [withoutDataset, Query.form] using hs)
      simp only [referenceSelect, hq, namesAreIris_mapRestrict, hI, if_true,
        runSelect_mapRestrict env (withoutDataset q) (keepPred P) (queryDataset q D) hf hkp]
      cases hr : runSelectQueryBackendDataset env (withoutDataset q)
          (indexedDatasetBackend (queryDataset q D)) with
      | some r => rfl
      | none => rw [hr] at hsome; cases hsome

/-! ## 6. A graph-name selection

With `queryGraphNames? q = some gs` the model drops the named graphs that `gs`
does not name and, when `gs` does not name the default graph, the default
graph. A pattern whose reads the collector bounds by `gs` does not read the
active graph when `gs` does not name it (`evalPatternBackend_active`), so the
default graph can be put back (`runSelect_default`), and the rest is a
`DatasetRestricted` restriction with the IRIs of `gs` readable. -/

section GraphSelection

open ShardManifest (GraphName graphsReadFrom)

theorem reads_bin {a : GraphName} {l r : QueryPattern} {gs : List GraphName}
    (h : (do let l' ← graphsReadFrom a l; let r' ← graphsReadFrom a r; some (l' ++ r'))
      = some gs) :
    ∃ gl gr, graphsReadFrom a l = some gl ∧ graphsReadFrom a r = some gr ∧ gs = gl ++ gr := by
  cases hl : graphsReadFrom a l <;> cases hr : graphsReadFrom a r <;> simp [hl, hr] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem reads_graph {a : GraphName} {name : WfIri} {p : QueryPattern} {gs : List GraphName}
    (h : graphsReadFrom a (.graph (.iri name) p) = some gs) :
    ∃ inner, graphsReadFrom (.iri name) p = some inner ∧ (∀ x ∈ inner, x ∈ gs) ∧
      GraphName.iri name ∈ gs := by
  simp only [graphsReadFrom] at h
  cases hi : graphsReadFrom (.iri name) p with
  | none => rw [hi] at h; cases h
  | some inner =>
      rw [hi] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
      refine ⟨inner, rfl, ?_, ?_⟩
      · intro x hx
        rw [← h]
        split
        · exact hx
        · exact List.mem_cons_of_mem _ hx
      · rw [← h]
        split
        · rename_i hc
          exact List.contains_iff_mem.mp hc
        · exact List.mem_cons_self

/-- The constant `GRAPH` names of a pattern are in its reads. -/
theorem graphNames_of_reads :
    ∀ (p : QueryPattern) (a : GraphName) (gs : List GraphName),
      graphsReadFrom a p = some gs → ∀ i ∈ graphNamesIn p, GraphName.iri i ∈ gs
  | .join l r, a, gs, h | .union l r, a, gs, h | .minus l r, a, gs, h => by
      obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
      intro i hi
      simp only [graphNamesIn, List.mem_append] at hi
      rcases hi with hi | hi
      · exact List.mem_append_left _ (graphNames_of_reads l a gl hl i hi)
      · exact List.mem_append_right _ (graphNames_of_reads r a gr hr i hi)
  | .leftJoin l r c, a, gs, h => by
      simp only [graphsReadFrom] at h
      split at h
      · obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
        intro i hi
        simp only [graphNamesIn, List.mem_append] at hi
        rcases hi with hi | hi
        · exact List.mem_append_left _ (graphNames_of_reads l a gl hl i hi)
        · exact List.mem_append_right _ (graphNames_of_reads r a gr hr i hi)
      · cases h
  | .filter c p, a, gs, h | .bind c _ p, a, gs, h => by
      simp only [graphsReadFrom] at h
      split at h
      · intro i hi
        exact graphNames_of_reads p a gs h i hi
      · cases h
  | .graph (.iri name) p, a, gs, h => by
      obtain ⟨inner, hin, hsub, hname⟩ := reads_graph h
      intro i hi
      simp only [graphNamesIn, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hname
      · exact hsub _ (graphNames_of_reads p (.iri name) inner hin i hi)
  | .graph (.var _) _, _, _, _ | .graph (.bnode _) _, _, _, _ | .graph (.literal _) _, _, _, _
  | .graph (.tripleTerm _ _ _) _, _, _, _ | .bgp _, _, _, _ | .empty, _, _, _
  | .propertyPath _ _ _, _, _, _ | .values _ _, _, _, _ | .lateral _ _, _, _, _
  | .service _ _ _, _, _, _ | .serviceVar _ _ _, _, _, _ | .subSelect _, _, _, _ => by
      intro i hi
      simp [graphNamesIn] at hi

/-- A pattern whose reads the collector bounds holds no `GRAPH ?v`. -/
theorem graphVarIn_of_reads :
    ∀ (p : QueryPattern) (a : GraphName) (gs : List GraphName),
      graphsReadFrom a p = some gs → graphVarIn p = false
  | .join l r, a, gs, h | .union l r, a, gs, h | .minus l r, a, gs, h => by
      obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
      simp only [graphVarIn, graphVarIn_of_reads l a gl hl, graphVarIn_of_reads r a gr hr,
        Bool.or_false]
  | .leftJoin l r c, a, gs, h => by
      simp only [graphsReadFrom] at h
      split at h
      · obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
        simp only [graphVarIn, graphVarIn_of_reads l a gl hl, graphVarIn_of_reads r a gr hr,
          Bool.or_false]
      · cases h
  | .filter c p, a, gs, h | .bind c _ p, a, gs, h => by
      simp only [graphsReadFrom] at h
      split at h
      · simp only [graphVarIn, graphVarIn_of_reads p a gs h]
      · cases h
  | .graph (.iri name) p, a, gs, h => by
      obtain ⟨inner, hin, _, _⟩ := reads_graph h
      simp only [graphVarIn, graphVarIn_of_reads p (.iri name) inner hin]
  | .graph (.var _) _, _, _, h | .graph (.bnode _) _, _, _, h | .graph (.literal _) _, _, _, h
  | .graph (.tripleTerm _ _ _) _, _, _, h => by simp [graphsReadFrom] at h
  | .bgp _, _, _, _ | .empty, _, _, _ | .propertyPath _ _ _, _, _, _ | .values _ _, _, _, _
  | .lateral _ _, _, _, _ | .service _ _ _, _, _, _ | .serviceVar _ _ _, _, _, _
  | .subSelect _, _, _, _ => rfl

/-- **A pattern does not read the active graph that its reads do not name.**
Over two dataset backends with the same named graphs, a planner-fragment
pattern whose reads from the active graph `a` are bounded by `gs` answers the
same over any two active graphs when `a` is not in `gs`, and over the same
active graph otherwise. -/
theorem evalPatternBackend_active (env : EvalEnv) {dsb dsb' : DatasetBackend}
    (hn : dsb.named = dsb'.named) :
    ∀ (p : QueryPattern) (a : GraphName) (gs : List GraphName),
      plannerFragment p = true → graphsReadFrom a p = some gs →
      ∀ gb gb' : StoreBackend.GraphBackend, (a ∈ gs → gb = gb') →
        evalPatternBackend env dsb p gb = evalPatternBackend env dsb' p gb'
  | .bgp [], _, _, _, _, gb, gb', _ => by
      simp only [evalPatternBackend, StorePlan.evalBgpBackend_nil]
  | .bgp (tp :: rest), a, gs, _, h, gb, gb', hg => by
      simp only [graphsReadFrom, List.isEmpty_cons, Bool.false_eq_true, if_false,
        Option.some.injEq] at h
      subst h
      rw [hg List.mem_cons_self]
      rfl
  | .empty, _, _, _, _, _, _, _ => rfl
  | .join l r, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
      simp only [evalPatternBackend,
        evalPatternBackend_active env hn l a gl hf.1 hl gb gb'
          (fun hm => hg (List.mem_append_left _ hm)),
        evalPatternBackend_active env hn r a gr hf.2 hr gb gb'
          (fun hm => hg (List.mem_append_right _ hm))]
  | .union l r, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
      simp only [evalPatternBackend,
        evalPatternBackend_active env hn l a gl hf.1 hl gb gb'
          (fun hm => hg (List.mem_append_left _ hm)),
        evalPatternBackend_active env hn r a gr hf.2 hr gb gb'
          (fun hm => hg (List.mem_append_right _ hm))]
  | .minus l r, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
      simp only [evalPatternBackend,
        evalPatternBackend_active env hn l a gl hf.1 hl gb gb'
          (fun hm => hg (List.mem_append_left _ hm)),
        evalPatternBackend_active env hn r a gr hf.2 hr gb gb'
          (fun hm => hg (List.mem_append_right _ hm))]
  | .leftJoin l r c, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphsReadFrom] at h
      split at h
      · obtain ⟨gl, gr, hl, hr, rfl⟩ := reads_bin h
        simp only [evalPatternBackend, hf.1.1, if_true,
          evalPatternBackend_active env hn l a gl hf.1.2 hl gb gb'
            (fun hm => hg (List.mem_append_left _ hm)),
          evalPatternBackend_active env hn r a gr hf.2 hr gb gb'
            (fun hm => hg (List.mem_append_right _ hm))]
      · cases h
  | .filter c p, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphsReadFrom] at h
      split at h
      · simp only [evalPatternBackend, hf.1, if_true,
          evalPatternBackend_active env hn p a gs hf.2 h gb gb' hg]
      · cases h
  | .bind e v p, a, gs, hf, h, gb, gb', hg => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      simp only [graphsReadFrom] at h
      split at h
      · simp only [evalPatternBackend, hf.1, if_true,
          evalPatternBackend_active env hn p a gs hf.2 h gb gb' hg]
      · cases h
  | .graph (.iri name) p, a, gs, hf, h, gb, gb', _ => by
      simp only [plannerFragment, Bool.and_eq_true] at hf
      obtain ⟨inner, hin, _, _⟩ := reads_graph h
      simp only [evalPatternBackend, hn]
      cases lookupNamedBackend name.val dsb'.named with
      | none => rfl
      | some g =>
          exact evalPatternBackend_active env hn p (.iri name) inner hf.2 hin g g (fun _ => rfl)
  | .graph (.var _) _, _, _, _, h, _, _, _ | .graph (.bnode _) _, _, _, _, h, _, _, _
  | .graph (.literal _) _, _, _, _, h, _, _, _ | .graph (.tripleTerm _ _ _) _, _, _, _, h, _, _, _ => by
      simp [graphsReadFrom] at h
  | .propertyPath _ _ _, _, _, hf, _, _, _, _ | .values _ _, _, _, hf, _, _, _, _
  | .lateral _ _, _, _, hf, _, _, _, _ | .service _ _ _, _, _, hf, _, _, _, _
  | .serviceVar _ _ _, _, _, hf, _, _, _, _ | .subSelect _, _, _, hf, _, _, _, _ => by
      simp [plannerFragment] at hf

/-- Two indexed datasets with the same named graphs give the same SELECT answer
when the query's reads from the default graph (`gs`) do not name it. -/
theorem evalSelectBackendOnGraph_active (env : EvalEnv) (q : Query) {d d' : Dataset}
    (hn : d.named = d'.named) {gs : List GraphName}
    (hf : plannerFragment q.pattern = true)
    (hr : graphsReadFrom .defaultGraph q.pattern = some gs)
    (hd : GraphName.defaultGraph ∉ gs) :
    evalSelectBackendOnGraph env q (indexedGraphBackend d.default) (indexedDatasetBackend d)
      = evalSelectBackendOnGraph env q (indexedGraphBackend d'.default)
          (indexedDatasetBackend d') := by
  have hN : (indexedDatasetBackend d).named = (indexedDatasetBackend d').named := by
    rw [indexedDatasetBackend_named, indexedDatasetBackend_named, hn]
  have hbgp : ∀ tp, q.pattern ≠ .bgp [tp] := by
    intro tp hp
    rw [hp] at hr
    simp only [graphsReadFrom, List.isEmpty_cons, Bool.false_eq_true, if_false,
      Option.some.injEq] at hr
    exact hd (hr ▸ List.mem_cons_self)
  have hvar : ∀ w p', q.pattern ≠ .graph (.var w) p' := by
    intro w p' hp
    rw [hp] at hr
    simp [graphsReadFrom] at hr
  cases hcs : detectStreamingCountStar q with
  | some triple =>
      obtain ⟨alias, tp, scope⟩ := triple
      have hex := detectStreamingCountStar_extract hcs
      cases scope with
      | none => exact absurd (extractSingleTpBgpScoped_bare hex) (hbgp tp)
      | some gname => simp only [evalSelectBackendOnGraph, hcs, hN]
  | none =>
      cases hcl : detectLimitSingleTpScoped q with
      | none =>
          simp only [evalSelectBackendOnGraph, hcs, hcl,
            resolveStreamingCountGroupByPredicate_indexed]
          cases q.form with
          | select _ =>
              rw [evalPatternBackend_active env hN q.pattern .defaultGraph gs hf hr _ _
                (fun h => absurd h hd)]
          | construct _ => rfl
          | ask => rfl
          | describe _ => rfl
      | some tr =>
          obtain ⟨tp, scope, k⟩ := tr
          have hex := detectLimitSingleTpScoped_extract hcl
          simp only [evalSelectBackendOnGraph, hcs, hcl,
            resolveStreamingCountGroupByPredicate_indexed]
          cases q.form with
          | construct _ => rfl
          | ask => rfl
          | describe _ => rfl
          | select sel =>
              simp only [evalLimitSingleTpScoped]
              cases scope with
              | active => exact absurd (extractSingleTpBgpLimitScope_active hex) (hbgp tp)
              | named gname => simp only [hN]
              | everyNamed w =>
                  exact absurd (extractSingleTpBgpLimitScope_everyNamed hex) (hvar w _)

theorem runSelect_default (env : EvalEnv) (q : Query) {d d' : Dataset}
    (hn : d.named = d'.named) {gs : List GraphName}
    (hf : plannerFragment q.pattern.rewriteBnodes = true)
    (hr : graphsReadFrom .defaultGraph q.pattern.rewriteBnodes = some gs)
    (hd : GraphName.defaultGraph ∉ gs) :
    runSelectQueryBackendDataset env q (indexedDatasetBackend d)
      = runSelectQueryBackendDataset env q (indexedDatasetBackend d') := by
  simp only [runSelectQueryBackendDataset]
  split
  · rfl
  · rename_i _
    simp only [evalSelectBackendDataset]
    cases hg : detectStreamingCountGroupByGraph
        (.mk q.form q.dataset q.pattern.rewriteBnodes q.groupBy q.having q.modifier
          q.postValues q.base) with
    | some pair =>
        obtain ⟨w, tp, _, _, _, hp, _⟩ := detectStreamingCountGroupByGraph_shape hg
        have hp' : q.pattern.rewriteBnodes = .graph (.var w) (.bgp [tp]) := hp
        rw [hp'] at hr
        simp [graphsReadFrom] at hr
    | none =>
        exact evalSelectBackendOnGraph_active env _ hn hf hr hd

theorem patternKept_true : ∀ p : QueryPattern, PatternKept (fun _ => true) p
  | .bgp [] => fun _ => rfl
  | .bgp (_ :: _) => by simp [PatternKept, TpKept, BoundKept]
  | .empty => fun _ => rfl
  | .join a b | .union a b | .minus a b => ⟨patternKept_true a, patternKept_true b⟩
  | .leftJoin a b _ => ⟨patternKept_true a, patternKept_true b⟩
  | .filter _ p | .bind _ _ p | .graph _ p => patternKept_true p
  | .values _ _ | .propertyPath _ _ _ | .lateral _ _ | .service _ _ _ | .serviceVar _ _ _
  | .subSelect _ => trivial

theorem selectKept (q : Query) : PatternKept (selectKeep q) q.pattern.rewriteBnodes := by
  cases hp : ShardManifest.queryQuadConstantPredicates? q with
  | none =>
      have hk : selectKeep q = fun _ => true := by simp only [selectKeep, hp]
      rw [hk]
      exact patternKept_true _
  | some P =>
      have hk : selectKeep q = keepPred P := by simp only [selectKeep, hp]
      rw [hk]
      exact patternKept_of_queryPredicates q P hp

theorem lookupGraph_filter {P : NamedGraph → Bool} (n : Iri) :
    ∀ l : List NamedGraph, (∀ ng ∈ l, iriNamed ng.name n = true → P ng = true) →
      lookupGraph (l.filter P) n = lookupGraph l n
  | [], _ => rfl
  | ng :: rest, h => by
      have ih := lookupGraph_filter n rest (fun x hx => h x (List.mem_cons_of_mem _ hx))
      by_cases hp : P ng = true
      · rw [List.filter_cons, if_pos hp]
        by_cases hk : iriNamed ng.name n = true
        · rw [lookupGraph_cons_pos hk, lookupGraph_cons_pos hk]
        · rw [lookupGraph_cons_neg hk, lookupGraph_cons_neg hk, ih]
      · rw [List.filter_cons, if_neg hp]
        have hk : ¬ iriNamed ng.name n = true := fun hk => hp (h ng List.mem_cons_self hk)
        rw [lookupGraph_cons_neg hk, ih]

/-- The IRIs among the collector's graph names. -/
def readableOf (gs : List GraphName) : List WfIri :=
  gs.filterMap fun g => match g with
    | .iri v => some v
    | _ => none

theorem mem_readableOf {gs : List GraphName} {i : WfIri} (h : GraphName.iri i ∈ gs) :
    i ∈ readableOf gs :=
  List.mem_filterMap.mpr ⟨.iri i, h, rfl⟩

theorem namesAreIris_iff (d : Dataset) :
    QuadDataset.namesAreIris d = true ↔ ∀ ng ∈ d.named, ∃ w, ng.name = .iri w := by
  simp only [QuadDataset.namesAreIris, List.all_eq_true]
  constructor
  · intro h ng hng
    have := h ng hng
    split at this
    · rename_i w hw
      exact ⟨w, hw⟩
    · cases this
  · intro h ng hng
    obtain ⟨w, hw⟩ := h ng hng
    rw [hw]

/-- **The reference fallback answers over the selected dataset as over the
whole store, with a graph-name selection.** When the graph-name collector names
the graphs `gs` and every graph name of the store is an IRI, the SELECT answer
of the reference fallback over `selectedModel q D` is its answer over `D` (the
same list). The collector names graphs only for a query with no dataset clause,
so both query datasets are the datasets themselves. -/
theorem referenceSelect_selectedModel_graphs (env : EvalEnv) (q : Query) (D : Dataset)
    {sel : SelectClause} (hs : q.form = .select sel)
    {gs : List GraphName} (hg : ShardManifest.queryGraphNames? q = some gs)
    (hI : QuadDataset.namesAreIris D = true) :
    referenceSelect env q (queryDataset q (selectedModel q D))
      = referenceSelect env q (queryDataset q D) := by
  have hguard : (q.patternBoundedReads && q.dataset.isEmpty && ShardManifest.plannerFragmentQuery q)
      = true := by
    simp only [ShardManifest.queryGraphNames?] at hg
    split at hg
    · assumption
    · cases hg
  have hr : graphsReadFrom .defaultGraph q.pattern.rewriteBnodes = some gs := by
    simp only [ShardManifest.queryGraphNames?, hguard, if_true] at hg
    exact hg
  simp only [Bool.and_eq_true] at hguard
  have hf : plannerFragment q.pattern.rewriteBnodes = true := hguard.2
  have hdcs : q.dataset = [] := List.isEmpty_iff.mp hguard.1.2
  have hqd : ∀ X : Dataset, queryDataset q X = X := by
    intro X
    simp only [queryDataset, applyDataset, hdcs, List.isEmpty_nil, if_true]
  rw [hqd, hqd]
  let keep := selectKeep q
  let M := selectedModel q D
  let M' : Dataset := { default := D.default.filter keep, named := M.named }
  have hgk : ∀ i : WfIri, GraphName.iri i ∈ gs → ∀ w : WfIri, w.val = i.val →
      graphKept q (some (.iri w)) = true := by
    intro i hi w hw
    simp only [graphKept, hg, List.any_eq_true]
    exact ⟨.iri i, hi, by simp [graphNameIs, hw]⟩
  have hrestr : DatasetRestricted keep (some (readableOf gs)) D M' :=
    { dflt := rfl
    , named := by
        intro i hi
        refine Or.inl ?_
        show lookupGraph ((D.named.filter fun ng => graphKept q (some ng.name)).map
            fun ng => { ng with graph := ng.graph.filter keep }) i.val = _
        rw [lookupGraph_map, lookupGraph_filter]
        intro ng hng hk
        obtain ⟨w, hw⟩ := (namesAreIris_iff D).mp hI ng hng
        have hiv : GraphName.iri i ∈ gs := by
          simp only [readableName, readableOf, List.mem_filterMap] at hi
          obtain ⟨g, hgm, hgv⟩ := hi
          cases g with
          | iri v => simp only [Option.some.injEq] at hgv; rw [← hgv]; exact hgm
          | defaultGraph => cases hgv
          | bnode _ => cases hgv
        have hwv : w.val = i.val := by
          simp only [iriNamed, hw, beq_iff_eq] at hk
          exact hk
        rw [hw]
        exact hgk i hiv w hwv
    , namedList := fun h => by cases h }
  have hkp : PatternKept keep q.pattern.rewriteBnodes := selectKept q
  have hrM' : runSelectQueryBackendDataset env (withoutDataset q) (indexedDatasetBackend M')
      = runSelectQueryBackendDataset env (withoutDataset q) (indexedDatasetBackend D) := by
    refine runSelectQueryBackendDataset_restrict env hrestr (withoutDataset q) ?_ ?_ ?_ ?_
    · rw [withoutDataset_pattern]; exact hf
    · rw [withoutDataset_pattern]; exact hkp
    · rw [withoutDataset_pattern]
      intro i hi
      exact mem_readableOf (graphNames_of_reads _ _ gs hr i hi)
    · rw [withoutDataset_pattern, graphVarIn_of_reads _ _ gs hr]
      intro h; cases h
  have hrM : runSelectQueryBackendDataset env (withoutDataset q) (indexedDatasetBackend M)
      = runSelectQueryBackendDataset env (withoutDataset q) (indexedDatasetBackend M') := by
    by_cases hdg : GraphName.defaultGraph ∈ gs
    · have hk0 : graphKept q none = true := by
        simp only [graphKept, hg, List.any_eq_true]
        exact ⟨.defaultGraph, hdg, rfl⟩
      have : M = M' := by
        show selectedModel q D = M'
        simp only [selectedModel, hk0, if_true]
        rfl
      rw [this]
    · exact runSelect_default env (withoutDataset q) rfl
        (by rw [withoutDataset_pattern]; exact hf) (by rw [withoutDataset_pattern]; exact hr) hdg
  have hIM : QuadDataset.namesAreIris M = true := by
    rw [namesAreIris_iff]
    intro ng hng
    simp only [M, selectedModel, List.mem_map, List.mem_filter] at hng
    obtain ⟨ng0, ⟨hng0, _⟩, rfl⟩ := hng
    exact (namesAreIris_iff D).mp hI ng0 hng0
  have hsome := runSelect_isSome env (withoutDataset q) (indexedDatasetBackend D)
    (by rw [withoutDataset_pattern, ← mentionsFulltext_rewriteBnodes]
        exact mentionsFulltext_of_plannerFragment _ hf) (sel := sel)
    (by cases q; simpa [withoutDataset, Query.form] using hs)
  show referenceSelect env q M = referenceSelect env q D
  simp only [referenceSelect, hIM, hI, if_true, hrM, hrM']
  cases hr0 : runSelectQueryBackendDataset env (withoutDataset q) (indexedDatasetBackend D) with
  | some r => rfl
  | none => rw [hr0] at hsome; cases hsome


theorem namesAreIris_queryDataset (q : Query) {d : Dataset}
    (h : QuadDataset.namesAreIris d = true) :
    QuadDataset.namesAreIris (queryDataset q d) = true := by
  simp only [queryDataset, applyDataset]
  split
  · exact h
  · rw [namesAreIris_iff]
    intro ng hng
    simp only [List.mem_filterMap] at hng
    obtain ⟨dc, _, hdc⟩ := hng
    cases dc with
    | named i =>
        simp only [Option.map_eq_some_iff] at hdc
        obtain ⟨_, _, rfl⟩ := hdc
        exact ⟨i, rfl⟩
    | default _ => cases hdc

/-- **The reference fallback answers over the selected dataset as over the
whole store** (both collectors). For a SELECT query over a store whose graph
names are IRIs, or a query for which neither collector selects anything, the
SELECT answer of the reference fallback over the query dataset of
`selectedModel q D` is its answer over the query dataset of `D`: the same list
of solution mappings. -/
theorem referenceSelect_selected (env : EvalEnv) (q : Query) (D : Dataset)
    {sel : SelectClause} (hs : q.form = .select sel)
    (hI : QuadDataset.namesAreIris D = true ∨
      (ShardManifest.queryQuadConstantPredicates? q = none ∧
        ShardManifest.queryGraphNames? q = none)) :
    referenceSelect env q (queryDataset q (selectedModel q D))
      = referenceSelect env q (queryDataset q D) := by
  cases hg : ShardManifest.queryGraphNames? q with
  | none =>
      refine referenceSelect_selectedModel env q D hs hg ?_
      rcases hI with h | h
      · exact Or.inl (namesAreIris_queryDataset q h)
      · exact Or.inr h.1
  | some gs =>
      refine referenceSelect_selectedModel_graphs env q D hs hg ?_
      rcases hI with h | h
      · exact h
      · rw [hg] at h; cases h.2

end GraphSelection

/-! ## 6. The model over the dataset denotation -/

theorem selectKeep_key (q : Query) :
    ∀ t u : Triple, t.key = u.key → selectKeep q t = selectKeep q u := by
  intro t u e
  cases h : ShardManifest.queryQuadConstantPredicates? q with
  | some ps => simp only [selectKeep, h]; exact keepPred_key ps t u e
  | none => simp only [selectKeep, h]

/-- The part of a dataset denotation that a triple selection `keep` (which
respects RDF term equality) and a graph selection `gk` keep. -/
def DatasetDen.select (keep : Triple → Bool)
    (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u)
    (gk : Option Subject → Bool) (d : DatasetDen) : DatasetDen where
  graph gn t := gk gn = true ∧ keep t = true ∧ d.graph gn t
  names n := gk (some n) = true ∧ d.names n
  graph_key := by
    intro gn t u e ⟨h1, h2, h3⟩
    exact ⟨h1, (hkey t u e) ▸ h2, d.graph_key gn t u e h3⟩
  named_mem := by
    intro n t ⟨h1, _, h3⟩
    exact ⟨h1, d.named_mem n t h3⟩

theorem mem_filter_iff {keep : Triple → Bool}
    (hkey : ∀ t u : Triple, t.key = u.key → keep t = keep u) (g : Graph) (t : Triple) :
    Graph.mem t (g.filter keep) = true ↔ keep t = true ∧ g.mem t = true := by
  by_cases ht : keep t = true
  · rw [mem_filter_of_keep hkey ht g]
    exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩
  · refine ⟨fun h => ?_, fun h => absurd h.1 ht⟩
    exfalso
    obtain ⟨u, hu, e⟩ := (Graph.mem_iff_key t _).mp h
    have hku : keep u = true := (List.mem_filter.mp hu).2
    exact ht (by rw [← hkey u t e]; exact hku)

/-- **The model over `RDF.DatasetDen`.** A quad is in the denotation of the
selected dataset exactly when its graph is kept, its triple is kept and it is
in the denotation of `D`; a graph name is in it exactly when it is kept and is
a graph name of `D`. -/
theorem den_selectedModel (q : Query) (D : Dataset) :
    (selectedModel q D).den = DatasetDen.select (selectKeep q) (selectKeep_key q) (graphKept q) D.den := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
        show (selectedModel q D).default.mem t = true ↔
          graphKept q none = true ∧ selectKeep q t = true ∧ D.default.mem t = true
        simp only [selectedModel]
        by_cases hgk : graphKept q none = true
        · rw [if_pos hgk, mem_filter_iff (selectKeep_key q)]
          exact ⟨fun h => ⟨hgk, h⟩, fun h => h.2⟩
        · rw [if_neg hgk]
          exact ⟨fun h => by simp [Graph.mem] at h, fun h => absurd h.1 hgk⟩
    | some n =>
        show (∃ ng ∈ (selectedModel q D).named, ng.name = n ∧ ng.graph.mem t = true) ↔
          graphKept q (some n) = true ∧ selectKeep q t = true ∧
            ∃ ng ∈ D.named, ng.name = n ∧ ng.graph.mem t = true
        simp only [selectedModel, List.mem_map, List.mem_filter]
        constructor
        · rintro ⟨_, ⟨ng, ⟨hng, hk⟩, rfl⟩, hn, hm⟩
          rw [mem_filter_iff (selectKeep_key q)] at hm
          exact ⟨hn ▸ hk, hm.1, ng, hng, hn, hm.2⟩
        · rintro ⟨hk, ht, ng, hng, hn, hm⟩
          refine ⟨_, ⟨ng, ⟨hng, hn ▸ hk⟩, rfl⟩, hn, ?_⟩
          exact (mem_filter_iff (selectKeep_key q) _ t).mpr ⟨ht, hm⟩
  · intro n
    show n ∈ (selectedModel q D).names ↔ graphKept q (some n) = true ∧ n ∈ D.names
    simp only [Dataset.names, selectedModel, List.map_map, List.mem_map, List.mem_filter,
      Function.comp_def]
    constructor
    · rintro ⟨ng, ⟨hng, hk⟩, rfl⟩
      exact ⟨hk, ng, hng, rfl⟩
    · rintro ⟨hk, ng, hng, rfl⟩
      exact ⟨ng, ⟨hng, hk⟩, rfl⟩

/-! ## 7. The stage -/

/-- The contract of the reference fallback's SELECT over the model of its read:
for a SELECT query over a store whose graph names are IRIs (or a query for which
neither collector selects anything), the answer is the reference fallback's
answer over the query dataset of the whole store. -/
def FallbackSelectContract (env : EvalEnv) (q : Query) (D : Dataset) (r : SolutionSeq) : Prop :=
  (∃ sel, q.form = .select sel) →
    (QuadDataset.namesAreIris D = true ∨
      (ShardManifest.queryQuadConstantPredicates? q = none ∧
        ShardManifest.queryGraphNames? q = none)) →
    r = referenceSelect env q (queryDataset q D)

/-- The store's dataset (for SBM11, `G.denote`) → the model of the selected
read → the query dataset → the reference fallback's SELECT answer. -/
def fallbackSelectStage (env : EvalEnv) (q : Query) :
    L4Factoidal.Dataflow.Stage String Dataset SolutionSeq :=
  L4Factoidal.Dataflow.Stage.ofFun
    (fun D => referenceSelect env q (queryDataset q (selectedModel q D)))
    (FallbackSelectContract env q)
    (fun D ⟨_, hs⟩ hI => referenceSelect_selected env q D hs hI)

#print axioms namedRestricted_map
#print axioms datasetRestricted_mapRestrict
#print axioms fromMerge_filter
#print axioms applyDataset_mapRestrict
#print axioms referenceSelect_selectedModel
#print axioms evalPatternBackend_active
#print axioms referenceSelect_selectedModel_graphs
#print axioms referenceSelect_selected
#print axioms den_selectedModel
#print axioms fallbackSelectStage

end L4Factoidal.Storage.SelectedDataset
