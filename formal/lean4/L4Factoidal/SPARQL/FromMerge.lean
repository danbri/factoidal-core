/-
L4Factoidal.SPARQL.FromMerge — the default graph of FROM is an RDF merge
(https://github.com/danbri/factoidal/issues/979; parent
https://github.com/danbri/factoidal/issues/975).

SPARQL 1.1 Query section 13.2.1: "If a query provides more than one FROM
clause, providing more than one IRI to indicate the default graph, then the
default graph is the RDF merge of the graphs obtained from representations of
the resources identified by the given IRIs." RDF 1.1 Semantics section 5.2
defines the merge of a set of graphs.

## Definitions

* `graphDen g`: the denotation of the graph `g` (the dataset with default graph
  `g` and no named graph, `Dataset.den`).
* `DatasetDen.emptyDen`: the denotation with no triple and no graph name.
* `IsMergeOf ds m`: `m` is a merge of the list of denotations `ds`: the union
  of a list of denotations, isomorphic one by one to `ds`, that share no blank
  node two by two (RDF 1.1 Semantics section 5.2, for a list of any length).
  `isMergeOf_pair`: for two denotations this is `DatasetDen.IsMerge`
  (`RDF/DocumentScope.lean`).

## Theorems

* `mem_union`, `mem_foldl_union`: membership in `Graph.union`.
* `graphDen_foldl_union`: the denotation of the union of a list of graphs is
  the union of their denotations.
* `fromMerge_isMergeOf`: `fromMerge gs` denotes a merge of the graphs `gs`.
* `applyDataset_default_isMergeOf`: with a dataset clause, the default graph
  that `applyDataset` builds denotes a merge of the denotations of the FROM
  graphs (`fromIris`, looked up in the dataset), and it is the active graph.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.FromMerge

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Membership in a union -/

theorem mem_union (u : Triple) : ∀ (b a : Graph),
    (Graph.union a b).mem u = true ↔ a.mem u = true ∨ b.mem u = true := by
  intro b
  induction b with
  | nil => intro a; simp [Graph.union, Graph.mem]
  | cons t ts ih =>
    intro a
    have h : Graph.union a (t :: ts) = Graph.union (a.add t) ts := rfl
    rw [h, ih, Graph.mem_add_iff]
    have ht : (Graph.mem u (t :: ts) = true) ↔ (u.key = t.key ∨ Graph.mem u ts = true) := by
      simp only [Graph.mem, Bool.or_eq_true, Triple.eqb_iff_key]
      exact ⟨fun h => h.elim (fun e => Or.inl e.symm) Or.inr,
        fun h => h.elim (fun e => Or.inl e.symm) Or.inr⟩
    rw [ht]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem mem_foldl_union (u : Triple) : ∀ (gs : List Graph) (acc : Graph),
    Graph.mem u (gs.foldl Graph.union acc) = true ↔ Graph.mem u acc = true ∨
      ∃ g ∈ gs, Graph.mem u g = true := by
  intro gs
  induction gs with
  | nil => intro acc; simp
  | cons g gs ih =>
    intro acc
    rw [List.foldl_cons, ih, mem_union]
    constructor
    · rintro ((h | h) | ⟨g', hg', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨g, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨g', List.mem_cons_of_mem _ hg', h⟩
    · rintro (h | ⟨g', hg', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.mp hg' with rfl | hg'
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨g', hg', h⟩

/-! ## Denotations of graphs -/

/-- The denotation of a graph: the dataset with that default graph and no
named graph. -/
def graphDen (g : Graph) : DatasetDen := ({ default := g, named := [] } : Dataset).den

/-- The denotation with no triple and no graph name. -/
def emptyDen : DatasetDen where
  graph _ _ := False
  names _ := False
  graph_key := fun _ _ _ _ h => h
  named_mem := fun _ _ h => h

theorem graphDen_graph_none (g : Graph) (t : Triple) : (graphDen g).graph none t ↔ g.mem t = true :=
  Iff.rfl

theorem graphDen_graph_some (g : Graph) (n : Subject) (t : Triple) : ¬ (graphDen g).graph (some n) t := by
  rintro ⟨ng, hng, -⟩
  cases hng

theorem graphDen_names (g : Graph) (n : Subject) : ¬ (graphDen g).names n := by
  intro h
  cases h

theorem foldr_union_graph (es : List DatasetDen) (gn : Option Subject) (t : Triple) :
    (es.foldr DatasetDen.union emptyDen).graph gn t ↔ ∃ e ∈ es, e.graph gn t := by
  induction es with
  | nil => exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => by cases h⟩
  | cons e es ih =>
    show e.graph gn t ∨ (es.foldr DatasetDen.union emptyDen).graph gn t ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem foldr_union_names (es : List DatasetDen) (n : Subject) :
    (es.foldr DatasetDen.union emptyDen).names n ↔ ∃ e ∈ es, e.names n := by
  induction es with
  | nil => exact ⟨fun h => h.elim, fun ⟨_, h, _⟩ => by cases h⟩
  | cons e es ih =>
    show e.names n ∨ (es.foldr DatasetDen.union emptyDen).names n ↔ _
    rw [ih]
    simp only [List.mem_cons, exists_eq_or_imp]

/-- **The denotation of the union of graphs is the union of their
denotations.** -/
theorem graphDen_foldl_union (gs : List Graph) :
    graphDen (gs.foldl Graph.union Graph.empty) = (gs.map graphDen).foldr DatasetDen.union emptyDen := by
  apply DatasetDen.ext
  · intro gn t
    rw [foldr_union_graph]
    cases gn with
    | none =>
      rw [graphDen_graph_none, mem_foldl_union]
      simp only [Graph.empty, Graph.mem, Bool.false_eq_true, false_or, List.mem_map]
      constructor
      · rintro ⟨g, hg, h⟩
        exact ⟨graphDen g, ⟨g, hg, rfl⟩, h⟩
      · rintro ⟨_, ⟨g, hg, rfl⟩, h⟩
        exact ⟨g, hg, h⟩
    | some n =>
      constructor
      · intro h; exact absurd h (graphDen_graph_some _ n t)
      · rintro ⟨_, he, h⟩
        obtain ⟨g, -, rfl⟩ := List.mem_map.mp he
        exact absurd h (graphDen_graph_some g n t)
  · intro n
    rw [foldr_union_names]
    constructor
    · intro h; exact absurd h (graphDen_names _ n)
    · rintro ⟨_, he, h⟩
      obtain ⟨g, -, rfl⟩ := List.mem_map.mp he
      exact absurd h (graphDen_names g n)

/-! ## Merge of a list -/

/-- Two lists of denotations, isomorphic one by one. -/
inductive IsoList : List DatasetDen → List DatasetDen → Prop
  | nil : IsoList [] []
  | cons {d e : DatasetDen} {ds es : List DatasetDen} :
      DatasetDen.Iso d e → IsoList ds es → IsoList (d :: ds) (e :: es)

theorem IsoList.refl : ∀ (ds : List DatasetDen), IsoList ds ds
  | [] => .nil
  | d :: ds => .cons (DatasetDen.Iso.refl d) (IsoList.refl ds)

/-- **RDF 1.1 Semantics section 5.2, for a list.** `m` is a merge of `ds`:
the union of denotations isomorphic one by one to `ds` (`IsoList`) that share
no blank node two by two. -/
def IsMergeOf (ds : List DatasetDen) (m : DatasetDen) : Prop :=
  ∃ es : List DatasetDen, IsoList ds es ∧
    es.Pairwise (fun e1 e2 => ∀ b, e1.BnodeOccurs b → ¬ e2.BnodeOccurs b) ∧
    m = es.foldr DatasetDen.union emptyDen

theorem union_emptyDen (e : DatasetDen) : e.union emptyDen = e := by
  apply DatasetDen.ext
  · intro gn t
    show e.graph gn t ∨ False ↔ _
    rw [or_false]
  · intro n
    show e.names n ∨ False ↔ _
    rw [or_false]

/-- For two denotations, `IsMergeOf` is `DatasetDen.IsMerge`. -/
theorem isMergeOf_pair (d1 d2 m : DatasetDen) : IsMergeOf [d1, d2] m ↔ DatasetDen.IsMerge d1 d2 m := by
  constructor
  · rintro ⟨es, h2, hp, rfl⟩
    obtain _ | @⟨_, e1, _, es', h1, h2'⟩ := h2
    obtain _ | @⟨_, e2, _, es'', he2, hnil⟩ := h2'
    cases hnil
    refine ⟨e1, e2, h1, he2, ?_, ?_⟩
    · exact (List.pairwise_cons.mp hp).1 e2 (List.mem_singleton_self _)
    · show e1.union (e2.union emptyDen) = e1.union e2
      rw [union_emptyDen]
  · rintro ⟨e1, e2, h1, h2, hd, rfl⟩
    refine ⟨[e1, e2], .cons h1 (.cons h2 .nil), ?_, ?_⟩
    · exact List.pairwise_cons.mpr ⟨fun e he => by
        rw [List.mem_singleton] at he; subst he; exact hd, List.pairwise_singleton _ _⟩
    · show e1.union e2 = e1.union (e2.union emptyDen)
      rw [union_emptyDen]

/-! ## The FROM graphs -/

theorem graphDen_iso_scoped (n : Nat) (g : Graph) :
    DatasetDen.Iso (graphDen g) (graphDen (Graph.renameBnodes (docLabel n) g)) :=
  Dataset.den_iso_scopeDocument n { default := g, named := [] }

theorem graphDen_scoped_disjoint {n m : Nat} (hnm : n ≠ m) (g h : Graph) (b : BNodeId)
    (hb : (graphDen (Graph.renameBnodes (docLabel n) g)).BnodeOccurs b) :
    ¬ (graphDen (Graph.renameBnodes (docLabel m) h)).BnodeOccurs b := fun hb' =>
  Dataset.scopeDocument_disjoint hnm { default := g, named := [] } { default := h, named := [] }
    (Dataset.bnodeOccurs_of_den hb) (Dataset.bnodeOccurs_of_den hb')

theorem mem_scopeFromGraphs : ∀ (n : Nat) (gs : List Graph) (x : Graph),
    x ∈ scopeFromGraphs n gs → ∃ g k, n ≤ k ∧ x = Graph.renameBnodes (docLabel k) g
  | _, [], _, h => by cases h
  | n, g :: gs, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨g, n, Nat.le_refl n, rfl⟩
    · obtain ⟨g', k, hk, rfl⟩ := mem_scopeFromGraphs (n + 1) gs x h
      exact ⟨g', k, Nat.le_of_succ_le hk, rfl⟩

theorem forall₂_scopeFromGraphs : ∀ (n : Nat) (gs : List Graph),
    IsoList (gs.map graphDen) ((scopeFromGraphs n gs).map graphDen)
  | _, [] => .nil
  | n, g :: gs => .cons (graphDen_iso_scoped n g) (forall₂_scopeFromGraphs (n + 1) gs)

theorem pairwise_scopeFromGraphs : ∀ (n : Nat) (gs : List Graph),
    ((scopeFromGraphs n gs).map graphDen).Pairwise
      (fun e1 e2 => ∀ b, e1.BnodeOccurs b → ¬ e2.BnodeOccurs b)
  | _, [] => List.Pairwise.nil
  | n, g :: gs => by
    refine List.pairwise_cons.mpr ⟨?_, pairwise_scopeFromGraphs (n + 1) gs⟩
    intro e he b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨g', k, hk, rfl⟩ := mem_scopeFromGraphs (n + 1) gs x hx
    exact graphDen_scoped_disjoint (Nat.ne_of_lt hk) g g' b hb

/-- **`fromMerge` is an RDF merge** (RDF 1.1 Semantics section 5.2) of the
graphs it is given. -/
theorem fromMerge_isMergeOf (gs : List Graph) : IsMergeOf (gs.map graphDen) (graphDen (fromMerge gs)) := by
  unfold fromMerge
  split
  · rename_i hlen
    refine ⟨gs.map graphDen, ?_, ?_, graphDen_foldl_union gs⟩
    · exact IsoList.refl _
    · match gs, hlen with
      | [], _ => exact List.Pairwise.nil
      | [_], _ => exact List.pairwise_singleton _ _
  · exact ⟨_, forall₂_scopeFromGraphs 0 gs, pairwise_scopeFromGraphs 0 gs,
      graphDen_foldl_union _⟩

/-- **SPARQL 1.1 Query section 13.2.1.** With a dataset clause, the default
graph that `applyDataset` builds denotes an RDF merge of the denotations of the
graphs that the FROM clauses name (each IRI once, in clause order, looked up in
the dataset), and it is the active graph of the query. -/
theorem applyDataset_default_isMergeOf (dcs : List DatasetClause) (ds : Dataset) (active : Graph)
    (h : dcs ≠ []) :
    IsMergeOf (((fromIris dcs).filterMap (fun i => ds.lookupNamedIri i.val)).map graphDen)
        (graphDen (applyDataset dcs ds active).1.default) ∧
      (applyDataset dcs ds active).2 = (applyDataset dcs ds active).1.default := by
  have he : dcs.isEmpty = false := by
    cases dcs with
    | nil => exact absurd rfl h
    | cons _ _ => rfl
  simp only [applyDataset, he, Bool.false_eq_true, if_false]
  exact ⟨fromMerge_isMergeOf _, by first | trivial | rfl⟩

#print axioms mem_foldl_union
#print axioms graphDen_foldl_union
#print axioms isMergeOf_pair
#print axioms fromMerge_isMergeOf
#print axioms applyDataset_default_isMergeOf

/-! ## Tests (issue 979)

Two FROM graphs that both use `_:b0`: the join on the shared label must not
match across the graphs; the control holds both triples in one graph. -/

private def exI (s : String) : WfIri := if h : isIri s = true then ⟨s, h⟩ else ⟨"http://ex.org/x", by decide⟩
private def tP : Triple := { s := .bnode "b0", p := exI "http://ex.org/p", o := .iri (exI "http://ex.org/o") }
private def tQ : Triple := { s := .bnode "b0", p := exI "http://ex.org/q", o := .iri (exI "http://ex.org/o") }
private def g1 : Graph := [tP]
private def g2 : Graph := [tQ]

-- two graphs: two blank nodes
#guard (fromMerge [g1, g2]).length == 2
#guard ((fromMerge [g1, g2]).map (·.s)) == [.bnode "d0_b0", .bnode "d1_b0"]
-- one graph: the store's labels
#guard fromMerge [g1 ++ g2] == [tP, tQ]
-- the same IRI twice names one graph
#guard (fromIris [.default (exI "http://ex.org/g1"), .named (exI "http://ex.org/g2"),
    .default (exI "http://ex.org/g1"), .default (exI "http://ex.org/g2")]).map (·.val) ==
  ["http://ex.org/g1", "http://ex.org/g2"]

end L4Factoidal.SPARQL.FromMerge
