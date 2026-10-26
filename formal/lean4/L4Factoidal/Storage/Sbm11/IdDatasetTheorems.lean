/-
L4Factoidal.Storage.Sbm11.IdDatasetTheorems — FROM and FROM NAMED on the
SBM11 id path (https://github.com/danbri/factoidal/issues/953, parent
https://github.com/danbri/factoidal/issues/775): the dataset that the id path
reads, against the dataset that the reference evaluator builds
(`SPARQL.applyDataset`, SPARQL 1.1 section 13.2).

## The model

The store's named graphs are a list of (IRI, triples of ids): `named`. The
reference dataset is the same list decoded (`refDataset`: each id triple
decoded by `decT`), with any default graph. The id path reads:

* for the default graph, the graphs that the FROM IRIs name, merged by
  `idUnion` (`idDefault`): a triple is added unless it occurs, the order of
  `Graph.union`;
* for GRAPH, the graphs that the FROM NAMED IRIs name.

## Theorems

* `lookup_decode`: `Dataset.lookupNamedIri` of the reference dataset is the
  decoded graph of the store that the IRI names (none when no graph has that
  name).
* `from_default_decode`: the default graph that `applyDataset` builds from
  FROM clauses is the decoded `idDefault`, when `Triple.eqb` of two decoded
  id triples is equality of the id triples on the triples of the store (the
  hypothesis of `IdJoinTheorems.join_decode`, for triples), and when the FROM
  clauses name at most one graph or their graphs hold no blank node (issue
  979: two or more FROM graphs are relabelled apart by `SPARQL.fromMerge`).
* `from_named_decode`: the named graphs that `applyDataset` keeps are the
  store's graphs that the FROM NAMED IRIs name, decoded, in clause order.
* `mergedRows_eq`: the rows of a triple pattern over the merge are what
  `IdQuery.scanPatM` computes: the rows of the pattern in each graph,
  concatenated, duplicates removed (`idDedup`). Hypothesis: the row of a
  matching triple determines the triple (true of a triple pattern: its
  constants are fixed and its variables give the other positions).

Not proved (open, the step of lemma L5g″ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md): that the scans of
`IdQuery.scanPatM` give `(G.filter q).map f` for each graph `G` and that the
`Table` of `IdJoin.distinctRows` denotes `idDedup` of its rows (tested by the
`#guard`s at the end of this file); that the restriction of `GRAPH ?g` to the
FROM NAMED ids gives the rows of the reference's iteration over the kept named
graphs (the same rows; the order is that of the scan, not that of the
clauses). Tested by the gate queries `tests/sbm11/gate/ids-from-*.rq` and by
the census (`tests/sbm11/census.sh`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdJoin
import L4Factoidal.Storage.Sbm11.OptJoinTheorems
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.Storage.Sbm11.IdDataset

open L4Factoidal.RDF
open L4Factoidal.SPARQL (DatasetClause applyDataset)

/-! ## Set merge over ids -/

/-- `Graph.add` over ids: `t` is appended unless it occurs. -/
def idAdd {α : Type} [BEq α] (acc : List α) (t : α) : List α :=
  if acc.contains t then acc else acc ++ [t]

/-- The first occurrence of each element, in order. -/
def idDedup {α : Type} [BEq α] (L : List α) : List α := L.foldl idAdd []

/-- `Graph.union` over ids. -/
def idUnion {α : Type} [BEq α] (a b : List α) : List α := b.foldl idAdd a

abbrev IdTriple := UInt64 × UInt64 × UInt64

/-- The triples of the store's graph that `i` names. -/
def idGraphOf (named : List (WfIri × List IdTriple)) (i : WfIri) : Option (List IdTriple) :=
  (named.find? (·.1 == i)).map (·.2)

/-- The graphs that the FROM clauses name, in clause order, each IRI once
    (`SPARQL.fromIris`; the id path's `IdQuery.datasetSpec` keeps each FROM
    IRI once). -/
def idDefaults (dcs : List DatasetClause) (named : List (WfIri × List IdTriple)) :
    List (List IdTriple) :=
  (L4Factoidal.SPARQL.fromIris dcs).filterMap (idGraphOf named)

/-- The default graph of the id path under FROM: the merge of the FROM
    graphs. -/
def idDefault (dcs : List DatasetClause) (named : List (WfIri × List IdTriple)) : List IdTriple :=
  (idDefaults dcs named).foldl idUnion []

/-- The reference dataset of the store: its named graphs decoded. -/
def refDataset (decT : IdTriple → Triple) (dflt : Graph) (named : List (WfIri × List IdTriple)) :
    Dataset :=
  { default := dflt, named := named.map fun p => { name := .iri p.1, graph := p.2.map decT } }

/-! ## Lookup -/

theorem lookup_decode (decT : IdTriple → Triple) (dflt : Graph) (named : List (WfIri × List IdTriple))
    (i : WfIri) :
    (refDataset decT dflt named).lookupNamedIri i.val = (idGraphOf named i).map (·.map decT) := by
  unfold Dataset.lookupNamedIri
  rw [dif_pos i.property]
  unfold Dataset.lookupNamed refDataset idGraphOf
  rw [List.find?_map]
  have hp : ((fun ng : NamedGraph => ng.name == Subject.iri ⟨i.val, i.property⟩) ∘
      (fun p : WfIri × List IdTriple => ({ name := .iri p.1, graph := p.2.map decT } : NamedGraph))) =
      (fun p : WfIri × List IdTriple => p.1 == i) := by
    funext p
    simp only [Function.comp_def]
    exact Bool.eq_iff_iff.mpr (by simp [Subtype.ext_iff])
  rw [hp]
  cases named.find? (fun p => p.1 == i) <;> rfl

/-! ## Membership and union -/

theorem mem_foldl_idAdd {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (b a : List α) (x : α), x ∈ b.foldl idAdd a → x ∈ a ∨ x ∈ b := by
  intro b
  induction b with
  | nil => intro a x h; exact Or.inl h
  | cons t ts ih =>
    intro a x h
    rw [List.foldl_cons] at h
    rcases ih (idAdd a t) x h with h1 | h1
    · unfold idAdd at h1
      split at h1
      · exact Or.inl h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by simp at h2; simp [h2])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem mem_decode (decT : IdTriple → Triple) (ok : IdTriple → Prop)
    (hdec : ∀ x y, ok x → ok y → (decT x).eqb (decT y) = (x == y)) (t : IdTriple) (ht : ok t) :
    ∀ (a : List IdTriple), (∀ x ∈ a, ok x) → Graph.mem (decT t) (a.map decT) = a.contains t := by
  intro a
  induction a with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [List.map_cons, Graph.mem, List.contains_cons]
    rw [hdec x t (h x (List.mem_cons_self ..)) ht,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have hs : (x == t) = (t == x) := by
      apply Bool.eq_iff_iff.mpr
      rw [beq_iff_eq, beq_iff_eq]
      exact ⟨Eq.symm, Eq.symm⟩
    rw [hs]

theorem add_decode (decT : IdTriple → Triple) (ok : IdTriple → Prop)
    (hdec : ∀ x y, ok x → ok y → (decT x).eqb (decT y) = (x == y)) (t : IdTriple) (ht : ok t)
    (a : List IdTriple) (ha : ∀ x ∈ a, ok x) :
    (idAdd a t).map decT = Graph.add (decT t) (a.map decT) := by
  unfold idAdd Graph.add
  rw [mem_decode decT ok hdec t ht a ha]
  split <;> simp

/-- `Graph.union` of decoded graphs is the decoded `idUnion`. -/
theorem union_decode (decT : IdTriple → Triple) (ok : IdTriple → Prop)
    (hdec : ∀ x y, ok x → ok y → (decT x).eqb (decT y) = (x == y)) :
    ∀ (b a : List IdTriple), (∀ x ∈ a, ok x) → (∀ x ∈ b, ok x) →
      (idUnion a b).map decT = Graph.union (a.map decT) (b.map decT) := by
  intro b
  induction b with
  | nil => intro a _ _; rfl
  | cons t ts ih =>
    intro a ha hb
    have ht : ok t := hb t (List.mem_cons_self ..)
    have hts : ∀ x ∈ ts, ok x := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have ha' : ∀ x ∈ idAdd a t, ok x := by
      intro x hx
      rcases mem_foldl_idAdd [t] a x (by simpa using hx) with h | h
      · exact ha x h
      · simp at h; rw [h]; exact ht
    unfold idUnion Graph.union at *
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← add_decode decT ok hdec t ht a ha]
    exact ih (idAdd a t) ha' hts

theorem foldl_union_decode (decT : IdTriple → Triple) (ok : IdTriple → Prop)
    (hdec : ∀ x y, ok x → ok y → (decT x).eqb (decT y) = (x == y)) :
    ∀ (Gs : List (List IdTriple)) (acc : List IdTriple), (∀ x ∈ acc, ok x) →
      (∀ G ∈ Gs, ∀ x ∈ G, ok x) →
      (Gs.foldl idUnion acc).map decT = (Gs.map (·.map decT)).foldl Graph.union (acc.map decT) := by
  intro Gs
  induction Gs with
  | nil => intro acc _ _; rfl
  | cons G Gs ih =>
    intro acc hacc hGs
    have hG : ∀ x ∈ G, ok x := hGs G (List.mem_cons_self ..)
    rw [List.foldl_cons, List.map_cons, List.foldl_cons,
      ← union_decode decT ok hdec G acc hacc hG]
    apply ih
    · intro x hx
      rcases mem_foldl_idAdd G acc x hx with h | h
      · exact hacc x h
      · exact hG x h
    · exact fun G' h' => hGs G' (List.mem_cons_of_mem _ h')

/-! ## The dataset of FROM / FROM NAMED -/

theorem mem_idDefaults (dcs : List DatasetClause) (named : List (WfIri × List IdTriple))
    (G : List IdTriple) (h : G ∈ idDefaults dcs named) : ∃ p ∈ named, p.2 = G := by
  unfold idDefaults at h
  rcases List.mem_filterMap.mp h with ⟨i, _, hdc⟩
  simp only [idGraphOf] at hdc
  cases hf : named.find? (fun p => p.1 == i) with
  | none => rw [hf] at hdc; simp at hdc
  | some p =>
    rw [hf] at hdc
    simp at hdc
    exact ⟨p, List.mem_of_find?_eq_some hf, hdc⟩

/-- A relabelling leaves a graph with no blank node unchanged. -/
theorem renameBnodes_ground (f : BNodeId → BNodeId) (G : Graph)
    (h : ∀ t ∈ G, t.bnodes = []) : Graph.renameBnodes f G = G := by
  unfold Graph.renameBnodes
  conv => rhs; rw [← List.map_id G]
  apply List.map_congr_left
  intro t ht
  rw [Triple.renameBnodes_congr (g := fun b => b) (fun b hb => by rw [h t ht] at hb; cases hb),
    Triple.renameBnodes_idf]
  rfl

theorem scopeFromGraphs_ground : ∀ (n : Nat) (Gs : List Graph), (∀ G ∈ Gs, ∀ t ∈ G, t.bnodes = []) →
    L4Factoidal.SPARQL.scopeFromGraphs n Gs = Gs
  | _, [], _ => rfl
  | n, G :: Gs, h => by
    simp only [L4Factoidal.SPARQL.scopeFromGraphs]
    rw [renameBnodes_ground _ G (h G (List.mem_cons_self ..)),
      scopeFromGraphs_ground (n + 1) Gs (fun G' hG' => h G' (List.mem_cons_of_mem _ hG'))]

/-- The default graph that `applyDataset` builds from the FROM clauses
    (SPARQL 1.1 section 13.2.1: the RDF merge of the graphs they name,
    `SPARQL.fromMerge`) is the decoded union of the store's graphs that they
    name, when `Triple.eqb` of decoded triples is equality of the id triples of
    the store, and when the FROM clauses name at most one graph or the graphs
    they name hold no blank node. With two or more graphs and a blank node the
    reference evaluator relabels the graphs apart
    (https://github.com/danbri/factoidal/issues/979) and the id path refuses a
    merged row that holds a blank node (`IdQuery.scanPatM`). -/
theorem from_default_decode (decT : IdTriple → Triple) (ok : IdTriple → Prop)
    (hdec : ∀ x y, ok x → ok y → (decT x).eqb (decT y) = (x == y))
    (dflt active : Graph) (dcs : List DatasetClause) (named : List (WfIri × List IdTriple))
    (hne : dcs ≠ []) (hok : ∀ p ∈ named, ∀ x ∈ p.2, ok x)
    (hground : (idDefaults dcs named).length ≤ 1 ∨
      ∀ G ∈ idDefaults dcs named, ∀ x ∈ G, (decT x).bnodes = []) :
    (applyDataset dcs (refDataset decT dflt named) active).1.default =
      (idDefault dcs named).map decT := by
  have he : dcs.isEmpty = false := by
    cases dcs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  have hlook : (L4Factoidal.SPARQL.fromIris dcs).filterMap
      (fun i => (refDataset decT dflt named).lookupNamedIri i.val) =
      (idDefaults dcs named).map (·.map decT) := by
    unfold idDefaults
    rw [List.map_filterMap]
    apply L4Factoidal.Storage.Sbm11.OptJoin.filterMap_congr'
    intro i _
    simp only [lookup_decode]
  simp only [applyDataset, he, Bool.false_eq_true, if_false]
  rw [hlook, idDefault, foldl_union_decode decT ok hdec (idDefaults dcs named) [] (by simp)]
  · unfold L4Factoidal.SPARQL.fromMerge
    rw [List.length_map]
    split
    · rfl
    · rename_i hlen
      rcases hground with h | h
      · exact absurd h hlen
      · rw [scopeFromGraphs_ground]
        · rfl
        · intro G hG t ht
          obtain ⟨G0, hG0, rfl⟩ := List.mem_map.mp hG
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
          exact h G0 hG0 x hx
  · intro G hG x hx
    rcases mem_idDefaults dcs named G hG with ⟨p, hp, rfl⟩
    exact hok p hp x hx

/-- The named graphs that `applyDataset` keeps for the FROM NAMED clauses
    (SPARQL 1.1 section 13.2.3) are the store's graphs that they name,
    decoded, in clause order; an IRI that names no graph gives none. -/
theorem from_named_decode (decT : IdTriple → Triple) (dflt active : Graph)
    (dcs : List DatasetClause) (named : List (WfIri × List IdTriple)) (hne : dcs ≠ []) :
    (applyDataset dcs (refDataset decT dflt named) active).1.named =
      dcs.filterMap fun
        | .named i => (idGraphOf named i).map fun G => ({ name := .iri i, graph := G.map decT } : NamedGraph)
        | .default _ => none := by
  have he : dcs.isEmpty = false := by
    cases dcs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  simp only [applyDataset, he, Bool.false_eq_true, if_false]
  apply L4Factoidal.Storage.Sbm11.OptJoin.filterMap_congr'
  intro dc _
  cases dc with
  | named i => simp only [lookup_decode, Option.map_map]; rfl
  | default _ => rfl

/-! ## The rows of a pattern over the merge -/

theorem foldl_union_flatten {α : Type} [BEq α] :
    ∀ (Gs : List (List α)) (acc : List α), Gs.foldl idUnion acc = Gs.flatten.foldl idAdd acc := by
  intro Gs
  induction Gs with
  | nil => intro acc; rfl
  | cons G Gs ih =>
    intro acc
    rw [List.foldl_cons, ih, List.flatten_cons, List.foldl_append]
    rfl

theorem contains_filter {α : Type} [BEq α] [LawfulBEq α] (q : α → Bool) (t : α) (hq : q t = true)
    (acc : List α) : (acc.filter q).contains t = acc.contains t := by
  simp [List.mem_filter, hq]

/-- Removing duplicates commutes with a filter. -/
theorem dedup_filter {α : Type} [BEq α] [LawfulBEq α] (q : α → Bool) :
    ∀ (L acc : List α), (L.filter q).foldl idAdd (acc.filter q) = (L.foldl idAdd acc).filter q := by
  intro L
  induction L with
  | nil => intro acc; rfl
  | cons t ts ih =>
    intro acc
    rw [List.foldl_cons, ← ih (idAdd acc t)]
    by_cases hq : q t = true
    · rw [List.filter_cons_of_pos hq, List.foldl_cons]
      congr 1
      unfold idAdd
      rw [contains_filter q t hq acc]
      split
      · rfl
      · rw [List.filter_append]; simp [hq]
    · have hf : q t = false := by simpa using hq
      rw [List.filter_cons_of_neg (by simp [hf])]
      congr 1
      unfold idAdd
      split
      · rfl
      · rw [List.filter_append]; simp [hf]

/-- Removing duplicates commutes with a map that is injective on the
    elements. -/
theorem dedup_map {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β) (S : α → Prop)
    (hinj : ∀ x y, S x → S y → f x = f y → x = y) :
    ∀ (L acc : List α), (∀ x ∈ acc, S x) → (∀ x ∈ L, S x) →
      (L.map f).foldl idAdd (acc.map f) = (L.foldl idAdd acc).map f := by
  intro L
  induction L with
  | nil => intro acc _ _; rfl
  | cons t ts ih =>
    intro acc hacc hL
    have ht : S t := hL t (List.mem_cons_self ..)
    have hc : (acc.map f).contains (f t) = acc.contains t := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨x, hx, hfx⟩
        rw [← hinj x t (hacc x hx) ht hfx]
        exact hx
      · intro h
        exact ⟨t, h, rfl⟩
    have hstep : idAdd (acc.map f) (f t) = (idAdd acc t).map f := by
      unfold idAdd
      rw [hc]
      split
      · rfl
      · simp
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hstep]
    apply ih
    · intro x hx
      rcases mem_foldl_idAdd [t] acc x (by simpa using hx) with h | h
      · exact hacc x h
      · simp at h; rw [h]; exact ht
    · exact fun x hx => hL x (List.mem_cons_of_mem _ hx)

theorem flatMap_filter_map {α β : Type} (q : α → Bool) (f : α → β) :
    ∀ (Gs : List (List α)), Gs.flatMap (fun G => (G.filter q).map f) = (Gs.flatten.filter q).map f := by
  intro Gs
  induction Gs with
  | nil => rfl
  | cons G Gs ih =>
    rw [List.flatMap_cons, ih, List.flatten_cons, List.filter_append, List.map_append]

/-- The rows of a triple pattern over the merge of the graphs `Gs`
    (`idUnion`, the default graph of FROM): the rows of the pattern in each
    graph, concatenated, with duplicates removed (`IdQuery.scanPatM`). `q`:
    the triple matches the pattern; `f`: its row; on matching triples the row
    determines the triple. -/
theorem mergedRows_eq {β : Type} [BEq β] [LawfulBEq β] (q : IdTriple → Bool) (f : IdTriple → β)
    (hinj : ∀ x y, q x = true → q y = true → f x = f y → x = y) (Gs : List (List IdTriple)) :
    idDedup (Gs.flatMap fun G => (G.filter q).map f) = ((Gs.foldl idUnion []).filter q).map f := by
  unfold idDedup
  rw [flatMap_filter_map, foldl_union_flatten]
  have h0 : ([] : List β) = ([] : List IdTriple).map f := rfl
  rw [h0, dedup_map f (fun x => q x = true) hinj (Gs.flatten.filter q) [] (by simp)
    (fun x hx => (List.mem_filter.mp hx).2)]
  congr 1
  exact dedup_filter q Gs.flatten []

/-! ## The `Table` implementation on samples

`IdJoin.distinctRows` and `IdJoin.keepVars` against `idDedup` over the rows
of sample tables: duplicates across the parts of a concatenation, a table
with no column, an empty table. -/

open L4Factoidal.Qlvr (Table)

private def col (xs : List Nat) : ByteArray :=
  xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length }

private def rowsOf (t : Table) : List (List UInt64) :=
  (List.range t.rows).map fun i => (List.range t.vars.size).map fun c => t.at c i

private def T1 : Table := tab #["s", "o"] [[1, 2, 1, 3], [7, 8, 7, 9]]
private def T2 : Table := tab #["s", "o"] [[3, 1, 4], [9, 7, 4]]

#guard rowsOf (IdJoin.distinctRows (T1.append T2)) == idDedup (rowsOf T1 ++ rowsOf T2)
#guard (IdJoin.distinctRows (T1.append T2)).rows == 4
#guard rowsOf (IdJoin.distinctRows (tab #[] [])) == []
#guard (IdJoin.distinctRows { vars := #[], cols := #[], rows := 3 }).rows == 1
#guard (IdJoin.distinctRows (tab #["s"] [[]])).rows == 0
-- the projection after the merge keeps one row per triple
#guard rowsOf (IdJoin.keepVars (IdJoin.distinctRows (T1.append T2)) (· == "s")) == [[1], [2], [3], [4]].map (·.map Nat.toUInt64)
#guard (IdJoin.keepVars T1 (· == "o")).vars == #["o"] && (IdJoin.keepVars T1 (fun _ => false)).rows == 4

end L4Factoidal.Storage.Sbm11.IdDataset
