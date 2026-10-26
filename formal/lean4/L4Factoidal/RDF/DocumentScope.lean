/-
L4Factoidal.RDF.DocumentScope — blank nodes scoped per document, and the
combination of separately parsed documents as an RDF merge
(https://github.com/danbri/factoidal/issues/975, phase C, blank nodes).

RDF 1.1 Concepts section 3.4: blank node identifiers "are always locally
scoped to the file or RDF store". So `_:b0` in one document and `_:b0` in
another document are two blank nodes. RDF 1.1 Semantics section 5.2: "If the
graphs in the set have no blank nodes in common, then the union of the graphs
is a merge; if they do share blank nodes, then it is the union of a set of
graphs that is obtained by replacing the graphs in the set by equivalent graphs
that share no blank nodes."

## Scope labels

A document gets a scope number `n` from a fresh-label supply (the Wasm
counter `nextDocumentScope`, the index of a fixture file in the W3C harness).
Each label `b` of the document becomes `docLabel n b = "d<n>_" ++ b`
(`docScope n` is the prefix). `docLabel_inj`: two scoped labels are equal only
when the scope numbers and the labels are equal. So `Dataset.scopeDocument n`
is an injective relabelling (identity transport, `RDF/BnodeTransport.lean`),
and two documents with different scope numbers share no blank node
(`scopeDocument_disjoint`).

## Merge

* `DatasetDen.union`: graph-wise union of two denotations.
* `DatasetDen.IsMerge d1 d2 m`: `m` is the union of denotations isomorphic to
  `d1` and `d2` that share no blank node (section 5.2, for datasets: one
  relabelling per input, over all its graphs and graph names).
* `Dataset.combine`: the dataset of two datasets (lists appended),
  `Dataset.den_combine`: its denotation is the union.
* `scopeDocument_combine_isMerge`: two documents scoped with different scope
  numbers and then combined give a merge of the two parsed datasets.
* Without the scope, `combine` is the union, and a label used in both
  documents is one blank node; the `#guard` lines of `DocumentScopeTests.lean`
  show both cases.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.BnodeTransport

namespace L4Factoidal.RDF

/-! ## Scope labels -/

/-- The label prefix of the document with scope number `n`: `d<n>_`. -/
def docScope (n : Nat) : String := "d" ++ toString n ++ "_"

/-- The label of the blank node `b` of the document with scope number `n`. -/
def docLabel (n : Nat) (b : BNodeId) : BNodeId := docScope n ++ b

#guard docScope 0 = "d0_"
#guard docScope 12 = "d12_"
#guard docLabel 3 "b0" = "d3_b0"

theorem append_cons_inj_of_not_mem {c : Char} :
    ∀ {x y r r' : List Char}, c ∉ x → c ∉ y → x ++ c :: r = y ++ c :: r' → x = y ∧ r = r'
  | [], [], _, _, _, _, h => by simpa using h
  | [], a :: y, _, _, _, hy, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hy
  | a :: x, [], _, _, hx, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1.symm ▸ List.mem_cons_self) hx
  | a :: x, a' :: y, _, _, hx, hy, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨e, h⟩ := h
      obtain ⟨h1, h2⟩ := append_cons_inj_of_not_mem (fun hm => hx (List.mem_cons_of_mem _ hm))
        (fun hm => hy (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [e, h1], h2⟩

theorem toList_toString_nat (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]

/-- **Scoped labels are renamed apart.** -/
theorem docLabel_inj {n m : Nat} {b b' : BNodeId} (h : docLabel n b = docLabel m b') :
    n = m ∧ b = b' := by
  have h1 := congrArg String.toList h
  simp only [docLabel, docScope, String.toList_append, toList_toString_nat] at h1
  have h2 : Nat.toDigits 10 n ++ '_' :: b.toList = Nat.toDigits 10 m ++ '_' :: b'.toList := by
    simpa using h1
  obtain ⟨hd, hb⟩ := append_cons_inj_of_not_mem Nat.underscore_not_in_toDigits
    Nat.underscore_not_in_toDigits h2
  refine ⟨?_, String.toList_inj.mp hb⟩
  rw [← Nat.ofDigitChars_toDigits (b := 10) (n := n) (by decide) (by decide),
    ← Nat.ofDigitChars_toDigits (b := 10) (n := m) (by decide) (by decide), hd]

theorem docLabel_injective (n : Nat) : Function.Injective (docLabel n) :=
  fun _ _ h => (docLabel_inj h).2

/-! ## Scoping a document -/

/-- The dataset of a document with scope number `n`: every blank-node label,
at every position (subjects, objects, graph names, inside triple terms), gets
the prefix `docScope n`. -/
def Dataset.scopeDocument (n : Nat) (ds : Dataset) : Dataset := ds.renameBnodes (docLabel n)

theorem Dataset.scopeDocument_eq_prefix (n : Nat) (ds : Dataset) :
    ds.scopeDocument n = ds.prefixBnodes (docScope n) := rfl

/-- Every blank node of `ds` has the scope `n`. -/
def Dataset.InScope (n : Nat) (ds : Dataset) : Prop :=
  ∀ b, ds.BnodeOccurs b → ∃ b0, b = docLabel n b0

theorem Dataset.scopeDocument_inScope (n : Nat) (ds : Dataset) : (ds.scopeDocument n).InScope n := by
  intro b hb
  obtain ⟨a, -, rfl⟩ := Dataset.bnodeOccurs_renameBnodes.mp hb
  exact ⟨a, rfl⟩

theorem Dataset.scopeDocument_isSet (n : Nat) {ds : Dataset} (h : ds.IsSet) :
    (ds.scopeDocument n).IsSet :=
  Dataset.renameBnodes_isSet h fun _ _ _ _ e => docLabel_injective n e

theorem Dataset.den_iso_scopeDocument (n : Nat) (ds : Dataset) :
    DatasetDen.Iso ds.den (ds.scopeDocument n).den :=
  Dataset.den_iso_renameBnodes (Dataset.injectiveOnBnodes_of_injective (docLabel_injective n) ds)

/-- Datasets in two different scopes share no blank node. -/
theorem Dataset.inScope_disjoint {n m : Nat} (hnm : n ≠ m) {a c : Dataset} (ha : a.InScope n)
    (hc : c.InScope m) {b : BNodeId} (hb : a.BnodeOccurs b) : ¬ c.BnodeOccurs b := by
  intro hb'
  obtain ⟨x, rfl⟩ := ha b hb
  obtain ⟨y, hy⟩ := hc _ hb'
  exact hnm (docLabel_inj hy).1

theorem Dataset.scopeDocument_disjoint {n m : Nat} (hnm : n ≠ m) (a c : Dataset) {b : BNodeId}
    (hb : (a.scopeDocument n).BnodeOccurs b) : ¬ (c.scopeDocument m).BnodeOccurs b :=
  Dataset.inScope_disjoint hnm (a.scopeDocument_inScope n) (c.scopeDocument_inScope m) hb

/-! ## Union and merge of denotations -/

/-- The graph-wise union of two dataset denotations. -/
def DatasetDen.union (d e : DatasetDen) : DatasetDen where
  graph gn t := d.graph gn t ∨ e.graph gn t
  names n := d.names n ∨ e.names n
  graph_key := by
    rintro gn t u h (ht | ht)
    · exact Or.inl (d.graph_key gn t u h ht)
    · exact Or.inr (e.graph_key gn t u h ht)
  named_mem := by
    rintro n t (ht | ht)
    · exact Or.inl (d.named_mem n t ht)
    · exact Or.inr (e.named_mem n t ht)

/-- **RDF 1.1 Semantics section 5.2, for datasets.** `m` is a merge of `d1`
and `d2`: the union of two denotations, isomorphic to `d1` and to `d2`, that
share no blank node. -/
def DatasetDen.IsMerge (d1 d2 m : DatasetDen) : Prop :=
  ∃ e1 e2 : DatasetDen, DatasetDen.Iso d1 e1 ∧ DatasetDen.Iso d2 e2 ∧
    (∀ b, e1.BnodeOccurs b → ¬ e2.BnodeOccurs b) ∧ m = e1.union e2

/-- The dataset of two datasets: the default graphs and the named-graph lists
appended. -/
def Dataset.combine (a c : Dataset) : Dataset :=
  { default := a.default ++ c.default, named := a.named ++ c.named }

/-- The denotation of `combine` is the union of the denotations. -/
theorem Dataset.den_combine (a c : Dataset) : (a.combine c).den = a.den.union c.den := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show Graph.mem t (a.default ++ c.default) = true ↔ _
      rw [Graph.mem_append, Bool.or_eq_true]
      rfl
    | some n =>
      show (∃ ng ∈ a.named ++ c.named, ng.name = n ∧ ng.graph.mem t = true) ↔ _
      simp only [List.mem_append]
      constructor
      · rintro ⟨ng, hng | hng, h⟩
        · exact Or.inl ⟨ng, hng, h⟩
        · exact Or.inr ⟨ng, hng, h⟩
      · rintro (⟨ng, hng, h⟩ | ⟨ng, hng, h⟩)
        · exact ⟨ng, Or.inl hng, h⟩
        · exact ⟨ng, Or.inr hng, h⟩
  · intro n
    show n ∈ (a.named ++ c.named).map (·.name) ↔ n ∈ a.names ∨ n ∈ c.names
    rw [List.map_append, List.mem_append]
    rfl

/-- **Two documents parsed separately and combined give the merge.** With
different scope numbers, `combine` of the scoped datasets denotes an RDF
merge (section 5.2) of the two parsed datasets. -/
theorem scopeDocument_combine_isMerge {n m : Nat} (hnm : n ≠ m) (a c : Dataset) :
    DatasetDen.IsMerge a.den c.den ((a.scopeDocument n).combine (c.scopeDocument m)).den :=
  ⟨_, _, a.den_iso_scopeDocument n, c.den_iso_scopeDocument m,
    fun _ hb hb' => Dataset.scopeDocument_disjoint hnm a c (Dataset.bnodeOccurs_of_den hb)
      (Dataset.bnodeOccurs_of_den hb'),
    Dataset.den_combine _ _⟩

#print axioms docLabel_inj
#print axioms Dataset.scopeDocument_isSet
#print axioms Dataset.den_iso_scopeDocument
#print axioms Dataset.scopeDocument_disjoint
#print axioms Dataset.den_combine
#print axioms scopeDocument_combine_isMerge

end L4Factoidal.RDF
