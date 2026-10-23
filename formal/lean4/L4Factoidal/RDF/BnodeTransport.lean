/-
L4Factoidal.RDF.BnodeTransport — identity transport for blank nodes: a
relabelling of blank nodes that is a bijection on the blank nodes that occur,
its action on datasets and on their denotations, and isomorphism of dataset
denotations (https://github.com/danbri/factoidal/issues/975, phase B3).

RDF 1.1 Concepts section 3.4: "Blank node identifiers are local identifiers
that are used in some concrete RDF syntaxes or RDF store implementations. They
are always locally scoped to the file or RDF store, and are not persistent or
portable identifiers for blank nodes." Section 3.6: two graphs are isomorphic
when a bijection `M` between their nodes maps blank nodes to blank nodes, is
the identity on IRIs and literals, and maps the triples of one onto the
triples of the other. Section 4 (datasets): "Blank nodes can be shared between
graphs in an RDF dataset."

So a component that changes blank-node labels (a document scope, a store that
renumbers blank nodes) must state a transport, not an equality: one mapping of
labels, used everywhere in the dataset (subjects, objects, graph names, and the
blank nodes inside RDF 1.2 triple terms), injective on the blank nodes that
occur. `Dataset.renameBnodes` (`RDF/Graph.lean`) is that action on a dataset;
`Term.renameBnodes` goes into triple terms.

## Definitions

* `BnodeInjOn f S`: `f` is injective on the labels that satisfy `S`.
* `bnodeInvOn f S`: a left inverse of `f` on `S` (classical choice).
* `Dataset.BnodeOccurs ds b`: `b` occurs in `ds` (in a triple of a graph, at
  any depth of triple terms, or as a graph name); `Dataset.mem_bnodes_iff`
  relates it to the list `Dataset.bnodes` of `RDF/Isomorphism.lean`.
* `DatasetDen.rename f d`: the image of the denotation `d` under `f`.
* `DatasetDen.BnodeOccurs d b`: `b` occurs in a triple of `d` or as a graph
  name of `d`.
* `DatasetDen.Iso d e`: there is an `f` injective on the blank nodes of `d`
  with `d.rename f = e`. On the occurring blank nodes `f` is then a bijection
  onto the blank nodes of `e` (`DatasetDen.bnodeOccurs_rename`).

## Theorems

* `Dataset.renameBnodes_isSet`: an injective relabelling keeps `IsSet`.
* `Dataset.den_renameBnodes`: the denotation of the relabelled dataset is the
  image of the denotation (no hypothesis on `f`).
* `Dataset.renameBnodes_invOn`, `Dataset.renameBnodes_invertible`: the
  relabelling is invertible on the dataset, and the inverse is injective on
  the relabelled dataset's blank nodes.
* `DatasetDen.Iso.refl`, `DatasetDen.Iso.symm`, `DatasetDen.Iso.trans`,
  `DatasetDen.iso_equivalence`: isomorphism is an equivalence relation.
* `Dataset.den_iso_renameBnodes`: a dataset and its injective relabelling have
  isomorphic denotations.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.RDF

/-! ## Relabelling of terms -/

theorem Subject.renameBnodes_comp (f g : BNodeId → BNodeId) (s : Subject) :
    (s.renameBnodes f).renameBnodes g = s.renameBnodes (g ∘ f) := by
  cases s <;> rfl

theorem Term.renameBnodes_comp (f g : BNodeId → BNodeId) (t : Term) :
    (t.renameBnodes f).renameBnodes g = t.renameBnodes (g ∘ f) := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm s p o ih => simp only [Term.renameBnodes, Subject.renameBnodes_comp, ih]

theorem Triple.renameBnodes_comp (f g : BNodeId → BNodeId) (t : Triple) :
    (t.renameBnodes f).renameBnodes g = t.renameBnodes (g ∘ f) := by
  simp only [Triple.renameBnodes, Subject.renameBnodes_comp, Term.renameBnodes_comp]

theorem Subject.renameBnodes_congr {f g : BNodeId → BNodeId} {s : Subject}
    (h : ∀ b ∈ s.bnodes, f b = g b) : s.renameBnodes f = s.renameBnodes g := by
  cases s with
  | iri _ => rfl
  | bnode b => simp [Subject.renameBnodes, h b (by simp [Subject.bnodes])]

theorem Term.renameBnodes_congr {f g : BNodeId → BNodeId} {t : Term}
    (h : ∀ b ∈ t.bnodes, f b = g b) : t.renameBnodes f = t.renameBnodes g := by
  induction t with
  | iri _ => rfl
  | bnode b => simp [Term.renameBnodes, h b (by simp [Term.bnodes])]
  | literal _ => rfl
  | tripleTerm s p o ih =>
    simp only [Term.bnodes, List.mem_append] at h
    simp only [Term.renameBnodes, Subject.renameBnodes_congr (fun b hb => h b (.inl hb)),
      ih (fun b hb => h b (.inr hb))]

theorem Triple.renameBnodes_congr {f g : BNodeId → BNodeId} {t : Triple}
    (h : ∀ b ∈ t.bnodes, f b = g b) : t.renameBnodes f = t.renameBnodes g := by
  simp only [Triple.bnodes, List.mem_append] at h
  simp only [Triple.renameBnodes, Subject.renameBnodes_congr (fun b hb => h b (.inl hb)),
    Term.renameBnodes_congr (fun b hb => h b (.inr hb))]

theorem Subject.bnodes_renameBnodes (f : BNodeId → BNodeId) (s : Subject) :
    (s.renameBnodes f).bnodes = s.bnodes.map f := by
  cases s <;> rfl

theorem Term.bnodes_renameBnodes (f : BNodeId → BNodeId) (t : Term) :
    (t.renameBnodes f).bnodes = t.bnodes.map f := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm s p o ih =>
    simp only [Term.renameBnodes, Term.bnodes, Subject.bnodes_renameBnodes, ih, List.map_append]

theorem Triple.bnodes_renameBnodes (f : BNodeId → BNodeId) (t : Triple) :
    (t.renameBnodes f).bnodes = t.bnodes.map f := by
  simp only [Triple.renameBnodes, Triple.bnodes, Subject.bnodes_renameBnodes,
    Term.bnodes_renameBnodes, List.map_append]

/-! ## Relabelling commutes with the key

The key (`Triple.key`, RDF term equality) changes only literals; the
relabelling changes only blank-node labels. -/

theorem Term.joinKey_renameBnodes (f : BNodeId → BNodeId) (t : Term) :
    (t.renameBnodes f).joinKey = t.joinKey.renameBnodes f := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm s p o ih => simp only [Term.renameBnodes, Term.joinKey, ih]

theorem Triple.key_renameBnodes (f : BNodeId → BNodeId) (t : Triple) :
    (t.renameBnodes f).key = t.key.renameBnodes f := by
  simp only [Triple.renameBnodes, Triple.key, Term.joinKey_renameBnodes]

theorem Term.bnodes_joinKey (t : Term) : t.joinKey.bnodes = t.bnodes := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm s p o ih => simp only [Term.joinKey, Term.bnodes, ih]

theorem Triple.bnodes_key (t : Triple) : t.key.bnodes = t.bnodes := by
  simp only [Triple.key, Triple.bnodes, Term.bnodes_joinKey]

/-- Relabelling keeps RDF term equality: equal keys stay equal. -/
theorem Triple.key_renameBnodes_congr (f : BNodeId → BNodeId) {t u : Triple}
    (h : t.key = u.key) : (t.renameBnodes f).key = (u.renameBnodes f).key := by
  rw [Triple.key_renameBnodes, Triple.key_renameBnodes, h]

theorem Subject.renameBnodes_idf (s : Subject) : s.renameBnodes (fun b => b) = s := by
  cases s <;> rfl

theorem Term.renameBnodes_idf (t : Term) : t.renameBnodes (fun b => b) = t := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal _ => rfl
  | tripleTerm s p o ih => simp only [Term.renameBnodes, Subject.renameBnodes_idf, ih]

theorem Triple.renameBnodes_idf (t : Triple) : t.renameBnodes (fun b => b) = t := by
  simp only [Triple.renameBnodes, Subject.renameBnodes_idf, Term.renameBnodes_idf]

/-! ## Injective on a set of labels, and a left inverse -/

/-- `f` is injective on the labels that satisfy `S`. -/
def BnodeInjOn (f : BNodeId → BNodeId) (S : BNodeId → Prop) : Prop :=
  ∀ a b, S a → S b → f a = f b → a = b

open Classical in
/-- A left inverse of `f` on `S`: for `b = f a` with `S a`, an `a` (unique
when `f` is injective on `S`); `b` otherwise. -/
noncomputable def bnodeInvOn (f : BNodeId → BNodeId) (S : BNodeId → Prop) (b : BNodeId) :
    BNodeId :=
  if h : ∃ a, S a ∧ f a = b then Classical.choose h else b

theorem bnodeInvOn_left {f : BNodeId → BNodeId} {S : BNodeId → Prop} (h : BnodeInjOn f S)
    {a : BNodeId} (ha : S a) : bnodeInvOn f S (f a) = a := by
  have hex : ∃ a', S a' ∧ f a' = f a := ⟨a, ha, rfl⟩
  unfold bnodeInvOn
  split
  · next h' =>
    obtain ⟨h1, h2⟩ := Classical.choose_spec h'
    exact h _ _ h1 ha h2
  · next h' => exact absurd hex h'

/-! ## Blank nodes that occur in a dataset -/

/-- `b` occurs in `ds`: in a triple of the default graph, in a triple of a
named graph (at any depth of triple terms), or as a graph name. -/
def Dataset.BnodeOccurs (ds : Dataset) (b : BNodeId) : Prop :=
  (∃ t ∈ ds.default, b ∈ t.bnodes) ∨
    ∃ ng ∈ ds.named, b ∈ ng.name.bnodes ∨ ∃ t ∈ ng.graph, b ∈ t.bnodes

theorem mem_dedupLabels {l : List BNodeId} {b : BNodeId} : b ∈ dedupLabels l ↔ b ∈ l := by
  induction l with
  | nil => simp [dedupLabels]
  | cons x xs ih =>
    simp only [dedupLabels, List.mem_cons]
    split
    · next hc =>
      rw [ih]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact ih.mp (List.contains_iff_mem.mp hc)
        · exact h
    · rw [List.mem_cons, ih]

theorem NamedGraph.nameBnodes_eq (ng : NamedGraph) : ng.nameBnodes = ng.name.bnodes := by
  unfold NamedGraph.nameBnodes
  cases ng.name <;> rfl

theorem Dataset.mem_bnodes_iff {ds : Dataset} {b : BNodeId} : b ∈ ds.bnodes ↔ ds.BnodeOccurs b := by
  simp only [Dataset.bnodes, mem_dedupLabels, List.mem_append, List.mem_flatMap,
    NamedGraph.nameBnodes_eq, Dataset.BnodeOccurs]

theorem Dataset.injectiveOnBnodes_iff {f : BNodeId → BNodeId} {ds : Dataset} :
    ds.InjectiveOnBnodes f ↔ BnodeInjOn f ds.BnodeOccurs := by
  unfold Dataset.InjectiveOnBnodes BnodeInjOn
  simp only [Dataset.mem_bnodes_iff]
  exact ⟨fun h a b ha hb => h a ha b hb, fun h a ha b hb => h a b ha hb⟩

/-! ## Relabelling of datasets -/

theorem Dataset.renameBnodes_default (f : BNodeId → BNodeId) (ds : Dataset) :
    (ds.renameBnodes f).default = ds.default.map (Triple.renameBnodes f) := rfl

theorem Dataset.renameBnodes_named (f : BNodeId → BNodeId) (ds : Dataset) :
    (ds.renameBnodes f).named = ds.named.map (fun ng =>
      { name := ng.name.renameBnodes f, graph := ng.graph.map (Triple.renameBnodes f) }) := rfl

theorem Dataset.renameBnodes_comp (f g : BNodeId → BNodeId) (ds : Dataset) :
    (ds.renameBnodes f).renameBnodes g = ds.renameBnodes (g ∘ f) := by
  simp only [Dataset.renameBnodes, Graph.renameBnodes, List.map_map, Function.comp_def,
    Triple.renameBnodes_comp, Subject.renameBnodes_comp]

theorem Dataset.renameBnodes_congr {f g : BNodeId → BNodeId} {ds : Dataset}
    (h : ∀ b, ds.BnodeOccurs b → f b = g b) : ds.renameBnodes f = ds.renameBnodes g := by
  obtain ⟨dflt, named⟩ := ds
  simp only [Dataset.renameBnodes, Graph.renameBnodes, Dataset.mk.injEq]
  constructor
  · exact List.map_inj_left.mpr fun t ht =>
      Triple.renameBnodes_congr fun b hb => h b (Or.inl ⟨t, ht, hb⟩)
  · refine List.map_inj_left.mpr fun ng hng => ?_
    simp only [NamedGraph.mk.injEq]
    exact ⟨Subject.renameBnodes_congr fun b hb => h b (Or.inr ⟨ng, hng, Or.inl hb⟩),
      List.map_inj_left.mpr fun t ht =>
        Triple.renameBnodes_congr fun b hb => h b (Or.inr ⟨ng, hng, Or.inr ⟨t, ht, hb⟩⟩)⟩

theorem Dataset.renameBnodes_idf (ds : Dataset) : ds.renameBnodes (fun b => b) = ds := by
  obtain ⟨dflt, named⟩ := ds
  have e : (Triple.renameBnodes fun b => b) = fun t => t := funext Triple.renameBnodes_idf
  simp [Dataset.renameBnodes, Graph.renameBnodes, e, Subject.renameBnodes_idf]

/-- The blank nodes of the relabelled dataset are the images of the blank
nodes of the dataset. -/
theorem Dataset.bnodeOccurs_renameBnodes {f : BNodeId → BNodeId} {ds : Dataset} {b : BNodeId} :
    (ds.renameBnodes f).BnodeOccurs b ↔ ∃ a, ds.BnodeOccurs a ∧ f a = b := by
  simp only [Dataset.BnodeOccurs, Dataset.renameBnodes_default, Dataset.renameBnodes_named,
    List.mem_map]
  constructor
  · rintro (⟨_, ⟨t, ht, rfl⟩, hb⟩ | ⟨_, ⟨ng, hng, rfl⟩, hb⟩)
    · rw [Triple.bnodes_renameBnodes, List.mem_map] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, Or.inl ⟨t, ht, ha⟩, rfl⟩
    · rcases hb with hb | ⟨t', ht', hb⟩
      · dsimp only at hb
        rw [Subject.bnodes_renameBnodes, List.mem_map] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        exact ⟨a, Or.inr ⟨ng, hng, Or.inl ha⟩, rfl⟩
      · dsimp only at ht'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
        rw [Triple.bnodes_renameBnodes, List.mem_map] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        exact ⟨a, Or.inr ⟨ng, hng, Or.inr ⟨t, ht, ha⟩⟩, rfl⟩
  · rintro ⟨a, ha | ⟨ng, hng, ha | ⟨t, ht, ha⟩⟩, rfl⟩
    · obtain ⟨t, ht, ha⟩ := ha
      exact Or.inl ⟨_, ⟨t, ht, rfl⟩, by
        rw [Triple.bnodes_renameBnodes]; exact List.mem_map_of_mem ha⟩
    · exact Or.inr ⟨_, ⟨ng, hng, rfl⟩, Or.inl (by
        show f a ∈ (ng.name.renameBnodes f).bnodes
        rw [Subject.bnodes_renameBnodes]; exact List.mem_map_of_mem ha)⟩
    · exact Or.inr ⟨_, ⟨ng, hng, rfl⟩, Or.inr ⟨t.renameBnodes f, List.mem_map_of_mem ht, by
        rw [Triple.bnodes_renameBnodes]; exact List.mem_map_of_mem ha⟩⟩

/-- **Invertible.** A relabelling injective on the blank nodes of `ds` is
undone by its left inverse on them. -/
theorem Dataset.renameBnodes_invOn {f : BNodeId → BNodeId} {ds : Dataset}
    (h : BnodeInjOn f ds.BnodeOccurs) :
    (ds.renameBnodes f).renameBnodes (bnodeInvOn f ds.BnodeOccurs) = ds := by
  rw [Dataset.renameBnodes_comp]
  calc ds.renameBnodes (bnodeInvOn f ds.BnodeOccurs ∘ f)
      = ds.renameBnodes (fun b => b) :=
        Dataset.renameBnodes_congr fun b hb => bnodeInvOn_left h hb
    _ = ds := Dataset.renameBnodes_idf ds

/-- The inverse is injective on the blank nodes of the relabelled dataset. -/
theorem Dataset.invOn_injOn {f : BNodeId → BNodeId} {ds : Dataset}
    (h : BnodeInjOn f ds.BnodeOccurs) :
    BnodeInjOn (bnodeInvOn f ds.BnodeOccurs) (ds.renameBnodes f).BnodeOccurs := by
  intro x y hx hy he
  obtain ⟨a, ha, rfl⟩ := Dataset.bnodeOccurs_renameBnodes.mp hx
  obtain ⟨b, hb, rfl⟩ := Dataset.bnodeOccurs_renameBnodes.mp hy
  rw [bnodeInvOn_left h ha, bnodeInvOn_left h hb] at he
  rw [he]

/-- **Invertible, as an existence statement.** -/
theorem Dataset.renameBnodes_invertible {f : BNodeId → BNodeId} {ds : Dataset}
    (h : ds.InjectiveOnBnodes f) :
    ∃ g : BNodeId → BNodeId, (ds.renameBnodes f).renameBnodes g = ds ∧
      (ds.renameBnodes f).InjectiveOnBnodes g ∧
      ∀ b, (ds.renameBnodes f).BnodeOccurs b → f (g b) = b := by
  have h' := Dataset.injectiveOnBnodes_iff.mp h
  refine ⟨bnodeInvOn f ds.BnodeOccurs, Dataset.renameBnodes_invOn h',
    Dataset.injectiveOnBnodes_iff.mpr (Dataset.invOn_injOn h'), ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Dataset.bnodeOccurs_renameBnodes.mp hb
  rw [bnodeInvOn_left h' ha]

/-! ## A relabelling injective on the blank nodes keeps a set a set -/

/-- `List.Nodup` of an image, from a left inverse on the list. -/
theorem nodup_map_of_leftInv {α β : Type} {f : α → β} {g : β → α} {l : List α}
    (hl : l.Nodup) (h : ∀ x ∈ l, g (f x) = x) : (l.map f).Nodup := by
  have e : (l.map f).map g = l := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id l]
    exact List.map_inj_left.mpr h
  have hl' : ((l.map f).map g).Nodup := by rw [e]; exact hl
  exact List.Pairwise.of_map g (fun a b hne he => hne (by rw [he])) hl'

theorem Graph.KeyNodup.renameBnodes {g : Graph} {f h : BNodeId → BNodeId}
    (hk : g.KeyNodup) (hinv : ∀ t ∈ g, ∀ b ∈ t.bnodes, h (f b) = b) :
    (g.renameBnodes f).KeyNodup := by
  unfold Graph.KeyNodup Graph.renameBnodes
  rw [List.map_map]
  have e : (Triple.key ∘ Triple.renameBnodes f) = (Triple.renameBnodes f ∘ Triple.key) :=
    funext (Triple.key_renameBnodes f)
  rw [e, ← List.map_map]
  apply nodup_map_of_leftInv hk (g := Triple.renameBnodes h)
  intro k hk'
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk'
  rw [Triple.renameBnodes_comp]
  calc t.key.renameBnodes (h ∘ f) = t.key.renameBnodes (fun b => b) :=
        Triple.renameBnodes_congr fun b hb => hinv t ht b (by rw [← Triple.bnodes_key]; exact hb)
    _ = t.key := Triple.renameBnodes_idf _

/-- **A relabelling injective on the blank nodes keeps `IsSet`.** -/
theorem Dataset.renameBnodes_isSet {f : BNodeId → BNodeId} {ds : Dataset} (h : ds.IsSet)
    (hf : BnodeInjOn f ds.BnodeOccurs) : (ds.renameBnodes f).IsSet := by
  have hinv := fun b hb => bnodeInvOn_left (f := f) hf (a := b) hb
  refine ⟨?_, ?_, ?_⟩
  · exact h.default.renameBnodes fun t ht b hb => hinv b (Or.inl ⟨t, ht, hb⟩)
  · have e : (ds.renameBnodes f).names = ds.names.map (Subject.renameBnodes f) := by
      simp only [Dataset.names, Dataset.renameBnodes_named, List.map_map, Function.comp_def]
    rw [e]
    apply nodup_map_of_leftInv h.names (g := Subject.renameBnodes (bnodeInvOn f ds.BnodeOccurs))
    intro n hn
    obtain ⟨ng, hng, rfl⟩ := List.mem_map.mp hn
    rw [Subject.renameBnodes_comp]
    calc ng.name.renameBnodes (bnodeInvOn f ds.BnodeOccurs ∘ f)
        = ng.name.renameBnodes (fun b => b) :=
          Subject.renameBnodes_congr fun b hb => hinv b (Or.inr ⟨ng, hng, Or.inl hb⟩)
      _ = ng.name := Subject.renameBnodes_idf _
  · intro ng hng
    rw [Dataset.renameBnodes_named, List.mem_map] at hng
    obtain ⟨ng0, h0, rfl⟩ := hng
    exact (h.graphs ng0 h0).renameBnodes fun t ht b hb =>
      hinv b (Or.inr ⟨ng0, h0, Or.inr ⟨t, ht, hb⟩⟩)

/-! ## The image of a denotation -/

/-- The image of the denotation `d` under the relabelling `f`: a triple is in
the graph `gn` when it is (by RDF term equality) the image of a triple of `d`
in a graph whose name has the image `gn`. -/
def DatasetDen.rename (f : BNodeId → BNodeId) (d : DatasetDen) : DatasetDen where
  graph gn t := ∃ gn0 u, d.graph gn0 u ∧ gn = gn0.map (Subject.renameBnodes f) ∧
    (u.renameBnodes f).key = t.key
  names n := ∃ n0, d.names n0 ∧ n = n0.renameBnodes f
  graph_key := by
    rintro gn t u h ⟨gn0, v, hv, hg, hk⟩
    exact ⟨gn0, v, hv, hg, hk.trans h⟩
  named_mem := by
    rintro n t ⟨gn0, u, hu, hg, -⟩
    cases gn0 with
    | none => cases hg
    | some n0 => exact ⟨n0, d.named_mem n0 u hu, Option.some.inj hg⟩

/-- The blank nodes of a denotation: in a triple of a graph, or as a graph
name. -/
def DatasetDen.BnodeOccurs (d : DatasetDen) (b : BNodeId) : Prop :=
  (∃ gn t, d.graph gn t ∧ b ∈ t.bnodes) ∨ d.names (.bnode b)

/-- **Isomorphism of dataset denotations** (RDF 1.1 Concepts sections 3.6 and
4): one relabelling, injective on the blank nodes of `d`, carries `d` onto `e`
(all graphs and graph names at once). -/
def DatasetDen.Iso (d e : DatasetDen) : Prop :=
  ∃ f : BNodeId → BNodeId, BnodeInjOn f d.BnodeOccurs ∧ d.rename f = e

theorem DatasetDen.rename_idf (d : DatasetDen) : d.rename (fun b => b) = d := by
  apply DatasetDen.ext
  · intro gn t
    constructor
    · rintro ⟨gn0, u, hu, hg, hk⟩
      have e : gn = gn0 := by
        rw [hg]; cases gn0 <;> simp [Subject.renameBnodes_idf]
      rw [Triple.renameBnodes_idf] at hk
      rw [e]
      exact d.graph_key gn0 u t hk hu
    · intro h
      exact ⟨gn, t, h, by cases gn <;> simp [Subject.renameBnodes_idf], by
        rw [Triple.renameBnodes_idf]⟩
  · intro n
    constructor
    · rintro ⟨n0, hn, rfl⟩
      rw [Subject.renameBnodes_idf]; exact hn
    · intro h; exact ⟨n, h, (Subject.renameBnodes_idf n).symm⟩

theorem DatasetDen.rename_rename (f g : BNodeId → BNodeId) (d : DatasetDen) :
    (d.rename f).rename g = d.rename (g ∘ f) := by
  apply DatasetDen.ext
  · intro gn t
    constructor
    · rintro ⟨gn1, u, ⟨gn0, v, hv, rfl, hk⟩, rfl, hk'⟩
      refine ⟨gn0, v, hv, by cases gn0 <;> simp [Subject.renameBnodes_comp], ?_⟩
      rw [← Triple.renameBnodes_comp, ← hk']
      exact Triple.key_renameBnodes_congr g hk
    · rintro ⟨gn0, v, hv, rfl, hk⟩
      refine ⟨gn0.map (Subject.renameBnodes f), v.renameBnodes f, ⟨gn0, v, hv, rfl, rfl⟩,
        by cases gn0 <;> simp [Subject.renameBnodes_comp], ?_⟩
      rw [Triple.renameBnodes_comp]; exact hk
  · intro n
    constructor
    · rintro ⟨n1, ⟨n0, hn, rfl⟩, rfl⟩
      exact ⟨n0, hn, Subject.renameBnodes_comp f g n0⟩
    · rintro ⟨n0, hn, rfl⟩
      exact ⟨n0.renameBnodes f, ⟨n0, hn, rfl⟩, (Subject.renameBnodes_comp f g n0).symm⟩

theorem DatasetDen.bnodeOccurs_of_name {d : DatasetDen} {n0 : Subject} (hn : d.names n0)
    {b : BNodeId} (hb : b ∈ n0.bnodes) : d.BnodeOccurs b := by
  cases n0 with
  | iri _ => simp [Subject.bnodes] at hb
  | bnode b' =>
    simp only [Subject.bnodes, List.mem_singleton] at hb
    subst hb
    exact Or.inr hn

theorem DatasetDen.rename_sub {f g : BNodeId → BNodeId} {d : DatasetDen}
    (h : ∀ b, d.BnodeOccurs b → f b = g b) :
    ∀ gn t, (d.rename f).graph gn t → (d.rename g).graph gn t := by
  rintro gn t ⟨gn0, u, hu, rfl, hk⟩
  refine ⟨gn0, u, hu, ?_, ?_⟩
  · cases gn0 with
    | none => rfl
    | some n0 =>
      simp only [Option.map_some, Option.some.injEq]
      exact Subject.renameBnodes_congr fun b hb =>
        h b (DatasetDen.bnodeOccurs_of_name (d.named_mem n0 u hu) hb)
  · rw [← hk, Triple.renameBnodes_congr fun b hb => (h b (Or.inl ⟨gn0, u, hu, hb⟩)).symm]

theorem DatasetDen.rename_congr {f g : BNodeId → BNodeId} {d : DatasetDen}
    (h : ∀ b, d.BnodeOccurs b → f b = g b) : d.rename f = d.rename g := by
  apply DatasetDen.ext
  · intro gn t
    exact ⟨DatasetDen.rename_sub h gn t, DatasetDen.rename_sub (fun b hb => (h b hb).symm) gn t⟩
  · intro n
    constructor
    · rintro ⟨n0, hn, rfl⟩
      exact ⟨n0, hn, Subject.renameBnodes_congr fun b hb =>
        h b (DatasetDen.bnodeOccurs_of_name hn hb)⟩
    · rintro ⟨n0, hn, rfl⟩
      exact ⟨n0, hn, Subject.renameBnodes_congr fun b hb =>
        (h b (DatasetDen.bnodeOccurs_of_name hn hb)).symm⟩

/-- The blank nodes of the image are the images of the blank nodes. -/
theorem DatasetDen.bnodeOccurs_rename {f : BNodeId → BNodeId} {d : DatasetDen} {b : BNodeId} :
    (d.rename f).BnodeOccurs b ↔ ∃ a, d.BnodeOccurs a ∧ f a = b := by
  constructor
  · rintro (⟨gn, t, ⟨gn0, u, hu, -, hk⟩, hb⟩ | ⟨n0, hn, he⟩)
    · rw [← Triple.bnodes_key, ← hk, Triple.bnodes_key, Triple.bnodes_renameBnodes,
        List.mem_map] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      exact ⟨a, Or.inl ⟨gn0, u, hu, ha⟩, rfl⟩
    · cases n0 with
      | iri _ => cases he
      | bnode a =>
        simp only [Subject.renameBnodes, Subject.bnode.injEq] at he
        exact ⟨a, Or.inr hn, he.symm⟩
  · rintro ⟨a, ⟨gn0, u, hu, ha⟩ | hn, rfl⟩
    · exact Or.inl ⟨gn0.map (Subject.renameBnodes f), u.renameBnodes f, ⟨gn0, u, hu, rfl, rfl⟩,
        by rw [Triple.bnodes_renameBnodes]; exact List.mem_map_of_mem ha⟩
    · exact Or.inr ⟨.bnode a, hn, rfl⟩

/-! ## Isomorphism is an equivalence relation -/

theorem DatasetDen.Iso.refl (d : DatasetDen) : DatasetDen.Iso d d :=
  ⟨fun b => b, fun _ _ _ _ h => h, DatasetDen.rename_idf d⟩

theorem DatasetDen.Iso.symm {d e : DatasetDen} (h : DatasetDen.Iso d e) : DatasetDen.Iso e d := by
  obtain ⟨f, hf, rfl⟩ := h
  refine ⟨bnodeInvOn f d.BnodeOccurs, ?_, ?_⟩
  · intro x y hx hy he
    obtain ⟨a, ha, rfl⟩ := DatasetDen.bnodeOccurs_rename.mp hx
    obtain ⟨b, hb, rfl⟩ := DatasetDen.bnodeOccurs_rename.mp hy
    rw [bnodeInvOn_left hf ha, bnodeInvOn_left hf hb] at he
    rw [he]
  · rw [DatasetDen.rename_rename]
    calc d.rename (bnodeInvOn f d.BnodeOccurs ∘ f) = d.rename (fun b => b) :=
          DatasetDen.rename_congr fun b hb => bnodeInvOn_left hf hb
      _ = d := DatasetDen.rename_idf d

theorem DatasetDen.Iso.trans {d e k : DatasetDen} (h1 : DatasetDen.Iso d e)
    (h2 : DatasetDen.Iso e k) : DatasetDen.Iso d k := by
  obtain ⟨f, hf, rfl⟩ := h1
  obtain ⟨g, hg, rfl⟩ := h2
  refine ⟨g ∘ f, ?_, (DatasetDen.rename_rename f g d).symm⟩
  intro a b ha hb he
  apply hf a b ha hb
  exact hg (f a) (f b) (DatasetDen.bnodeOccurs_rename.mpr ⟨a, ha, rfl⟩)
    (DatasetDen.bnodeOccurs_rename.mpr ⟨b, hb, rfl⟩) he

/-- **Isomorphism of dataset denotations is an equivalence relation.** -/
theorem DatasetDen.iso_equivalence : Equivalence DatasetDen.Iso :=
  ⟨DatasetDen.Iso.refl, DatasetDen.Iso.symm, DatasetDen.Iso.trans⟩

/-! ## The denotation of a relabelled dataset -/

theorem Dataset.mem_renameBnodes_graph {f : BNodeId → BNodeId} {g : Graph} {t : Triple} :
    Graph.mem t (g.map (Triple.renameBnodes f)) = true ↔ ∃ u, g.mem u = true ∧
      (u.renameBnodes f).key = t.key := by
  rw [Graph.mem_iff_key]
  constructor
  · rintro ⟨_, hv, hk⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact ⟨u, (Graph.mem_iff_key u g).mpr ⟨u, hu, rfl⟩, hk⟩
  · rintro ⟨u, hu, hk⟩
    obtain ⟨w, hw, hwk⟩ := (Graph.mem_iff_key u g).mp hu
    exact ⟨w.renameBnodes f, List.mem_map_of_mem hw,
      (Triple.key_renameBnodes_congr f hwk).trans hk⟩

/-- **The denotation of the relabelled dataset is the image of the
denotation.** No hypothesis on `f`. -/
theorem Dataset.den_renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) :
    (ds.renameBnodes f).den = ds.den.rename f := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show ((ds.renameBnodes f).default.mem t = true) ↔ _
      rw [Dataset.renameBnodes_default, Dataset.mem_renameBnodes_graph]
      constructor
      · rintro ⟨u, hu, hk⟩
        exact ⟨none, u, hu, rfl, hk⟩
      · rintro ⟨gn0, u, hu, hg, hk⟩
        cases gn0 with
        | none => exact ⟨u, hu, hk⟩
        | some _ => cases hg
    | some n =>
      show (∃ ng ∈ (ds.renameBnodes f).named, ng.name = n ∧ ng.graph.mem t = true) ↔ _
      rw [Dataset.renameBnodes_named]
      constructor
      · rintro ⟨_, hng, rfl, hm⟩
        obtain ⟨ng0, h0, rfl⟩ := List.mem_map.mp hng
        obtain ⟨u, hu, hk⟩ := Dataset.mem_renameBnodes_graph.mp hm
        exact ⟨some ng0.name, u, ⟨ng0, h0, rfl, hu⟩, rfl, hk⟩
      · rintro ⟨gn0, u, hu, hg, hk⟩
        cases gn0 with
        | none => cases hg
        | some n0 =>
          obtain ⟨ng0, h0, hn0, hm⟩ := hu
          refine ⟨_, List.mem_map_of_mem h0, ?_, Dataset.mem_renameBnodes_graph.mpr ⟨u, hm, hk⟩⟩
          simp only [Option.map_some, Option.some.injEq] at hg
          rw [hg, hn0]
  · intro n
    show n ∈ (ds.renameBnodes f).names ↔ ∃ n0, n0 ∈ ds.names ∧ n = n0.renameBnodes f
    simp only [Dataset.names, Dataset.renameBnodes_named, List.map_map, List.mem_map,
      Function.comp_def]
    constructor
    · rintro ⟨ng, hng, rfl⟩
      exact ⟨ng.name, ⟨ng, hng, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨ng, hng, rfl⟩, rfl⟩
      exact ⟨ng, hng, rfl⟩

/-- The blank nodes of the denotation of a dataset occur in the dataset. -/
theorem Dataset.bnodeOccurs_of_den {ds : Dataset} {b : BNodeId} (h : ds.den.BnodeOccurs b) :
    ds.BnodeOccurs b := by
  rcases h with ⟨gn, t, ht, hb⟩ | hn
  · cases gn with
    | none =>
      obtain ⟨u, hu, hk⟩ := (Graph.mem_iff_key t ds.default).mp ht
      rw [← Triple.bnodes_key, ← hk, Triple.bnodes_key] at hb
      exact Or.inl ⟨u, hu, hb⟩
    | some n =>
      obtain ⟨ng, hng, -, hm⟩ := ht
      obtain ⟨u, hu, hk⟩ := (Graph.mem_iff_key t ng.graph).mp hm
      rw [← Triple.bnodes_key, ← hk, Triple.bnodes_key] at hb
      exact Or.inr ⟨ng, hng, Or.inr ⟨u, hu, hb⟩⟩
  · obtain ⟨ng, hng, he⟩ := List.mem_map.mp (show Subject.bnode b ∈ ds.names from hn)
    exact Or.inr ⟨ng, hng, Or.inl (by rw [he]; simp [Subject.bnodes])⟩

/-- **Transport.** A dataset and its relabelling by a map injective on its
blank nodes have isomorphic denotations. -/
theorem Dataset.den_iso_renameBnodes {f : BNodeId → BNodeId} {ds : Dataset}
    (h : ds.InjectiveOnBnodes f) : DatasetDen.Iso ds.den (ds.renameBnodes f).den := by
  have h' := Dataset.injectiveOnBnodes_iff.mp h
  exact ⟨f, fun a b ha hb => h' a b (Dataset.bnodeOccurs_of_den ha) (Dataset.bnodeOccurs_of_den hb),
    (Dataset.den_renameBnodes f ds).symm⟩

/-- A map injective on all labels is injective on the blank nodes of every
dataset. -/
theorem Dataset.injectiveOnBnodes_of_injective {f : BNodeId → BNodeId} (hf : Function.Injective f)
    (ds : Dataset) : ds.InjectiveOnBnodes f :=
  fun _ _ _ _ h => hf h

#print axioms Dataset.renameBnodes_isSet
#print axioms Dataset.den_renameBnodes
#print axioms Dataset.renameBnodes_invOn
#print axioms Dataset.renameBnodes_invertible
#print axioms DatasetDen.iso_equivalence
#print axioms Dataset.den_iso_renameBnodes

end L4Factoidal.RDF
