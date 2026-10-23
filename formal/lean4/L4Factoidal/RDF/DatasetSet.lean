/-
L4Factoidal.RDF.DatasetSet — the set of quads of a parsed document.

RDF 1.1 Concepts and Abstract Syntax, section 3: "An RDF graph is a set of RDF
triples." Section 4: "An RDF dataset is a collection of RDF graphs" — one
default graph and zero or more named graphs, each a pair of a graph name and a
graph, with the graph names unique in the dataset. A `Graph` here is a
`List Triple`, so the representation can hold a triple two times. The N-Quads
reader and the TriG reader add each quad with `addQuad` (set semantics by
`Triple.eqb`, named graphs of one name merged), and so give a set. The
N-Triples, Turtle, RDF/XML and JSON-LD readers put every triple they read in
the list, so a document that states a triple two times gave a graph with two
list entries: `datasetOpen` counted 2, `COUNT(*)` answered 2 and the writers
wrote the triple two times.

`Dataset.toSet` gives the set. It adds every quad of the dataset, in the order
of the list (the default graph, then each named graph), with `addQuad`, and
declares every named graph with `ensureNamed`, so an empty named graph stays.
The first occurrence of a triple fixes its place in the result. The equality
is `Triple.eqb`, the equality of the N-Quads reader: language tags compare
without case (RDF 1.1 Concepts section 3.3, "The value space of language tags
is always in lower case") and `rdf:XMLLiteral` lexical forms compare in their
canonical form. The compiler runs `Dataset.toSetFast`, the same steps on the
hash-indexed accumulator of `parseNQuadsFast` (`FastDataset`); it takes time
linear in the number of quads, where `addQuad` scans the graph
(`Dataset.toSet_eq_fast`).

What is proved, for every dataset `ds`:

* `Dataset.toSet_isSet`: the result is a set (`Dataset.IsSet`): the keys
  (`Triple.key`, equal exactly when the triples are `Triple.eqb`-equal) of the
  default graph have no duplicate, the graph names have no duplicate, and the
  keys of each named graph have no duplicate. `Graph.KeyNodup.nodup` gives
  `List.Nodup` from it, and `Graph.KeyNodup.pairwise` that no two triples of
  the list are `Triple.eqb`-equal.
* `Dataset.memQuad_toSet`: a triple is in a graph of the result exactly when it
  is in that graph of `ds` (engine membership, `Graph.mem`).
* `Dataset.names_toSet`: the result names exactly the graphs `ds` names.
* `Dataset.listQuad_toSet`: every list entry of the result is a list entry of
  `ds`, in the graph of the same name: nothing is made up.

`parseNQuadsFast_isSet` and `parseTriG_isSet` prove that the two readers that
already add with `addQuad` give a set, so the source layer
(`RDF/Source.lean`) does not run `toSet` over their output.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.TriG
import L4Factoidal.RDF.GraphIndex

namespace L4Factoidal.RDF

open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## Graphs: keys without duplicates -/

/-- No two triples of the list have the same key, so no two are
`Triple.eqb`-equal. -/
def Graph.KeyNodup (g : Graph) : Prop := (g.map Triple.key).Nodup

theorem Graph.mem_iff_keys (t : Triple) (g : Graph) :
    g.mem t = true ↔ t.key ∈ g.map Triple.key := by
  rw [Graph.mem_iff_key, List.mem_map]

theorem Graph.KeyNodup.nodup {g : Graph} (h : g.KeyNodup) : g.Nodup :=
  List.Pairwise.of_map Triple.key (fun _ _ hne he => hne (he ▸ rfl)) h

theorem Graph.KeyNodup.pairwise {g : Graph} (h : g.KeyNodup) :
    g.Pairwise (fun a b => a.eqb b = false) := by
  have hp := List.pairwise_map.mp h
  refine hp.imp ?_
  intro a b hne
  cases hb : a.eqb b
  · rfl
  · exact absurd ((Triple.eqb_iff_key a b).mp hb) hne

theorem Graph.keys_add (t : Triple) (g : Graph) :
    (g.add t).map Triple.key =
      if t.key ∈ g.map Triple.key then g.map Triple.key else g.map Triple.key ++ [t.key] := by
  unfold Graph.add
  by_cases h : g.mem t = true
  · rw [if_pos h, if_pos ((Graph.mem_iff_keys t g).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((Graph.mem_iff_keys t g).mpr h'))]
    simp

theorem Graph.KeyNodup.add {g : Graph} (t : Triple) (h : g.KeyNodup) : (g.add t).KeyNodup := by
  unfold Graph.KeyNodup
  rw [Graph.keys_add]
  split
  · exact h
  · next hn =>
    rw [List.nodup_append]
    refine ⟨h, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    intro e
    exact hn (e ▸ ha)

theorem Graph.mem_add_iff (u t : Triple) (g : Graph) :
    (g.add t).mem u = true ↔ g.mem u = true ∨ u.key = t.key := by
  rw [Graph.mem_iff_keys, Graph.keys_add, Graph.mem_iff_keys]
  split
  · next h =>
    constructor
    · exact Or.inl
    · rintro (h' | h')
      · exact h'
      · rw [h']; exact h
  · simp [List.mem_append]

theorem Graph.keyNodup_nil : Graph.KeyNodup [] := List.nodup_nil

theorem Graph.keyNodup_single (t : Triple) : Graph.KeyNodup [t] := List.pairwise_singleton _ _

theorem Graph.mem_single_iff (u t : Triple) : Graph.mem u [t] = true ↔ u.key = t.key := by
  rw [Graph.mem_iff_keys]; simp

/-! ## Datasets: the set conditions -/

/-- The graph names of a dataset, in list order. -/
def Dataset.names (ds : Dataset) : List Subject := ds.named.map (·.name)

/-- A dataset that is a set of quads: no duplicate key in the default graph, no
duplicate graph name, no duplicate key in a named graph. -/
structure Dataset.IsSet (ds : Dataset) : Prop where
  default : ds.default.KeyNodup
  names : ds.names.Nodup
  graphs : ∀ ng ∈ ds.named, ng.graph.KeyNodup

/-- Engine membership of a triple in the default graph (`none`) or in the
named graph of a name. -/
def Dataset.memQuad (ds : Dataset) (u : Triple) : Option Subject → Prop
  | none => ds.default.mem u = true
  | some n => ∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem u = true

/-- List membership of a triple in the default graph (`none`) or in a named
graph of a name. -/
def Dataset.listQuad (ds : Dataset) (u : Triple) : Option Subject → Prop
  | none => u ∈ ds.default
  | some n => ∃ ng ∈ ds.named, ng.name = n ∧ u ∈ ng.graph

theorem Dataset.isSet_empty : Dataset.empty.IsSet :=
  ⟨Graph.keyNodup_nil, List.nodup_nil, fun _ h => by simp [Dataset.empty] at h⟩

/-- Two entries of a list whose images have no duplicate, with one image, are
one entry. -/
private theorem eq_of_nodup_map {α β : Type} (f : α → β) :
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
      · exact eq_of_nodup_map f h.2 ha' hb' hf

/-! ## One step: `addQuad` and `ensureNamed` -/

section Step

variable (n : Subject) (U : NamedGraph)

/-- The named-graph update `addQuad` makes when the graph `n` is there. -/
private def upd (ng' : NamedGraph) : NamedGraph := if ng'.name == n then U else ng'

private theorem upd_name (hU : U.name = n) (ng' : NamedGraph) : (upd n U ng').name = ng'.name := by
  unfold upd
  split
  · next h => rw [hU]; exact (eq_of_beq h).symm
  · rfl

private theorem names_upd (hU : U.name = n) (l : List NamedGraph) :
    (l.map (upd n U)).map (·.name) = l.map (·.name) := by
  rw [List.map_map]
  exact List.map_congr_left (fun ng' _ => upd_name n U hU ng')

end Step

theorem addQuad_default (ds : Dataset) (t : Triple) :
    addQuad ds t none = { ds with default := ds.default.add t } := rfl

/-- `addQuad` keeps a set a set. -/
theorem addQuad_isSet {ds : Dataset} (t : Triple) (g : Option Subject) (h : ds.IsSet) :
    (addQuad ds t g).IsSet := by
  cases g with
  | none => exact ⟨h.default.add t, h.names, h.graphs⟩
  | some n =>
    simp only [addQuad]
    split
    · next ng hf =>
      have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
      refine ⟨h.default, ?_, ?_⟩
      · show ((ds.named.map (upd n { name := n, graph := ng.graph.add t })).map (·.name)).Nodup
        rw [names_upd n _ rfl]; exact h.names
      · intro x hx
        obtain ⟨ng', hng', rfl⟩ := List.mem_map.mp hx
        show (upd n { name := n, graph := ng.graph.add t } ng').graph.KeyNodup
        unfold upd
        split
        · exact (h.graphs ng hng).add t
        · exact h.graphs ng' hng'
    · next hf =>
      have hnot : n ∉ ds.names := by
        intro hc
        obtain ⟨ng', hng', he⟩ := List.mem_map.mp hc
        have := List.find?_eq_none.mp hf ng' hng'
        simp [he] at this
      refine ⟨h.default, ?_, ?_⟩
      · show ((ds.named ++ [({ name := n, graph := [t] } : NamedGraph)]).map (·.name)).Nodup
        rw [List.map_append, List.nodup_append]
        refine ⟨h.names, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        intro e; exact hnot (e ▸ ha)
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h.graphs x hx
        · rw [List.mem_singleton] at hx; subst hx; exact Graph.keyNodup_single t

/-- The names after `addQuad`. -/
theorem addQuad_names (ds : Dataset) (t : Triple) (g : Option Subject) (m : Subject) :
    m ∈ (addQuad ds t g).names ↔ m ∈ ds.names ∨ g = some m := by
  cases g with
  | none => simp [addQuad, Dataset.names]
  | some n =>
    simp only [addQuad]
    split
    · next ng hf =>
      have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
      have hn : ng.name = n := by
        have hb := List.find?_some hf; simpa using hb
      show m ∈ (ds.named.map (upd n { name := n, graph := ng.graph.add t })).map (·.name) ↔ _
      rw [names_upd n _ rfl]
      constructor
      · exact Or.inl
      · rintro (h' | h')
        · exact h'
        · cases h'; exact List.mem_map.mpr ⟨ng, hng, hn⟩
    · show m ∈ (ds.named ++ [({ name := n, graph := [t] } : NamedGraph)]).map (·.name) ↔ _
      simp [Dataset.names, eq_comm]

/-- Engine membership after `addQuad`. -/
theorem addQuad_memQuad {ds : Dataset} (t : Triple) (g : Option Subject) (h : ds.IsSet)
    (u : Triple) (g' : Option Subject) :
    (addQuad ds t g).memQuad u g' ↔ ds.memQuad u g' ∨ (g' = g ∧ u.key = t.key) := by
  cases g with
  | none =>
    cases g' with
    | none =>
      show (ds.default.add t).mem u = true ↔ _
      rw [Graph.mem_add_iff]; simp [Dataset.memQuad]
    | some m => simp [addQuad, Dataset.memQuad]
  | some n =>
    simp only [addQuad]
    split
    · next ng hf =>
      have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
      have hn : ng.name = n := by
        have hb := List.find?_some hf; simpa using hb
      cases g' with
      | none => simp [Dataset.memQuad]
      | some m =>
        show (∃ x ∈ ds.named.map (upd n { name := n, graph := ng.graph.add t }),
                x.name = m ∧ x.graph.mem u = true) ↔ _
        simp only [List.mem_map, Dataset.memQuad]
        by_cases hm : m = n
        · subst hm
          constructor
          · rintro ⟨x, ⟨ng', hng', rfl⟩, hx1, hx2⟩
            have hname : ng'.name = m := by rw [← hx1, upd_name m _ rfl]
            have hu : upd m { name := m, graph := ng.graph.add t } ng' =
                { name := m, graph := ng.graph.add t } := by
              unfold upd; rw [if_pos (by rw [hname]; exact beq_self_eq_true m)]
            rw [hu] at hx2
            rcases (Graph.mem_add_iff u t ng.graph).mp hx2 with h2 | h2
            · exact Or.inl ⟨ng, hng, hn, h2⟩
            · exact Or.inr ⟨rfl, h2⟩
          · intro hr
            refine ⟨{ name := m, graph := ng.graph.add t }, ⟨ng, hng, ?_⟩, rfl, ?_⟩
            · unfold upd; rw [if_pos (by rw [hn]; exact beq_self_eq_true m)]
            · rcases hr with ⟨ng', hng', hn', h2⟩ | ⟨-, h2⟩
              · have he : ng' = ng :=
                  eq_of_nodup_map (fun x : NamedGraph => x.name) (l := ds.named) h.names hng' hng (by rw [hn', hn])
                subst he
                exact (Graph.mem_add_iff u t ng'.graph).mpr (Or.inl h2)
              · exact (Graph.mem_add_iff u t ng.graph).mpr (Or.inr h2)
        · have hne : ∀ ng' : NamedGraph, ng'.name = m →
              upd n { name := n, graph := ng.graph.add t } ng' = ng' := by
            intro ng' h'
            unfold upd
            rw [if_neg (by rw [h']; simpa using hm)]
          constructor
          · rintro ⟨x, ⟨ng', hng', rfl⟩, hx1, hx2⟩
            have hname : ng'.name = m := by rw [← hx1, upd_name n _ rfl]
            rw [hne ng' hname] at hx2
            exact Or.inl ⟨ng', hng', hname, hx2⟩
          · rintro (⟨ng', hng', hn', h2⟩ | ⟨h1, -⟩)
            · exact ⟨ng', ⟨ng', hng', hne ng' hn'⟩, hn', h2⟩
            · cases h1; exact absurd rfl hm
    · cases g' with
      | none => simp [Dataset.memQuad]
      | some m =>
        show (∃ x ∈ ds.named ++ [({ name := n, graph := [t] } : NamedGraph)],
                x.name = m ∧ x.graph.mem u = true) ↔ _
        simp only [List.mem_append, List.mem_singleton, Dataset.memQuad]
        constructor
        · rintro ⟨x, hx | hx, hx1, hx2⟩
          · exact Or.inl ⟨x, hx, hx1, hx2⟩
          · subst hx
            exact Or.inr ⟨by rw [← hx1], (Graph.mem_single_iff u t).mp hx2⟩
        · rintro (⟨x, hx, hx1, hx2⟩ | ⟨h1, h2⟩)
          · exact ⟨x, Or.inl hx, hx1, hx2⟩
          · cases h1
            exact ⟨_, Or.inr rfl, rfl, (Graph.mem_single_iff u t).mpr h2⟩

/-- List membership after `addQuad`: an entry is an old entry or `t`. -/
theorem addQuad_listQuad (ds : Dataset) (t : Triple) (g : Option Subject)
    (u : Triple) (g' : Option Subject) :
    (addQuad ds t g).listQuad u g' → ds.listQuad u g' ∨ (g' = g ∧ u = t) := by
  cases g with
  | none =>
    cases g' with
    | none =>
      intro hu
      rcases mem_add_cases hu with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, h1⟩
    | some m => intro hu; exact Or.inl hu
  | some n =>
    simp only [addQuad]
    split
    · next ng hf =>
      have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
      have hn : ng.name = n := by
        have hb := List.find?_some hf; simpa using hb
      cases g' with
      | none => intro hu; exact Or.inl hu
      | some m =>
        rintro ⟨x, hx, hx1, hx2⟩
        obtain ⟨ng', hng', rfl⟩ := List.mem_map.mp hx
        by_cases hb : (ng'.name == n) = true
        · rw [if_pos hb] at hx1 hx2
          have hnm : n = m := hx1
          rcases mem_add_cases hx2 with h1 | h1
          · exact Or.inl ⟨ng, hng, hn.trans hnm, h1⟩
          · exact Or.inr ⟨by rw [hnm], h1⟩
        · rw [if_neg hb] at hx1 hx2
          exact Or.inl ⟨ng', hng', hx1, hx2⟩
    · cases g' with
      | none => intro hu; exact Or.inl hu
      | some m =>
        rintro ⟨x, hx, hx1, hx2⟩
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inl ⟨x, hx, hx1, hx2⟩
        · rw [List.mem_singleton] at hx
          subst hx
          simp only [List.mem_singleton] at hx2
          exact Or.inr ⟨by rw [← hx1], hx2⟩

theorem ensureNamed_isSet {ds : Dataset} (n : Subject) (h : ds.IsSet) : (ensureNamed ds n).IsSet := by
  unfold ensureNamed
  split
  · exact h
  · next hf =>
    have hnot : n ∉ ds.names := by
      intro hc
      obtain ⟨ng', hng', he⟩ := List.mem_map.mp hc
      have := List.find?_eq_none.mp hf ng' hng'
      simp [he] at this
    refine ⟨h.default, ?_, ?_⟩
    · show ((ds.named ++ [({ name := n, graph := [] } : NamedGraph)]).map (·.name)).Nodup
      rw [List.map_append, List.nodup_append]
      refine ⟨h.names, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro e; exact hnot (e ▸ ha)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h.graphs x hx
      · rw [List.mem_singleton] at hx; subst hx; exact Graph.keyNodup_nil

theorem ensureNamed_names (ds : Dataset) (n m : Subject) :
    m ∈ (ensureNamed ds n).names ↔ m ∈ ds.names ∨ n = m := by
  unfold ensureNamed
  split
  · next ng hf =>
    have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
    have hn : ng.name = n := by
        have hb := List.find?_some hf; simpa using hb
    constructor
    · exact Or.inl
    · rintro (h' | h')
      · exact h'
      · subst h'; exact List.mem_map.mpr ⟨ng, hng, hn⟩
  · show m ∈ (ds.named ++ [({ name := n, graph := [] } : NamedGraph)]).map (·.name) ↔ _
    simp [Dataset.names]
    exact or_congr_right eq_comm

theorem ensureNamed_memQuad (ds : Dataset) (n : Subject) (u : Triple) (g : Option Subject) :
    (ensureNamed ds n).memQuad u g ↔ ds.memQuad u g := by
  unfold ensureNamed
  split
  · exact Iff.rfl
  · cases g with
    | none => exact Iff.rfl
    | some m =>
      show (∃ x ∈ ds.named ++ [({ name := n, graph := [] } : NamedGraph)], x.name = m ∧ x.graph.mem u = true) ↔ _
      simp only [List.mem_append, List.mem_singleton, Dataset.memQuad]
      constructor
      · rintro ⟨x, hx | hx, hx1, hx2⟩
        · exact ⟨x, hx, hx1, hx2⟩
        · subst hx; simp [Graph.mem] at hx2
      · rintro ⟨x, hx, hx1, hx2⟩
        exact ⟨x, Or.inl hx, hx1, hx2⟩

theorem ensureNamed_listQuad (ds : Dataset) (n : Subject) (u : Triple) (g : Option Subject) :
    (ensureNamed ds n).listQuad u g → ds.listQuad u g := by
  unfold ensureNamed
  split
  · exact id
  · cases g with
    | none => exact id
    | some m =>
      rintro ⟨x, hx, hx1, hx2⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact ⟨x, hx, hx1, hx2⟩
      · rw [List.mem_singleton] at hx; subst hx; simp at hx2

/-! ## Events: the steps `toSet` takes -/

/-- One step of `Dataset.toSet`: add a quad, or declare a named graph. -/
inductive SetEvent where
  | quad (t : Triple) (g : Option Subject)
  | name (n : Subject)

def SetEvent.apply (ds : Dataset) : SetEvent → Dataset
  | .quad t g => addQuad ds t g
  | .name n => ensureNamed ds n

def SetEvent.applyFast (ds : FastDataset) : SetEvent → FastDataset
  | .quad t g => addQuadFast ds t g
  | .name n => ensureNamedFast ds n

/-- The quads an event adds, by key. -/
def SetEvent.Adds : SetEvent → Triple → Option Subject → Prop
  | .quad t g, u, g' => g' = g ∧ u.key = t.key
  | .name _, _, _ => False

/-- The graph names an event declares. -/
def SetEvent.Names : SetEvent → Subject → Prop
  | .quad _ g, m => g = some m
  | .name n, m => n = m

/-- The events of a dataset: the quads of the default graph, then for each
named graph its declaration and its quads, in list order. -/
def Dataset.events (ds : Dataset) : List SetEvent :=
  ds.default.map (fun t => .quad t none) ++
    ds.named.flatMap (fun ng => .name ng.name :: ng.graph.map (fun t => .quad t (some ng.name)))

theorem SetEvent.apply_isSet {ds : Dataset} (e : SetEvent) (h : ds.IsSet) : (e.apply ds).IsSet := by
  cases e with
  | quad t g => exact addQuad_isSet t g h
  | name n => exact ensureNamed_isSet n h

theorem SetEvent.apply_memQuad {ds : Dataset} (e : SetEvent) (h : ds.IsSet) (u : Triple)
    (g : Option Subject) : (e.apply ds).memQuad u g ↔ ds.memQuad u g ∨ e.Adds u g := by
  cases e with
  | quad t g0 => exact addQuad_memQuad t g0 h u g
  | name n => simp only [SetEvent.apply, SetEvent.Adds, or_false]; exact ensureNamed_memQuad ds n u g

theorem SetEvent.apply_names (ds : Dataset) (e : SetEvent) (m : Subject) :
    m ∈ (e.apply ds).names ↔ m ∈ ds.names ∨ e.Names m := by
  cases e with
  | quad t g0 => exact addQuad_names ds t g0 m
  | name n => exact ensureNamed_names ds n m

theorem SetEvent.apply_listQuad (ds : Dataset) (e : SetEvent) (u : Triple) (g : Option Subject) :
    (e.apply ds).listQuad u g → ds.listQuad u g ∨ e = .quad u g := by
  cases e with
  | quad t g0 =>
    intro hu
    rcases addQuad_listQuad ds t g0 u g hu with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · subst h1; subst h2; exact Or.inr rfl
  | name n => intro hu; exact Or.inl (ensureNamed_listQuad ds n u g hu)

/-- What a fold of events gives, from any set. -/
theorem foldEvents (evs : List SetEvent) :
    ∀ ds : Dataset, ds.IsSet →
      (evs.foldl SetEvent.apply ds).IsSet
      ∧ (∀ u g, (evs.foldl SetEvent.apply ds).memQuad u g ↔ ds.memQuad u g ∨ ∃ e ∈ evs, e.Adds u g)
      ∧ (∀ m, m ∈ (evs.foldl SetEvent.apply ds).names ↔ m ∈ ds.names ∨ ∃ e ∈ evs, e.Names m)
      ∧ (∀ u g, (evs.foldl SetEvent.apply ds).listQuad u g →
          ds.listQuad u g ∨ SetEvent.quad u g ∈ evs) := by
  induction evs with
  | nil => intro ds h; simp [h]
  | cons e es ih =>
    intro ds h
    obtain ⟨h1, h2, h3, h4⟩ := ih (e.apply ds) (e.apply_isSet h)
    simp only [List.foldl_cons]
    refine ⟨h1, ?_, ?_, ?_⟩
    · intro u g
      rw [h2, e.apply_memQuad h]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((a | a) | a)
        · exact Or.inl a
        · exact Or.inr (Or.inl a)
        · exact Or.inr (Or.inr a)
      · rintro (a | a | a)
        · exact Or.inl (Or.inl a)
        · exact Or.inl (Or.inr a)
        · exact Or.inr a
    · intro m
      rw [h3, e.apply_names]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((a | a) | a)
        · exact Or.inl a
        · exact Or.inr (Or.inl a)
        · exact Or.inr (Or.inr a)
      · rintro (a | a | a)
        · exact Or.inl (Or.inl a)
        · exact Or.inl (Or.inr a)
        · exact Or.inr a
    · intro u g hu
      rcases h4 u g hu with a | a
      · rcases e.apply_listQuad ds u g a with b | b
        · exact Or.inl b
        · exact Or.inr (List.mem_cons.mpr (Or.inl b.symm))
      · exact Or.inr (List.mem_cons_of_mem _ a)

theorem events_adds (ds : Dataset) (u : Triple) (g : Option Subject) :
    (∃ e ∈ ds.events, e.Adds u g) ↔ ds.memQuad u g := by
  cases g with
  | none =>
    simp only [Dataset.events, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      Dataset.memQuad, Graph.mem_iff_key]
    constructor
    · rintro ⟨e, ⟨t, ht, rfl⟩ | ⟨ng, _, rfl | ⟨t, _, rfl⟩⟩, he⟩
      · exact ⟨t, ht, he.2.symm⟩
      · exact he.elim
      · exact absurd he.1 (by simp)
    · rintro ⟨t, ht, hk⟩
      exact ⟨.quad t none, Or.inl ⟨t, ht, rfl⟩, rfl, hk.symm⟩
  | some m =>
    simp only [Dataset.events, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
      Dataset.memQuad, Graph.mem_iff_key]
    constructor
    · rintro ⟨e, ⟨t, _, rfl⟩ | ⟨ng, hng, rfl | ⟨t, ht, rfl⟩⟩, he⟩
      · exact absurd he.1 (by simp)
      · exact he.elim
      · obtain ⟨h1, h2⟩ := he
        exact ⟨ng, hng, (Option.some.inj h1).symm, t, ht, h2.symm⟩
    · rintro ⟨ng, hng, hn, t, ht, hk⟩
      exact ⟨.quad t (some ng.name), Or.inr ⟨ng, hng, Or.inr ⟨t, ht, rfl⟩⟩,
        by rw [hn], hk.symm⟩

theorem events_names (ds : Dataset) (m : Subject) :
    (∃ e ∈ ds.events, e.Names m) ↔ m ∈ ds.names := by
  simp only [Dataset.events, Dataset.names, List.mem_append, List.mem_map, List.mem_flatMap,
    List.mem_cons]
  constructor
  · rintro ⟨e, ⟨t, _, rfl⟩ | ⟨ng, hng, rfl | ⟨t, _, rfl⟩⟩, he⟩
    · exact absurd he (by simp [SetEvent.Names])
    · exact ⟨ng, hng, he⟩
    · exact ⟨ng, hng, Option.some.inj he⟩
  · rintro ⟨ng, hng, hn⟩
    exact ⟨.name ng.name, Or.inr ⟨ng, hng, Or.inl rfl⟩, hn⟩

theorem events_quad (ds : Dataset) (u : Triple) (g : Option Subject) :
    SetEvent.quad u g ∈ ds.events → ds.listQuad u g := by
  simp only [Dataset.events, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons]
  rintro (⟨t, ht, he⟩ | ⟨ng, hng, he | ⟨t, ht, he⟩⟩)
  · cases he; exact ht
  · cases he
  · cases he; exact ⟨ng, hng, rfl, ht⟩

/-! ## `Dataset.toSet` -/

/-- The set of quads of a dataset (module header). -/
def Dataset.toSet (ds : Dataset) : Dataset := ds.events.foldl SetEvent.apply Dataset.empty

/-- `Dataset.toSet` on the hash-indexed accumulator, with no list of events
built. -/
def Dataset.toSetFast (ds : Dataset) : Dataset :=
  (ds.named.foldl
      (fun a ng => ng.graph.foldl (fun a t => addQuadFast a t (some ng.name))
        (ensureNamedFast a ng.name))
      (ds.default.foldl (fun a t => addQuadFast a t none) {})).toDataset

theorem foldEventsFast (evs : List SetEvent) :
    ∀ a : FastDataset, a.Inv →
      (evs.foldl SetEvent.applyFast a).Inv
      ∧ (evs.foldl SetEvent.applyFast a).toDataset = evs.foldl SetEvent.apply a.toDataset := by
  induction evs with
  | nil => intro a h; exact ⟨h, rfl⟩
  | cons e es ih =>
    intro a h
    cases e with
    | quad t g =>
      obtain ⟨h1, h2⟩ := ih (addQuadFast a t g) (FastDataset.add_inv h)
      refine ⟨h1, ?_⟩
      simp only [List.foldl_cons, SetEvent.applyFast, SetEvent.apply] at h2 ⊢
      rw [h2, addQuadFast_toDataset t g h]
    | name n =>
      obtain ⟨h1, h2⟩ := ih (ensureNamedFast a n) (FastDataset.ensure_inv n h)
      refine ⟨h1, ?_⟩
      simp only [List.foldl_cons, SetEvent.applyFast, SetEvent.apply] at h2 ⊢
      rw [h2, ensureNamedFast_toDataset n h]

private theorem foldl_named_events (l : List NamedGraph) (a : FastDataset) :
    l.foldl (fun a ng => ng.graph.foldl (fun a t => addQuadFast a t (some ng.name))
        (ensureNamedFast a ng.name)) a
      = (l.flatMap (fun ng => SetEvent.name ng.name ::
          ng.graph.map (fun t => SetEvent.quad t (some ng.name)))).foldl SetEvent.applyFast a := by
  induction l generalizing a with
  | nil => rfl
  | cons ng rest ih =>
    simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, List.foldl_map, ih]
    rfl

theorem Dataset.toSetFast_eq_events (ds : Dataset) :
    ds.toSetFast = (ds.events.foldl SetEvent.applyFast {}).toDataset := by
  simp only [Dataset.toSetFast, Dataset.events, List.foldl_append, List.foldl_map,
    foldl_named_events]
  rfl

/-- The compiler runs the indexed form. -/
@[csimp] theorem Dataset.toSet_eq_fast : @Dataset.toSet = @Dataset.toSetFast := by
  funext ds
  rw [Dataset.toSetFast_eq_events, (foldEventsFast ds.events {} FastDataset.inv_empty).2,
    FastDataset.toDataset_empty]
  rfl

/-! ## What `toSet` gives -/

/-- The result is a set. -/
theorem Dataset.toSet_isSet (ds : Dataset) : ds.toSet.IsSet :=
  (foldEvents ds.events Dataset.empty Dataset.isSet_empty).1

/-- A triple is in a graph of the result exactly when it is in that graph of
`ds`. -/
theorem Dataset.memQuad_toSet (ds : Dataset) (u : Triple) (g : Option Subject) :
    ds.toSet.memQuad u g ↔ ds.memQuad u g := by
  rw [Dataset.toSet, (foldEvents ds.events Dataset.empty Dataset.isSet_empty).2.1, events_adds]
  cases g <;> simp [Dataset.memQuad, Dataset.empty, Graph.mem]

/-- The result names exactly the graphs that `ds` names. -/
theorem Dataset.names_toSet (ds : Dataset) (m : Subject) :
    m ∈ ds.toSet.names ↔ m ∈ ds.names := by
  rw [Dataset.toSet, (foldEvents ds.events Dataset.empty Dataset.isSet_empty).2.2.1, events_names]
  simp [Dataset.names, Dataset.empty]

/-- Every list entry of the result is a list entry of `ds` in the graph of the
same name. -/
theorem Dataset.listQuad_toSet (ds : Dataset) (u : Triple) (g : Option Subject) :
    ds.toSet.listQuad u g → ds.listQuad u g := by
  intro h
  rcases (foldEvents ds.events Dataset.empty Dataset.isSet_empty).2.2.2 u g h with h1 | h1
  · cases g <;> simp [Dataset.listQuad, Dataset.empty] at h1
  · exact events_quad ds u g h1

/-- The default graph of the result has the engine members of the default
graph of `ds`. -/
theorem Dataset.mem_default_toSet (ds : Dataset) (u : Triple) :
    ds.toSet.default.mem u = ds.default.mem u :=
  Bool.eq_iff_iff.mpr (Dataset.memQuad_toSet ds u none)

/-! ## The two readers that add with `addQuad` give a set -/

/-- The N-Quads reader gives a set. -/
theorem parseNQuadsFast_isSet (s : String) (mode : Mode) (ds : Dataset)
    (h : parseNQuadsFast s mode = .ok ds) : ds.IsSet := by
  rw [parseNQuadsFast_eq_parseNQuads] at h
  simp only [parseNQuads, parseQuadLinesAcc_eq_fold] at h
  have hrel := foldQuadLinesAcc_rel mode
    (fun (a : Dataset) (b : Dataset) => a = b ∧ a.IsSet)
    (fun ds t gopt => addQuad ds t gopt) (fun ds t gopt => addQuad ds t gopt)
    (by
      intro a b t g hab
      obtain ⟨rfl, hs⟩ := hab
      exact ⟨rfl, addQuad_isSet t g hs⟩)
    (s.toList.length + 1) 0 s.toList Dataset.empty Dataset.empty ⟨rfl, Dataset.isSet_empty⟩
  rw [h] at hrel
  exact hrel.2

theorem ensureGraphOf_isSet {ds : Dataset} (g : Option Subject) (h : ds.IsSet) :
    (ensureGraphOf ds g).IsSet := by
  cases g with
  | none => exact h
  | some n => exact ensureNamed_isSet n h

theorem foldl_addQuad_isSet (g : Option Subject) :
    ∀ (ts : List Triple) (d : Dataset), d.IsSet → (ts.foldl (fun d t => addQuad d t g) d).IsSet
  | [], _, h => h
  | t :: ts, _, h => foldl_addQuad_isSet g ts _ (addQuad_isSet t g h)

theorem addTriplesTo_isSet {ds : Dataset} (g : Option Subject) (ts : List Triple) (h : ds.IsSet) :
    (addTriplesTo ds g ts).IsSet :=
  foldl_addQuad_isSet g ts _ (ensureGraphOf_isSet g h)

/-- The TriG statement loop keeps the invariant and a set. -/
theorem parseTriGStatements_isSet :
    ∀ (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) (ds : FastDataset)
      (r : FastDataset × TurtleState), ds.Inv → ds.toDataset.IsSet →
      parseTriGStatements fuel st pos cs ds = .ok r → r.1.toDataset.IsSet
  | 0, st, pos, cs, ds, r, _, hs, h => by
      simp only [parseTriGStatements, Except.ok.injEq] at h
      subst h; exact hs
  | fuel + 1, st, pos, cs, ds, r, hi, hs, h => by
      simp only [parseTriGStatements] at h
      split at h
      · simp only [Except.ok.injEq] at h; subst h; exact hs
      · split at h
        · cases h
        · next gname ts st' p2 r2 _ =>
          have ha := addTriplesToFast_toDataset gname ts ds hi
          have hset : (addTriplesToFast ds gname ts).toDataset.IsSet := by
            rw [ha.2]; exact addTriplesTo_isSet gname ts hs
          split at h
          · simp only [Except.ok.injEq] at h; subst h; exact hset
          · exact parseTriGStatements_isSet fuel st' p2 r2 _ r ha.1 hset h

/-- The TriG reader gives a set. -/
theorem parseTriG_isSet (text : String) (base : Option String) (mode : Mode) (ds : Dataset)
    (h : parseTriG text base mode = .ok ds) : ds.IsSet := by
  simp only [parseTriG] at h
  split at h
  · cases h
  · next r hr =>
    simp only [Except.ok.injEq] at h
    subst h
    exact parseTriGStatements_isSet _ _ _ _ _ _ FastDataset.inv_empty
      (by rw [FastDataset.toDataset_empty]; exact Dataset.isSet_empty) hr

theorem parseTriGWithPrefixes_isSet (text : String) (base : Option String) (mode : Mode)
    (r : Dataset × List (String × String))
    (h : parseTriGWithPrefixes text base mode = .ok r) : r.1.IsSet := by
  simp only [parseTriGWithPrefixes] at h
  split at h
  · cases h
  · next r' hr =>
    simp only [Except.ok.injEq] at h
    subst h
    exact parseTriGStatements_isSet _ _ _ _ _ _ FastDataset.inv_empty
      (by rw [FastDataset.toDataset_empty]; exact Dataset.isSet_empty) hr

/-! ## Checks -/

private def gi : WfIri := ⟨"http://e/g", by decide⟩
private def px : WfIri := ⟨"http://e/p", by decide⟩
private def ax : WfIri := ⟨"http://e/a", by decide⟩
private def tV : Triple := ⟨.iri ax, px, .literal (Literal.string "v")⟩
private def tEn : Triple := ⟨.iri ax, px, .literal (Literal.langString "v" "en")⟩
private def tEN : Triple := ⟨.iri ax, px, .literal (Literal.langString "v" "EN")⟩

-- A repeated triple is kept once, at its first place.
#guard (Dataset.toSet { default := [tV, tEn, tV], named := [] }).default == [tV, tEn]
-- Language tags compare without case, as in the N-Quads reader.
#guard (Dataset.toSet { default := [tEN, tEn], named := [] }).default == [tEN]
-- Named graphs of one name are merged; an empty named graph stays.
#guard Dataset.toSet { default := [tV], named := [⟨.iri gi, [tV]⟩, ⟨.iri gi, [tV, tEn]⟩] } ==
  { default := [tV], named := [⟨.iri gi, [tV, tEn]⟩] }
#guard Dataset.toSet { default := [], named := [⟨.iri gi, []⟩] } ==
  { default := [], named := [⟨.iri gi, []⟩] }
-- The compiled form and the definition give the same value.
#guard Dataset.toSetFast { default := [tV, tEn, tV], named := [⟨.iri gi, [tV, tV]⟩] } ==
  (Dataset.events { default := [tV, tEn, tV], named := [⟨.iri gi, [tV, tV]⟩] }).foldl
    SetEvent.apply Dataset.empty

#print axioms Dataset.toSet_eq_fast
#print axioms Dataset.toSet_isSet
#print axioms Dataset.memQuad_toSet
#print axioms Dataset.names_toSet
#print axioms Dataset.listQuad_toSet
#print axioms Graph.KeyNodup.nodup
#print axioms Graph.KeyNodup.pairwise
#print axioms parseNQuadsFast_isSet
#print axioms parseTriG_isSet
#print axioms parseTriGWithPrefixes_isSet

end L4Factoidal.RDF
