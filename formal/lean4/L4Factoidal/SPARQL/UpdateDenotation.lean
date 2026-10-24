/-
L4Factoidal.SPARQL.UpdateDenotation — the SPARQL 1.1 Update operations on
the dataset denotation `RDF.DatasetDen`, and the proof that the Graph Store
semantics of `SPARQL/Update.lean` has that effect
(https://github.com/danbri/factoidal/issues/975, phase D).

## The operations on `DatasetDen`

SPARQL 1.1 Update, section 3 (operations on a Graph Store), stated on the
denotation (membership per graph, graph names with empty named graphs, RDF
term equality by `Triple.key`):

* `insertQuads qs` (§3.1.1 INSERT DATA, the insert half of §3.1.3): the quads
  are added; a named graph that the store does not hold gets its name.
* `deleteQuads qs` (§3.1.2 DELETE DATA, §3.1.3.3 DELETE WHERE, the delete half
  of §3.1.3): the quads are removed; graph names do not change, so a named
  graph that becomes empty stays in the store.
* `clearSlot gn`, `clearNamed` (§3.1.5 CLEAR): the graphs lose their triples;
  graph names do not change.
* `dropName n`, `dropNamed` (§3.2.2 DROP): the named graph and its name go;
  `DROP DEFAULT` is `clearSlot none` ("the default graph ... cannot be
  removed").
* `addName n` (§3.2.1 CREATE): the name is added; no triple is added.
* `setSlot gn G` (§3.2.3 COPY, §3.2.4 MOVE, §3.2.5 ADD): the graph at the slot
  is `G`; a named slot gets its name.

So graph existence (`names`) is separate from triples (`graph`): CLEAR keeps
the name, DROP removes it, CREATE adds it with no triple.

## What is proved

* `Dataset.den_insertQuads`, `Dataset.den_deleteQuads`,
  `Dataset.den_setGraph`, `Dataset.den_dropGraph`, `Dataset.den_ensureGraph`,
  `Dataset.den_clearAllNamed`, `Dataset.den_withDefault`: the list operations
  of `SPARQL/Update.lean` denote the operations above. The ones that change
  one named graph need `Dataset.IsSet` (no two named graphs with one name):
  `replaceNamed` changes the first entry of the name only.
* `applyOp_den`: every successful operation, applied to a set, gives a set
  whose denotation is `OpDen` of the input's denotation (`OpDen` below, one
  case for each §3 operation).
* `applyUpdateIn_den`: a request is its operations in order (`OpsDen`), and
  the result is a set.

## The boundary

The quad lists of INSERT DATA / DELETE DATA (`collectQuads` with the request
blank-node scope) and of DELETE WHERE / DELETE ... INSERT ... WHERE (the WHERE
solutions of `evalWhere` and the template instantiation `instQuads`) are the
implementation's own: `OpDen` takes them as inputs. The correctness of
`evalWhere` against SPARQL 1.1 Query section 18 is not proved here; the W3C
SPARQL 1.1 suites test it (manifest-all, update entries). `LOAD` without
`SILENT` is an error (no document fetch); with `SILENT` it changes nothing.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.CertifiedDataset
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.RDF

/-! ## The graph slot of a quad -/

/-- The graph position of an update quad in the denotation: `none` for the
default graph, the IRI as a graph name otherwise. -/
def quadSlot (q : Quad) : Option Subject := q.1.map Subject.iri

/-- One of the quads `qs` is the triple `t` (by RDF term equality) in the
graph `gn`. -/
def QuadsHold (qs : List Quad) (gn : Option Subject) (t : Triple) : Prop :=
  ∃ q ∈ qs, quadSlot q = gn ∧ q.2.key = t.key

theorem QuadsHold.key {qs : List Quad} {gn : Option Subject} {t u : Triple}
    (h : t.key = u.key) : QuadsHold qs gn t → QuadsHold qs gn u
  | ⟨q, hq, hs, e⟩ => ⟨q, hq, hs, e.trans h⟩

/-! ## The operations on the denotation -/

namespace DatasetDen

/-- Add the quads `qs`. -/
def insertQuads (d : DatasetDen) (qs : List Quad) : DatasetDen where
  graph gn t := d.graph gn t ∨ QuadsHold qs gn t
  names n := d.names n ∨ ∃ q ∈ qs, quadSlot q = some n
  graph_key := by
    rintro gn t u h (h1 | h1)
    · exact Or.inl (d.graph_key gn t u h h1)
    · exact Or.inr (h1.key h)
  named_mem := by
    rintro n t (h1 | ⟨q, hq, hs, _⟩)
    · exact Or.inl (d.named_mem n t h1)
    · exact Or.inr ⟨q, hq, hs⟩

/-- Remove the quads `qs`; the graph names stay. -/
def deleteQuads (d : DatasetDen) (qs : List Quad) : DatasetDen where
  graph gn t := d.graph gn t ∧ ¬ QuadsHold qs gn t
  names := d.names
  graph_key := by
    rintro gn t u h ⟨h1, h2⟩
    exact ⟨d.graph_key gn t u h h1, fun h3 => h2 (h3.key h.symm)⟩
  named_mem := fun n t h => d.named_mem n t h.1

/-- The graph at the slot `gn` loses its triples; the graph names stay. -/
def clearSlot (d : DatasetDen) (gn : Option Subject) : DatasetDen where
  graph x t := d.graph x t ∧ x ≠ gn
  names := d.names
  graph_key := by
    rintro x t u h ⟨h1, h2⟩
    exact ⟨d.graph_key x t u h h1, h2⟩
  named_mem := fun n t h => d.named_mem n t h.1

/-- Every named graph loses its triples; the graph names stay. -/
def clearNamed (d : DatasetDen) : DatasetDen where
  graph x t := d.graph x t ∧ x = none
  names := d.names
  graph_key := by
    rintro x t u h ⟨h1, h2⟩
    exact ⟨d.graph_key x t u h h1, h2⟩
  named_mem := fun n t h => d.named_mem n t h.1

/-- The named graph `n` and its name go. -/
def dropName (d : DatasetDen) (n : Subject) : DatasetDen where
  graph x t := d.graph x t ∧ x ≠ some n
  names m := d.names m ∧ m ≠ n
  graph_key := by
    rintro x t u h ⟨h1, h2⟩
    exact ⟨d.graph_key x t u h h1, h2⟩
  named_mem := fun m t h => ⟨d.named_mem m t h.1, fun e => h.2 (e ▸ rfl)⟩

/-- Every named graph and every name go; the default graph stays. -/
def dropNamed (d : DatasetDen) : DatasetDen where
  graph x t := d.graph x t ∧ x = none
  names _ := False
  graph_key := by
    rintro x t u h ⟨h1, h2⟩
    exact ⟨d.graph_key x t u h h1, h2⟩
  named_mem := fun _ _ h => by cases h.2

/-- The empty dataset. -/
def empty : DatasetDen where
  graph _ _ := False
  names _ := False
  graph_key := fun _ _ _ _ h => h
  named_mem := fun _ _ h => h

/-- The name `n` is added; no triple is added. -/
def addName (d : DatasetDen) (n : Subject) : DatasetDen where
  graph := d.graph
  names m := d.names m ∨ m = n
  graph_key := d.graph_key
  named_mem := fun m t h => Or.inl (d.named_mem m t h)

/-- The graph at the slot `gn` is `G`; a named slot gets its name. -/
def setSlot (d : DatasetDen) (gn : Option Subject) (G : Triple → Prop)
    (hG : ∀ t u, t.key = u.key → G t → G u) : DatasetDen where
  graph x t := (x = gn ∧ G t) ∨ (x ≠ gn ∧ d.graph x t)
  names n := d.names n ∨ gn = some n
  graph_key := by
    rintro x t u h (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, hG t u h h2⟩
    · exact Or.inr ⟨h1, d.graph_key x t u h h2⟩
  named_mem := by
    rintro n t (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact Or.inr h1.symm
    · exact Or.inl (d.named_mem n t h2)

theorem insertQuads_nil (d : DatasetDen) : d.insertQuads [] = d := by
  apply DatasetDen.ext
  · intro gn t
    simp [insertQuads, QuadsHold]
  · intro n
    simp [insertQuads]

theorem insertQuads_cons (d : DatasetDen) (q : Quad) (qs : List Quad) :
    (d.insertQuads [q]).insertQuads qs = d.insertQuads (q :: qs) := by
  apply DatasetDen.ext
  · intro gn t
    simp only [insertQuads, QuadsHold, List.mem_cons, List.not_mem_nil]
    constructor
    · rintro ((h | ⟨q', rfl | h, hs, e⟩) | ⟨q', hq, hs, e⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q', Or.inl rfl, hs, e⟩
      · exact absurd h (by simp)
      · exact Or.inr ⟨q', Or.inr hq, hs, e⟩
    · rintro (h | ⟨q', rfl | hq, hs, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨q', Or.inl rfl, hs, e⟩)
      · exact Or.inr ⟨q', hq, hs, e⟩
  · intro n
    simp only [insertQuads, List.mem_cons, List.not_mem_nil]
    constructor
    · rintro ((h | ⟨q', rfl | h, hs⟩) | ⟨q', hq, hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q', Or.inl rfl, hs⟩
      · exact absurd h (by simp)
      · exact Or.inr ⟨q', Or.inr hq, hs⟩
    · rintro (h | ⟨q', rfl | hq, hs⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨q', Or.inl rfl, hs⟩)
      · exact Or.inr ⟨q', hq, hs⟩

theorem deleteQuads_nil (d : DatasetDen) : d.deleteQuads [] = d := by
  apply DatasetDen.ext
  · intro gn t
    simp [deleteQuads, QuadsHold]
  · intro n
    rfl

theorem deleteQuads_cons (d : DatasetDen) (q : Quad) (qs : List Quad) :
    (d.deleteQuads [q]).deleteQuads qs = d.deleteQuads (q :: qs) := by
  apply DatasetDen.ext
  · intro gn t
    simp only [deleteQuads, QuadsHold, List.mem_cons, List.not_mem_nil]
    constructor
    · rintro ⟨⟨h, h1⟩, h2⟩
      refine ⟨h, ?_⟩
      rintro ⟨q', rfl | hq, hs, e⟩
      · exact h1 ⟨q', Or.inl rfl, hs, e⟩
      · exact h2 ⟨q', hq, hs, e⟩
    · rintro ⟨h, h1⟩
      refine ⟨⟨h, ?_⟩, ?_⟩
      · rintro ⟨q', rfl | hq, hs, e⟩
        · exact h1 ⟨q', Or.inl rfl, hs, e⟩
        · exact absurd hq (by simp)
      · rintro ⟨q', hq, hs, e⟩
        exact h1 ⟨q', Or.inr hq, hs, e⟩
  · intro n
    rfl

/-- `CREATE` of a graph that exists changes nothing. -/
theorem addName_of_names {d : DatasetDen} {n : Subject} (h : d.names n) : d.addName n = d := by
  apply DatasetDen.ext
  · intro gn t; rfl
  · intro m
    constructor
    · rintro (hm | rfl)
      · exact hm
      · exact h
    · exact Or.inl

/-- `CLEAR` of a named graph that the store does not hold changes nothing. -/
theorem clearSlot_of_not_names {d : DatasetDen} {n : Subject} (h : ¬ d.names n) :
    d.clearSlot (some n) = d := by
  apply DatasetDen.ext
  · intro gn t
    constructor
    · exact fun h' => h'.1
    · intro h'
      refine ⟨h', ?_⟩
      rintro rfl
      exact h (d.named_mem n t h')
  · intro m; rfl

/-- `DROP` of a named graph that the store does not hold changes nothing. -/
theorem dropName_of_not_names {d : DatasetDen} {n : Subject} (h : ¬ d.names n) :
    d.dropName n = d := by
  apply DatasetDen.ext
  · intro gn t
    constructor
    · exact fun h' => h'.1
    · intro h'
      refine ⟨h', ?_⟩
      rintro rfl
      exact h (d.named_mem n t h')
  · intro m
    constructor
    · exact fun h' => h'.1
    · intro h'
      refine ⟨h', ?_⟩
      rintro rfl
      exact h h'

theorem setSlot_congr (d : DatasetDen) (gn : Option Subject) {G G' : Triple → Prop}
    (hG : ∀ t u, t.key = u.key → G t → G u) (hG' : ∀ t u, t.key = u.key → G' t → G' u)
    (e : ∀ t, G t ↔ G' t) : d.setSlot gn G hG = d.setSlot gn G' hG' := by
  apply DatasetDen.ext
  · intro x t
    simp only [setSlot, e]
  · intro n; rfl

/-- An empty graph at a slot whose name the store holds is `CLEAR` of it. -/
theorem setSlot_false_eq_clearSlot (d : DatasetDen) (gn : Option Subject)
    (hG : ∀ t u : Triple, t.key = u.key → False → False)
    (hn : ∀ n, gn = some n → d.names n) :
    d.setSlot gn (fun _ => False) hG = d.clearSlot gn := by
  apply DatasetDen.ext
  · intro x t
    simp only [setSlot, clearSlot, and_false, false_or]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · intro n
    simp only [setSlot, clearSlot]
    constructor
    · rintro (h | h)
      · exact h
      · exact hn n h
    · exact Or.inl

end DatasetDen

/-! ## The list operations denote the operations on the denotation -/

theorem graphKey_mem (g : Graph) : ∀ t u : Triple, t.key = u.key →
    g.mem t = true → g.mem u = true :=
  fun _ _ h ht => Graph.mem_of_key_eq h ht

/-- A new default graph. -/
theorem Dataset.den_withDefault (ds : Dataset) (g : Graph) :
    ({ ds with default := g } : Dataset).den =
      ds.den.setSlot none (fun t => g.mem t = true) (graphKey_mem g) := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show g.mem t = true ↔ _
      simp [DatasetDen.setSlot]
    | some n =>
      show (∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true) ↔ _
      simp only [DatasetDen.setSlot, reduceCtorEq, false_and, ne_eq, not_false_eq_true,
        true_and, false_or]
      rfl
  · intro n
    simp only [DatasetDen.setSlot, reduceCtorEq, or_false]
    rfl

theorem mem_names_replaceNamed (i : WfIri) (g : Graph) :
    ∀ (l : List NamedGraph) (n : Subject),
      n ∈ (replaceNamed i g l).map (·.name) ↔ n ∈ l.map (·.name) ∨ n = .iri i
  | [], n => by simp [replaceNamed]
  | ng :: rest, n => by
      unfold replaceNamed
      split
      · next he =>
        have he' : ng.name = .iri i := beq_iff_eq.mp he
        simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans he'.symm)
      · simp only [List.map_cons, List.mem_cons]
        rw [mem_names_replaceNamed i g rest n]
        constructor
        · rintro (h | h | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)

theorem mem_graph_replaceNamed (i : WfIri) (g : Graph) :
    ∀ (l : List NamedGraph), (l.map (·.name)).Nodup → ∀ (n : Subject) (t : Triple),
      (∃ ng ∈ replaceNamed i g l, ng.name = n ∧ ng.graph.mem t = true) ↔
        (n = .iri i ∧ g.mem t = true) ∨
          (n ≠ .iri i ∧ ∃ ng ∈ l, ng.name = n ∧ ng.graph.mem t = true)
  | [], _, n, t => by
      simp only [replaceNamed, List.mem_singleton, exists_eq_left, List.not_mem_nil,
        false_and, exists_false, and_false, or_false]
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
  | ng :: rest, hnd, n, t => by
      rw [List.map_cons, List.nodup_cons] at hnd
      unfold replaceNamed
      split
      · next he =>
        have he' : ng.name = .iri i := beq_iff_eq.mp he
        have hrest : ∀ x ∈ rest, x.name ≠ .iri i := by
          intro x hx e
          exact hnd.1 (he' ▸ e ▸ List.mem_map_of_mem hx)
        constructor
        · rintro ⟨x, hx, hxn, hxm⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inl ⟨hxn.symm.trans he', hxm⟩
          · refine Or.inr ⟨fun e => hrest x hx (hxn.trans e), x, List.mem_cons_of_mem _ hx, hxn, hxm⟩
        · rintro (⟨rfl, hm⟩ | ⟨hne, x, hx, hxn, hxm⟩)
          · exact ⟨{ ng with graph := g }, List.mem_cons_self, he', hm⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact absurd (hxn.symm.trans he') hne
            · exact ⟨x, List.mem_cons_of_mem _ hx, hxn, hxm⟩
      · next he =>
        have he' : ng.name ≠ .iri i := fun e => he (beq_iff_eq.mpr e)
        have ih := mem_graph_replaceNamed i g rest hnd.2 n t
        constructor
        · rintro ⟨x, hx, hxn, hxm⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr ⟨fun e => he' (hxn.trans e), x, List.mem_cons_self, hxn, hxm⟩
          · rcases ih.mp ⟨x, hx, hxn, hxm⟩ with h | ⟨hne, y, hy, hyn, hym⟩
            · exact Or.inl h
            · exact Or.inr ⟨hne, y, List.mem_cons_of_mem _ hy, hyn, hym⟩
        · rintro (h | ⟨hne, x, hx, hxn, hxm⟩)
          · obtain ⟨y, hy, hyn, hym⟩ := ih.mpr (Or.inl h)
            exact ⟨y, List.mem_cons_of_mem _ hy, hyn, hym⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨x, List.mem_cons_self, hxn, hxm⟩
            · obtain ⟨y, hy, hyn, hym⟩ := ih.mpr (Or.inr ⟨hne, x, hx, hxn, hxm⟩)
              exact ⟨y, List.mem_cons_of_mem _ hy, hyn, hym⟩

/-- **A new graph for the name `i`**, on a set. -/
theorem Dataset.den_setGraph {ds : Dataset} (hs : ds.IsSet) (i : WfIri) (g : Graph) :
    (ds.setGraph i g).den =
      ds.den.setSlot (some (.iri i)) (fun t => g.mem t = true) (graphKey_mem g) := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show ds.default.mem t = true ↔ _
      simp only [DatasetDen.setSlot, reduceCtorEq, false_and, ne_eq, not_false_eq_true,
        true_and, false_or]
      rfl
    | some n =>
      show (∃ ng ∈ replaceNamed i g ds.named, ng.name = n ∧ ng.graph.mem t = true) ↔ _
      rw [mem_graph_replaceNamed i g ds.named hs.names n t]
      simp only [DatasetDen.setSlot, Option.some.injEq, ne_eq]
      rfl
  · intro n
    show n ∈ (replaceNamed i g ds.named).map (·.name) ↔ _
    rw [mem_names_replaceNamed]
    simp only [DatasetDen.setSlot, Option.some.injEq]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm

/-- On a set, the graph `graphOf i` holds the triples of the name `i`. -/
theorem Dataset.mem_graphOf {ds : Dataset} (hs : ds.IsSet) (i : WfIri) (t : Triple) :
    (ds.graphOf i).mem t = true ↔ ds.den.graph (some (.iri i)) t := by
  unfold Dataset.graphOf Dataset.lookupNamed
  cases hf : ds.named.find? (fun ng => ng.name == .iri i) with
  | some ng =>
    have hng : ng ∈ ds.named := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have hn : ng.name = .iri i := beq_iff_eq.mp hp
    have := ((hs.den_named hng).2 t)
    rw [hn] at this
    show ng.graph.mem t = true ↔ _
    rw [this, Graph.mem_iff_keys]
  | none =>
    rw [List.find?_eq_none] at hf
    show Graph.mem t [] = true ↔ _
    constructor
    · intro h; simp [Graph.mem] at h
    · rintro ⟨ng, hng, hn, _⟩
      exact absurd (beq_iff_eq.mpr hn) (hf ng hng)

theorem Dataset.hasGraph_iff (ds : Dataset) (i : WfIri) :
    ds.hasGraph i = true ↔ ds.den.names (.iri i) := by
  unfold Dataset.hasGraph
  rw [List.any_eq_true, Dataset.den_names]
  simp only [Dataset.names, List.mem_map, beq_iff_eq]

/-- `DROP GRAPH <i>`: the name and its triples go. No set condition. -/
theorem Dataset.den_dropGraph (ds : Dataset) (i : WfIri) :
    (ds.dropGraph i).den = ds.den.dropName (.iri i) := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show ds.default.mem t = true ↔ ds.default.mem t = true ∧ _
      simp
    | some n =>
      show (∃ ng ∈ ds.named.filter (fun ng : NamedGraph => !(ng.name == .iri i)),
          ng.name = n ∧ ng.graph.mem t = true) ↔
        (∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true) ∧ some n ≠ some (.iri i)
      simp only [List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        Option.some.injEq]
      constructor
      · rintro ⟨ng, ⟨hng, hne⟩, rfl, hm⟩
        exact ⟨⟨ng, hng, rfl, hm⟩, hne⟩
      · rintro ⟨⟨ng, hng, rfl, hm⟩, hne⟩
        exact ⟨ng, ⟨hng, hne⟩, rfl, hm⟩
  · intro n
    show n ∈ (ds.named.filter (fun ng : NamedGraph => !(ng.name == .iri i))).map (·.name) ↔
      n ∈ ds.names ∧ n ≠ .iri i
    simp only [Dataset.names, List.mem_map, List.mem_filter, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨ng, ⟨hng, hne⟩, rfl⟩
      exact ⟨⟨ng, hng, rfl⟩, hne⟩
    · rintro ⟨⟨ng, hng, rfl⟩, hne⟩
      exact ⟨ng, ⟨hng, hne⟩, rfl⟩

/-- `CREATE GRAPH <i>`: the name is added, no triple. No set condition. -/
theorem Dataset.den_ensureGraph (ds : Dataset) (i : WfIri) :
    (ds.ensureGraph i).den = ds.den.addName (.iri i) := by
  unfold Dataset.ensureGraph
  split
  · next h => exact (DatasetDen.addName_of_names ((ds.hasGraph_iff i).mp h)).symm
  · apply DatasetDen.ext
    · intro gn t
      cases gn with
      | none => rfl
      | some n =>
        show (∃ ng ∈ ds.named ++ [({ name := .iri i, graph := [] } : NamedGraph)],
            ng.name = n ∧ ng.graph.mem t = true) ↔
          (∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true)
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ng, hng | rfl, hn, hm⟩
          · exact ⟨ng, hng, hn, hm⟩
          · simp [Graph.mem] at hm
        · rintro ⟨ng, hng, hn, hm⟩
          exact ⟨ng, Or.inl hng, hn, hm⟩
    · intro n
      show n ∈ (ds.named ++ [({ name := .iri i, graph := [] } : NamedGraph)]).map (·.name) ↔
        n ∈ ds.names ∨ n = .iri i
      simp [Dataset.names]

/-- `CLEAR NAMED`: every named graph is empty, every name stays. -/
theorem Dataset.den_clearAllNamed (ds : Dataset) :
    ds.clearAllNamed.den = ds.den.clearNamed := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show ds.default.mem t = true ↔ ds.default.mem t = true ∧ (none : Option Subject) = none
      simp
    | some n =>
      simp [Dataset.den, Dataset.memQuad, Dataset.clearAllNamed, DatasetDen.clearNamed, Graph.mem]
  · intro n
    simp [Dataset.den, Dataset.clearAllNamed, DatasetDen.clearNamed, Dataset.names, List.map_map,
      Function.comp_def]

theorem Dataset.den_empty : Dataset.empty.den = DatasetDen.empty := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none => simp [Dataset.den, Dataset.memQuad, Dataset.empty, DatasetDen.empty, Graph.mem]
    | some n => simp [Dataset.den, Dataset.memQuad, Dataset.empty, DatasetDen.empty]
  · intro n
    simp [Dataset.den, Dataset.names, Dataset.empty, DatasetDen.empty]

/-- Dropping every named graph. -/
theorem Dataset.den_dropAllNamed (ds : Dataset) :
    ({ ds with named := [] } : Dataset).den = ds.den.dropNamed := by
  apply DatasetDen.ext
  · intro gn t
    cases gn with
    | none =>
      show ds.default.mem t = true ↔ ds.default.mem t = true ∧ (none : Option Subject) = none
      simp
    | some n =>
      simp [Dataset.den, Dataset.memQuad, DatasetDen.dropNamed]
  · intro n
    simp [Dataset.den, Dataset.names, DatasetDen.dropNamed]

/-! ### One quad, then many -/

theorem Dataset.den_insertQuad {ds : Dataset} (hs : ds.IsSet) (q : Quad) :
    (ds.insertQuad q).den = ds.den.insertQuads [q] := by
  obtain ⟨g, t⟩ := q
  cases g with
  | none =>
    show ({ ds with default := ds.default.add t } : Dataset).den = _
    rw [Dataset.den_withDefault]
    apply DatasetDen.ext
    · intro gn u
      simp only [DatasetDen.setSlot, DatasetDen.insertQuads, QuadsHold, List.mem_singleton,
        exists_eq_left, quadSlot, Option.map_none, Graph.mem_add_iff]
      cases gn with
      | none =>
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr h.symm
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr h.symm
      | some n => simp
    · intro n
      simp [DatasetDen.setSlot, DatasetDen.insertQuads, quadSlot]
  | some i =>
    show (ds.setGraph i ((ds.graphOf i).add t)).den = _
    rw [Dataset.den_setGraph hs]
    apply DatasetDen.ext
    · intro gn u
      simp only [DatasetDen.setSlot, DatasetDen.insertQuads, QuadsHold, List.mem_singleton,
        exists_eq_left, quadSlot, Option.map_some, Graph.mem_add_iff, ds.mem_graphOf hs]
      by_cases hg : gn = some (.iri i)
      · subst hg
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr h.symm
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr h.symm
      · have hg' : ¬ (some (Subject.iri i) = gn) := fun e => hg e.symm
        simp [hg, hg']
    · intro n
      simp only [DatasetDen.setSlot, DatasetDen.insertQuads, List.mem_singleton, exists_eq_left,
        quadSlot, Option.map_some]

theorem Dataset.den_insertQuads (qs : List Quad) :
    ∀ {ds : Dataset}, ds.IsSet → (ds.insertQuads qs).den = ds.den.insertQuads qs := by
  induction qs with
  | nil => intro ds _; exact (DatasetDen.insertQuads_nil _).symm
  | cons q qs ih =>
    intro ds hs
    show ((ds.insertQuad q).insertQuads qs).den = _
    rw [ih (Dataset.insertQuad_isSet hs q), Dataset.den_insertQuad hs,
      DatasetDen.insertQuads_cons]

theorem Dataset.den_deleteQuad {ds : Dataset} (hs : ds.IsSet) (q : Quad) :
    (ds.deleteQuad q).den = ds.den.deleteQuads [q] := by
  obtain ⟨g, t⟩ := q
  cases g with
  | none =>
    show ({ ds with default := ds.default.remove t } : Dataset).den = _
    rw [Dataset.den_withDefault]
    apply DatasetDen.ext
    · intro gn u
      simp only [DatasetDen.setSlot, DatasetDen.deleteQuads, QuadsHold, List.mem_singleton,
        exists_eq_left, quadSlot, Option.map_none]
      cases gn with
      | none =>
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
        show Graph.mem u (Graph.remove t ds.default) = true ↔ _
        rw [mem_graph_remove, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
          Triple.eqb_iff_key]
        rfl
      | some n => simp
    · intro n
      simp [DatasetDen.setSlot, DatasetDen.deleteQuads]
  | some i =>
    show (if ds.hasGraph i then ds.setGraph i ((ds.graphOf i).remove t) else ds).den = _
    split
    · next hh =>
      rw [Dataset.den_setGraph hs]
      apply DatasetDen.ext
      · intro gn u
        simp only [DatasetDen.setSlot, DatasetDen.deleteQuads, QuadsHold, List.mem_singleton,
          exists_eq_left, quadSlot, Option.map_some]
        by_cases hg : gn = some (.iri i)
        · subst hg
          simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false]
          show Graph.mem u (Graph.remove t (ds.graphOf i)) = true ↔ _
          rw [mem_graph_remove, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true,
            Triple.eqb_iff_key, ds.mem_graphOf hs]
        · have hg' : ¬ (some (Subject.iri i) = gn) := fun e => hg e.symm
          simp [hg, hg']
      · intro n
        simp only [DatasetDen.setSlot, DatasetDen.deleteQuads, Option.some.injEq]
        constructor
        · rintro (h | rfl)
          · exact h
          · exact (ds.hasGraph_iff i).mp hh
        · exact Or.inl
    · next hh =>
      apply DatasetDen.ext
      · intro gn u
        simp only [DatasetDen.deleteQuads, QuadsHold, List.mem_singleton, exists_eq_left,
          quadSlot, Option.map_some]
        constructor
        · intro h
          refine ⟨h, ?_⟩
          rintro ⟨rfl, _⟩
          exact hh ((ds.hasGraph_iff i).mpr (ds.den.named_mem _ u h))
        · exact fun h => h.1
      · intro n; rfl

theorem Dataset.den_deleteQuads (qs : List Quad) :
    ∀ {ds : Dataset}, ds.IsSet → (ds.deleteQuads qs).den = ds.den.deleteQuads qs := by
  induction qs with
  | nil => intro ds _; exact (DatasetDen.deleteQuads_nil _).symm
  | cons q qs ih =>
    intro ds hs
    show ((ds.deleteQuad q).deleteQuads qs).den = _
    rw [ih (Dataset.deleteQuad_isSet hs q), Dataset.den_deleteQuad hs,
      DatasetDen.deleteQuads_cons]

/-- The empty graph has no member. -/
theorem graph_nil_mem (t : Triple) : (Graph.mem t [] = true) ↔ False := by
  simp [Graph.mem]

theorem Dataset.den_withDefault_nil (ds : Dataset) :
    ({ ds with default := [] } : Dataset).den = ds.den.clearSlot none := by
  rw [Dataset.den_withDefault,
    DatasetDen.setSlot_congr _ _ _ (fun _ _ _ h => h) graph_nil_mem,
    DatasetDen.setSlot_false_eq_clearSlot]
  intro n h; cases h

theorem Dataset.den_setGraph_nil {ds : Dataset} (hs : ds.IsSet) {i : WfIri}
    (hh : ds.hasGraph i = true) : (ds.setGraph i []).den = ds.den.clearSlot (some (.iri i)) := by
  rw [Dataset.den_setGraph hs,
    DatasetDen.setSlot_congr _ _ _ (fun _ _ _ h => h) graph_nil_mem,
    DatasetDen.setSlot_false_eq_clearSlot]
  intro n h
  cases h
  exact (ds.hasGraph_iff i).mp hh

end L4Factoidal.RDF

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## The operations of a request on the denotation -/

/-- §3.1.1: the quads of INSERT DATA, blank nodes in the request scope. -/
def insertDataQuads (pre : String) (q : QueryPattern) : List Quad :=
  (collectQuads none q).map (Quad.renameBnodes (freshDataBnode pre))

/-- §3.1.2: the quads of DELETE DATA (a quad with a blank node matches
nothing). -/
def deleteDataQuads (q : QueryPattern) : List Quad :=
  (collectQuads none q).filter (fun q => !q.2.hasBnode)

/-- §3.1.3.3: the quads of DELETE WHERE: the pattern instantiated at each
WHERE solution. -/
def deleteWhereQuads (env : EvalEnv) (ds : Dataset) (p : QueryPattern) : List Quad :=
  (evalWhere env ds p).flatMap (fun mu => instQuads id mu none p.rewriteBnodes)

/-- §3.1.3: the DELETE template at each WHERE solution over the view. -/
def modifyDeleteQuads (env : EvalEnv) (ds : Dataset) (w : Option WfIri)
    (d : Option QueryPattern) (u : List DatasetClause) (p : QueryPattern) : List Quad :=
  match d with
  | none => []
  | some dt =>
    ((evalWhere env (whereDataset ds w u) p).flatMap (fun mu => instQuads id mu none dt)).map
      (redirectQuad w)

/-- §3.1.3: the INSERT template at each WHERE solution over the view, with
blank nodes fresh for each solution. -/
def modifyInsertQuads (env : EvalEnv) (pre : String) (ix : Nat) (ds : Dataset)
    (w : Option WfIri) (i : Option QueryPattern) (u : List DatasetClause) (p : QueryPattern) :
    List Quad :=
  match i with
  | none => []
  | some it => insertQuadsFor pre ix w it (evalWhere env (whereDataset ds w u) p) 0

/-- The graph a `GraphOrDefault` reference reads in the denotation. -/
def refRead (d : DatasetDen) : GraphRef → Triple → Prop
  | .default => d.graph none
  | .graph i => d.graph (some (.iri i))
  | _ => fun _ => False

theorem refRead_key (d : DatasetDen) : ∀ (r : GraphRef) (t u : Triple), t.key = u.key →
    refRead d r t → refRead d r u
  | .default, t, u, h, ht => d.graph_key none t u h ht
  | .graph _, t, u, h, ht => d.graph_key _ t u h ht
  | .named, _, _, _, ht => ht
  | .all, _, _, _, ht => ht

/-- The reference exists: the default graph always (§3.2.2), a named graph
when its name is in the store. -/
def refExistsDen (d : DatasetDen) : GraphRef → Prop
  | .default => True
  | .graph i => d.names (.iri i)
  | _ => False

/-- The graph `G` written at a `GraphOrDefault` reference. -/
def refWrite (d : DatasetDen) (G : Triple → Prop) (hG : ∀ t u, t.key = u.key → G t → G u) :
    GraphRef → DatasetDen
  | .default => d.setSlot none G hG
  | .graph i => d.setSlot (some (.iri i)) G hG
  | _ => d

theorem refWrite_congr (d : DatasetDen) {G G' : Triple → Prop}
    (hG : ∀ t u, t.key = u.key → G t → G u) (hG' : ∀ t u, t.key = u.key → G' t → G' u)
    (e : ∀ t, G t ↔ G' t) : ∀ r, refWrite d G hG r = refWrite d G' hG' r
  | .default => DatasetDen.setSlot_congr _ _ hG hG' e
  | .graph _ => DatasetDen.setSlot_congr _ _ hG hG' e
  | .named => rfl
  | .all => rfl

/-- §3.2.4: the effect of MOVE when the source exists: COPY, then DROP of the
source (the default graph is emptied). -/
def moveDen (d : DatasetDen) (src dst : GraphRef) : DatasetDen :=
  let copied := refWrite d (refRead d src) (refRead_key d src) dst
  match src with
  | .default => copied.clearSlot none
  | .graph i => copied.dropName (.iri i)
  | _ => copied

theorem refAdd_key (d : DatasetDen) (src dst : GraphRef) : ∀ t u : Triple, t.key = u.key →
    (refRead d dst t ∨ refRead d src t) → (refRead d dst u ∨ refRead d src u) := by
  rintro t u h (h1 | h1)
  · exact Or.inl (refRead_key d dst t u h h1)
  · exact Or.inr (refRead_key d src t u h h1)

/-- **The SPARQL 1.1 Update semantics of one operation, on the denotation.**
`OpDen env pre ix ds op d'`: a successful run of `op` on `ds` has the
denotation `d'`. The quad lists of the DATA and WHERE forms are the
implementation's (module header). -/
def OpDen (env : EvalEnv) (pre : String) (ix : Nat) (ds : Dataset) :
    UpdateOp → DatasetDen → Prop
  | .load _ _ _, d' => d' = ds.den
  | .clear _ .default, d' => d' = ds.den.clearSlot none
  | .clear _ .named, d' => d' = ds.den.clearNamed
  | .clear _ .all, d' => d' = ds.den.clearNamed.clearSlot none
  | .clear _ (.graph i), d' => d' = ds.den.clearSlot (some (.iri i))
  | .drop _ .default, d' => d' = ds.den.clearSlot none
  | .drop _ .named, d' => d' = ds.den.dropNamed
  | .drop _ .all, d' => d' = DatasetDen.empty
  | .drop _ (.graph i), d' => d' = ds.den.dropName (.iri i)
  | .create _ i, d' => d' = ds.den.addName (.iri i)
  | .copy _ src dst, d' =>
    (src = dst → d' = ds.den) ∧ (src ≠ dst →
      (refExistsDen ds.den src → d' = refWrite ds.den (refRead ds.den src) (refRead_key _ src) dst) ∧
      (¬ refExistsDen ds.den src → d' = ds.den))
  | .move _ src dst, d' =>
    (src = dst → d' = ds.den) ∧ (src ≠ dst →
      (refExistsDen ds.den src → d' = moveDen ds.den src dst) ∧
      (¬ refExistsDen ds.den src → d' = ds.den))
  | .add _ src dst, d' =>
    (src = dst → d' = ds.den) ∧ (src ≠ dst →
      (refExistsDen ds.den src →
        d' = refWrite ds.den (fun t => refRead ds.den dst t ∨ refRead ds.den src t)
          (refAdd_key _ src dst) dst) ∧
      (¬ refExistsDen ds.den src → d' = ds.den))
  | .insertData q, d' => d' = ds.den.insertQuads (insertDataQuads pre q)
  | .deleteData q, d' => d' = ds.den.deleteQuads (deleteDataQuads q)
  | .deleteWhere p, d' => d' = ds.den.deleteQuads (deleteWhereQuads env ds p)
  | .modify w d i u p, d' =>
    d' = (ds.den.deleteQuads (modifyDeleteQuads env ds w d u p)).insertQuads
      (modifyInsertQuads env pre ix ds w i u p)

/-! ## The implementation has that effect -/

theorem refExists_iff (ds : Dataset) : ∀ r, refExists ds r = true ↔ refExistsDen ds.den r
  | .default => by simp [refExists, refExistsDen]
  | .graph i => ds.hasGraph_iff i
  | .named => by simp [refExists, refExistsDen]
  | .all => by simp [refExists, refExistsDen]

theorem mem_readRef {ds : Dataset} (hs : ds.IsSet) :
    ∀ r t, (readRef ds r).mem t = true ↔ refRead ds.den r t
  | .default, _ => Iff.rfl
  | .graph i, t => ds.mem_graphOf hs i t
  | .named, t => graph_nil_mem t
  | .all, t => graph_nil_mem t

theorem den_writeRef {ds : Dataset} (hs : ds.IsSet) (g : Graph) :
    ∀ r, (writeRef ds g r).den = refWrite ds.den (fun t => g.mem t = true) (graphKey_mem g) r
  | .default => ds.den_withDefault g
  | .graph i => Dataset.den_setGraph hs i g
  | .named => rfl
  | .all => rfl

theorem den_writeRef_read {ds : Dataset} (hs : ds.IsSet) (src dst : GraphRef) :
    (writeRef ds (readRef ds src) dst).den =
      refWrite ds.den (refRead ds.den src) (refRead_key _ src) dst := by
  rw [den_writeRef hs]
  exact refWrite_congr _ _ _ (mem_readRef hs src) dst

theorem den_writeRef_add {ds : Dataset} (hs : ds.IsSet) (src dst : GraphRef) :
    (writeRef ds ((readRef ds dst).union (readRef ds src)) dst).den =
      refWrite ds.den (fun t => refRead ds.den dst t ∨ refRead ds.den src t)
        (refAdd_key _ src dst) dst := by
  rw [den_writeRef hs]
  refine refWrite_congr _ _ _ (fun t => ?_) dst
  show Graph.mem t (Graph.union (readRef ds dst) (readRef ds src)) = true ↔ _
  rw [mem_graph_union, Bool.or_eq_true, mem_readRef hs, mem_readRef hs]

/-- **One operation.** A successful SPARQL 1.1 Update operation on a set gives a
set with the denotation `OpDen` states. -/
theorem applyOp_den (env : EvalEnv) (pre : String) (ix : Nat) {ds ds' : Dataset}
    (hs : ds.IsSet) (op : UpdateOp) (h : applyOp env pre ix ds op = .ok ds') :
    ds'.IsSet ∧ OpDen env pre ix ds op ds'.den := by
  refine ⟨applyOp_isSet env pre ix hs op h, ?_⟩
  cases op with
  | load silent src g =>
    simp only [applyOp] at h
    split at h
    · cases h; rfl
    · cases h
  | clear silent gr =>
    simp only [applyOp] at h
    cases gr <;> simp only [applyClear] at h
    · cases h; exact ds.den_withDefault_nil
    · cases h; exact ds.den_clearAllNamed
    · cases h
      show ({ ds.clearAllNamed with default := [] } : Dataset).den = _
      rw [Dataset.den_withDefault_nil, Dataset.den_clearAllNamed]
    · next i =>
      split at h
      · next hh => cases h; exact Dataset.den_setGraph_nil hs hh
      · next hh =>
        split at h
        · cases h
          exact (DatasetDen.clearSlot_of_not_names (fun hn => hh ((ds.hasGraph_iff i).mpr hn))).symm
        · cases h
  | drop silent gr =>
    simp only [applyOp] at h
    cases gr <;> simp only [applyDrop] at h
    · cases h; exact ds.den_withDefault_nil
    · cases h; exact ds.den_dropAllNamed
    · cases h; exact Dataset.den_empty
    · next i =>
      split at h
      · cases h; exact ds.den_dropGraph i
      · next hh =>
        split at h
        · cases h
          exact (DatasetDen.dropName_of_not_names (fun hn => hh ((ds.hasGraph_iff i).mpr hn))).symm
        · cases h
  | create silent i =>
    simp only [applyOp, applyCreate] at h
    split at h
    · next hh =>
      split at h
      · cases h
        exact (DatasetDen.addName_of_names ((ds.hasGraph_iff i).mp hh)).symm
      · cases h
    · cases h; exact ds.den_ensureGraph i
  | add silent src dst =>
    simp only [applyOp, applyAdd] at h
    simp only [OpDen]
    split at h
    · next he => cases h; exact ⟨fun _ => rfl, fun hne => absurd (beq_iff_eq.mp he) hne⟩
    · next he =>
      have hne : src ≠ dst := fun e => he (beq_iff_eq.mpr e)
      refine ⟨fun e => absurd e hne, fun _ => ?_⟩
      split at h
      · cases h
      · split at h
        · next hx =>
          cases h
          refine ⟨fun hex => absurd ((refExists_iff ds src).mpr hex) (by simpa using hx), fun _ => rfl⟩
        · next hx =>
          cases h
          have hex : refExists ds src = true := by simpa using hx
          exact ⟨fun _ => den_writeRef_add hs src dst,
            fun hn => absurd ((refExists_iff ds src).mp hex) hn⟩
  | move silent src dst =>
    simp only [applyOp, applyMove] at h
    simp only [OpDen]
    split at h
    · next he => cases h; exact ⟨fun _ => rfl, fun hne => absurd (beq_iff_eq.mp he) hne⟩
    · next he =>
      have hne : src ≠ dst := fun e => he (beq_iff_eq.mpr e)
      refine ⟨fun e => absurd e hne, fun _ => ?_⟩
      split at h
      · cases h
      · split at h
        · next hx =>
          cases h
          refine ⟨fun hex => absurd ((refExists_iff ds src).mpr hex) (by simpa using hx), fun _ => rfl⟩
        · next hx =>
          have hex : refExists ds src = true := by simpa using hx
          refine ⟨fun _ => ?_, fun hn => absurd ((refExists_iff ds src).mp hex) hn⟩
          have hc := den_writeRef_read hs src dst
          split at h
          · cases h
            show ({ writeRef ds (readRef ds .default) dst with default := [] } : Dataset).den = _
            rw [Dataset.den_withDefault_nil, hc]
            rfl
          · next i =>
            cases h
            rw [Dataset.den_dropGraph, hc]
            rfl
          · next hd hg =>
            cases h
            rw [hc]
            cases src with
            | default => exact absurd rfl hd
            | graph i => exact absurd rfl (hg i)
            | named => rfl
            | all => rfl
  | copy silent src dst =>
    simp only [applyOp, applyCopy] at h
    simp only [OpDen]
    split at h
    · next he => cases h; exact ⟨fun _ => rfl, fun hne => absurd (beq_iff_eq.mp he) hne⟩
    · next he =>
      have hne : src ≠ dst := fun e => he (beq_iff_eq.mpr e)
      refine ⟨fun e => absurd e hne, fun _ => ?_⟩
      split at h
      · cases h
      · split at h
        · next hex =>
          cases h
          exact ⟨fun _ => den_writeRef_read hs src dst,
            fun hn => absurd ((refExists_iff ds src).mp hex) hn⟩
        · next hx =>
          cases h
          exact ⟨fun hex => absurd ((refExists_iff ds src).mpr hex) hx, fun _ => rfl⟩
  | insertData q =>
    simp only [applyOp, applyInsertData] at h
    cases h
    exact Dataset.den_insertQuads _ hs
  | deleteData q =>
    simp only [applyOp, applyDeleteData] at h
    cases h
    exact Dataset.den_deleteQuads _ hs
  | deleteWhere p =>
    simp only [applyOp] at h
    split at h
    · cases h
    · cases h
      exact Dataset.den_deleteQuads _ hs
  | modify w d i u p =>
    simp only [applyOp] at h
    split at h
    · cases h
    · cases h
      show (applyModify env pre ix ds w d i u p).den = _
      unfold applyModify
      dsimp only
      cases i with
      | none =>
        simp only [modifyInsertQuads, DatasetDen.insertQuads_nil]
        rw [Dataset.den_deleteQuads _ hs]
        rfl
      | some it =>
        rw [Dataset.den_insertQuads _ (Dataset.deleteQuads_isSet _ hs), Dataset.den_deleteQuads _ hs]
        rfl

/-- **A request on the denotation**: the operations in order, each with the
effect `OpDen` states, at the intermediate datasets of the run. -/
def OpsDen (env : EvalEnv) (pre : String) : Nat → Dataset → List UpdateOp → Dataset → Prop
  | _, ds, [], ds' => ds'.den = ds.den
  | ix, ds, op :: rest, ds' => ∃ mid : Dataset, applyOp env pre ix ds op = .ok mid ∧
      OpDen env pre ix ds op mid.den ∧ OpsDen env pre (ix + 1) mid rest ds'

theorem applyOps_den (env : EvalEnv) (pre : String) :
    ∀ (ix : Nat) (ds : Dataset) (ops : List UpdateOp) (ds' : Dataset),
      ds.IsSet → applyOps env pre ix ds ops = .ok ds' → ds'.IsSet ∧ OpsDen env pre ix ds ops ds'
  | _, ds, [], ds', hs, h => by
      simp only [applyOps] at h; cases h; exact ⟨hs, rfl⟩
  | ix, ds, op :: rest, ds', hs, h => by
      simp only [applyOps] at h
      split at h
      · cases h
      · next mid hm =>
        obtain ⟨hms, hmd⟩ := applyOp_den env pre ix hs op hm
        obtain ⟨hs', hr⟩ := applyOps_den env pre (ix + 1) mid rest ds' hms h
        exact ⟨hs', mid, hm, hmd, hr⟩

/-- **A SPARQL 1.1 Update request, on the denotation.** A successful request on
a set gives a set; the operations run in order, each with the effect `OpDen`
states. -/
theorem applyUpdateIn_den (env : EvalEnv) {ds ds' : Dataset} (u : Update) (hs : ds.IsSet)
    (h : applyUpdateIn env ds u = .ok ds') :
    ds'.IsSet ∧ OpsDen env (requestPrefix ds) 0 ds u.ops ds' :=
  applyOps_den env (requestPrefix ds) 0 ds u.ops ds' hs h

/-! ## Axiom audit -/

#print axioms Dataset.den_insertQuads
#print axioms Dataset.den_deleteQuads
#print axioms Dataset.den_setGraph
#print axioms Dataset.den_dropGraph
#print axioms Dataset.den_ensureGraph
#print axioms Dataset.den_clearAllNamed
#print axioms applyOp_den
#print axioms applyUpdateIn_den

end L4Factoidal.SPARQL
