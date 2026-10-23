/-
L4Factoidal.RDF.DatasetDenotation — the denotation of an RDF dataset as
membership, the one target that every store maps into
(https://github.com/danbri/factoidal/issues/975, step 1).

RDF 1.1 Concepts and Abstract Syntax, section 4: "An RDF dataset is a
collection of RDF graphs, and comprises: exactly one default graph ... zero or
more named graphs. Each named graph is a pair consisting of an IRI or a blank
node (the graph name), and an RDF graph. Graph names are unique within an RDF
dataset." Section 3: "An RDF graph is a set of RDF triples."

`DatasetDen` holds two predicates:

* `graph gn t`: the triple `t` is in the default graph (`gn = none`) or in the
  named graph `n` (`gn = some n`);
* `names n`: the dataset has a named graph with the name `n`. The graph can be
  empty: `names n` does not need a triple.

Graph names are unique by the form of the predicates: `graph (some n)` is one
graph for each `n`, so two named graphs with one name cannot be expressed.
Each graph is a set: a predicate has no order and no multiplicity. RDF 1.2
triple terms are terms (`Term.tripleTerm`), so they are in the target with no
special case.

Two conditions hold of every `DatasetDen`:

* `graph_key`: membership is closed under RDF term equality, here the equality
  of `Triple.key` (equivalently `Triple.eqb`, `Triple.eqb_iff_key`);
* `named_mem`: a triple in the named graph `n` makes `n` a graph name.

Which equality. `DecidableEq Triple` is structural: it tells `"chat"@EN` from
`"chat"@en`. RDF 1.1 Concepts section 3.3 says "Lexical representations of
language tags MAY be converted to lower case. The value space of language tags
is always in lower case", so the two literals are one RDF term. Since
https://github.com/danbri/factoidal-core/pull/25 `Triple.eqb` is that RDF term
equality: language tags without case, lexical form, datatype and base
direction exactly. The target uses it (through `Triple.key`), so a store that
lowers language tags and a store that keeps them denote one dataset. Literal
VALUE equality (`Literal.valueEqb`, for example two `rdf:XMLLiteral` lexical
forms with one canonical form) is not used: those are two terms.

Prop, and a Bool view. The target is a specification, so the predicates are
`Prop`, and a store with an infinite or a computed membership can map into it.
For a finite `Dataset` the membership is decidable: `Dataset.memQuadB` is the
Bool view (`Dataset.memQuadB_iff`), and `Decidable` instances are given for
`ds.den.graph gn t`, `ds.den.names n` and `ds.den.mem q`.

What is proved, for every `Dataset`:

* `Dataset.den_graph_iff`, `Dataset.den_names`: membership iff for triples and
  names, in terms of the lists;
* `Dataset.den_eq_of_listQuad_iff`, `Dataset.den_eq_of_sub`,
  `Dataset.den_eq_of_sameB`, `Dataset.den_default_perm`,
  `Dataset.den_default_cons_of_mem`, `Dataset.den_named_perm`: the denotation
  does not change under a permutation or a repetition of triples or of named
  graph entries;
* `Dataset.IsSet.den_default`, `Dataset.IsSet.den_named`,
  `Dataset.IsSet.unique_rep`, `Dataset.IsSet.default_perm_of_den_eq`,
  `Dataset.IsSet.names_perm_of_den_eq`: with `Dataset.IsSet` (PR 26) the lists
  are a duplicate-free enumeration of the denotation, and two sets with one
  denotation are permutations of each other;
* `Dataset.den_toSet`: `Dataset.toSet` keeps the denotation;
* `Dataset.den_eq_ofQuads`: a dataset denotes the quads of its lists and its
  names (`DatasetDen.ofQuads`).

`DatasetDen.ofRows` is the denotation of a store of rows with a decoder (an
id-based store: decode after denote). `DictInjective` is the condition on a
dictionary that the id-based layers need (step 2 of issue 975 proves it).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetSet

namespace L4Factoidal.RDF

/-! ## The target -/

/-- The denotation of an RDF dataset (RDF 1.1 Concepts section 4) as
membership. `graph none` is the default graph, `graph (some n)` the named graph
`n`, `names` the graph names (an empty named graph included). -/
structure DatasetDen where
  graph : Option Subject → Triple → Prop
  names : Subject → Prop
  /-- Membership is closed under RDF term equality (`Triple.key`). -/
  graph_key : ∀ gn t u, t.key = u.key → graph gn t → graph gn u
  /-- A triple in the named graph `n` makes `n` a graph name. -/
  named_mem : ∀ n t, graph (some n) t → names n

/-- Membership of a quad (graph position first). -/
def DatasetDen.mem (d : DatasetDen) (q : Option Subject × Triple) : Prop := d.graph q.1 q.2

/-- Two denotations with the same members are equal. -/
theorem DatasetDen.ext {d e : DatasetDen} (hg : ∀ gn t, d.graph gn t ↔ e.graph gn t)
    (hn : ∀ n, d.names n ↔ e.names n) : d = e := by
  obtain ⟨g1, n1, _, _⟩ := d
  obtain ⟨g2, n2, _, _⟩ := e
  have h1 : g1 = g2 := funext fun x => funext fun t => propext (hg x t)
  have h2 : n1 = n2 := funext fun x => propext (hn x)
  subst h1
  subst h2
  rfl

theorem DatasetDen.graph_eqb (d : DatasetDen) {gn : Option Subject} {t u : Triple}
    (h : t.eqb u = true) (ht : d.graph gn t) : d.graph gn u :=
  d.graph_key gn t u ((Triple.eqb_iff_key t u).mp h) ht

/-! ## Rows with a decoder, quad lists -/

/-- The denotation of a store of rows `R`: `mem` says which rows the store
holds, `dec` decodes a row to a quad (graph position first; `none` refuses the
row), `decl` gives the declared graph names. The names are the declared ones
and the graph names of the decoded rows. -/
def DatasetDen.ofRows {R : Type} (dec : R → Option (Option Subject × Triple)) (mem : R → Prop)
    (decl : Subject → Prop) : DatasetDen where
  graph gn t := ∃ r, mem r ∧ ∃ u, dec r = some (gn, u) ∧ u.key = t.key
  names n := decl n ∨ ∃ r u, mem r ∧ dec r = some (some n, u)
  graph_key := by
    rintro gn t u h ⟨r, hr, v, hv, e⟩
    exact ⟨r, hr, v, hv, e.trans h⟩
  named_mem := by
    rintro n t ⟨r, hr, v, hv, _⟩
    exact Or.inr ⟨r, v, hr, hv⟩

/-- The denotation of a list of quads and a list of declared graph names. -/
def DatasetDen.ofQuads (qs : List (Option Subject × Triple)) (decl : List Subject) : DatasetDen :=
  DatasetDen.ofRows some (· ∈ qs) (· ∈ decl)

theorem DatasetDen.ofQuads_graph (qs : List (Option Subject × Triple)) (decl : List Subject)
    (gn : Option Subject) (t : Triple) :
    (DatasetDen.ofQuads qs decl).graph gn t ↔ ∃ u, (gn, u) ∈ qs ∧ u.key = t.key := by
  constructor
  · rintro ⟨r, hr, u, hu, e⟩
    cases hu
    exact ⟨u, hr, e⟩
  · rintro ⟨u, hu, e⟩
    exact ⟨(gn, u), hu, u, rfl, e⟩

theorem DatasetDen.ofQuads_names (qs : List (Option Subject × Triple)) (decl : List Subject)
    (n : Subject) :
    (DatasetDen.ofQuads qs decl).names n ↔ n ∈ decl ∨ ∃ u, (some n, u) ∈ qs := by
  constructor
  · rintro (h | ⟨r, u, hr, hu⟩)
    · exact Or.inl h
    · cases hu
      exact Or.inr ⟨u, hr⟩
  · rintro (h | ⟨u, hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨(some n, u), u, hu, rfl⟩

/-- The quad lists denote the same dataset when they hold the same quads. -/
theorem DatasetDen.ofQuads_congr {qs qs' : List (Option Subject × Triple)} {decl decl' : List Subject}
    (hq : ∀ q, q ∈ qs ↔ q ∈ qs') (hd : ∀ n, n ∈ decl ↔ n ∈ decl') :
    DatasetDen.ofQuads qs decl = DatasetDen.ofQuads qs' decl' := by
  apply DatasetDen.ext
  · intro gn t
    rw [DatasetDen.ofQuads_graph, DatasetDen.ofQuads_graph]
    simp only [hq]
  · intro n
    rw [DatasetDen.ofQuads_names, DatasetDen.ofQuads_names]
    simp only [hq, hd]

/-! ## Dictionaries -/

/-- A dictionary `dec` from ids to terms is injective on the ids in use, up to
RDF term equality: two ids in use whose terms have one join key are one id. So
one term (up to the case of its language tags) never has two ids, and, `dec`
being a function, one id never names two terms. Step 2 of
https://github.com/danbri/factoidal/issues/975 proves this for the id-based
stores; the theorems of step 1 take it as a hypothesis. -/
def DictInjective {I : Type} (dec : I → Term) (inUse : I → Prop) : Prop :=
  ∀ x y, inUse x → inUse y → (dec x).joinKey = (dec y).joinKey → x = y

/-! ## The denotation of a `Dataset` -/

theorem Graph.mem_of_key_eq {g : Graph} {t u : Triple} (h : t.key = u.key)
    (ht : g.mem t = true) : g.mem u = true := by
  obtain ⟨v, hv, e⟩ := (Graph.mem_iff_key t g).mp ht
  exact (Graph.mem_iff_key u g).mpr ⟨v, hv, e.trans h⟩

/-- The denotation of a dataset: engine membership (`Dataset.memQuad`, by
`Triple.eqb`) and the names of its named-graph entries. -/
def Dataset.den (ds : Dataset) : DatasetDen where
  graph gn t := ds.memQuad t gn
  names n := n ∈ ds.names
  graph_key := by
    intro gn t u h ht
    cases gn with
    | none => exact Graph.mem_of_key_eq h ht
    | some n =>
      obtain ⟨ng, hng, hn, hm⟩ := ht
      exact ⟨ng, hng, hn, Graph.mem_of_key_eq h hm⟩
  named_mem := by
    intro n t ht
    obtain ⟨ng, hng, hn, _⟩ := ht
    exact List.mem_map.mpr ⟨ng, hng, hn⟩

theorem Dataset.den_graph (ds : Dataset) (gn : Option Subject) (t : Triple) :
    ds.den.graph gn t ↔ ds.memQuad t gn := Iff.rfl

theorem Dataset.den_names (ds : Dataset) (n : Subject) : ds.den.names n ↔ n ∈ ds.names := Iff.rfl

theorem Dataset.memQuad_iff_listQuad (ds : Dataset) (t : Triple) (gn : Option Subject) :
    ds.memQuad t gn ↔ ∃ u, ds.listQuad u gn ∧ u.key = t.key := by
  cases gn with
  | none =>
    show ds.default.mem t = true ↔ ∃ u, u ∈ ds.default ∧ u.key = t.key
    rw [Graph.mem_iff_key]
  | some n =>
    show (∃ ng ∈ ds.named, ng.name = n ∧ ng.graph.mem t = true) ↔
      ∃ u, (∃ ng ∈ ds.named, ng.name = n ∧ u ∈ ng.graph) ∧ u.key = t.key
    constructor
    · rintro ⟨ng, hng, hn, hm⟩
      obtain ⟨u, hu, e⟩ := (Graph.mem_iff_key t _).mp hm
      exact ⟨u, ⟨ng, hng, hn, hu⟩, e⟩
    · rintro ⟨u, ⟨ng, hng, hn, hu⟩, e⟩
      exact ⟨ng, hng, hn, (Graph.mem_iff_key t _).mpr ⟨u, hu, e⟩⟩

/-- **Membership iff, triples.** A triple is in a graph of the denotation
exactly when a list entry of that graph is RDF-term-equal to it. -/
theorem Dataset.den_graph_iff (ds : Dataset) (gn : Option Subject) (t : Triple) :
    ds.den.graph gn t ↔ ∃ u, ds.listQuad u gn ∧ u.key = t.key :=
  ds.memQuad_iff_listQuad t gn

/-- Every list entry is a member. -/
theorem Dataset.den_graph_of_listQuad {ds : Dataset} {u : Triple} {gn : Option Subject}
    (h : ds.listQuad u gn) : ds.den.graph gn u :=
  (ds.den_graph_iff gn u).mpr ⟨u, h, rfl⟩

/-! ### The Bool view -/

/-- Engine membership as a Bool. -/
def Dataset.memQuadB (ds : Dataset) (u : Triple) : Option Subject → Bool
  | none => ds.default.mem u
  | some n => ds.named.any (fun ng => ng.name == n && ng.graph.mem u)

theorem Dataset.memQuadB_iff (ds : Dataset) (u : Triple) (gn : Option Subject) :
    ds.memQuadB u gn = true ↔ ds.memQuad u gn := by
  cases gn with
  | none => exact Iff.rfl
  | some n =>
    simp only [Dataset.memQuadB, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact Iff.rfl

instance (ds : Dataset) (gn : Option Subject) (t : Triple) : Decidable (ds.den.graph gn t) :=
  decidable_of_iff _ (ds.memQuadB_iff t gn)

instance (ds : Dataset) (n : Subject) : Decidable (ds.den.names n) :=
  inferInstanceAs (Decidable (n ∈ ds.names))

instance (ds : Dataset) (q : Option Subject × Triple) : Decidable (ds.den.mem q) :=
  inferInstanceAs (Decidable (ds.den.graph q.1 q.2))

/-! ### The quads of the lists -/

/-- The list entries of a dataset as quads, graph position first. -/
def Dataset.listQuads (ds : Dataset) : List (Option Subject × Triple) :=
  ds.default.map (fun t => (none, t)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (some ng.name, t)))

theorem Dataset.mem_listQuads (ds : Dataset) (gn : Option Subject) (u : Triple) :
    (gn, u) ∈ ds.listQuads ↔ ds.listQuad u gn := by
  cases gn with
  | none =>
    simp [Dataset.listQuads, Dataset.listQuad]
  | some n =>
    simp only [Dataset.listQuads, Dataset.listQuad, List.mem_append, List.mem_map, List.mem_flatMap,
      Prod.mk.injEq, reduceCtorEq, false_and, and_false, exists_false, false_or, Option.some.injEq]
    constructor
    · rintro ⟨ng, hng, v, hv, hn, rfl⟩
      exact ⟨ng, hng, hn, hv⟩
    · rintro ⟨ng, hng, hn, hu⟩
      exact ⟨ng, hng, u, hu, hn, rfl⟩

/-- A dataset denotes the quads of its lists and its graph names. -/
theorem Dataset.den_eq_ofQuads (ds : Dataset) : ds.den = DatasetDen.ofQuads ds.listQuads ds.names := by
  apply DatasetDen.ext
  · intro gn t
    rw [Dataset.den_graph_iff, DatasetDen.ofQuads_graph]
    simp only [Dataset.mem_listQuads]
  · intro n
    rw [Dataset.den_names, DatasetDen.ofQuads_names]
    constructor
    · exact Or.inl
    · rintro (h | ⟨u, hu⟩)
      · exact h
      · exact ds.den.named_mem n u (Dataset.den_graph_of_listQuad ((ds.mem_listQuads _ u).mp hu))

/-! ## Order and repetition do not change the denotation -/

/-- Two datasets whose lists hold the same entries in each graph, and the same
names, have one denotation, whatever the order and the repetitions. -/
theorem Dataset.den_eq_of_listQuad_iff {ds₁ ds₂ : Dataset}
    (hq : ∀ u gn, ds₁.listQuad u gn ↔ ds₂.listQuad u gn)
    (hn : ∀ n, n ∈ ds₁.names ↔ n ∈ ds₂.names) : ds₁.den = ds₂.den :=
  DatasetDen.ext (fun gn t => by rw [Dataset.den_graph_iff, Dataset.den_graph_iff]; simp only [hq]) hn

/-- Two datasets each of whose list entries is a member of the other (up to
RDF term equality), with the same names, have one denotation. -/
theorem Dataset.den_eq_of_sub {ds₁ ds₂ : Dataset}
    (h12 : ∀ u gn, ds₁.listQuad u gn → ds₂.memQuad u gn)
    (h21 : ∀ u gn, ds₂.listQuad u gn → ds₁.memQuad u gn)
    (hn : ∀ n, n ∈ ds₁.names ↔ n ∈ ds₂.names) : ds₁.den = ds₂.den := by
  apply DatasetDen.ext _ hn
  intro gn t
  rw [Dataset.den_graph_iff, Dataset.den_graph_iff]
  constructor
  · rintro ⟨u, hu, e⟩
    exact (ds₂.den_graph_iff gn t).mp (ds₂.den.graph_key gn u t e (h12 u gn hu))
  · rintro ⟨u, hu, e⟩
    exact (ds₁.den_graph_iff gn t).mp (ds₁.den.graph_key gn u t e (h21 u gn hu))

/-- Every list entry of `ds₁` is a member of `ds₂` and every name of `ds₁` is
a name of `ds₂`, as a Bool. -/
def Dataset.SubB (ds₁ ds₂ : Dataset) : Bool :=
  ds₁.listQuads.all (fun q => ds₂.memQuadB q.2 q.1) && ds₁.names.all (fun n => decide (n ∈ ds₂.names))

/-- The two datasets denote one dataset, as a Bool check (`den_eq_of_sameB`). -/
def Dataset.SameB (ds₁ ds₂ : Dataset) : Bool := Dataset.SubB ds₁ ds₂ && Dataset.SubB ds₂ ds₁

theorem Dataset.SubB_spec {ds₁ ds₂ : Dataset} (h : Dataset.SubB ds₁ ds₂ = true) :
    (∀ u gn, ds₁.listQuad u gn → ds₂.memQuad u gn) ∧ ∀ n, n ∈ ds₁.names → n ∈ ds₂.names := by
  simp only [Dataset.SubB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine ⟨fun u gn hu => ?_, h.2⟩
  exact (ds₂.memQuadB_iff u gn).mp (h.1 (gn, u) ((ds₁.mem_listQuads gn u).mpr hu))

theorem Dataset.den_eq_of_sameB (ds₁ ds₂ : Dataset) (h : Dataset.SameB ds₁ ds₂ = true) :
    ds₁.den = ds₂.den := by
  simp only [Dataset.SameB, Bool.and_eq_true] at h
  obtain ⟨a1, a2⟩ := Dataset.SubB_spec h.1
  obtain ⟨b1, b2⟩ := Dataset.SubB_spec h.2
  exact Dataset.den_eq_of_sub a1 b1 (fun n => ⟨a2 n, b2 n⟩)

/-- A permutation of the default graph does not change the denotation. -/
theorem Dataset.den_default_perm {g₁ g₂ : Graph} (hp : g₁.Perm g₂) (named : List NamedGraph) :
    ({ default := g₁, named := named } : Dataset).den = ({ default := g₂, named := named } : Dataset).den :=
  Dataset.den_eq_of_listQuad_iff
    (fun u gn => by
      cases gn with
      | none => exact hp.mem_iff
      | some n => exact Iff.rfl)
    (fun _ => Iff.rfl)

/-- A repeated triple of the default graph does not change the denotation. -/
theorem Dataset.den_default_cons_of_mem {t : Triple} {g : Graph} (h : t ∈ g) (named : List NamedGraph) :
    ({ default := t :: g, named := named } : Dataset).den = ({ default := g, named := named } : Dataset).den :=
  Dataset.den_eq_of_listQuad_iff
    (fun u gn => by
      cases gn with
      | none =>
        show u ∈ t :: g ↔ u ∈ g
        constructor
        · intro hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact h
          · exact hu
        · exact List.mem_cons_of_mem t
      | some n => exact Iff.rfl)
    (fun _ => Iff.rfl)

/-- A permutation of the named-graph entries does not change the denotation. -/
theorem Dataset.den_named_perm {l₁ l₂ : List NamedGraph} (hp : l₁.Perm l₂) (default : Graph) :
    ({ default := default, named := l₁ } : Dataset).den = ({ default := default, named := l₂ } : Dataset).den :=
  Dataset.den_eq_of_listQuad_iff
    (fun u gn => by
      cases gn with
      | none => exact Iff.rfl
      | some n =>
        show (∃ ng ∈ l₁, ng.name = n ∧ u ∈ ng.graph) ↔ ∃ ng ∈ l₂, ng.name = n ∧ u ∈ ng.graph
        simp only [hp.mem_iff])
    (fun _ => (hp.map (·.name)).mem_iff)

/-! ## Sets: the lists enumerate the denotation without duplicates -/

private theorem eq_of_mem_nodup_map {α β : Type} (f : α → β) :
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
      · exact eq_of_mem_nodup_map f h.2 ha' hb' hf

/-- For a set, the default graph has no two RDF-term-equal entries, and its
keys are exactly the members of the default graph of the denotation. -/
theorem Dataset.IsSet.den_default {ds : Dataset} (h : ds.IsSet) :
    ds.default.KeyNodup ∧ ∀ t, ds.den.graph none t ↔ t.key ∈ ds.default.map Triple.key :=
  ⟨h.default, fun t => Graph.mem_iff_keys t ds.default⟩

/-- For a set, each named-graph entry is the whole graph of its name: it has
no two RDF-term-equal entries, and its keys are exactly the members of the
graph of that name in the denotation. -/
theorem Dataset.IsSet.den_named {ds : Dataset} (h : ds.IsSet) {ng : NamedGraph} (hng : ng ∈ ds.named) :
    ng.graph.KeyNodup ∧ ∀ t, ds.den.graph (some ng.name) t ↔ t.key ∈ ng.graph.map Triple.key := by
  refine ⟨h.graphs ng hng, fun t => ?_⟩
  rw [← Graph.mem_iff_keys]
  constructor
  · rintro ⟨ng', hng', hn, hm⟩
    have e : ng' = ng := eq_of_mem_nodup_map (fun x : NamedGraph => x.name) (l := ds.named) h.names hng' hng hn
    exact e ▸ hm
  · intro hm
    exact ⟨ng, hng, rfl, hm⟩

/-- For a set, one graph has one list entry for each RDF term-equality class:
two entries of one graph with one key are one entry. -/
theorem Dataset.IsSet.unique_rep {ds : Dataset} (h : ds.IsSet) {gn : Option Subject} {u v : Triple}
    (hu : ds.listQuad u gn) (hv : ds.listQuad v gn) (e : u.key = v.key) : u = v := by
  cases gn with
  | none => exact eq_of_mem_nodup_map Triple.key h.default hu hv e
  | some n =>
    obtain ⟨ng1, h1, n1, hu'⟩ := hu
    obtain ⟨ng2, h2, n2, hv'⟩ := hv
    have e12 : ng1 = ng2 := eq_of_mem_nodup_map (fun x : NamedGraph => x.name) (l := ds.named) h.names h1 h2 (n1.trans n2.symm)
    subst e12
    exact eq_of_mem_nodup_map Triple.key (h.graphs ng1 h1) hu' hv' e

/-- Two sets with one denotation have default graphs whose keys are a
permutation of each other. -/
theorem Dataset.IsSet.default_perm_of_den_eq {ds ds' : Dataset} (h : ds.IsSet) (h' : ds'.IsSet)
    (e : ds.den = ds'.den) : (ds.default.map Triple.key).Perm (ds'.default.map Triple.key) := by
  apply (List.perm_ext_iff_of_nodup h.default h'.default).2
  intro k
  constructor
  · intro hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
    have hm : ds.den.graph none t := (h.den_default.2 t).mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)
    rw [e] at hm
    exact (h'.den_default.2 t).mp hm
  · intro hk
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hk
    have hm : ds'.den.graph none t := (h'.den_default.2 t).mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)
    rw [← e] at hm
    exact (h.den_default.2 t).mp hm

/-- Two sets with one denotation have graph-name lists that are a permutation
of each other. -/
theorem Dataset.IsSet.names_perm_of_den_eq {ds ds' : Dataset} (h : ds.IsSet) (h' : ds'.IsSet)
    (e : ds.den = ds'.den) : ds.names.Perm ds'.names := by
  apply (List.perm_ext_iff_of_nodup h.names h'.names).2
  intro n
  show ds.den.names n ↔ ds'.den.names n
  rw [e]

instance (g : Graph) : Decidable g.KeyNodup := inferInstanceAs (Decidable ((g.map Triple.key).Nodup))

/-- The set check as a Bool. -/
def Dataset.IsSetB (ds : Dataset) : Bool :=
  decide ds.default.KeyNodup && decide ds.names.Nodup && ds.named.all (fun ng => decide ng.graph.KeyNodup)

theorem Dataset.isSetB_iff (ds : Dataset) : ds.IsSetB = true ↔ ds.IsSet := by
  simp only [Dataset.IsSetB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩⟩

/-! ## `toSet` keeps the denotation -/

/-- `Dataset.toSet` (PR 26) does not change the denotation. -/
theorem Dataset.den_toSet (ds : Dataset) : ds.toSet.den = ds.den :=
  DatasetDen.ext (fun gn t => Dataset.memQuad_toSet ds t gn) (fun n => Dataset.names_toSet ds n)

/-- Every dataset has a set with its denotation. -/
theorem Dataset.exists_isSet_den (ds : Dataset) : ∃ s : Dataset, s.IsSet ∧ s.den = ds.den :=
  ⟨ds.toSet, ds.toSet_isSet, ds.den_toSet⟩

#print axioms DatasetDen.ext
#print axioms Dataset.den_graph_iff
#print axioms Dataset.den_eq_ofQuads
#print axioms Dataset.den_eq_of_sameB
#print axioms Dataset.den_named_perm
#print axioms Dataset.IsSet.unique_rep
#print axioms Dataset.IsSet.den_named
#print axioms Dataset.IsSet.default_perm_of_den_eq
#print axioms Dataset.den_toSet

end L4Factoidal.RDF
