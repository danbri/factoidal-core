/-
L4Factoidal.Storage.Sbm11.DenotationTheorems — the SBM11 layers mapped into
the one dataset denotation `RDF.DatasetDen`
(https://github.com/danbri/factoidal/issues/975, step 1). No code of SBM11
changes; this module adds definitions and theorems.

The generation in memory (`MemGen.denote`, a `Dataset` in SPO row order):

* `MemGen.den G := G.denote.den`; `MemGen.den_default`, `MemGen.den_named`,
  `MemGen.den_names`: membership iff, in terms of the rows of `G`;
* `PackSpec.den_packSpec`: the generation that `packSpec` makes denotes its
  input quads and declared graphs, `DatasetDen.ofQuads`. There is no
  hypothesis on the input: the packer lowers language tags, and the target
  compares them without case (`PackSpec.key_normTriple`), so the input and the
  generation denote one dataset;
* `PackSpec.harness_where_allowed_den`: the WHERE clause theorem of the harness
  (`harness_where_allowed_input`, PR 31) for any dataset `D` that is a set,
  whose triples are their own keys, and that denotes the input. `DatasetOf`, the
  list-level condition of PR 31, follows from these (`PackSpec.datasetOf_of_den`).

The delta overlay (`Overlay.denote`, `Overlay.denoteNamed`, `Row → Bool` and
`Nat → Bool` over ids) with the dictionary `dec : Nat → Option Term` as a
parameter (decode after denote; for SBM11 `OverlayDict.ovDec keys ov`):

* `Overlay.overlayDen dec base bn st`: `DatasetDen.ofRows` over the rows that
  `denote base st` holds, decoded by `Overlay.rowQuad?`, with the graph names
  that `denoteNamed bn st` holds, decoded;
* `Overlay.overlayDen_add`, `Overlay.overlayDen_create_names`,
  `Overlay.overlayDen_create_graph`: INSERT and CREATE, no hypothesis on the
  dictionary;
* `Overlay.overlayDen_remove`: DELETE removes the quad from the dataset, under
  `RDF.DictInjective` (step 2, PR 32; for SBM11
  `DictInjectiveTheorems.overlay_dictInjective`) and `Overlay.HeldFolded`
  (the terms of the dictionary have lower-case language tags). Without these,
  another row with other ids could decode to an RDF-term-equal quad and stay.
  `HeldFolded` is open here: SBM11 folds every term before it gives an id
  (`normalizeTerm`), and the proof that the held terms are their own join keys
  is not in this module.

Normalisation. The target compares language tags without case. SBM11 gives one
id per RDF term (`MemGen.cid_eq_iff_eqb`), so it maps into the target with the
fold it already does. IBK, PTD and the other stores of
https://github.com/danbri/factoidal/issues/977 give one id per structural term:
their decoded triples map into the target (membership is by key), but a theorem
that compares their ids needs a fold before the ids are assigned.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.Storage.Sbm11.PackSpecInputTheorems
import L4Factoidal.Storage.Sbm11.OverlayTheorems
import L4Factoidal.RDF.DictInjective
import L4Factoidal.Storage.Sbm11.DictInjectiveTheorems

/-! ## The generation in memory -/

namespace L4Factoidal.Storage.Sbm11.MemGen

open L4Factoidal.RDF

/-- The dataset a generation denotes. -/
def MemGen.den (G : MemGen) : DatasetDen := G.denote.den

theorem MemGen.den_default (G : MemGen) (t : Triple) :
    G.den.graph none t ↔ ∃ u ∈ G.graphOf 0, u.key = t.key := by
  rw [MemGen.den, Dataset.den_graph_iff]
  exact ⟨fun ⟨u, hu, e⟩ => ⟨u, hu, e⟩, fun ⟨u, hu, e⟩ => ⟨u, hu, e⟩⟩

theorem MemGen.den_named (G : MemGen) (n : Subject) (t : Triple) :
    G.den.graph (some n) t ↔
      ∃ x ∈ G.named.toList, subjOf (G.dec x) = n ∧ ∃ u ∈ G.graphOf x, u.key = t.key := by
  rw [MemGen.den, Dataset.den_graph_iff]
  show (∃ u, (∃ ng ∈ G.named.toList.map (fun x => (⟨subjOf (G.dec x), G.graphOf x⟩ : NamedGraph)),
      ng.name = n ∧ u ∈ ng.graph) ∧ u.key = t.key) ↔ _
  simp only [List.mem_map]
  constructor
  · rintro ⟨u, ⟨_, ⟨x, hx, rfl⟩, hn, hu⟩, e⟩
    exact ⟨x, hx, hn, u, hu, e⟩
  · rintro ⟨x, hx, hn, u, hu, e⟩
    exact ⟨u, ⟨_, ⟨x, hx, rfl⟩, hn, hu⟩, e⟩

theorem MemGen.den_names (G : MemGen) (n : Subject) :
    G.den.names n ↔ ∃ x ∈ G.named.toList, subjOf (G.dec x) = n := by
  rw [MemGen.den, Dataset.den_names]
  show n ∈ (G.named.toList.map (fun x => (⟨subjOf (G.dec x), G.graphOf x⟩ : NamedGraph))).map (·.name) ↔ _
  simp

end L4Factoidal.Storage.Sbm11.MemGen

/-! ## The packer: the generation denotes its input -/

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.AllowedPerm

/-- Lowering the language tags of a term does not change its join key. -/
theorem joinKey_normalizeTerm : ∀ t : Term, (normalizeTerm t).joinKey = t.joinKey
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal l => by
      obtain ⟨⟨lex, dt, tag, dir⟩, hwf⟩ := l
      cases tag with
      | none => rfl
      | some tg =>
        simp only [normalizeTerm, normalizeLit]
        split
        · simp [Term.joinKey, Literal.joinKey, FilterIdTheorems.string_toLower_idem]
        · rfl
  | .tripleTerm s p o => by
      simp only [normalizeTerm, Term.joinKey, joinKey_normalizeTerm o]

/-- The packer's normalisation does not change the key of a triple. -/
theorem key_normTriple (t : Triple) : (normTriple t).key = t.key := by
  simp only [normTriple, Triple.key, joinKey_normalizeTerm]

theorem mem_map_swap {α β : Type} (qs : List (α × β)) (a : β) (b : α) :
    (a, b) ∈ qs.map Prod.swap ↔ (b, a) ∈ qs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨⟨x, y⟩, hq, he⟩
    simp only [Prod.swap, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact hq
  · intro hq
    exact ⟨(b, a), hq, rfl⟩

/-- The quads of the input with the graph position first. -/
def inputDen (qs : List Quad) (decl : List Subject) : DatasetDen :=
  DatasetDen.ofQuads (qs.map Prod.swap) decl

/-- **The generation denotes its input.** For `packSpec B qs decl = some (G, F)`,
the dataset of the generation is the dataset of the input quads and the
declared graph names, as RDF datasets (sets of triples per graph, RDF term
equality, empty declared graphs included). -/
theorem den_packSpec (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) : G.den = inputDen qs decl := by
  apply DatasetDen.ext
  · intro gn t
    rw [MemGen.den, Dataset.den_graph_iff, inputDen, DatasetDen.ofQuads_graph]
    have hl : ∀ u, G.denote.listQuad u gn ↔ ∃ q ∈ qs, q.2 = gn ∧ normTriple q.1 = u := by
      intro u
      cases gn with
      | none => exact packSpec_default B qs decl G F h u
      | some n => exact packSpec_named B qs decl G F h n u
    simp only [hl, mem_map_swap]
    constructor
    · rintro ⟨u, ⟨q, hq, hg, rfl⟩, e⟩
      refine ⟨q.1, ?_, by rw [← key_normTriple]; exact e⟩
      rw [← hg]
      exact hq
    · rintro ⟨u, hu, e⟩
      exact ⟨normTriple u, ⟨(u, gn), hu, rfl, rfl⟩, by rw [key_normTriple]; exact e⟩
  · intro n
    rw [MemGen.den, Dataset.den_names, inputDen, DatasetDen.ofQuads_names]
    have hn : n ∈ G.denote.names ↔ ∃ ng ∈ G.denote.named, ng.name = n := by
      simp [Dataset.names]
    rw [hn, packSpec_names B qs decl G F h n, List.mem_filterMap]
    simp only [mem_map_swap]
    constructor
    · rintro (⟨q, hq, hg⟩ | hd)
      · refine Or.inr ⟨q.1, ?_⟩
        rw [← hg]
        exact hq
      · exact Or.inl hd
    · rintro (hd | ⟨u, hu⟩)
      · exact Or.inr hd
      · exact Or.inl ⟨(u, some n), hu, rfl⟩

theorem Triple.key_eq_self {t : Triple} (h : t.o.joinKey = t.o) : t.key = t := by
  obtain ⟨s, p, o⟩ := t
  simp only [Triple.key] at h ⊢
  rw [h]

/-- `DatasetOf` (PR 31) from the denotation: a set whose triples are their own
keys and that denotes the input. -/
theorem datasetOf_of_den (qs : List Quad) (decl : List Subject) (D : Dataset)
    (hset : D.IsSet) (hfixD : ∀ u gn, D.listQuad u gn → u.key = u)
    (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o)
    (hden : D.den = inputDen qs decl) : DatasetOf qs decl D := by
  have hl : ∀ gn tr, D.listQuad tr gn ↔ ∃ q ∈ qs, q.2 = gn ∧ q.1 = tr := by
    intro gn tr
    constructor
    · intro ht
      have hm := Dataset.den_graph_of_listQuad ht
      rw [hden, inputDen, DatasetDen.ofQuads_graph] at hm
      obtain ⟨u, hu, e⟩ := hm
      rw [mem_map_swap] at hu
      have hu' : u.key = u := Triple.key_eq_self (hfix (u, gn) hu)
      refine ⟨(u, gn), hu, rfl, ?_⟩
      show u = tr
      rw [← hu', e, hfixD tr gn ht]
    · rintro ⟨q, hq, hg, rfl⟩
      have hm : (inputDen qs decl).graph gn q.1 := by
        rw [inputDen, DatasetDen.ofQuads_graph]
        exact ⟨q.1, (mem_map_swap _ _ _).mpr (hg ▸ hq), rfl⟩
      rw [← hden, Dataset.den_graph_iff] at hm
      obtain ⟨u, hu, e⟩ := hm
      have e' : u = q.1 := by rw [← hfixD u gn hu, e, Triple.key_eq_self (hfix q hq)]
      exact e' ▸ hu
  refine ⟨fun tr => hl none tr, fun g tr => hl (some g) tr, ?_, hset.default.nodup, hset.names,
    fun ng h => (hset.graphs ng h).nodup⟩
  intro g
  have hn : (∃ ng ∈ D.named, ng.name = g) ↔ D.den.names g := by
    rw [Dataset.den_names]
    simp [Dataset.names]
  rw [hn, hden, inputDen, DatasetDen.ofQuads_names, List.mem_filterMap]
  simp only [mem_map_swap]
  constructor
  · rintro (hd | ⟨u, hu⟩)
    · exact Or.inr hd
    · exact Or.inl ⟨(u, some g), hu, rfl⟩
  · rintro (⟨q, hq, hg⟩ | hd)
    · refine Or.inr ⟨q.1, ?_⟩
      rw [← hg]
      exact hq
    · exact Or.inl hd

open L4Factoidal.Storage.Sbm11.IdQuery in
open L4Factoidal.Storage.Sbm11.IdGroup (nestedTableM queryEnvOf Allowed) in
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (WhereOk) in
open L4Factoidal.Storage.Sbm11.LocalVocab in
/-- **The WHERE clause theorem of the harness, through the denotation.**
`harness_where_allowed_input` for every dataset `D` that is a set
(`Dataset.IsSet`), whose triples are their own keys (language tags in lower
case), and that denotes the input quads (`D.den = inputDen qs decl`). -/
theorem harness_where_allowed_den (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) (D : Dataset)
    (hset : D.IsSet) (hfixD : ∀ u gn, D.listQuad u gn → u.key = u) (hden : D.den = inputDen qs decl)
    (hnorm : ∀ q ∈ qs, normTriple q.1 = q.1) (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o)
    (clock : EvalEnv) (base : Option String)
    (plan : Plan) (p : QueryPattern) (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hq : QHyps G.cid p) (hp : PermOk p) :
    (∃ e, nestedTableM F.store plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM F.store plan (queryEnvOf clock base) =
          pure (t, F.store.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
          G.denote.default {} t s ∧
        Allowed { queryEnvOf clock base with dataset := some D } D p D.default
          (t.idRows.map (OptJoin.decRow (decV G.dec s.vocab))) :=
  harness_where_allowed_input B qs decl G F h D (datasetOf_of_den qs decl D hset hfixD hfix hden)
    hnorm hfix clock base plan p hnest hdsq hq hp

#print axioms joinKey_normalizeTerm
#print axioms den_packSpec
#print axioms datasetOf_of_den
#print axioms harness_where_allowed_den

end L4Factoidal.Storage.Sbm11.PackSpec

/-! ## The delta overlay -/

namespace L4Factoidal.Storage.Sbm11.Overlay

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.Block (Row)
open L4Factoidal.Storage.Sbm11.OverlayTheorems

/-- A term as a predicate IRI. -/
def iriOf? : Term → Option WfIri
  | .iri i => some i
  | _ => none

/-- The subject of an id: its term, when that is an IRI or a blank node. -/
def subjAt (dec : Nat → Option Term) (n : Nat) : Option Subject := (dec n).bind Term.toSubject?

/-- The predicate of an id: its term, when that is an IRI. -/
def iriAt (dec : Nat → Option Term) (n : Nat) : Option WfIri := (dec n).bind iriOf?

/-- The graph position of a graph id: 0 is the default graph, another id names
the graph its term names (an IRI or a blank node). -/
def graphOf? (dec : Nat → Option Term) (g : Nat) : Option (Option Subject) :=
  if g = 0 then some none else (subjAt dec g).map some

/-- The quad an SPO-order row decodes to; `none` when an id names no term or a
position does not decode to a term of its kind. -/
def rowQuad? (dec : Nat → Option Term) (r : Row) : Option (Option Subject × Triple) :=
  match graphOf? dec r.g, subjAt dec r.c0, iriAt dec r.c1, dec r.c2 with
  | some g, some s, some p, some o => some (g, ⟨s, p, o⟩)
  | _, _, _, _ => none

/-- The dataset of the overlaid generation: the rows that `denote base st`
holds, decoded, and the graph names that `denoteNamed bn st` holds, decoded.
`dec` is the dictionary (`OverlayDict.ovDec keys ov` for SBM11). -/
def overlayDen (dec : Nat → Option Term) (base : Row → Bool) (bn : Nat → Bool) (st : State) : DatasetDen :=
  DatasetDen.ofRows (rowQuad? dec) (fun r => denote base st r = true)
    (fun n => ∃ x, denoteNamed bn st x = true ∧ subjAt dec x = some n)

/-- The ids of a row are in use (the graph id when it is not the default
graph). -/
def RowInUse (used : Nat → Prop) (r : Row) : Prop :=
  used r.c0 ∧ used r.c1 ∧ used r.c2 ∧ (r.g ≠ 0 → used r.g)

/-- The terms of the store have their language tags in lower case: each is its
own join key. SBM11 folds a term before it gives an id (`Session.idOf`,
`normalizeTerm`; `OverlayDict.vocabAdd`). A store that gives one id per
structural term (https://github.com/danbri/factoidal/issues/977) does not
satisfy it. -/
def HeldFolded (dom : Term → Prop) : Prop := ∀ t, dom t → t.joinKey = t

theorem rowQuad?_eq_some (dec : Nat → Option Term) (r : Row) (gn : Option Subject) (u : Triple) :
    rowQuad? dec r = some (gn, u) ↔
      graphOf? dec r.g = some gn ∧ subjAt dec r.c0 = some u.s ∧ iriAt dec r.c1 = some u.p ∧
        dec r.c2 = some u.o := by
  obtain ⟨s, p, o⟩ := u
  unfold rowQuad?
  cases h0 : graphOf? dec r.g <;> cases h1 : subjAt dec r.c0 <;> cases h2 : iriAt dec r.c1 <;>
    cases h3 : dec r.c2 <;> simp [eq_comm]

theorem subjAt_eq {dec : Nat → Option Term} {n : Nat} {s : Subject} (h : subjAt dec n = some s) :
    dec n = some s.toTerm := by
  unfold subjAt at h
  cases hd : dec n with
  | none => rw [hd] at h; cases h
  | some t =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    cases t <;> simp [Term.toSubject?] at h <;> subst h <;> rfl

theorem iriAt_eq {dec : Nat → Option Term} {n : Nat} {p : WfIri} (h : iriAt dec n = some p) :
    dec n = some (.iri p) := by
  unfold iriAt at h
  cases hd : dec n with
  | none => rw [hd] at h; cases h
  | some t =>
    rw [hd] at h
    simp only [Option.bind_some] at h
    cases t <;> simp [iriOf?] at h
    subst h; rfl

theorem graphOf?_none {dec : Nat → Option Term} {g : Nat} (h : graphOf? dec g = some none) : g = 0 := by
  unfold graphOf? at h
  by_cases hg : g = 0
  · exact hg
  · rw [if_neg hg] at h
    cases hs : subjAt dec g <;> simp [hs] at h

theorem graphOf?_some {dec : Nat → Option Term} {g : Nat} {n : Subject} (h : graphOf? dec g = some (some n)) :
    g ≠ 0 ∧ dec g = some n.toTerm := by
  unfold graphOf? at h
  by_cases hg : g = 0
  · rw [if_pos hg] at h; cases h
  · rw [if_neg hg] at h
    cases hs : subjAt dec g with
    | none => simp [hs] at h
    | some m =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨hg, subjAt_eq hs⟩

/-- Under `DictInjective` (step 2) and `HeldFolded`, two rows in use that decode
to RDF-term-equal quads of one graph are one row. -/
theorem rowQuad?_inj {enc : Term → Option Nat} {dec : Nat → Option Term} {dom : Term → Prop}
    {used : Nat → Prop} (D : DictInjective enc dec dom used) (hfold : HeldFolded dom)
    {r q : Row} (hr : RowInUse used r) (hq : RowInUse used q) {gn : Option Subject} {u v : Triple}
    (hu : rowQuad? dec r = some (gn, u)) (hv : rowQuad? dec q = some (gn, v)) (e : u.key = v.key) :
    r = q := by
  obtain ⟨hug, hu0, hu1, hu2⟩ := (rowQuad?_eq_some dec r gn u).mp hu
  obtain ⟨hvg, hv0, hv1, hv2⟩ := (rowQuad?_eq_some dec q gn v).mp hv
  obtain ⟨us, up, uo⟩ := u
  obtain ⟨vs, vp, vo⟩ := v
  simp only [Triple.key, Triple.mk.injEq] at e
  obtain ⟨rfl, rfl, eo⟩ := e
  simp only at hu0 hu1 hu2 hv0 hv1 hv2
  have folded : ∀ n t, used n → dec n = some t → t.joinKey = t := by
    intro n t hn hd
    obtain ⟨t', ht', hd', _⟩ := D.encDec n hn
    rw [hd] at hd'
    cases Option.some.inj hd'
    exact hfold t ht'
  have huo := folded _ _ hr.2.2.1 hu2
  have hvo := folded _ _ hq.2.2.1 hv2
  have eo' : uo = vo := by rw [← huo, eo, hvo]
  subst eo'
  have c0 : r.c0 = q.c0 := D.decInj _ _ _ hr.1 hq.1 (subjAt_eq hu0) (subjAt_eq hv0)
  have c1 : r.c1 = q.c1 := D.decInj _ _ _ hr.2.1 hq.2.1 (iriAt_eq hu1) (iriAt_eq hv1)
  have c2 : r.c2 = q.c2 := D.decInj _ _ _ hr.2.2.1 hq.2.2.1 hu2 hv2
  have cg : r.g = q.g := by
    cases gn with
    | none => rw [graphOf?_none hug, graphOf?_none hvg]
    | some n =>
      obtain ⟨hr0, hrd⟩ := graphOf?_some hug
      obtain ⟨hq0, hqd⟩ := graphOf?_some hvg
      exact D.decInj _ _ _ (hr.2.2.2 hr0) (hq.2.2.2 hq0) hrd hqd
  obtain ⟨_, _, _, _⟩ := r
  obtain ⟨_, _, _, _⟩ := q
  simp_all

/-- An empty overlay denotes the base generation. -/
theorem overlayDen_empty (dec : Nat → Option Term) (base : Row → Bool) (bn : Nat → Bool) :
    overlayDen dec base bn {} = DatasetDen.ofRows (rowQuad? dec) (fun r => base r = true)
      (fun n => ∃ x, (x ≠ 0 ∧ bn x = true) ∧ subjAt dec x = some n) := by
  apply DatasetDen.ext
  · intro gn t
    show (∃ r, denote base {} r = true ∧ _) ↔ (∃ r, base r = true ∧ _)
    simp only [denote_empty]
  · intro n
    have hx : ∀ x, denoteNamed bn {} x = (x != 0 && bn x) := by intro x; simp [denoteNamed]
    show ((∃ x, denoteNamed bn {} x = true ∧ _) ∨ _) ↔ ((∃ x, (x ≠ 0 ∧ bn x = true) ∧ _) ∨ _)
    simp only [hx, denote_empty, Bool.and_eq_true, bne_iff_ne, ne_eq]

/-- INSERT DATA (SPARQL 1.1 Update section 3.1.1): the overlay after `add q`
denotes the quads before and the quad of `q`. -/
theorem overlayDen_add (dec : Nat → Option Term) (base : Row → Bool) (bn : Nat → Bool) (st : State) (q : Row)
    (gn : Option Subject) (t : Triple) :
    (overlayDen dec base bn (step st (.add q))).graph gn t ↔
      (overlayDen dec base bn st).graph gn t ∨ ∃ u, rowQuad? dec q = some (gn, u) ∧ u.key = t.key := by
  show (∃ r, denote base (step st (.add q)) r = true ∧ _) ↔ (∃ r, denote base st r = true ∧ _) ∨ _
  simp only [step_add, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨r, hr | rfl, hd⟩
    · exact Or.inl ⟨r, hr, hd⟩
    · exact Or.inr hd
  · rintro (⟨r, hr, hd⟩ | hd)
    · exact ⟨r, Or.inl hr, hd⟩
    · exact ⟨q, Or.inr rfl, hd⟩

/-- DELETE DATA (SPARQL 1.1 Update section 3.1.2): the overlay after
`remove q` denotes the quads before without the quad of `q`. Hypotheses: the
dictionary contract of step 2 (`DictInjective`, for SBM11
`DictInjectiveTheorems.overlay_dictInjective`), its terms folded
(`HeldFolded`), and the ids of `q` and of every row the overlay holds in use. -/
theorem overlayDen_remove {enc : Term → Option Nat} {dec : Nat → Option Term} {dom : Term → Prop}
    {used : Nat → Prop} (D : DictInjective enc dec dom used) (hfold : HeldFolded dom)
    (base : Row → Bool) (bn : Nat → Bool) (st : State) (q : Row) (hq : RowInUse used q)
    (hrows : ∀ r, denote base st r = true → RowInUse used r) (gn : Option Subject) (t : Triple) :
    (overlayDen dec base bn (step st (.remove q))).graph gn t ↔
      (overlayDen dec base bn st).graph gn t ∧ ¬ ∃ u, rowQuad? dec q = some (gn, u) ∧ u.key = t.key := by
  show (∃ r, denote base (step st (.remove q)) r = true ∧ _) ↔ (∃ r, denote base st r = true ∧ _) ∧ _
  simp only [step_remove, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · rintro ⟨r, ⟨hr, hne⟩, u, hd, e⟩
    refine ⟨⟨r, hr, u, hd, e⟩, ?_⟩
    rintro ⟨v, hv, e'⟩
    exact hne (rowQuad?_inj D hfold hq (hrows r hr) hv hd (e'.trans e.symm))
  · rintro ⟨⟨r, hr, u, hd, e⟩, hn⟩
    refine ⟨r, ⟨hr, ?_⟩, u, hd, e⟩
    rintro rfl
    exact hn ⟨u, hd, e⟩

/-- `overlayDen_remove` for the SBM11 dictionary of a generation with its
overlay vocabulary: `DictInjective` is `OverlayDict.overlay_dictInjective`
(step 2), from the check of the vocabulary and of the base ids. `HeldFolded`
stays a hypothesis. -/
theorem overlayDen_remove_sbm11 (keys : List Key) (ov : List Term) (baseUsed : Nat → Prop)
    (hv : OverlayDict.vocabOk keys ov = true) (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true)
    (hfold : HeldFolded (OverlayDict.ovHeld keys baseUsed ov))
    (base : Row → Bool) (bn : Nat → Bool) (st : State) (q : Row)
    (hq : RowInUse (OverlayDict.ovUsed baseUsed ov) q)
    (hrows : ∀ r, denote base st r = true → RowInUse (OverlayDict.ovUsed baseUsed ov) r)
    (gn : Option Subject) (t : Triple) :
    (overlayDen (OverlayDict.ovDec keys ov) base bn (step st (.remove q))).graph gn t ↔
      (overlayDen (OverlayDict.ovDec keys ov) base bn st).graph gn t ∧
        ¬ ∃ u, rowQuad? (OverlayDict.ovDec keys ov) q = some (gn, u) ∧ u.key = t.key :=
  overlayDen_remove (OverlayDict.overlay_dictInjective keys ov baseUsed hv hb) hfold base bn st q hq hrows gn t

/-- CREATE (SPARQL 1.1 Update section 3.2.1) adds the graph name of `g` (an
empty named graph). -/
theorem overlayDen_create_names (dec : Nat → Option Term) (base : Row → Bool) (bn : Nat → Bool) (st : State)
    (g : Nat) (n : Subject) :
    (overlayDen dec base bn (step st (.create g))).names n ↔
      (overlayDen dec base bn st).names n ∨ (g ≠ 0 ∧ subjAt dec g = some n) := by
  show ((∃ x, denoteNamed bn (step st (.create g)) x = true ∧ _) ∨
      ∃ r u, denote base (step st (.create g)) r = true ∧ _) ↔
    ((∃ x, denoteNamed bn st x = true ∧ _) ∨ ∃ r u, denote base st r = true ∧ _) ∨ _
  simp only [named_create, step_create, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq]
  constructor
  · rintro (⟨x, hx | ⟨hx0, rfl⟩, hs⟩ | hr)
    · exact Or.inl (Or.inl ⟨x, hx, hs⟩)
    · exact Or.inr ⟨hx0, hs⟩
    · exact Or.inl (Or.inr hr)
  · rintro ((⟨x, hx, hs⟩ | hr) | ⟨hg0, hs⟩)
    · exact Or.inl ⟨x, Or.inl hx, hs⟩
    · exact Or.inr hr
    · exact Or.inl ⟨g, Or.inr ⟨hg0, rfl⟩, hs⟩

/-- CREATE adds no triple. -/
theorem overlayDen_create_graph (dec : Nat → Option Term) (base : Row → Bool) (bn : Nat → Bool) (st : State)
    (g : Nat) (gn : Option Subject) (t : Triple) :
    (overlayDen dec base bn (step st (.create g))).graph gn t ↔ (overlayDen dec base bn st).graph gn t := by
  show (∃ r, denote base (step st (.create g)) r = true ∧ _) ↔ (∃ r, denote base st r = true ∧ _)
  simp only [step_create]

#print axioms rowQuad?_inj
#print axioms overlayDen_empty
#print axioms overlayDen_add
#print axioms overlayDen_remove
#print axioms overlayDen_remove_sbm11
#print axioms overlayDen_create_names

end L4Factoidal.Storage.Sbm11.Overlay
