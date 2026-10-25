/-
L4Factoidal.LWS.DatasetView — the dataset view of a Linked Web Storage
snapshot (https://github.com/danbri/factoidal/issues/1011, KR1).

Source specification: Linked Web Storage Protocol 1.0 Core,
<https://w3c.github.io/lws-protocol/lws10-core/> (W3C Linked Web Storage
Working Group editor's draft). The sections this module reads:

* "Terminology": an LWS resource, a container ("an LWS resource that is able
  to enumerate a collection of LWS resources"), a data resource, a metadata
  resource ("an auxiliary resource ... that describes an LWS resource"), and
  containment ("the relationship between a container and the LWS resources
  whose lifecycle the container manages").
* "Containers": a container enumerates its members.
* "Read Resource": a GET of a resource answers its representation, with an
  entity tag (`ETag`) and `Last-Modified`.

**LWS 1.0 does not define this view.** The draft defines resources and their
representations; it says nothing about an RDF dataset made from a storage.
The definition below is Factoidal's (owner, 2026-10-25, issue 1011), and it
is a question for the LWS Working Group
(`docs/designissues/2026-10-25-lws-dataset-view.md`).

## The definition

A snapshot is what a client read from one storage: the containment pairs of
the container listings it read, and, for each RDF resource it read, the
resource IRI, the entity tag and `Last-Modified` of the representation, and
the RDF graph that representation denotes (RDF 1.1 Concepts §3). The view
(`view`) is the RDF dataset (RDF 1.1 Concepts §4):

* the **default graph** holds one triple `<container> ldp:contains <member>`
  for each containment pair (the predicate of W3C LDP 1.0 §5.2.1.4, which the
  Solid Protocol, the binding this repository's LWS server uses, also uses);
* for each RDF resource read (a data resource or a metadata resource), one
  **named graph whose name is the resource IRI** and whose triples are the
  graph its representation denotes. When the snapshot holds two reads of one
  IRI, the first one is the graph (`graphOf`).

Non-RDF resources are not in the view: a reader that has no RDF reader for a
representation's media type leaves the resource out of `reads`.

Blank nodes: RDF 1.1 Concepts §3.4 scopes blank nodes to a document, so the
graphs of two reads share no blank node. The readers give each document its
own scope (`Dataset.scopeDocument`); this module takes the graphs as given.

## Properties (proved below)

* `view_names_nodup`: the graph names of the view are distinct.
* `view_names`: the names are exactly the IRIs of the reads (`mem_resources`).
* `view_replace`: replacing one resource's representation (`Snapshot.replace`)
  leaves the default graph and the list of names unchanged and changes the
  named graph of that IRI only; with `view_names_nodup` that is exactly one
  graph. `view_replace_lookup` states it per name.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.LWS.DatasetView

open L4Factoidal.RDF

/-- `ldp:contains` (W3C Linked Data Platform 1.0 §5.2.1.4): the containment
predicate of the default graph of the view. -/
def ldpContains : WfIri := ⟨"http://www.w3.org/ns/ldp#contains", by decide⟩

/-- What a read resource is to the storage (LWS 1.0 Core, "Terminology"). The
view treats both the same; the role is kept for the evidence. -/
inductive Role where
  /-- A data resource. -/
  | data
  /-- A metadata resource (an auxiliary resource that describes another). -/
  | metadata
  deriving DecidableEq, Repr, Inhabited

/-- One GET of an RDF resource (LWS 1.0 Core, "Read Resource"): the resource
IRI, the entity tag and `Last-Modified` of the representation, and the RDF
graph the representation denotes. -/
structure Read where
  resource : WfIri
  etag : String
  lastModified : String := ""
  role : Role := .data
  graph : Graph
  deriving Repr

/-- What a client read from one storage: the containment pairs
`(container, member)` of the listings, and the RDF resources. -/
structure Snapshot where
  members : List (WfIri × WfIri)
  reads : List Read
  deriving Repr

/-- The IRIs of a list of reads, each once, in first-read order. A loop
(`List.foldl`), so its depth does not grow with the list. -/
def resourcesOf (rs : List Read) : List WfIri :=
  rs.foldl (fun acc r => if acc.contains r.resource then acc else acc ++ [r.resource]) []

/-- The IRIs of the RDF resources of a snapshot, each once. -/
def Snapshot.resources (s : Snapshot) : List WfIri := resourcesOf s.reads

/-- The graph of the first read of the IRI `i`, or the empty graph. -/
def Snapshot.graphOf (s : Snapshot) (i : WfIri) : Graph :=
  match s.reads.find? (fun r => r.resource == i) with
  | some r => r.graph
  | none => []

/-- The default graph of the view: one `ldp:contains` triple per pair. -/
def Snapshot.containment (s : Snapshot) : Graph :=
  s.members.map (fun cm => ⟨.iri cm.1, ldpContains, .iri cm.2⟩)

/-- **The dataset view of a snapshot.** The default graph is the containment
graph; each RDF resource is the named graph whose name is its IRI. -/
def view (s : Snapshot) : Dataset :=
  { default := s.containment
    named := s.resources.map (fun i => ⟨.iri i, s.graphOf i⟩) }

/-- The snapshot with the representation of `i` replaced: every read of `i`
gets the entity tag `etag` and the graph `g`; nothing else changes. -/
def Snapshot.replace (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) : Snapshot :=
  { s with reads := s.reads.map (fun r => if r.resource = i then { r with etag, graph := g } else r) }

/-! ## The IRIs of the reads -/

private theorem foldl_resources_spec (rs : List Read) :
    ∀ acc : List WfIri, acc.Nodup →
      (rs.foldl (fun acc r => if acc.contains r.resource then acc else acc ++ [r.resource]) acc).Nodup ∧
      ∀ i, i ∈ rs.foldl (fun acc r => if acc.contains r.resource then acc else acc ++ [r.resource]) acc ↔
        i ∈ acc ∨ ∃ r ∈ rs, r.resource = i := by
  induction rs with
  | nil => intro acc h; simp [h]
  | cons r rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    by_cases hc : acc.contains r.resource = true
    · rw [if_pos hc]
      obtain ⟨h1, h2⟩ := ih acc hacc
      refine ⟨h1, fun i => ?_⟩
      rw [h2 i]
      have hm : r.resource ∈ acc := by simpa using hc
      constructor
      · rintro (h | ⟨x, hx, e⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, e⟩
      · rintro (h | ⟨x, hx, e⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact Or.inl (e ▸ hm)
          · exact Or.inr ⟨x, hx', e⟩
    · rw [if_neg hc]
      have hn : r.resource ∉ acc := by simpa using hc
      have hacc' : (acc ++ [r.resource]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hacc, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
        intro a ha b hb e
        rw [List.mem_singleton] at hb
        subst hb; subst e
        exact hn ha
      obtain ⟨h1, h2⟩ := ih _ hacc'
      refine ⟨h1, fun i => ?_⟩
      rw [h2 i, List.mem_append, List.mem_singleton]
      constructor
      · rintro ((h | h) | ⟨x, hx, e⟩)
        · exact Or.inl h
        · exact Or.inr ⟨r, List.mem_cons_self, h.symm⟩
        · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, e⟩
      · rintro (h | ⟨x, hx, e⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.mp hx with rfl | hx'
          · exact Or.inl (Or.inr e.symm)
          · exact Or.inr ⟨x, hx', e⟩

/-- Each IRI is listed once. -/
theorem resources_nodup (s : Snapshot) : s.resources.Nodup :=
  (foldl_resources_spec s.reads [] List.nodup_nil).1

/-- The listed IRIs are exactly the IRIs of the reads. -/
theorem mem_resources (s : Snapshot) (i : WfIri) :
    i ∈ s.resources ↔ ∃ r ∈ s.reads, r.resource = i := by
  rw [Snapshot.resources, resourcesOf, (foldl_resources_spec s.reads [] List.nodup_nil).2 i]
  simp

/-- A map that keeps every IRI keeps the list of IRIs. -/
theorem resourcesOf_map (f : Read → Read) (hf : ∀ r, (f r).resource = r.resource)
    (rs : List Read) : resourcesOf (rs.map f) = resourcesOf rs := by
  unfold resourcesOf
  rw [List.foldl_map]
  simp only [hf]

/-! ## The graph names of the view -/

/-- The graph names of the view are the IRIs of the reads, in order. -/
theorem view_names (s : Snapshot) : (view s).names = s.resources.map Subject.iri := by
  show ((s.resources.map (fun i => (⟨.iri i, s.graphOf i⟩ : NamedGraph))).map (·.name)) = _
  rw [List.map_map]
  rfl

/-- **The graph names of the view are distinct.** -/
theorem view_names_nodup (s : Snapshot) : (view s).names.Nodup := by
  rw [view_names]
  exact List.Pairwise.map Subject.iri (fun _ _ h e => h (Subject.iri.inj e)) (resources_nodup s)

/-- A name of the view is the IRI of a read. -/
theorem view_mem_names (s : Snapshot) (n : Subject) :
    n ∈ (view s).names ↔ ∃ r ∈ s.reads, n = .iri r.resource := by
  rw [view_names, List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨r, hr, e⟩ := (mem_resources s i).mp hi
    exact ⟨r, hr, e ▸ rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.resource, (mem_resources s _).mpr ⟨r, hr, rfl⟩, rfl⟩

/-! ## A resource change changes one graph -/

private def replaceRead (i : WfIri) (etag : String) (g : Graph) (r : Read) : Read :=
  if r.resource = i then { r with etag, graph := g } else r

private theorem replaceRead_resource (i : WfIri) (etag : String) (g : Graph) (r : Read) :
    (replaceRead i etag g r).resource = r.resource := by
  unfold replaceRead
  split <;> rfl

theorem replace_resources (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (s.replace i etag g).resources = s.resources :=
  resourcesOf_map (replaceRead i etag g) (replaceRead_resource i etag g) s.reads

theorem replace_graphOf (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) (j : WfIri)
    (hj : j ∈ s.resources) :
    (s.replace i etag g).graphOf j = if j = i then g else s.graphOf j := by
  unfold Snapshot.graphOf
  show (match (s.reads.map (replaceRead i etag g)).find? (fun r => r.resource == j) with
    | some r => r.graph | none => []) = _
  rw [List.find?_map]
  have hp : ((fun r : Read => r.resource == j) ∘ replaceRead i etag g) = (fun r => r.resource == j) := by
    funext r
    simp [replaceRead_resource]
  rw [hp]
  cases hf : s.reads.find? (fun r => r.resource == j) with
  | none =>
    exfalso
    obtain ⟨r, hr, e⟩ := (mem_resources s j).mp hj
    exact absurd (List.find?_eq_none.mp hf r hr) (by simp [e])
  | some r =>
    have hrj : r.resource = j := Subtype.ext (by simpa using List.find?_some hf)
    simp only [Option.map_some]
    unfold replaceRead
    by_cases h : j = i
    · rw [if_pos (hrj.trans h), if_pos h]
    · rw [if_neg (fun e => h (hrj.symm.trans e)), if_neg h]

/-- **Replacing one resource's representation changes exactly one graph.**
The default graph is the same, and the named graphs are those of the view
before the change with the graph named by `i` replaced by `g`. Since the
names are distinct (`view_names_nodup`), at most one entry is named `i`. -/
theorem view_replace (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (view (s.replace i etag g)).default = (view s).default ∧
      (view (s.replace i etag g)).named =
        (view s).named.map (fun ng => if ng.name = .iri i then ⟨ng.name, g⟩ else ng) := by
  refine ⟨rfl, ?_⟩
  show (s.replace i etag g).resources.map _ = (s.resources.map _).map _
  rw [replace_resources, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp, replace_graphOf s i etag g j hj]
  by_cases h : j = i
  · subst h; simp
  · have : (Subject.iri j ≠ Subject.iri i) := fun e => h (by cases e; rfl)
    simp [h, this]

/-- The same, per name: the graph named `i` is `g` (when `i` was read), and
every other name has the graph it had. -/
theorem view_replace_lookup (s : Snapshot) (i : WfIri) (etag : String) (g : Graph) :
    (i ∈ s.resources → (view (s.replace i etag g)).lookupNamed (.iri i) = some g) ∧
      ∀ n, n ≠ .iri i → (view (s.replace i etag g)).lookupNamed n = (view s).lookupNamed n := by
  constructor
  · intro hi
    unfold Dataset.lookupNamed
    show (match ((s.replace i etag g).resources.map
        (fun j => (⟨.iri j, (s.replace i etag g).graphOf j⟩ : NamedGraph))).find? _ with
      | some ng => some ng.graph | none => none) = _
    rw [List.find?_map]
    have hf : ((s.replace i etag g).resources.find?
        ((fun ng : NamedGraph => ng.name == Subject.iri i) ∘
          (fun j => (⟨.iri j, (s.replace i etag g).graphOf j⟩ : NamedGraph)))) = some i := by
      rw [replace_resources]
      apply List.find?_eq_some_iff_append.mpr
      refine ⟨by simp, ?_⟩
      obtain ⟨as, bs, e⟩ := List.append_of_mem hi
      refine ⟨as, bs, e, fun a ha => ?_⟩
      have hnd := resources_nodup s
      rw [e] at hnd
      have hna : a ≠ i := by
        intro hai
        subst hai
        have := List.nodup_append.mp hnd
        exact this.2.2 a ha a List.mem_cons_self rfl
      simp [hna]
    rw [hf]
    simp only [Option.map_some]
    rw [replace_graphOf s i etag g i hi, if_pos rfl]
  · intro n hn
    unfold Dataset.lookupNamed
    rw [(view_replace s i etag g).2, List.find?_map]
    have hp : ((fun ng : NamedGraph => ng.name == n) ∘
        (fun ng : NamedGraph => if ng.name = .iri i then (⟨ng.name, g⟩ : NamedGraph) else ng)) =
        (fun ng => ng.name == n) := by
      funext ng
      by_cases h : ng.name = .iri i <;> simp [h]
    rw [hp]
    cases hf : (view s).named.find? (fun ng => ng.name == n) with
    | none => rfl
    | some ng =>
      have hng : ng.name = n := by simpa using List.find?_some hf
      have : ¬ ng.name = .iri i := fun e => hn (hng.symm.trans e)
      simp [this]

/-- The view's named graph of a read IRI is the graph of its first read. -/
theorem view_lookup (s : Snapshot) (i : WfIri) (hi : i ∈ s.resources) :
    (view s).lookupNamed (.iri i) = some (s.graphOf i) := by
  have h := (view_replace_lookup s i "" (s.graphOf i)).1 hi
  -- replacing the graph of `i` by the graph it has changes no named graph
  have hv : (view (s.replace i "" (s.graphOf i))).named = (view s).named := by
    rw [(view_replace s i "" (s.graphOf i)).2]
    conv => rhs; rw [← List.map_id (view s).named]
    apply List.map_congr_left
    intro ng hng
    by_cases hn : ng.name = .iri i
    · simp only [hn, if_true, id]
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hng
      cases hn
      rfl
    · simp [hn]
  unfold Dataset.lookupNamed at h ⊢
  rw [hv] at h
  exact h

#print axioms resources_nodup
#print axioms mem_resources
#print axioms view_names_nodup
#print axioms view_mem_names
#print axioms view_replace
#print axioms view_replace_lookup
#print axioms view_lookup

end L4Factoidal.LWS.DatasetView
