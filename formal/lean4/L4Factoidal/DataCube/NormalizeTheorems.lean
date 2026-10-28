/-
L4Factoidal.DataCube.NormalizeTheorems — properties of the Data Cube
normalization algorithm (RDF Data Cube Recommendation, 16 January 2014,
section 10.1), stated against RDF 1.1 Semantics.

* `normalize_extensive`: normalization keeps every triple of the input (both
  phases only INSERT).
* `phase1_rdfs_sound`: every triple of phase 1's result is derivable, by the
  RDF 1.1 Semantics section 9.2 rules (`RDFS.Derives`: rdfs2, rdfs3, rdfs7),
  from the input and `qbPhase1Schema`, the ten declarations of the Data Cube
  vocabulary (`tests/datacube/spec/cube.ttl`) that phase 1 uses. Section 10.1
  says: "These closure operations are implied by the RDFS semantics of the Data
  Cube vocabulary." `l4datacube --check-schema` checks that the ten triples
  are in the vendored vocabulary.

The statements name the versions: Data Cube 2014 (namespace `QB2014`) and the
RDF 1.1 Semantics rule relation of `RDFS/RdfsCore.lean`.
-/
import L4Factoidal.DataCube.Normalize
import L4Factoidal.RDFS.RdfsCore

namespace L4Factoidal.DataCube.QB2014

open L4Factoidal.RDF
open L4Factoidal.RDFS

/-- The declarations of the Data Cube vocabulary that phase 1 relies on. -/
def qbPhase1Schema : Graph :=
  [⟨.iri qbObservationP, rdfsRange, .iri qbObservation⟩,
   ⟨.iri qbDataSetP, rdfsDomain, .iri qbObservation⟩,
   ⟨.iri qbDataSetP, rdfsRange, .iri qbDataSet⟩,
   ⟨.iri qbSliceP, rdfsRange, .iri qbSlice⟩,
   ⟨.iri qbDimension, rdfsSubPropertyOf, .iri qbComponentProperty⟩,
   ⟨.iri qbDimension, rdfsRange, .iri qbDimensionProperty⟩,
   ⟨.iri qbMeasure, rdfsSubPropertyOf, .iri qbComponentProperty⟩,
   ⟨.iri qbMeasure, rdfsRange, .iri qbMeasureProperty⟩,
   ⟨.iri qbAttribute, rdfsSubPropertyOf, .iri qbComponentProperty⟩,
   ⟨.iri qbAttribute, rdfsRange, .iri qbAttributeProperty⟩]

/-! ## `addNew` and `applyOps` only add -/

theorem mem_addNew_of_mem {g : Graph} {t : Triple} (new : List Triple) (h : t ∈ g) :
    t ∈ addNew g new := by
  induction new generalizing g with
  | nil => exact h
  | cons x xs ih =>
    simp only [addNew, List.foldl_cons]
    apply ih
    split
    · exact h
    · exact List.mem_append_left _ h

theorem mem_addNew {g : Graph} {t : Triple} {new : List Triple} (h : t ∈ addNew g new) :
    t ∈ g ∨ t ∈ new := by
  induction new generalizing g with
  | nil => exact .inl h
  | cons x xs ih =>
    simp only [addNew, List.foldl_cons] at h
    rcases ih h with h' | h'
    · split at h'
      · exact .inl h'
      · rcases List.mem_append.mp h' with h'' | h''
        · exact .inl h''
        · simp only [List.mem_singleton] at h''
          exact .inr (h'' ▸ List.mem_cons_self)
    · exact .inr (List.mem_cons_of_mem _ h')

theorem applyOps_extensive {g : Graph} {t : Triple} (ops : List (Graph → List Triple))
    (h : t ∈ g) : t ∈ applyOps g ops := by
  induction ops generalizing g with
  | nil => exact h
  | cons op rest ih =>
    simp only [applyOps, List.foldl_cons]
    exact ih (mem_addNew_of_mem _ h)

/-- Normalization keeps every triple of the input. -/
theorem normalize_extensive {g : Graph} {t : Triple} (h : t ∈ g) : t ∈ normalize g :=
  applyOps_extensive _ (applyOps_extensive _ h)

/-! ## Phase 1 is RDFS-entailed -/

/-- An invariant carried through `applyOps`: when each operation emits only
triples derivable from its input and `S`, the result is derivable from the
input and `S`. -/
theorem applyOps_derives {S : Graph} (ops : List (Graph → List Triple))
    (hops : ∀ op ∈ ops, ∀ acc t, t ∈ op acc → Derives (acc ++ S) t) :
    ∀ (g : Graph) (G : Graph), (∀ u ∈ g, Derives G u) → (∀ u ∈ S, Derives G u) →
      ∀ t ∈ applyOps g ops, Derives G t := by
  induction ops with
  | nil => intro g G hg _ t ht; exact hg t ht
  | cons op rest ih =>
    intro g G hg hS t ht
    simp only [applyOps, List.foldl_cons] at ht
    have hrest : ∀ op' ∈ rest, ∀ acc t, t ∈ op' acc → Derives (acc ++ S) t :=
      fun op' h => hops op' (List.mem_cons_of_mem _ h)
    refine ih hrest (addNew g (op g)) G ?_ hS t ht
    intro u hu
    rcases mem_addNew hu with h | h
    · exact hg u h
    · refine Derives.cut (g := G) (g' := g ++ S) ?_ (hops op List.mem_cons_self g u h)
      intro v hv
      rcases List.mem_append.mp hv with h' | h'
      · exact hg v h'
      · exact hS v h'

theorem mem_withPredicate {g : Graph} {p : WfIri} {u : Triple} (h : u ∈ withPredicate g p) :
    u ∈ g ∧ u.p = p := by
  simp only [withPredicate, List.mem_filter, beq_iff_eq] at h
  exact h

/-- rdfs3 through `typeTriple?`. -/
theorem typeTriple_derives {G : Graph} {u : Triple} {c : WfIri} {t : Triple}
    (hu : Derives G u) (hr : Derives G ⟨.iri u.p, rdfsRange, .iri c⟩)
    (ht : t ∈ typeTriple? u.o c) : Derives G t := by
  unfold typeTriple? at ht
  split at ht
  · rename_i s hs
    simp only [List.mem_singleton] at ht
    subst ht
    exact Derives.rdfs3 hr hu hs
  · simp at ht

theorem schema_derives {acc : Graph} {t : Triple} (h : t ∈ qbPhase1Schema) :
    Derives (acc ++ qbPhase1Schema) t :=
  Derives.base (List.mem_append_right _ h)

theorem data_derives {acc : Graph} {u : Triple} (h : u ∈ acc) :
    Derives (acc ++ qbPhase1Schema) u :=
  Derives.base (List.mem_append_left _ h)

theorem p1ObservationOf_derives (acc : Graph) (t : Triple) (h : t ∈ p1ObservationOf acc) :
    Derives (acc ++ qbPhase1Schema) t := by
  simp only [p1ObservationOf, List.mem_flatMap] at h
  obtain ⟨u, hu, ht⟩ := h
  obtain ⟨hug, hup⟩ := mem_withPredicate hu
  refine typeTriple_derives (data_derives hug) ?_ ht
  rw [hup]; exact schema_derives (by simp [qbPhase1Schema])

theorem p1DataSetOf_derives (acc : Graph) (t : Triple) (h : t ∈ p1DataSetOf acc) :
    Derives (acc ++ qbPhase1Schema) t := by
  simp only [p1DataSetOf, List.mem_flatMap, List.mem_cons] at h
  obtain ⟨u, hu, ht⟩ := h
  obtain ⟨hug, hup⟩ := mem_withPredicate hu
  rcases ht with ht | ht
  · subst ht
    have hdata : Derives (acc ++ qbPhase1Schema) ⟨u.s, qbDataSetP, u.o⟩ := by
      have : (⟨u.s, qbDataSetP, u.o⟩ : Triple) = u := by rw [← hup]
      rw [this]; exact data_derives hug
    exact Derives.rdfs2 (schema_derives (by simp [qbPhase1Schema])) hdata
  · refine typeTriple_derives (data_derives hug) ?_ ht
    rw [hup]; exact schema_derives (by simp [qbPhase1Schema])

theorem p1SliceOf_derives (acc : Graph) (t : Triple) (h : t ∈ p1SliceOf acc) :
    Derives (acc ++ qbPhase1Schema) t := by
  simp only [p1SliceOf, List.mem_flatMap] at h
  obtain ⟨u, hu, ht⟩ := h
  obtain ⟨hug, hup⟩ := mem_withPredicate hu
  refine typeTriple_derives (data_derives hug) ?_ ht
  rw [hup]; exact schema_derives (by simp [qbPhase1Schema])

theorem p1ComponentOf_derives {p c : WfIri}
    (hsub : (⟨.iri p, rdfsSubPropertyOf, .iri qbComponentProperty⟩ : Triple) ∈ qbPhase1Schema)
    (hran : (⟨.iri p, rdfsRange, .iri c⟩ : Triple) ∈ qbPhase1Schema)
    (acc : Graph) (t : Triple) (h : t ∈ p1ComponentOf acc p c) :
    Derives (acc ++ qbPhase1Schema) t := by
  simp only [p1ComponentOf, List.mem_flatMap, List.mem_cons] at h
  obtain ⟨u, hu, ht⟩ := h
  obtain ⟨hug, hup⟩ := mem_withPredicate hu
  have hdata : Derives (acc ++ qbPhase1Schema) ⟨u.s, p, u.o⟩ := by
    have : (⟨u.s, p, u.o⟩ : Triple) = u := by rw [← hup]
    rw [this]; exact data_derives hug
  rcases ht with ht | ht
  · subst ht
    exact Derives.rdfs7 (schema_derives hsub) hdata
  · refine typeTriple_derives (data_derives hug) ?_ ht
    rw [hup]; exact schema_derives hran

/-- Section 10.1: every triple of phase 1's result is RDFS-derivable from the
input graph and the Data Cube vocabulary's declarations (`qbPhase1Schema`). -/
theorem phase1_rdfs_sound (g : Graph) :
    ∀ t ∈ phase1 g, Derives (g ++ qbPhase1Schema) t := by
  refine applyOps_derives phase1Ops ?_ g (g ++ qbPhase1Schema)
    (fun u hu => data_derives hu) (fun u hu => schema_derives hu)
  intro op hop
  simp only [phase1Ops, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1ObservationOf_derives
  · exact p1DataSetOf_derives
  · exact p1SliceOf_derives
  · exact p1ComponentOf_derives (by simp [qbPhase1Schema]) (by simp [qbPhase1Schema])
  · exact p1ComponentOf_derives (by simp [qbPhase1Schema]) (by simp [qbPhase1Schema])
  · exact p1ComponentOf_derives (by simp [qbPhase1Schema]) (by simp [qbPhase1Schema])

end L4Factoidal.DataCube.QB2014
