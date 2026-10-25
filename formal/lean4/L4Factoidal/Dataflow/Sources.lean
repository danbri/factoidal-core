/-
L4Factoidal.Dataflow.Sources — sources of a `LawfulDataset` with a stated
denotation (https://github.com/danbri/factoidal/issues/975, owner-approved
plan of 2026-10-25, step 1, the per-source theorems).

A source theorem says: this source yields a `Sourced` (`Dataflow/Compose.lean`)
whose `den` is X, and lists the named assumptions of its record. With
`Sourced.query_sound`, a SPARQL query over the output then satisfies the
evaluator contract over X. Each source here takes a `Sourced` or a certified
dataset as input, so sources compose: an update of a union of shards, a
reasoner over a handle after its operations, and so on; the den theorem of
the composition is the composition of the den theorems.

| source | den | named assumptions |
|---|---|---|
| reader (`readerSource`, `Dataflow/EndToEnd.lean`) | the parse's `raw.den` | none |
| API dataset handle after `add`/`delete` (`handleSource`) | `HandleOp.den` of each operation, in order, on the input den (`DatasetDen.insertQuads`, `deleteQuads`) | none |
| SPARQL 1.1 Update (`updateSource`) | the result of `applyUpdateIn`, whose den is `OpsDen` (each operation's section 3 effect) of the input | none |
| reasoner (`reasonerSource`) | default graph = the closure `r.run g`, `r.regime.Entails g (r.run g)`, no named graph | none |
| union of two records (`Sourced.union`), of shards (`Sourced.unionAll`) | `DatasetDen.union` of the dens | the members' |
| any `LawfulStore` as the default graph (`Sourced.ofStore`: HDT, COTTAS, RML, overlays, store unions) | `defaultDen st.graph` | the store's (`backendReadOpsExact`, `cottasReadOpsExact`, ...) |

`Sourced.den_eq` (the reference value has the record's den) rests on the
record's named assumptions: for `Sourced.ofStore` the reference value is the
store's unbounded search, which is the store's graph only under the store's
law.

The wasm handle ops (`Wasm/Ops/Handles.lean`): `datasetAddQuads` and
`datasetDeleteQuads` apply `CertifiedDataset.insertQuads` and `deleteQuads`
and store `LawfulDataset.ofCertified` of the result (`openDataset`); that is
`handleSource` with one operation. `datasetUpdate` stores
`LawfulDataset.ofCertified` of the `applyUpdateIn` result: `updateSource`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Compose
import L4Factoidal.Dataflow.Reasoner
import L4Factoidal.SPARQL.UpdateDenotation
import L4Factoidal.RDF.DocumentScope

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.StorePlan (NamedGraphBackend)
open L4Factoidal.Storage.PlannerSoundness (DatasetBackendExact)

/-! ## `certify` keeps the denotation -/

theorem Dataset.certify_den (ds : Dataset) : ds.certify.val.den = ds.den := by
  apply DatasetDen.ext
  · intro gn t
    exact Dataset.certify_memQuad ds t gn
  · intro n
    exact Dataset.certify_names ds n

/-! ## (b) An API dataset handle after its operations -/

/-- An operation of the dataset handle API: add or delete quads
(`datasetAddQuads`, `datasetDeleteQuads`). -/
inductive HandleOp where
  | add (qs : List Quad)
  | delete (qs : List Quad)

/-- The operation on a certified dataset. -/
def HandleOp.apply : HandleOp → CertifiedDataset → CertifiedDataset
  | .add qs, c => c.insertQuads qs
  | .delete qs, c => c.deleteQuads qs

/-- The operation on the denotation (SPARQL 1.1 Update section 3.1.1 and
3.1.2, `SPARQL/UpdateDenotation.lean`). -/
def HandleOp.den : HandleOp → DatasetDen → DatasetDen
  | .add qs, d => d.insertQuads qs
  | .delete qs, d => d.deleteQuads qs

def applyHandleOps (c : CertifiedDataset) (ops : List HandleOp) : CertifiedDataset :=
  ops.foldl (fun c op => op.apply c) c

theorem HandleOp.apply_den (op : HandleOp) (c : CertifiedDataset) :
    (op.apply c).val.den = op.den c.val.den := by
  cases op with
  | add qs => exact Dataset.den_insertQuads qs c.property
  | delete qs => exact Dataset.den_deleteQuads qs c.property

theorem applyHandleOps_den (ops : List HandleOp) :
    ∀ c : CertifiedDataset,
      (applyHandleOps c ops).val.den = ops.foldl (fun d op => op.den d) c.val.den := by
  induction ops with
  | nil => intro c; rfl
  | cons op rest ih =>
    intro c
    show (applyHandleOps (op.apply c) rest).val.den = _
    rw [ih (op.apply c), HandleOp.apply_den]
    rfl

/-- The record of a handle after its operations. -/
def handleSource (c : CertifiedDataset) (ops : List HandleOp) : Sourced :=
  Sourced.ofCertified (applyHandleOps c ops)

/-- **Source theorem (b), the dataset handle**: after the operations, the
record's den is each operation's effect on the den, in order, and the record
has no named assumption. -/
theorem handleSource_spec (c : CertifiedDataset) (ops : List HandleOp) :
    (handleSource c ops).den = ops.foldl (fun d op => op.den d) c.val.den ∧
      (handleSource c ops).assumptions = [] :=
  ⟨applyHandleOps_den ops c, rfl⟩

/-- A handle over any source's output. -/
def Sourced.handle (s : Sourced) (ops : List HandleOp) : Sourced :=
  handleSource ⟨s.ref, s.isSet⟩ ops

theorem Sourced.handle_den (s : Sourced) (hs : Assumed s.assumptions) (ops : List HandleOp) :
    (s.handle ops).den = ops.foldl (fun d op => op.den d) s.den := by
  rw [Sourced.handle, (handleSource_spec _ ops).1]
  show ops.foldl _ s.ref.den = _
  rw [s.den_eq hs]
  rfl

/-! ## (c) A SPARQL 1.1 Update -/

/-- The record of the result of a SPARQL 1.1 Update request on a source's
output (`applyUpdateIn`, `updateStage`, the wasm op `datasetUpdate`). -/
def updateSource (env : EvalEnv) (s : Sourced) (u : Update) {ds' : Dataset}
    (h : applyUpdateIn env s.ref u = .ok ds') : Sourced :=
  Sourced.ofCertified ⟨ds', applyUpdateIn_isSet env u s.isSet h⟩

/-- **Source theorem (c), SPARQL Update**: the record's den is the den of the
result, the request has the effect `OpsDen` states (its operations in order,
each with its SPARQL 1.1 Update section 3 effect, `OpDen`) starting from a
dataset whose den is the input's, and the record has no named assumption.
The quad lists of the operations with a WHERE clause are the implementation's
(`SPARQL/UpdateDenotation.lean`, "The boundary"). -/
theorem updateSource_spec (env : EvalEnv) (s : Sourced) (u : Update) {ds' : Dataset}
    (h : applyUpdateIn env s.ref u = .ok ds') :
    (updateSource env s u h).den = ds'.den ∧ (Assumed s.assumptions → s.ref.den = s.den) ∧
      OpsDen env (requestPrefix s.ref) 0 s.ref u.ops ds' ∧
      (updateSource env s u h).assumptions = [] :=
  ⟨rfl, s.den_eq, (applyUpdateIn_den env u s.isSet h).2, rfl⟩

/-! ## (d) A reasoner -/

/-- The record of a reasoner's output: the closure as the default graph, no
named graph. -/
def reasonerSource (r : SoundReasoner) (g : Graph) : Sourced :=
  Sourced.ofCertified (Dataset.certify { default := r.run g, named := [] })

/-- **Source theorem (d), a reasoner**: the record's default graph holds
exactly the triples of the closure `r.run g`, the record has no named graph,
every output graph is entailed by the input in the reasoner's regime
(`SoundReasoner.sound`), and the record has no named assumption. -/
theorem reasonerSource_spec (r : SoundReasoner) (g : Graph) :
    (∀ t, (reasonerSource r g).den.graph none t ↔ (r.run g).mem t = true) ∧
      (∀ n, ¬ (reasonerSource r g).den.names n) ∧
      r.regime.Entails g (r.run g) ∧
      (reasonerSource r g).assumptions = [] := by
  refine ⟨fun t => ?_, fun n hn => ?_, r.sound g, rfl⟩
  · exact Dataset.certify_memQuad _ t none
  · have := (Dataset.certify_names { default := r.run g, named := [] } n).mp hn
    simp [Dataset.names] at this

/-- A reasoner over the default graph of a source's output. -/
def Sourced.reason (s : Sourced) (r : SoundReasoner) : Sourced := reasonerSource r s.ref.default

theorem Sourced.reason_input (s : Sourced) (hs : Assumed s.assumptions) (t : Triple) :
    s.ref.default.mem t = true ↔ s.den.graph none t := by
  show s.ref.den.graph none t ↔ _
  rw [s.den_eq hs]
  rfl

/-! ## (f) A store read as the default graph (HDT, COTTAS, RML, overlays) -/

/-- Any `LawfulStore` as the default graph of a record (`LawfulDataset.ofDefault`),
with the triples of its unbounded search as the reference value. -/
def Sourced.ofStore (st : LawfulStore) : Sourced where
  store := LawfulDataset.ofDefault st
  ref := (Dataset.certify { default := st.search patternBoundAll, named := [] }).val
  isSet := (Dataset.certify { default := st.search patternBoundAll, named := [] }).property
  den_eq := fun h => by
    rw [Dataset.certify_den]
    apply DatasetDen.ext
    · intro gn t
      cases gn with
      | none =>
        show Graph.mem t (st.search patternBoundAll) = true ↔ none = none ∧ ∃ u, st.graph u ∧ u.key = t.key
        rw [← keyMem_iff_mem]
        constructor
        · intro hk
          obtain ⟨u, hu, e⟩ := hk
          have := (st.search_exact h patternBoundAll u).mp (KeyMem.of_mem hu)
          exact ⟨rfl, u, this.1, e⟩
        · rintro ⟨-, u, hu, e⟩
          exact (KeyMem.congr e).mp ((st.search_exact h patternBoundAll u).mpr
            ⟨hu, boundMatches_all u⟩)
      | some n =>
        show (∃ ng ∈ ([] : List NamedGraph), _) ↔ some n = none ∧ _
        simp
    · intro n
      show n ∈ ([] : List NamedGraph).map (·.name) ↔ False
      simp

/-- **Source theorem (f), a store**: the record's den is the store's graph as
the default graph (`defaultDen`), with the store's named assumptions. -/
theorem Sourced.ofStore_spec (st : LawfulStore) :
    (Sourced.ofStore st).den = LawfulDataset.defaultDen st.graph ∧
      (Sourced.ofStore st).assumptions = st.assumed_contracts :=
  ⟨rfl, rfl⟩

/-! ## (e) A union of records (shards) -/

/-- The named backend of the name `n`, the first one. -/
abbrev lookupNamedBackend (l : List NamedGraphBackend) (n : Subject) : Option NamedGraphBackend :=
  l.find? (fun b => b.name == n)

/-- A named backend of the first record merged with the second record's
backend of the same name, when there is one. -/
def mergeArm (b : GraphBackend) : Option NamedGraphBackend → GraphBackend
  | some b2 => .union [b, b2.backend]
  | none => b

/-- The named backends of a union: the first record's names, each merged with
the second's backend of that name, then the second record's other names. -/
def unionNamed (l1 l2 : List NamedGraphBackend) : List NamedGraphBackend :=
  l1.map (fun b => ⟨b.name, mergeArm b.backend (lookupNamedBackend l2 b.name)⟩) ++
    l2.filter (fun b => !(l1.any (fun x => x.name == b.name)))

/-- The backend of a union of two dataset records. -/
def unionBackend (a b : DatasetBackend) : DatasetBackend :=
  { default := .union [a.default, b.default], named := unionNamed a.named b.named }

theorem backendExact_union2 {x y : GraphBackend} {Gx Gy : Triple → Prop}
    (hx : BackendExact x Gx) (hy : BackendExact y Gy) :
    BackendExact (.union [x, y]) (fun t => Gx t ∨ Gy t) :=
  ⟨[Gx, Gy], ⟨hx, hy, trivial⟩, fun t => by simp [unionPred]⟩

theorem unionNamed_left_names (l1 l2 : List NamedGraphBackend) :
    (l1.map (fun b => (⟨b.name, mergeArm b.backend (lookupNamedBackend l2 b.name)⟩ :
      NamedGraphBackend))).map (·.name) = l1.map (·.name) := by
  rw [List.map_map]
  rfl

/-- **The union backend reads the union of the denotations.** -/
theorem unionBackend_exact {DA DB : DatasetDen} {a b : DatasetBackend}
    (hA : DatasetBackendExact DA a) (hB : DatasetBackendExact DB b) :
    DatasetBackendExact (DA.union DB) (unionBackend a b) where
  default := backendExact_union2 hA.default hB.default
  named := by
    intro ngb hngb
    rcases List.mem_append.mp hngb with h1 | h2
    · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp h1
      obtain ⟨m, hm, e, hbx⟩ := hA.named b0 hb0
      subst e
      refine ⟨b0.name, Or.inl hm, rfl, ?_⟩
      show BackendExact (mergeArm b0.backend (lookupNamedBackend b.named b0.name)) _
      cases hl : lookupNamedBackend b.named b0.name with
      | some b2 =>
        have hm2 : b2 ∈ b.named := List.mem_of_find?_eq_some hl
        have hp := _root_.List.find?_some hl
        have hn2 : b2.name = b0.name := beq_iff_eq.mp hp
        obtain ⟨m2, _, e2, hby⟩ := hB.named b2 hm2
        rw [hn2] at e2
        subst e2
        exact backendExact_union2 hbx hby
      | none =>
        refine backendExact_congr hbx (fun t => ⟨Or.inl, fun h => h.elim id (fun hb => ?_)⟩)
        exfalso
        obtain ⟨b2, hb2, e2⟩ := hB.names _ (DB.named_mem _ _ hb)
        exact List.find?_eq_none.mp hl b2 hb2 (beq_iff_eq.mpr e2.symm)
    · obtain ⟨hb2, hnot⟩ := List.mem_filter.mp h2
      obtain ⟨m, hm, e, hby⟩ := hB.named ngb hb2
      subst e
      refine ⟨ngb.name, Or.inr hm, rfl, ?_⟩
      refine backendExact_congr hby (fun t => ⟨Or.inr, fun h => h.elim (fun ha => ?_) id⟩)
      exfalso
      obtain ⟨b1, hb1, e1⟩ := hA.names _ (DA.named_mem _ _ ha)
      have : a.named.any (fun x => x.name == ngb.name) = true :=
        List.any_eq_true.mpr ⟨b1, hb1, beq_iff_eq.mpr e1.symm⟩
      simp [this] at hnot
  names := by
    rintro n (hn | hn)
    · obtain ⟨b0, hb0, e⟩ := hA.names n hn
      exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨b0, hb0, rfl⟩), e⟩
    · by_cases hany : a.named.any (fun x => x.name == n) = true
      · obtain ⟨b0, hb0, he⟩ := List.any_eq_true.mp hany
        exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨b0, hb0, rfl⟩),
          (beq_iff_eq.mp he).symm⟩
      · obtain ⟨b2, hb2, e⟩ := hB.names n hn
        refine ⟨b2, List.mem_append_right _ (List.mem_filter.mpr ⟨hb2, ?_⟩), e⟩
        subst e
        simpa using hany
  namesNodup := by
    show ((unionNamed a.named b.named).map (·.name)).Nodup
    rw [unionNamed, List.map_append, unionNamed_left_names, List.nodup_append]
    refine ⟨hA.namesNodup,
      List.Nodup.sublist ((List.filter_sublist).map _) hB.namesNodup, ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨b2, hb2, rfl⟩ := List.mem_map.mp hy
    obtain ⟨_, hnot⟩ := List.mem_filter.mp hb2
    obtain ⟨b1, hb1, e1⟩ := List.mem_map.mp hx
    have : a.named.any (fun x => x.name == b2.name) = true :=
      List.any_eq_true.mpr ⟨b1, hb1, beq_iff_eq.mpr e1⟩
    simp [this] at hnot

/-- **The union of two lawful records**: the union backend, the union of the
denotations, both records' named assumptions. -/
def LawfulDataset.union (A B : LawfulDataset) : LawfulDataset where
  backend := unionBackend A.backend B.backend
  den := A.den.union B.den
  assumed_contracts := A.assumed_contracts ++ B.assumed_contracts
  law := fun h => unionBackend_exact (A.law (Assumed.left h)) (B.law (Assumed.right h))

/-- The union of two sources' outputs. The reference dataset is the set of
quads of the two datasets combined. -/
def Sourced.union (s t : Sourced) : Sourced where
  store := LawfulDataset.union s.store t.store
  ref := (Dataset.combine s.ref t.ref).certify.val
  isSet := (Dataset.combine s.ref t.ref).certify.property
  den_eq := fun h => by
    rw [Dataset.certify_den, Dataset.den_combine, s.den_eq (Assumed.left h),
      t.den_eq (Assumed.right h)]
    rfl

/-- **Source theorem (e), a union**: the den is the union of the dens; the
named assumptions are both members'. -/
theorem Sourced.union_spec (s t : Sourced) :
    (s.union t).den = s.den.union t.den ∧
      (s.union t).assumptions = s.assumptions ++ t.assumptions :=
  ⟨rfl, rfl⟩

/-- The union of shards: `s` and then each of `ss`, in order. -/
def Sourced.unionAll (s : Sourced) (ss : List Sourced) : Sourced :=
  ss.foldl Sourced.union s

/-- **Source theorem (e), shards**: the den is the union of the shards' dens;
the named assumptions are all the shards'. -/
theorem Sourced.unionAll_spec (ss : List Sourced) :
    ∀ s : Sourced,
      (s.unionAll ss).den = ss.foldl (fun d x => d.union x.den) s.den ∧
        (s.unionAll ss).assumptions = s.assumptions ++ ss.flatMap (·.assumptions) := by
  induction ss with
  | nil => intro s; simp [Sourced.unionAll]
  | cons x xs ih =>
    intro s
    obtain ⟨h1, h2⟩ := ih (s.union x)
    refine ⟨h1, ?_⟩
    show ((s.union x).unionAll xs).assumptions = _
    rw [h2, (Sourced.union_spec s x).2, List.flatMap_cons, List.append_assoc]

#print axioms Dataset.certify_den
#print axioms handleSource_spec
#print axioms Sourced.handle_den
#print axioms updateSource_spec
#print axioms reasonerSource_spec
#print axioms unionBackend_exact
#print axioms Sourced.ofStore
#print axioms Sourced.ofStore_spec
#print axioms Sourced.union
#print axioms Sourced.union_spec
#print axioms Sourced.unionAll_spec

end L4Factoidal.Dataflow
