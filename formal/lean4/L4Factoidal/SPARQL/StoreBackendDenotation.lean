/-
L4Factoidal.SPARQL.StoreBackendDenotation — the backends of
`SPARQL/StoreBackend.lean` against the denotation laws of
`RDF/StoreCapsDenotation.lean` (https://github.com/danbri/factoidal/issues/975,
phase B: B1 for the builders of this layer, B2 for the dispatchers).

## B1: the builders

* `capsOfReadOps_exact`: the two read-ops arms (HDT, in-memory COTTAS), from
  the law of the reader (`BackendReadOpsExact`, a named assumption: the reader
  is file access).
* `capsOfList_exact`: the list record, for a list with no two RDF-term-equal
  entries (`Graph.KeyNodup`; for a graph of a dataset, `Dataset.IsSet`).
  `capsOfList_solveExact` needs no set hypothesis. `keyNodup_of_capsOfList_exact`
  is the converse: a list record is lawful ONLY for a list without repeats, so
  `capsOfList [a, a]` has no denotation (`capsOfList_dup_not_exact`).
* `capsOfRmlSource_lawful` and `capsOfRmlSource_nodupKeys`: the RML virtual
  source satisfies the five laws and has no repeated row, with no hypothesis
  (`rmlSolve` ends with `dedupeTriples`). `capsOfRmlSource_exact`: it reads
  `rmlGraph vs`, the default graph of the materialising evaluation
  (`RML.evalMapping`) of the mapping over its documents, under two OPEN
  hypotheses: `RmlPushdownInvisible` (the pushdown, structural narrowing and
  the record-level subject probe, drops no matching triple; seven `#guard`s in
  `RML/VirtualSource.lean`) and `RmlVirtualIsMaterialised` (the unbounded
  virtual solve holds the materialised default graph; `#guard`s in
  `SPARQL/StoreCapsDenotationTests.lean`). Neither is proved.
* `capsOfBackend_exact` and `capsOfBackendList_exact`: every arm of the one
  dispatch point, from `BackendExact`, a law per arm (the list is a set; the
  index is well formed over a set; each reader satisfies its reader law; each
  union member is lawful; the overlay's base reader satisfies its law; the RML
  source satisfies `RmlPushdownInvisible`; the record arm `.caps c` is
  `StoreCapsExact` of the record).

## B2: the dispatchers, against the denotation only

For a backend `gb` with `BackendExact gb G`:

* `backendSearch_exact`, `backendSearch_nodupKeys`: the rows of a search are
  the matching triples of `G`, each once;
* `backendSearchLimited_sub`: a limited search returns a prefix of them;
* `backendCountExact_eq_of_den`: two backends with one denotation give one
  exact count;
* `backendSearch_keys_perm_of_den`: two backends with one denotation give the
  same rows up to order and RDF term equality;
* `backendPredicatePresent_false`: a predicate reported absent is the
  predicate of no triple of `G`.

The six `_via_caps` theorems of `SPARQL/StoreBackend.lean` and
`capsOfReadOps_lawful`, `capsOfList_lawful` stay as they are: they state the
dispatch and the five laws; the theorems here add the denotation.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.StoreBackend
import L4Factoidal.RDF.StoreCapsDenotation

namespace L4Factoidal.SPARQL.StoreBackend

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.RDF.CottasCaps

/-! ## 1. The read-ops arms -/

/-- The reader `ops` reads exactly the graph `G`: the law the HDT and the
in-memory COTTAS reader must satisfy. -/
structure BackendReadOpsExact (G : Triple → Prop) (ops : BackendReadOps) : Prop where
  searchExact : ∀ b t, KeyMem (ops.search b) t ↔ G t ∧ boundMatches b t = true
  searchNodupKeys : ∀ b, ((ops.search b).map Triple.key).Nodup
  estimateIsCount : ∀ b, ops.estimate b = (ops.search b).length
  presenceSound : ∀ pred, ops.predicatePresent pred = false → ops.search { p := some pred } = []

theorem capsOfReadOps_exact {G : Triple → Prop} {ops : BackendReadOps} (named : Bool)
    (h : BackendReadOpsExact G ops) : StoreCapsExact G (capsOfReadOps ops named) where
  toStoreCapsLawful := capsOfReadOps_lawful ops named h.estimateIsCount h.presenceSound
  solveExact := h.searchExact
  solveNodupKeys := h.searchNodupKeys
  distinctPredicatesComplete f hf := absurd hf (by simp [capsOfReadOps])

/-! ## 2. The list record -/

/-- Exactness of the list record needs no set hypothesis. -/
theorem capsOfList_solveExact (g : Graph) (b : PatternBound) (t : Triple) :
    KeyMem ((capsOfList g).solve b) t ↔ KeyMem g t ∧ boundMatches b t = true :=
  keyMem_filter_bound g b t

/-- **The list record is lawful** for any graph predicate that `g` enumerates,
when `g` has no two RDF-term-equal entries. -/
theorem capsOfList_exact {g : Graph} {G : Triple → Prop} (hset : g.KeyNodup)
    (hG : ∀ t, G t ↔ KeyMem g t) : StoreCapsExact G (capsOfList g) where
  toStoreCapsLawful := capsOfList_lawful g
  solveExact b t := by rw [capsOfList_solveExact, hG]
  solveNodupKeys b := keyNodup_filter hset _
  distinctPredicatesComplete f hf := absurd hf (by simp [capsOfList, capsOfReadOps])

theorem capsOfList_denotes {g : Graph} (hset : g.KeyNodup) :
    StoreCapsDenotes g.den none (capsOfList g) :=
  capsOfList_exact hset (Graph.den_graph_none g)

theorem capsOfList_default_denotes {ds : Dataset} (hset : ds.IsSet) :
    StoreCapsDenotes ds.den none (capsOfList ds.default) :=
  capsOfList_exact hset.default (Dataset.den_default_iff_keyMem (ds := ds))

theorem capsOfList_named_denotes {ds : Dataset} (hset : ds.IsSet) {ng : NamedGraph}
    (hng : ng ∈ ds.named) : StoreCapsDenotes ds.den (some ng.name) (capsOfList ng.graph) :=
  capsOfList_exact (hset.graphs ng hng) (Dataset.IsSet.graph_iff_keyMem_named hset hng)

/-- The converse: a list record is lawful for SOME graph only when its list has
no two RDF-term-equal entries. The unbounded read returns the list itself. -/
theorem keyNodup_of_capsOfList_exact {g : Graph} {G : Triple → Prop}
    (h : StoreCapsExact G (capsOfList g)) : g.KeyNodup := by
  have hn := h.solveNodupKeys patternBoundAll
  have hall : (capsOfList g).solve patternBoundAll = g := by
    show g.filter (boundMatches patternBoundAll) = g
    exact List.filter_eq_self.mpr (fun _ _ => rfl)
  rw [hall] at hn
  exact hn

/-- **A duplicate-row backend has no denotation.** The list record of a list
with a repeated triple is lawful for no graph. -/
theorem capsOfList_dup_not_exact (t : Triple) (g : Graph) (G : Triple → Prop) :
    ¬ StoreCapsExact G (capsOfList (t :: t :: g)) := by
  intro h
  have hn := keyNodup_of_capsOfList_exact h
  simp [Graph.KeyNodup] at hn

/-! ## 3. The RML virtual source -/

section Rml

open L4Factoidal.RML

private def dedupeStep (acc : Graph) (t : Triple) : Graph :=
  if Graph.mem t acc then acc else acc ++ [t]

private theorem dedupe_foldl : ∀ (ts acc : Graph), acc.KeyNodup →
    (ts.foldl dedupeStep acc).KeyNodup ∧
      ∀ t, Graph.mem t (ts.foldl dedupeStep acc) = (Graph.mem t acc || Graph.mem t ts)
  | [], acc, h => ⟨h, fun t => by simp [Graph.mem]⟩
  | x :: ts, acc, h => by
      simp only [List.foldl_cons]
      have hstep : (dedupeStep acc x).KeyNodup ∧
          ∀ t, Graph.mem t (dedupeStep acc x) = (Graph.mem t acc || x.eqb t) := by
        have : dedupeStep acc x = acc.add x := rfl
        rw [this]
        exact ⟨h.add x, fun t => mem_graph_add x acc t⟩
      obtain ⟨hn, hm⟩ := dedupe_foldl ts _ hstep.1
      refine ⟨hn, fun t => ?_⟩
      rw [hm, hstep.2]
      simp only [Graph.mem, Bool.or_assoc]

theorem dedupeTriples_spec (ts : Graph) :
    (dedupeTriples ts).KeyNodup ∧ ∀ t, Graph.mem t (dedupeTriples ts) = Graph.mem t ts := by
  have e : dedupeTriples ts = ts.foldl dedupeStep [] := rfl
  have := dedupe_foldl ts [] Graph.keyNodup_nil
  rw [e]
  exact ⟨this.1, fun t => by have h := this.2 t; simpa [Graph.mem] using h⟩

/-- The RML record satisfies the five laws of `StoreCapsLawful`, with no
hypothesis. -/
theorem capsOfRmlSource_lawful (vs : VirtualSource) : StoreCapsLawful (capsOfRmlSource vs) where
  limitAgrees _ _ := rfl
  countIsSolve _ := rfl
  estimateExact _ _ := rfl
  selectiveAgrees _ hf := absurd hf (by simp [capsOfRmlSource])
  presenceSound pred hp := by
    show rmlSolve vs { p := some pred } = []
    simp only [capsOfRmlSource, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero_eq] at hp
    exact List.eq_nil_of_length_eq_zero hp

/-- No two rows of an RML answer are RDF-term-equal, with no hypothesis. -/
theorem capsOfRmlSource_nodupKeys (vs : VirtualSource) (b : PatternBound) :
    (((capsOfRmlSource vs).solve b).map Triple.key).Nodup :=
  (dedupeTriples_spec _).1

/-- The default graph that the materialising evaluation of the mapping gives
(`RML.evalMapping`, the represented state: the mapping and its documents). -/
def rmlMaterialised (vs : VirtualSource) : Graph :=
  (evalMapping vs.baseIri vs.mapping vs.docFor).filterMap (fun q =>
    match q.g with
    | none => some ({ s := q.s, p := q.p, o := q.o } : Triple)
    | some _ => none)

/-- The graph an RML source denotes: the default graph of its materialisation. -/
def rmlGraph (vs : VirtualSource) (t : Triple) : Prop := KeyMem (rmlMaterialised vs) t

/-- OPEN hypothesis 1: the pushdown of `rmlSolve` drops no matching triple. A
bounded solve is the unbounded solve filtered by the bound (and made a set).
`RML/VirtualSource.lean` checks this with seven `#guard`s
(`pushdownIsInvisible`); it is not proved. -/
def RmlPushdownInvisible (vs : VirtualSource) : Prop :=
  ∀ b, rmlSolve vs b = dedupeTriples (tripleMatchesBound b (rmlSolve vs patternBoundAll))

/-- OPEN hypothesis 2: the unbounded virtual solve holds the triples of the
materialised default graph, and no other. `SPARQL/StoreCapsDenotationTests`
checks it on fixtures; it is not proved. -/
def RmlVirtualIsMaterialised (vs : VirtualSource) : Prop :=
  ∀ t, KeyMem (rmlSolve vs patternBoundAll) t ↔ rmlGraph vs t

/-- The RML record reads the materialised default graph, under the two open
hypotheses. -/
theorem capsOfRmlSource_exact (vs : VirtualSource) (hpush : RmlPushdownInvisible vs)
    (hmat : RmlVirtualIsMaterialised vs) :
    StoreCapsExact (rmlGraph vs) (capsOfRmlSource vs) where
  toStoreCapsLawful := capsOfRmlSource_lawful vs
  solveExact b t := by
    show KeyMem (rmlSolve vs b) t ↔ _
    rw [hpush b, keyMem_iff_mem, (dedupeTriples_spec _).2, ← keyMem_iff_mem,
      keyMem_filter_bound, hmat]
  solveNodupKeys := capsOfRmlSource_nodupKeys vs
  distinctPredicatesComplete f hf := absurd hf (by simp [capsOfRmlSource])

end Rml

/-! ## 4. The one dispatch point

`BackendExact gb G` is the law of the backend `gb` for the graph `G`, one
clause per arm. Each clause names what the arm's builder needs and nothing
else. -/

mutual

def BackendExact : GraphBackend → (Triple → Prop) → Prop
  | .list g, G => g.KeyNodup ∧ ∀ t, G t ↔ KeyMem g t
  | .indexed i, G => ∃ g, OWL.RL.Index.Wf i g ∧ g.KeyNodup ∧ ∀ t, G t ↔ KeyMem g t
  | .hdt ops, G => BackendReadOpsExact G ops
  | .cottasInMemory ops, G => BackendReadOpsExact G ops
  | .cottasOnDisk ops scope, G => CottasReadOpsExact G ops scope
  | .cottasOnDiskDelta ops scope delta, G =>
      ∃ G₀, CottasReadOpsExact G₀ ops scope ∧ ∀ t, G t ↔ overlayPred G₀ delta t
  | .union members, G =>
      ∃ Gs, BackendsExact members Gs ∧ ∀ t, G t ↔ unionPred Gs t
  | .virtualRml vs, G =>
      RmlPushdownInvisible vs ∧ RmlVirtualIsMaterialised vs ∧ ∀ t, G t ↔ rmlGraph vs t
  | .caps c, G => StoreCapsExact G c

/-- One graph per member, in member order. -/
def BackendsExact : List GraphBackend → List (Triple → Prop) → Prop
  | [], [] => True
  | m :: ms, G :: Gs => BackendExact m G ∧ BackendsExact ms Gs
  | _, _ => False

end

private theorem membersOf_fst : ∀ (Gs : List (Triple → Prop)) (cs : List StoreCaps),
    Gs.length = cs.length → (Gs.zip cs).map Prod.fst = Gs
  | [], [], _ => rfl
  | _ :: Gs, _ :: cs, h => by
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact membersOf_fst Gs cs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

private theorem membersOf_snd : ∀ (Gs : List (Triple → Prop)) (cs : List StoreCaps),
    Gs.length = cs.length → (Gs.zip cs).map Prod.snd = cs
  | [], [], _ => rfl
  | _ :: Gs, _ :: cs, h => by
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact membersOf_snd Gs cs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

mutual

/-- **Every arm of the dispatch point is lawful.** -/
theorem capsOfBackend_exact : ∀ (gb : GraphBackend) (G : Triple → Prop),
    BackendExact gb G → StoreCapsExact G (capsOfBackend gb)
  | .list g, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact capsOfList_exact h.1 h.2
  | .indexed i, G, h => by
      simp only [BackendExact] at h
      obtain ⟨g, hw, hset, hG⟩ := h
      simp only [capsOfBackend]
      exact capsOfIndexed_exact hw hset hG
  | .hdt ops, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact capsOfReadOps_exact false h
  | .cottasInMemory ops, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact capsOfReadOps_exact true h
  | .cottasOnDisk ops scope, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact capsOfCottas_exact h
  | .cottasOnDiskDelta ops scope delta, G, h => by
      simp only [BackendExact] at h
      obtain ⟨G₀, h₀, hG⟩ := h
      simp only [capsOfBackend]
      exact (overlay_exact delta (capsOfCottas_exact h₀)).of_iff (fun t => (hG t).symm)
  | .union members, G, h => by
      simp only [BackendExact] at h
      obtain ⟨Gs, hms, hG⟩ := h
      simp only [capsOfBackend]
      obtain ⟨hlen, hex⟩ := capsOfBackendList_exact members Gs hms
      have := unionCaps_exact (ms := Gs.zip (capsOfBackendList members)) hex
      rw [membersOf_fst Gs _ hlen, membersOf_snd Gs _ hlen] at this
      exact this.of_iff (fun t => (hG t).symm)
  | .virtualRml vs, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact (capsOfRmlSource_exact vs h.1 h.2.1).of_iff (fun t => (h.2.2 t).symm)
  | .caps c, G, h => by
      simp only [BackendExact] at h
      simp only [capsOfBackend]
      exact h

/-- The members of a union, each lawful for its graph. -/
theorem capsOfBackendList_exact : ∀ (ms : List GraphBackend) (Gs : List (Triple → Prop)),
    BackendsExact ms Gs →
      Gs.length = (capsOfBackendList ms).length ∧ MembersExact (Gs.zip (capsOfBackendList ms))
  | [], [], _ => ⟨rfl, fun _ hx => absurd hx List.not_mem_nil⟩
  | m :: ms, G :: Gs, h => by
      simp only [BackendsExact] at h
      obtain ⟨hm, hrest⟩ := h
      obtain ⟨hlen, hex⟩ := capsOfBackendList_exact ms Gs hrest
      refine ⟨by simp [capsOfBackendList, hlen], ?_⟩
      intro x hx
      simp only [capsOfBackendList, List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact capsOfBackend_exact m G hm
      · exact hex x hx
  | [], _ :: _, h => by simp [BackendsExact] at h
  | _ :: _, [], h => by simp [BackendsExact] at h

end

/-! ## 5. B2: the dispatchers against the denotation -/

section Dispatchers

variable {gb gb' : GraphBackend} {G : Triple → Prop}

/-- The rows of a search are the matching triples of the denotation. -/
theorem backendSearch_exact (h : BackendExact gb G) (b : PatternBound) (t : Triple) :
    KeyMem (backendSearch gb b) t ↔ G t ∧ boundMatches b t = true :=
  (capsOfBackend_exact gb G h).solveExact b t

/-- Each matching triple is a row once. -/
theorem backendSearch_nodupKeys (h : BackendExact gb G) (b : PatternBound) :
    ((backendSearch gb b).map Triple.key).Nodup :=
  (capsOfBackend_exact gb G h).solveNodupKeys b

/-- A limited search returns a prefix of the full search, so every row is a
matching triple of the denotation. -/
theorem backendSearchLimited_sub (h : BackendExact gb G) (b : PatternBound) (n : Nat) {u : Triple}
    (hu : u ∈ backendSearchLimited gb b n) : G u ∧ boundMatches b u = true := by
  have hl := (capsOfBackend_exact gb G h).limitAgrees b n
  rw [backendSearchLimited, hl, capsTakeN] at hu
  exact (capsOfBackend_exact gb G h).mem_solve (List.mem_of_mem_take hu)

/-- Two backends with one denotation return the same rows up to order and RDF
term equality. -/
theorem backendSearch_keys_perm_of_den (h : BackendExact gb G) (h' : BackendExact gb' G)
    (b : PatternBound) :
    ((backendSearch gb b).map Triple.key).Perm ((backendSearch gb' b).map Triple.key) :=
  (capsOfBackend_exact gb G h).keys_perm (capsOfBackend_exact gb' G h') b

/-- Two backends with one denotation give one exact count. -/
theorem backendCountExact_eq_of_den (h : BackendExact gb G) (h' : BackendExact gb' G)
    (b : PatternBound) : backendCountExact gb b = backendCountExact gb' b :=
  (capsOfBackend_exact gb G h).countExact_eq (capsOfBackend_exact gb' G h') b

/-- A predicate that a backend reports absent is the predicate of no triple of
its denotation. -/
theorem backendPredicatePresent_false (h : BackendExact gb G) {pred : WfIri}
    (hp : backendPredicatePresent gb pred = false) (t : Triple) (ht : G t) : t.p ≠ pred := by
  intro e
  have hnil := (capsOfBackend_exact gb G h).presenceSound pred hp
  have hm : KeyMem ((capsOfBackend gb).solve { p := some pred }) t :=
    ((capsOfBackend_exact gb G h).solveExact _ t).mpr
      ⟨ht, by simp [boundMatches, e]⟩
  rw [hnil] at hm
  exact keyMem_nil t hm

end Dispatchers

#print axioms capsOfReadOps_exact
#print axioms capsOfList_exact
#print axioms capsOfList_default_denotes
#print axioms capsOfList_named_denotes
#print axioms keyNodup_of_capsOfList_exact
#print axioms capsOfList_dup_not_exact
#print axioms dedupeTriples_spec
#print axioms capsOfRmlSource_lawful
#print axioms capsOfRmlSource_nodupKeys
#print axioms capsOfRmlSource_exact
#print axioms capsOfBackend_exact
#print axioms capsOfBackendList_exact
#print axioms backendSearch_exact
#print axioms backendSearch_nodupKeys
#print axioms backendSearchLimited_sub
#print axioms backendSearch_keys_perm_of_den
#print axioms backendCountExact_eq_of_den
#print axioms backendPredicatePresent_false

end L4Factoidal.SPARQL.StoreBackend
