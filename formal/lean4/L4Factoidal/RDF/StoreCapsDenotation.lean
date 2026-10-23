/-
L4Factoidal.RDF.StoreCapsDenotation — lawful `StoreCaps` with a denotation
(https://github.com/danbri/factoidal/issues/975, phase B, step B1).

`StoreCaps` (`RDF/StoreCapabilities.lean`) is the record the planner and the
SPARQL evaluator call. `StoreCapsLawful` (`RDF/StoreCapabilitiesCottas.lean`)
states five laws that relate its fields to each other. Neither said WHICH
triples `solve` returns. This module adds that: a record denotes one graph, and
its reads return that graph's matching triples, each once.

## The laws

A `StoreCaps` record reads ONE graph: `PatternBound` binds subject, predicate
and object and has no graph position. So the denotation of a record is one
graph predicate `G : Triple → Prop`; for a graph of a dataset it is
`d.graph gn` for a `DatasetDen` `d` and a graph position `gn` (`none` is the
default graph, `some n` the named graph `n`). `StoreCapsDenotes d gn caps` is
`StoreCapsExact (d.graph gn) caps`. The runtime record is unchanged: the
denotation is a parameter of the law, not a field of the record.

`StoreCapsExact G caps` holds the five laws of `StoreCapsLawful` and three
more:

* `solveExact`: `KeyMem (caps.solve b) t ↔ G t ∧ boundMatches b t = true`.
  `KeyMem xs t` is `∃ u ∈ xs, u.key = t.key`: membership up to RDF term
  equality (`Triple.key`; RDF 1.2 Concepts section 3.4, language tags compare
  ASCII case-insensitively). A record returns one stored spelling of a term;
  `"chat"@EN` and `"chat"@en` are one RDF term, so structural list membership
  is not the right relation.
* `solveNodupKeys`: no two rows of one answer are RDF-term-equal
  (`((caps.solve b).map Triple.key).Nodup`). RDF 1.1 Concepts section 3: "An
  RDF graph is a set of RDF triples." SPARQL 1.1 section 18.4 counts each
  solution of a basic graph pattern once per matching triple of the graph, so
  a repeated row is a repeated solution.
* `distinctPredicatesComplete`: when the record enumerates predicates, the list
  has no duplicate and holds the predicate of every triple of the graph.

`distinctPredicates` is complete, not exact. The one consumer
(`SPARQL/StoreDataset.lean`, `predicateGroupByAcc`) counts each listed
predicate with `countExact` and drops a predicate whose count is zero, so a
listed predicate that the graph does not use costs one count and changes no
answer. The COTTAS reader cannot give an exact list for a graph scope: its
`distinctPredicates` takes no scope and enumerates the dictionary of the whole
file (`CottasReadOps.distinctPredicates : Unit → Option (List WfIri)`), so for
a named graph or for the default graph of a file with named graphs the list
can hold predicates that the scope does not use.

## Instances in this module

* `capsOfIndexed_exact`: the in-memory index, for an index with `Index.Wf i g`
  (every index made by `Index.ofGraph g`) and `g.KeyNodup`. The record reads
  the denotation of `g` exactly; without `KeyNodup` only `solveNodupKeys`
  fails (`capsOfIndexed_solveExact` needs no set hypothesis).
* `capsOfCottas_exact`: the COTTAS on-disk record, from the law of its reader
  (`CottasReadOpsExact`, a named I/O assumption: the reader is file access).
* `unionCaps_exact`: the union of records whose graphs are pairwise disjoint.
  Without disjointness `solveNodupKeys` fails: `unionSolve` concatenates the
  members' answers and does not remove a triple that two members hold.
* `overlay_exact`: a record with a resolved delta (`RDF/StoreCapabilitiesDelta`)
  denotes `overlayPred G dr`, the base graph without the tombstoned triples and
  with the added triples. Hypothesis: the base record does not advertise an
  exact estimate. The overlay copies the base's `estimateIsExact` flag and
  estimates `base.estimate + added`, which overcounts under a tombstone; over
  a record that advertises an exact estimate (the in-memory index) the
  overlay breaks `estimateExact`. Every overlay that `capsOfBackend` builds is
  over `capsOfCottas`, which does not advertise it.
  `overlayPred_fold` connects the overlay to the reference model of
  `RDF/StoreDeltaMerge.lean`: for a log folded with `foldEntriesForGraph`, the
  overlay of the graph `gBase` denotes the graph that the entries applied to
  `gBase` give (`applyEntriesRef`).

`SPARQL/StoreBackendDenotation.lean` adds `capsOfReadOps`, `capsOfList`,
`capsOfRmlSource`, `capsOfBackend` and `capsOfBackendList`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.StoreCapabilitiesCottas
import L4Factoidal.RDF.StoreCapabilitiesDelta
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.RDF

open L4Factoidal.SPARQL (PatternBound patternBoundAll boundMatches tripleMatchesBound
  boundMatches_congr mem_tripleMatchesBound)
open L4Factoidal.RDF.CottasCaps

/-! ## 1. Membership up to RDF term equality -/

/-- The rows `xs` hold the triple `t` up to RDF term equality. -/
def KeyMem (xs : List Triple) (t : Triple) : Prop := ∃ u ∈ xs, u.key = t.key

theorem KeyMem.of_mem {xs : List Triple} {t : Triple} (h : t ∈ xs) : KeyMem xs t := ⟨t, h, rfl⟩

theorem keyMem_iff_mem (xs : Graph) (t : Triple) : KeyMem xs t ↔ xs.mem t = true :=
  (Graph.mem_iff_key t xs).symm

theorem KeyMem.congr {xs : List Triple} {t u : Triple} (e : t.key = u.key) :
    KeyMem xs t ↔ KeyMem xs u :=
  ⟨fun ⟨v, hv, ev⟩ => ⟨v, hv, ev.trans e⟩, fun ⟨v, hv, ev⟩ => ⟨v, hv, ev.trans e.symm⟩⟩

theorem keyMem_nil (t : Triple) : ¬ KeyMem [] t := fun ⟨_, h, _⟩ => List.not_mem_nil h

/-- The bound test sees RDF term equality only. -/
theorem boundMatches_key (b : PatternBound) {u t : Triple} (e : u.key = t.key) :
    boundMatches b u = boundMatches b t :=
  boundMatches_congr b u t ((Triple.eqb_iff_key u t).mpr e)

/-- The matching rows of a list, up to RDF term equality. -/
theorem keyMem_filter_bound (g : Graph) (b : PatternBound) (t : Triple) :
    KeyMem (tripleMatchesBound b g) t ↔ KeyMem g t ∧ boundMatches b t = true := by
  constructor
  · rintro ⟨u, hu, e⟩
    have hu' := List.mem_filter.mp hu
    exact ⟨⟨u, hu'.1, e⟩, (boundMatches_key b e) ▸ hu'.2⟩
  · rintro ⟨⟨u, hu, e⟩, hb⟩
    exact ⟨u, List.mem_filter.mpr ⟨hu, (boundMatches_key b e).trans hb⟩, e⟩

theorem keyNodup_filter {g : Graph} (h : g.KeyNodup) (q : Triple → Bool) :
    ((g.filter q).map Triple.key).Nodup :=
  List.Nodup.sublist (List.Sublist.map Triple.key (List.filter_sublist)) h

/-! ## 2. The laws -/

/-- A record `caps` reads exactly the graph `G`: the five laws of
`StoreCapsLawful` and three about the rows. -/
structure StoreCapsExact (G : Triple → Prop) (caps : StoreCaps) : Prop
    extends StoreCapsLawful caps where
  /-- A read returns the triples of `G` that match the bound, up to RDF term
  equality, and no other. -/
  solveExact : ∀ b t, KeyMem (caps.solve b) t ↔ G t ∧ boundMatches b t = true
  /-- No two rows of one answer are RDF-term-equal. -/
  solveNodupKeys : ∀ b, ((caps.solve b).map Triple.key).Nodup
  /-- A predicate list, when the record gives one, has no duplicate and holds
  the predicate of every triple of `G`. -/
  distinctPredicatesComplete : ∀ f, caps.distinctPredicates = some f →
    ∀ ps, f () = some ps → ps.Nodup ∧ ∀ t, G t → t.p ∈ ps

/-- A record reads the graph `gn` of the dataset denotation `d`. -/
abbrev StoreCapsDenotes (d : DatasetDen) (gn : Option Subject) (caps : StoreCaps) : Prop :=
  StoreCapsExact (d.graph gn) caps

namespace StoreCapsExact

variable {G : Triple → Prop} {caps : StoreCaps}

/-- Every row of an answer is a triple of the graph that matches the bound. -/
theorem mem_solve (h : StoreCapsExact G caps) {b : PatternBound} {u : Triple}
    (hu : u ∈ caps.solve b) : G u ∧ boundMatches b u = true :=
  (h.solveExact b u).mp (KeyMem.of_mem hu)

/-- The unbounded read enumerates the graph. -/
theorem solve_all (h : StoreCapsExact G caps) (t : Triple) :
    KeyMem (caps.solve patternBoundAll) t ↔ G t := by
  rw [h.solveExact]
  exact ⟨And.left, fun ht => ⟨ht, rfl⟩⟩

/-- The graph of a lawful record is closed under RDF term equality. -/
theorem graph_key (h : StoreCapsExact G caps) {t u : Triple} (e : t.key = u.key) (ht : G t) : G u :=
  (h.solve_all u).mp ((KeyMem.congr e).mp ((h.solve_all t).mpr ht))

/-- Two lawful records of one graph return the same rows up to order and RDF
term equality: their key lists are permutations of each other. -/
theorem keys_perm {caps' : StoreCaps} (h : StoreCapsExact G caps) (h' : StoreCapsExact G caps')
    (b : PatternBound) : ((caps.solve b).map Triple.key).Perm ((caps'.solve b).map Triple.key) := by
  apply (List.perm_ext_iff_of_nodup (h.solveNodupKeys b) (h'.solveNodupKeys b)).2
  intro k
  constructor
  · intro hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
    obtain ⟨v, hv, e⟩ := (h'.solveExact b u).mpr (h.mem_solve hu)
    exact List.mem_map.mpr ⟨v, hv, e⟩
  · intro hk
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
    obtain ⟨v, hv, e⟩ := (h.solveExact b u).mpr (h'.mem_solve hu)
    exact List.mem_map.mpr ⟨v, hv, e⟩

/-- The exact count of a lawful record is the number of RDF-term-distinct
matching triples of its graph: two lawful records of one graph give one count. -/
theorem countExact_eq {caps' : StoreCaps} (h : StoreCapsExact G caps)
    (h' : StoreCapsExact G caps') (b : PatternBound) : caps.countExact b = caps'.countExact b := by
  rw [h.countIsSolve, h'.countIsSolve, ← List.length_map (f := Triple.key),
    ← List.length_map (as := caps'.solve b) (f := Triple.key)]
  exact (h.keys_perm h' b).length_eq

/-- A record that reads an equivalent graph reads this one. -/
theorem of_iff {G' : Triple → Prop} (h : StoreCapsExact G caps) (hG : ∀ t, G t ↔ G' t) :
    StoreCapsExact G' caps where
  toStoreCapsLawful := h.toStoreCapsLawful
  solveExact b t := by rw [h.solveExact, hG]
  solveNodupKeys := h.solveNodupKeys
  distinctPredicatesComplete f hf ps hps :=
    ⟨(h.distinctPredicatesComplete f hf ps hps).1,
     fun t ht => (h.distinctPredicatesComplete f hf ps hps).2 t ((hG t).mpr ht)⟩

end StoreCapsExact

/-! ## 3. The graph of a list -/

/-- The denotation of a list of triples as the default graph of a dataset with
no named graph. -/
def Graph.den (g : Graph) : DatasetDen := ({ default := g, named := [] } : Dataset).den

theorem Graph.den_graph_none (g : Graph) (t : Triple) : g.den.graph none t ↔ KeyMem g t := by
  rw [Graph.den, Dataset.den_graph_iff]
  exact Iff.rfl

theorem Graph.den_graph_some (g : Graph) (n : Subject) (t : Triple) : ¬ g.den.graph (some n) t := by
  rw [Graph.den, Dataset.den_graph_iff]
  rintro ⟨u, ⟨ng, hng, _⟩, _⟩
  exact List.not_mem_nil hng

/-- The default graph of a dataset denotes its list entries, up to RDF term
equality. -/
theorem Dataset.den_default_iff_keyMem {ds : Dataset} (t : Triple) :
    ds.den.graph none t ↔ KeyMem ds.default t := by
  rw [Dataset.den_graph_iff]
  exact Iff.rfl

theorem Dataset.IsSet.graph_iff_keyMem_named {ds : Dataset} (h : ds.IsSet) {ng : NamedGraph}
    (hng : ng ∈ ds.named) (t : Triple) : ds.den.graph (some ng.name) t ↔ KeyMem ng.graph t := by
  rw [(h.den_named hng).2 t, ← Graph.mem_iff_keys, keyMem_iff_mem]

/-! ## 4. The in-memory index -/

section Indexed

open L4Factoidal.OWL.RL

/-- An object for which `exactObjectIndexKeySafe` holds is RDF-term-equal only
to itself. -/
theorem eq_of_eqb_of_keySafe : ∀ {o u : Term}, exactObjectIndexKeySafe o = true →
    Term.eqb o u = true → o = u
  | .iri i, .iri j, _, h => by simp only [Term.eqb, beq_iff_eq] at h; rw [h]
  | .iri _, .bnode _, _, h => by simp [Term.eqb] at h
  | .iri _, .literal _, _, h => by simp [Term.eqb] at h
  | .iri _, .tripleTerm _ _ _, _, h => by simp [Term.eqb] at h
  | .bnode i, .bnode j, _, h => by simp only [Term.eqb, beq_iff_eq] at h; rw [h]
  | .bnode _, .iri _, _, h => by simp [Term.eqb] at h
  | .bnode _, .literal _, _, h => by simp [Term.eqb] at h
  | .bnode _, .tripleTerm _ _ _, _, h => by simp [Term.eqb] at h
  | .literal l, .literal m, hs, h => by
      obtain ⟨⟨lx, ld, lt, lr⟩, lw⟩ := l
      obtain ⟨⟨mx, md, mt, mr⟩, mw⟩ := m
      simp only [exactObjectIndexKeySafe, Bool.and_eq_true, Option.isNone_iff_eq_none] at hs
      obtain ⟨hlt, _⟩ := hs
      subst hlt
      simp only [Term.eqb, Literal.eqb, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hx, hd⟩, ht⟩, hr⟩ := h
      cases mt with
      | none => subst hx; subst hd; subst hr; rfl
      | some _ => simp [langTagOptionEq] at ht
  | .literal _, .iri _, _, h => by simp [Term.eqb] at h
  | .literal _, .bnode _, _, h => by simp [Term.eqb] at h
  | .literal _, .tripleTerm _ _ _, _, h => by simp [Term.eqb] at h
  | .tripleTerm _ _ _, _, hs, _ => by simp [exactObjectIndexKeySafe] at hs

/-- A candidate set that holds every matching triple does not change the
answer. -/
theorem tripleMatchesBound_filter_of_imp {b : PatternBound} {q : Triple → Bool}
    (hq : ∀ t, boundMatches b t = true → q t = true) (g : Graph) :
    tripleMatchesBound b (g.filter q) = tripleMatchesBound b g := by
  unfold tripleMatchesBound
  rw [List.filter_filter]
  apply List.filter_congr
  intro t _
  cases hb : boundMatches b t with
  | false => simp
  | true => simp [hq t hb]

private theorem bm_s {s : Subject} {b : PatternBound} (hs : b.s = some s) {t : Triple}
    (h : boundMatches b t = true) : t.s = s := by
  simp only [boundMatches, hs, Bool.and_eq_true] at h
  exact (Subject.eqb_eq h.1.1).symm

private theorem bm_p {p : WfIri} {b : PatternBound} (hp : b.p = some p) {t : Triple}
    (h : boundMatches b t = true) : t.p = p := by
  simp only [boundMatches, hp, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2.symm

private theorem bm_o {o : Term} {b : PatternBound} (ho : b.o = some o) (hsafe : exactObjectIndexKeySafe o = true)
    {t : Triple} (h : boundMatches b t = true) : t.o = o := by
  simp only [boundMatches, ho, Bool.and_eq_true] at h
  exact (eq_of_eqb_of_keySafe hsafe h.2).symm

/-- **The index reads its graph.** Under `Index.Wf i g` every access path of
`igSearch` is a filter of `g` that keeps every matching triple, so the answer
is the list filter. -/
theorem igSearch_of_wf {i : Index} {g : Graph} (hw : Index.Wf i g) (b : PatternBound) :
    igSearch i b = tripleMatchesBound b g := by
  have hall : i.toGraph = g := hw.all
  rcases b with ⟨s, p, o⟩
  cases s with
  | some s =>
    cases p with
    | some p =>
      show tripleMatchesBound _ (i.withSubjPred s p) = _
      rw [hw.withSubjPred_eq, L4Factoidal.OWL.RL.withSubjPred]
      exact tripleMatchesBound_filter_of_imp (fun t ht => by
        simp [bm_s (b := ⟨some s, some p, o⟩) rfl ht, bm_p (b := ⟨some s, some p, o⟩) rfl ht]) g
    | none =>
      show tripleMatchesBound _ (i.withSubj s) = _
      rw [hw.withSubj_eq, L4Factoidal.OWL.RL.withSubj]
      exact tripleMatchesBound_filter_of_imp (fun t ht => by
        simp [bm_s (b := ⟨some s, none, o⟩) rfl ht]) g
  | none =>
    cases p with
    | some p =>
      cases o with
      | some o =>
        show tripleMatchesBound _
          (if exactObjectIndexKeySafe o then i.withPredObj p o else i.withPred p) = _
        split
        · rename_i hsafe
          rw [hw.withPredObj_eq, L4Factoidal.OWL.RL.withPredObj]
          exact tripleMatchesBound_filter_of_imp (fun t ht => by
            simp [bm_p (b := ⟨none, some p, some o⟩) rfl ht,
              bm_o (b := ⟨none, some p, some o⟩) rfl hsafe ht]) g
        · rw [hw.withPred_eq, L4Factoidal.OWL.RL.withPred]
          exact tripleMatchesBound_filter_of_imp (fun t ht => by
            simp [bm_p (b := ⟨none, some p, some o⟩) rfl ht]) g
      | none =>
        show tripleMatchesBound _ (i.withPred p) = _
        rw [hw.withPred_eq, L4Factoidal.OWL.RL.withPred]
        exact tripleMatchesBound_filter_of_imp (fun t ht => by
          simp [bm_p (b := ⟨none, some p, none⟩) rfl ht]) g
    | none =>
      cases o with
      | some o =>
        show tripleMatchesBound _ (if exactObjectIndexKeySafe o then i.withObj o else i.toGraph) = _
        split
        · rename_i hsafe
          rw [hw.withObj_eq, L4Factoidal.OWL.RL.withObj]
          exact tripleMatchesBound_filter_of_imp (fun t ht => by
            simp [bm_o (b := ⟨none, none, some o⟩) rfl hsafe ht]) g
        · rw [hall]
      | none =>
        show tripleMatchesBound _ i.toGraph = _
        rw [hall]

/-- Exactness of the index needs no set hypothesis. -/
theorem capsOfIndexed_solveExact {i : Index} {g : Graph} (hw : Index.Wf i g) (b : PatternBound)
    (t : Triple) : KeyMem ((capsOfIndexed i).solve b) t ↔ KeyMem g t ∧ boundMatches b t = true := by
  show KeyMem (igSearch i b) t ↔ _
  rw [igSearch_of_wf hw]
  exact keyMem_filter_bound g b t

/-- **The in-memory record is lawful** for any graph predicate `G` that `g`
enumerates, when `g` has no two RDF-term-equal entries. -/
theorem capsOfIndexed_exact {i : Index} {g : Graph} {G : Triple → Prop} (hw : Index.Wf i g)
    (hset : g.KeyNodup) (hG : ∀ t, G t ↔ KeyMem g t) : StoreCapsExact G (capsOfIndexed i) where
  toStoreCapsLawful := capsOfIndexed_lawful i
  solveExact b t := by rw [capsOfIndexed_solveExact hw, hG]
  solveNodupKeys b := by
    show ((igSearch i b).map Triple.key).Nodup
    rw [igSearch_of_wf hw]
    exact keyNodup_filter hset _
  distinctPredicatesComplete f hf := absurd hf (by simp [capsOfIndexed])

/-- The record of `Index.ofGraph g` denotes the graph `g`. -/
theorem capsOfIndexed_ofGraph_denotes {g : Graph} (hset : g.KeyNodup) :
    StoreCapsDenotes g.den none (capsOfIndexed (Index.ofGraph g)) :=
  capsOfIndexed_exact (Index.Wf.ofGraph g) hset (Graph.den_graph_none g)

/-- The record of the index of the default graph of a dataset that is a set
denotes the default graph of the dataset. -/
theorem capsOfIndexed_default_denotes {ds : Dataset} (hset : ds.IsSet) :
    StoreCapsDenotes ds.den none (capsOfIndexed (Index.ofGraph ds.default)) :=
  capsOfIndexed_exact (Index.Wf.ofGraph _) hset.default
    (Dataset.den_default_iff_keyMem (ds := ds))

/-- The same for a named graph of the dataset. -/
theorem capsOfIndexed_named_denotes {ds : Dataset} (hset : ds.IsSet) {ng : NamedGraph}
    (hng : ng ∈ ds.named) :
    StoreCapsDenotes ds.den (some ng.name) (capsOfIndexed (Index.ofGraph ng.graph)) :=
  capsOfIndexed_exact (Index.Wf.ofGraph _) (hset.graphs ng hng)
    (Dataset.IsSet.graph_iff_keyMem_named hset hng)

end Indexed

/-! ## 5. The COTTAS record

`CottasReadOpsExact` is the law of the reader: a named assumption, because the
reader is file access (memory-mapped pages and dictionary pages). The record
adds no logic, so its law is the reader's law field for field
(`capsOfCottas_exact`). The predicate list is the whole file's
(`CottasReadOps.distinctPredicates` takes no scope), so the reader law asks
only that it is complete for the scope's graph. -/

/-- The reader `ops` reads exactly the graph `G` in the scope `scope`. -/
structure CottasReadOpsExact (G : Triple → Prop) (ops : CottasReadOps) (scope : CottasScope) : Prop
    extends CottasReadOpsLawful ops scope where
  searchExact : ∀ b t, KeyMem (ops.searchTok scope b) t ↔ G t ∧ boundMatches b t = true
  searchNodupKeys : ∀ b, ((ops.searchTok scope b).map Triple.key).Nodup
  distinctComplete : ∀ ps, ops.distinctPredicates () = some ps → ps.Nodup ∧ ∀ t, G t → t.p ∈ ps

theorem capsOfCottas_exact {G : Triple → Prop} {ops : CottasReadOps} {scope : CottasScope}
    (h : CottasReadOpsExact G ops scope) : StoreCapsExact G (capsOfCottas ops scope) where
  toStoreCapsLawful := capsOfCottas_lawful ops scope h.toCottasReadOpsLawful
  solveExact := h.searchExact
  solveNodupKeys := h.searchNodupKeys
  distinctPredicatesComplete f hf ps hps := by
    simp only [capsOfCottas, Option.some.injEq] at hf
    subst hf
    exact h.distinctComplete ps hps

/-! ## 6. The union of records

`unionCaps` concatenates its members' answers. It reads the union of the
members' graphs, and it reads each triple once when no two members hold one
triple (`unionCaps_exact`, hypothesis `hdisj`). -/

/-- The union of a list of graphs. -/
def unionPred (Gs : List (Triple → Prop)) (t : Triple) : Prop := ∃ G ∈ Gs, G t

section Union

private theorem foldl_add_sum {α : Type} (f : α → Nat) :
    ∀ (ms : List α) (a : Nat), ms.foldl (fun acc m => acc + f m) a = a + (ms.map f).sum
  | [], a => by simp
  | m :: ms, a => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [foldl_add_sum f ms]
      omega

private theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
        flatMap_congr' l (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem take_append_take (A S R : List Triple) (L : Nat) (hA : A.length < L) :
    (A ++ (S.take (L - A.length) ++ R)).take L = (A ++ (S ++ R)).take L := by
  rw [List.take_append, List.take_append]
  congr 1
  rw [List.take_append, List.take_append, List.take_take, Nat.min_self, List.length_take]
  by_cases hS : S.length ≤ L - A.length
  · rw [List.take_of_length_le hS]
    simp [Nat.min_eq_right hS]
  · have h1 : L - A.length - min (L - A.length) S.length = 0 := by omega
    have h2 : L - A.length - S.length = 0 := by omega
    rw [h1, h2]

private theorem unionSolveLimitedAcc_take (b : PatternBound) (L : Nat) :
    ∀ (ms : List StoreCaps), (∀ m ∈ ms, ∀ n, m.solveLimited b n = capsTakeN n (m.solve b)) →
      ∀ accRev : List Triple,
        (unionSolveLimitedAcc ms b L accRev accRev.length).reverse.take L
          = (accRev.reverse ++ ms.flatMap (fun m => m.solve b)).take L
  | [], _, accRev => by simp [unionSolveLimitedAcc]
  | m :: rest, hl, accRev => by
      simp only [unionSolveLimitedAcc]
      split
      · rename_i hge
        rw [List.take_append_of_le_length (by rw [List.length_reverse]; exact hge)]
      · rename_i hlt
        have hlen : accRev.length + (m.solveLimited b (L - accRev.length)).length
            = ((m.solveLimited b (L - accRev.length)).reverse ++ accRev).length := by
          simp [Nat.add_comm]
        rw [hlen, unionSolveLimitedAcc_take b L rest
          (fun x hx => hl x (List.mem_cons_of_mem _ hx)), List.reverse_append,
          List.reverse_reverse, hl m List.mem_cons_self, capsTakeN, List.flatMap_cons,
          List.append_assoc]
        have := take_append_take accRev.reverse (m.solve b) (rest.flatMap (fun m => m.solve b)) L
          (by rw [List.length_reverse]; omega)
        rw [List.length_reverse] at this
        exact this

theorem unionSolveLimited_eq (ms : List StoreCaps)
    (hl : ∀ m ∈ ms, ∀ b n, m.solveLimited b n = capsTakeN n (m.solve b)) (b : PatternBound)
    (n : Nat) : unionSolveLimited ms b n = capsTakeN n (unionSolve ms b) := by
  unfold unionSolveLimited
  split
  · rename_i h0
    have : n = 0 := by simpa using h0
    subst this
    rfl
  · have := unionSolveLimitedAcc_take b n ms (fun m hm k => hl m hm b k) []
    simpa [capsTakeN, unionSolve] using this

private def capsIriDedupeStep (acc : List WfIri) (x : WfIri) : List WfIri :=
  if acc.contains x then acc else acc ++ [x]

private theorem capsIriDedupe_foldl :
    ∀ (l acc : List WfIri), acc.Nodup →
      (l.foldl capsIriDedupeStep acc).Nodup ∧
        ∀ x, x ∈ l.foldl capsIriDedupeStep acc ↔ x ∈ acc ∨ x ∈ l
  | [], acc, h => ⟨h, fun x => by simp⟩
  | y :: l, acc, h => by
      simp only [List.foldl_cons]
      have hstep : (capsIriDedupeStep acc y).Nodup ∧
          ∀ x, x ∈ capsIriDedupeStep acc y ↔ x ∈ acc ∨ x = y := by
        unfold capsIriDedupeStep
        split
        · rename_i hc
          refine ⟨h, fun x => ⟨Or.inl, ?_⟩⟩
          rintro (hx | rfl)
          · exact hx
          · exact List.contains_iff_mem.mp hc
        · rename_i hc
          refine ⟨?_, fun x => by simp⟩
          rw [List.nodup_append]
          refine ⟨h, List.pairwise_singleton _ _, ?_⟩
          intro a ha c hc'
          rw [List.mem_singleton] at hc'
          subst hc'
          intro e
          subst e
          exact hc (List.contains_iff_mem.mpr ha)
      obtain ⟨hn, hm⟩ := capsIriDedupe_foldl l _ hstep.1
      refine ⟨hn, fun x => ?_⟩
      rw [hm, hstep.2]
      simp only [List.mem_cons, or_assoc]

theorem capsIriDedupe_spec (l : List WfIri) :
    (capsIriDedupe l).Nodup ∧ ∀ x, x ∈ capsIriDedupe l ↔ x ∈ l := by
  have := capsIriDedupe_foldl l [] List.nodup_nil
  refine ⟨this.1, fun x => ?_⟩
  have h := this.2 x
  simp only [List.not_mem_nil, false_or] at h
  exact h

/-- Each member of a union, with the graph it reads. -/
abbrev Members := List ((Triple → Prop) × StoreCaps)

/-- Every member reads its graph. -/
def MembersExact (ms : Members) : Prop := ∀ x ∈ ms, StoreCapsExact x.1 x.2

/-- No two members' graphs share a triple. -/
def MembersDisjoint (ms : Members) : Prop :=
  ms.Pairwise (fun x y => ∀ t, x.1 t → ¬ y.1 t)

private theorem union_distinct_acc :
    ∀ (ms : Members), MembersExact ms →
      ∀ (acc ps : List WfIri), unionDistinctPredicatesAcc acc (ms.map Prod.snd) = some ps →
        ps.Nodup ∧ (∀ x, x ∈ acc → x ∈ ps) ∧ ∀ x ∈ ms, ∀ t, x.1 t → t.p ∈ ps
  | [], _, acc, ps, h => by
      simp only [List.map_nil, unionDistinctPredicatesAcc, Option.some.injEq] at h
      subst h
      refine ⟨(capsIriDedupe_spec acc).1, fun x hx => ((capsIriDedupe_spec acc).2 x).mpr hx, ?_⟩
      intro x hx
      exact absurd hx List.not_mem_nil
  | (G, m) :: ms, hex, acc, ps, h => by
      have hm : StoreCapsExact G m := hex (G, m) List.mem_cons_self
      have hrest : MembersExact ms := fun x hx => hex x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, unionDistinctPredicatesAcc] at h
      split at h
      · rename_i f hf
        split at h
        · rename_i qs hq
          obtain ⟨hn, hacc, hall⟩ := union_distinct_acc ms hrest (acc ++ qs) ps h
          refine ⟨hn, fun x hx => hacc x (List.mem_append_left _ hx), ?_⟩
          intro x hx t ht
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hacc _ (List.mem_append_right _ ((hm.distinctPredicatesComplete f hf qs hq).2 t ht))
          · exact hall x hx t ht
        · cases h
      · split at h
        · rename_i hz
          obtain ⟨hn, hacc, hall⟩ := union_distinct_acc ms hrest acc ps h
          refine ⟨hn, hacc, ?_⟩
          intro x hx t ht
          rcases List.mem_cons.mp hx with rfl | hx
          · have h0 : m.solve patternBoundAll = [] := by
              apply List.eq_nil_of_length_eq_zero
              rw [← hm.countIsSolve]
              simpa using hz
            have := (hm.solve_all t).mpr ht
            rw [h0] at this
            exact absurd this (keyMem_nil t)
          · exact hall x hx t ht
        · cases h

private theorem keyMem_flatMap {b : PatternBound} (ms : List StoreCaps) (t : Triple) :
    KeyMem (ms.flatMap (fun m => m.solve b)) t ↔ ∃ m ∈ ms, KeyMem (m.solve b) t := by
  constructor
  · rintro ⟨u, hu, e⟩
    obtain ⟨m, hm, hum⟩ := List.mem_flatMap.mp hu
    exact ⟨m, hm, u, hum, e⟩
  · rintro ⟨m, hm, u, hum, e⟩
    exact ⟨u, List.mem_flatMap.mpr ⟨m, hm, hum⟩, e⟩

private theorem union_exact_aux (b : PatternBound) (t : Triple) :
    ∀ (ms : Members), MembersExact ms →
      ((∃ m ∈ ms.map Prod.snd, KeyMem (m.solve b) t) ↔
        unionPred (ms.map Prod.fst) t ∧ boundMatches b t = true)
  | [], _ => by simp [unionPred]
  | (G, m) :: ms, hex => by
      have hm : StoreCapsExact G m := hex (G, m) List.mem_cons_self
      have ih := union_exact_aux b t ms (fun x hx => hex x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.mem_cons, exists_eq_or_imp, unionPred] at ih ⊢
      rw [ih, hm.solveExact]
      constructor
      · rintro (⟨hg, hb⟩ | ⟨⟨H, hH, hht⟩, hb⟩)
        · exact ⟨Or.inl hg, hb⟩
        · exact ⟨Or.inr ⟨H, hH, hht⟩, hb⟩
      · rintro ⟨hg | ⟨H, hH, hht⟩, hb⟩
        · exact Or.inl ⟨hg, hb⟩
        · exact Or.inr ⟨⟨H, hH, hht⟩, hb⟩

private theorem union_nodup_aux (b : PatternBound) :
    ∀ (ms : Members), MembersExact ms → MembersDisjoint ms →
      (((ms.map Prod.snd).flatMap (fun m => m.solve b)).map Triple.key).Nodup
  | [], _, _ => by simp
  | (G, m) :: ms, hex, hdisj => by
      have hm : StoreCapsExact G m := hex (G, m) List.mem_cons_self
      have hrest : MembersExact ms := fun x hx => hex x (List.mem_cons_of_mem _ hx)
      have hd := List.pairwise_cons.mp hdisj
      rw [List.map_cons, List.flatMap_cons, List.map_append, List.nodup_append]
      refine ⟨hm.solveNodupKeys b, union_nodup_aux b ms hrest hd.2, ?_⟩
      intro k hk k' hk' e
      subst e
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hk
      obtain ⟨v, hv, ev⟩ := List.mem_map.mp hk'
      obtain ⟨m', hm', hvm⟩ := List.mem_flatMap.mp hv
      have hGu : G u := (hm.mem_solve hu).1
      obtain ⟨⟨H, hH, hHv⟩, _⟩ := (union_exact_aux b v ms hrest).mp ⟨m', hm', KeyMem.of_mem hvm⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hH
      exact hd.1 y hy u hGu (hrest y hy |>.graph_key ev hHv)

/-- **The union of records is lawful** when no two members' graphs share a
triple. It reads the union of the members' graphs. -/
theorem unionCaps_exact {ms : Members} (hex : MembersExact ms) (hdisj : MembersDisjoint ms) :
    StoreCapsExact (unionPred (ms.map Prod.fst)) (unionCaps (ms.map Prod.snd)) := by
  have hmem : ∀ m ∈ ms.map Prod.snd, ∃ G, StoreCapsExact G m := by
    intro m hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact ⟨x.1, hex x hx⟩
  refine
    { limitAgrees := fun b n => unionSolveLimited_eq _
        (fun m hm => (hmem m hm).choose_spec.limitAgrees) b n
      countIsSolve := fun b => ?_
      estimateExact := fun hex' => absurd hex' (by simp [unionCaps])
      selectiveAgrees := fun f hf b need => ?_
      presenceSound := fun pred hp => ?_
      solveExact := fun b t => ?_
      solveNodupKeys := fun b => union_nodup_aux b ms hex hdisj
      distinctPredicatesComplete := fun f hf ps hps => ?_ }
  · show unionCountExact _ b = (unionSolve _ b).length
    rw [unionCountExact, foldl_add_sum, unionSolve, List.length_flatMap, Nat.zero_add]
    congr 1
    apply List.map_congr_left
    intro m hm
    exact (hmem m hm).choose_spec.countIsSolve b
  · simp only [unionCaps, Option.some.injEq] at hf
    subst hf
    show unionSolveSelective _ b need = unionSolve _ b
    unfold unionSolveSelective unionSolve
    apply flatMap_congr'
    intro m hm
    split
    · rename_i g hg
      exact (hmem m hm).choose_spec.selectiveAgrees g hg b need
    · rfl
  · show unionSolve _ { p := some pred } = []
    have hall : ∀ m ∈ ms.map Prod.snd, m.predicatePresent pred = false := by
      intro m hm
      have : unionPredicatePresent (ms.map Prod.snd) pred = false := hp
      simp only [unionPredicatePresent, List.any_eq_false] at this
      simpa using this m hm
    unfold unionSolve
    rw [List.flatMap_eq_nil_iff]
    intro m hm
    exact (hmem m hm).choose_spec.presenceSound pred (hall m hm)
  · show KeyMem (unionSolve _ b) t ↔ _
    rw [unionSolve, keyMem_flatMap]
    exact union_exact_aux b t ms hex
  · simp only [unionCaps, Option.some.injEq] at hf
    subst hf
    obtain ⟨hn, _, hall⟩ := union_distinct_acc ms hex [] ps hps
    refine ⟨hn, fun t ⟨G, hG, ht⟩ => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hG
    exact hall x hx t ht

end Union

/-! ## 7. Base plus delta

`overlay base dr` (`RDF/StoreCapabilitiesDelta.lean`) reads the base's rows
without the tombstoned ones (none after a CLEAR) and adds the delta's matching
additions with `Graph.union`, which adds a triple only when the rows do not
hold it already. It denotes `overlayPred G dr`. -/

/-- The graph that the base graph `G` with the resolved delta `dr` gives. -/
def overlayPred (G : Triple → Prop) (dr : DeltaResolved) (t : Triple) : Prop :=
  (dr.cleared = false ∧ G t ∧ dr.removed.mem t = false) ∨ dr.added.mem t = true

theorem overlayPred_of_isEmpty {G : Triple → Prop} {dr : DeltaResolved}
    (h : deltaResolvedIsEmpty dr = true) (t : Triple) : overlayPred G dr t ↔ G t := by
  simp only [deltaResolvedIsEmpty, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨hc, ha⟩, hr⟩ := h
  simp [overlayPred, hc, ha, hr, Graph.mem]

private theorem graphUnion_keyNodup : ∀ (c a : Graph), a.KeyNodup → (Graph.union a c).KeyNodup
  | [], _, h => h
  | x :: c, a, h => graphUnion_keyNodup c (a.add x) (h.add x)

private theorem filterTombstoned_keyNodup {g : Graph} (h : g.KeyNodup) (dr : DeltaResolved) :
    (filterTombstoned g dr).KeyNodup := by
  unfold filterTombstoned
  split
  · exact Graph.keyNodup_nil
  · exact keyNodup_filter h _

private theorem graphUnion_nil (a : Graph) : Graph.union a [] = a := rfl

/-- **Base plus delta is lawful.** A lawful base record of the graph `G`, with
the resolved delta `dr`, reads `overlayPred G dr`. Hypothesis: the base does
not advertise an exact estimate (the overlay copies the flag and its estimate
overcounts under a tombstone). -/
theorem overlay_exact {G : Triple → Prop} {base : StoreCaps} (dr : DeltaResolved)
    (hb : StoreCapsExact G base) (hflag : base.flags.estimateIsExact = false) :
    StoreCapsExact (overlayPred G dr) (overlay base dr) := by
  by_cases he : deltaResolvedIsEmpty dr = true
  · have hov : overlay base dr = { base with flags := { base.flags with supportsUpdate := true } } := by
      simp [overlay, he]
    rw [hov]
    refine StoreCapsExact.of_iff ?_ (fun t => (overlayPred_of_isEmpty he t).symm)
    exact
      { limitAgrees := hb.limitAgrees
        countIsSolve := hb.countIsSolve
        estimateExact := fun hex => hb.estimateExact hex
        selectiveAgrees := hb.selectiveAgrees
        presenceSound := hb.presenceSound
        solveExact := hb.solveExact
        solveNodupKeys := hb.solveNodupKeys
        distinctPredicatesComplete := hb.distinctPredicatesComplete }
  · have hne : deltaResolvedIsEmpty dr = false := by simpa using he
    refine
      { limitAgrees := fun b n => by simp [overlay, hne]
        countIsSolve := fun b => by simp [overlay, hne]
        estimateExact := fun hex => absurd hex (by simp [overlay, hne, hflag])
        selectiveAgrees := fun f hf b need => by
          simp only [overlay, hne, Bool.false_eq_true, if_false, Option.some.injEq] at hf
          subst hf
          simp [overlay, hne]
        presenceSound := fun pred hp => ?_
        solveExact := fun b t => ?_
        solveNodupKeys := fun b => ?_
        distinctPredicatesComplete := fun f hf => absurd hf (by simp [overlay, hne]) }
    · simp only [overlay, hne, Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at hp ⊢
      obtain ⟨hp1, hp2⟩ := hp
      rw [hb.presenceSound pred hp1]
      have hadd : tripleMatchesBound { p := some pred } dr.added = [] := by
        unfold tripleMatchesBound
        rw [List.filter_eq_nil_iff]
        intro t ht hbt
        simp only [deltaAddedHasPredicate, List.any_eq_false] at hp2
        have h1 := hp2 t ht
        simp only [boundMatches, Bool.true_and, Bool.and_true, beq_iff_eq] at hbt
        exact h1 (by rw [hbt]; simp)
      rw [mergeOnRead, hadd, graphUnion_nil]
      unfold filterTombstoned
      split <;> rfl
    · have hs : (overlay base dr).solve b = mergeOnRead (base.solve b) dr b := by
        simp [overlay, hne]
      rw [hs, keyMem_iff_mem, mergeOnRead, mem_graph_union, mem_filterTombstoned,
        mem_tripleMatchesBound]
      have : (Graph.mem t (base.solve b) = true) ↔ G t ∧ boundMatches b t = true := by
        rw [← keyMem_iff_mem, hb.solveExact]
      unfold overlayPred
      cases hc : dr.cleared <;> cases hr : dr.removed.mem t <;> cases ha : dr.added.mem t <;>
        cases hbt : boundMatches b t <;> cases hm : Graph.mem t (base.solve b) <;>
        simp_all
    · have hs : (overlay base dr).solve b = mergeOnRead (base.solve b) dr b := by
        simp [overlay, hne]
      rw [hs]
      exact graphUnion_keyNodup _ _ (filterTombstoned_keyNodup (hb.solveNodupKeys b) dr)

/-- The overlay of a folded log over a list graph is the reference model of
`RDF/StoreDeltaMerge.lean`: the graph that the entries, applied to the base
as graph operations (`applyEntriesRef`), give. -/
theorem overlayPred_fold (graphKey : Option Storage.DeltaGraphName) (gBase : Graph)
    (es : List Storage.DeltaEntry) (t : Triple) :
    overlayPred (KeyMem gBase) (foldEntriesForGraph graphKey es deltaResolvedEmpty) t ↔
      KeyMem (applyEntriesRef graphKey gBase es) t := by
  have hag := applyEntries_stateAgrees graphKey gBase es gBase deltaResolvedEmpty
    (stateAgrees_init gBase) t
  rw [keyMem_iff_mem, hag]
  unfold overlayPred composedMem
  rw [keyMem_iff_mem]
  cases (foldEntriesForGraph graphKey es deltaResolvedEmpty).cleared <;>
    cases Graph.mem t gBase <;>
    cases Graph.mem t (foldEntriesForGraph graphKey es deltaResolvedEmpty).removed <;>
    cases Graph.mem t (foldEntriesForGraph graphKey es deltaResolvedEmpty).added <;> simp

/-- **The union law for base plus delta.** A lawful record of the list graph
`gBase`, with a log folded for one graph, reads the graph that the log applied
to `gBase` gives. -/
theorem overlay_fold_exact {gBase : Graph} {base : StoreCaps} (graphKey : Option Storage.DeltaGraphName)
    (es : List Storage.DeltaEntry) (hb : StoreCapsExact (KeyMem gBase) base)
    (hflag : base.flags.estimateIsExact = false) :
    StoreCapsExact (KeyMem (applyEntriesRef graphKey gBase es))
      (overlay base (foldEntriesForGraph graphKey es deltaResolvedEmpty)) :=
  (overlay_exact _ hb hflag).of_iff (overlayPred_fold graphKey gBase es)

#print axioms StoreCapsExact.keys_perm
#print axioms StoreCapsExact.countExact_eq
#print axioms igSearch_of_wf
#print axioms capsOfIndexed_exact
#print axioms capsOfIndexed_default_denotes
#print axioms capsOfIndexed_named_denotes
#print axioms capsOfCottas_exact
#print axioms unionSolveLimited_eq
#print axioms capsIriDedupe_spec
#print axioms unionCaps_exact
#print axioms overlay_exact
#print axioms overlayPred_fold
#print axioms overlay_fold_exact

end L4Factoidal.RDF
