/-
Capability-aware planner, OKR batch 3, KR 4.4: which answers are marked
exact.

https://github.com/danbri/factoidal/issues/875 (epic
https://github.com/danbri/factoidal/issues/800). Design record
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 15.

`Plan.execUsed` is `Plan.exec` with, for each row, the catalog indices of
the sources whose tuples made the row (in access order; a join adds the
indices of both sides, a union takes those of its branch). The theorems:

* `execUsed_rows`: dropping the indices gives `Plan.exec`;
* `execUsed_approx`: a row's marker is the marker of the start row, or
  that some used source is `approximate`;
* `runUsed_exact_iff`: a row of a run is unmarked (exact) if and only if
  every source it used is in the catalog and `exact`;
* `run_exact_only_if`: every unmarked row of `Plan.run` has a derivation
  whose sources are all `exact`;
* `rewriting_run_approx`: for the plan of a rewriting (a chain of
  dependent joins, then filters and a projection) every row uses every
  step, so a row is marked if and only if `Rewriting.approx` (some step's
  source is `approximate`).

The hypotheses are membership of a row in a run; none states the
conclusion (hazard 29).
-/
import L4Factoidal.Planner.Search

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- The source at catalog index `i` is `approximate`. -/
def srcApprox (cat : Catalog) (i : Nat) : Bool :=
  match cat[i]? with
  | some s => s.cap.exactness.isApprox
  | none   => false

/-- `Plan.exec`, with the catalog indices of the sources each row used. -/
def Plan.execUsed (cat : Catalog) : Plan → Row → List (Row × List Nat)
  | .unit, r => [(r, [])]
  | .access a, r =>
    match cat[a.src]? with
    | none => []
    | some s =>
      match a.inputs? s.cap r.binding with
      | none => []
      | some inp =>
        (s.sem.impl inp).filterMap (fun tup =>
          if s.wellTyped tup then
            (bindArgs a.args tup r.binding).map
              (fun b => ({ binding := b, approx := r.approx || s.cap.exactness.isApprox }, [a.src]))
          else none)
  | .join l q, r =>
    (l.execUsed cat r).flatMap (fun yu => (q.execUsed cat yu.1).map (fun xw => (xw.1, yu.2 ++ xw.2)))
  | .filter f p, r => (p.execUsed cat r).filter (fun xu => f.test xu.1.binding)
  | .project vs p, r =>
    (p.execUsed cat r).map (fun xu => ({ binding := projectBinding vs xu.1.binding, approx := xu.1.approx }, xu.2))
  | .union l q, r => l.execUsed cat r ++ q.execUsed cat r

def Plan.runUsed (cat : Catalog) (p : Plan) : List (Row × List Nat) :=
  p.execUsed cat { binding := [], approx := false }

/-- Dropping the indices gives `Plan.exec`. -/
theorem execUsed_rows (cat : Catalog) :
    ∀ (p : Plan) (r : Row), (p.execUsed cat r).map Prod.fst = p.exec cat r := by
  intro p
  induction p with
  | unit => intro r; rfl
  | access a =>
    intro r
    simp only [Plan.execUsed, Plan.exec]
    cases hc : cat[a.src]? with
    | none => rfl
    | some s =>
      cases hi : a.inputs? s.cap r.binding with
      | none => simp only [hi, List.map_nil]
      | some inp =>
        simp only [hi]
        rw [List.map_filterMap]
        congr 1
        funext tup
        split
        · cases bindArgs a.args tup r.binding <;> rfl
        · rfl
  | join l q ihl ihq =>
    intro r
    simp only [Plan.execUsed, Plan.exec, List.map_flatMap, List.map_map]
    rw [← ihl r, List.flatMap_map]
    congr 1
    funext yu
    rw [← ihq yu.1]
    rfl
  | filter f p ih =>
    intro r
    simp only [Plan.execUsed, Plan.exec]
    rw [← ih r, List.filter_map]
    rfl
  | project vs p ih =>
    intro r
    simp only [Plan.execUsed, Plan.exec, List.map_map]
    rw [← ih r, List.map_map]
    rfl
  | union l q ihl ihq =>
    intro r
    simp only [Plan.execUsed, Plan.exec, List.map_append, ihl, ihq]

/-- Every index a row used names a source of the catalog, and the
row's marker is the start row's marker or an `approximate` used source. -/
theorem execUsed_approx (cat : Catalog) :
    ∀ (p : Plan) (r x : Row) (u : List Nat), (x, u) ∈ p.execUsed cat r →
      (∀ i ∈ u, (cat[i]?).isSome = true) ∧ x.approx = (r.approx || u.any (srcApprox cat)) := by
  intro p
  induction p with
  | unit =>
    intro r x u h
    simp only [Plan.execUsed, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | access a =>
    intro r x u h
    simp only [Plan.execUsed] at h
    split at h
    · simp at h
    · rename_i s hs
      split at h
      · simp at h
      · rename_i inp _
        simp only [List.mem_filterMap] at h
        obtain ⟨tup, _, ht⟩ := h
        split at ht
        · cases hb : bindArgs a.args tup r.binding with
          | none => rw [hb] at ht; simp at ht
          | some b =>
            rw [hb] at ht
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            refine ⟨?_, ?_⟩
            · intro i hi
              simp only [List.mem_singleton] at hi
              subst hi
              simp [hs]
            · simp [srcApprox, hs]
        · simp at ht
  | join l q ihl ihq =>
    intro r x u h
    simp only [Plan.execUsed, List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨y, v⟩, hy, ⟨x', w⟩, hx, hxw⟩ := h
    simp only [Prod.mk.injEq] at hxw
    obtain ⟨rfl, rfl⟩ := hxw
    obtain ⟨hv, hya⟩ := ihl r y v hy
    obtain ⟨hw, hxa⟩ := ihq y x' w hx
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hv i hi
      · exact hw i hi
    · rw [hxa, hya, List.any_append, Bool.or_assoc]
  | filter f p ih =>
    intro r x u h
    simp only [Plan.execUsed, List.mem_filter] at h
    exact ih r x u h.1
  | project vs p ih =>
    intro r x u h
    simp only [Plan.execUsed, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨⟨y, v⟩, hy, rfl, rfl⟩ := h
    exact ih r y v hy
  | union l q ihl ihq =>
    intro r x u h
    simp only [Plan.execUsed, List.mem_append] at h
    rcases h with h | h
    · exact ihl r x u h
    · exact ihq r x u h

/-- A row of a run is unmarked (exact) if and only if every source it used
is in the catalog and is `exact`. -/
theorem runUsed_exact_iff {cat : Catalog} {p : Plan} {x : Row} {u : List Nat}
    (h : (x, u) ∈ p.runUsed cat) :
    x.approx = false ↔ ∀ i ∈ u, ∃ s, cat[i]? = some s ∧ s.cap.exactness = .exact := by
  obtain ⟨hsome, ha⟩ := execUsed_approx cat p _ x u h
  rw [ha]
  simp only [Bool.false_or, List.any_eq_false]
  constructor
  · intro hall i hi
    have hs := hsome i hi
    have hn := hall i hi
    cases hc : cat[i]? with
    | none => rw [hc] at hs; simp at hs
    | some s =>
      refine ⟨s, rfl, ?_⟩
      simp only [srcApprox, hc] at hn
      cases he : s.cap.exactness with
      | exact => rfl
      | approximate => rw [he] at hn; simp [Exactness.isApprox] at hn
  · intro hall i hi
    obtain ⟨s, hs, he⟩ := hall i hi
    simp [srcApprox, hs, he, Exactness.isApprox]

/-- An answer of `Plan.run` is marked exact only when the sources of one
of its derivations are all `exact`. -/
theorem run_exact_only_if {cat : Catalog} {p : Plan} {x : Row}
    (hx : x ∈ p.run cat) (hexact : x.approx = false) :
    ∃ u, (x, u) ∈ p.runUsed cat ∧ ∀ i ∈ u, ∃ s, cat[i]? = some s ∧ s.cap.exactness = .exact := by
  have hx' : x ∈ (p.runUsed cat).map Prod.fst := by
    unfold Plan.runUsed Plan.run at *
    rw [execUsed_rows]; exact hx
  obtain ⟨⟨x', u⟩, hmem, hfst⟩ := List.mem_map.mp hx'
  simp only at hfst
  subst hfst
  exact ⟨u, hmem, (runUsed_exact_iff hmem).mp hexact⟩

/-! ## Rewritings: every row uses every step -/

theorem chain_used (cat : Catalog) :
    ∀ (steps : List Access) (r x : Row) (u : List Nat),
      (x, u) ∈ (chainPlan steps).execUsed cat r → u = steps.map (·.src) := by
  intro steps
  induction steps with
  | nil =>
    intro r x u h
    simp only [chainPlan, List.foldr, Plan.execUsed, List.mem_singleton, Prod.mk.injEq] at h
    simp [h.2]
  | cons a rest ih =>
    intro r x u h
    have h' : (x, u) ∈ (Plan.join (.access a) (chainPlan rest)).execUsed cat r := by
      simpa [chainPlan, List.foldr] using h
    simp only [Plan.execUsed, List.mem_flatMap, List.mem_map] at h'
    obtain ⟨⟨y, v⟩, hy, ⟨x', w⟩, hx, hxw⟩ := h'
    simp only [Prod.mk.injEq] at hxw
    obtain ⟨rfl, rfl⟩ := hxw
    have hw := ih y x' w hx
    have hv : v = [a.src] := by
      split at hy
      · simp at hy
      · split at hy
        · simp at hy
        · simp only [List.mem_filterMap] at hy
          obtain ⟨tup, _, ht⟩ := hy
          split at ht
          · cases hb : bindArgs a.args tup r.binding with
            | none => rw [hb] at ht; simp at ht
            | some b =>
              rw [hb] at ht
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
              exact ht.2.symm
          · simp at ht
    simp [hv, hw]

theorem filters_used (cat : Catalog) (p : Plan) :
    ∀ (fs : List RowFilter) (r x : Row) (u : List Nat),
      (x, u) ∈ (filtersPlan fs p).execUsed cat r → (x, u) ∈ p.execUsed cat r := by
  intro fs
  induction fs with
  | nil => intro r x u h; simpa [filtersPlan] using h
  | cons f rest ih =>
    intro r x u h
    have h' : (x, u) ∈ (Plan.filter f (filtersPlan rest p)).execUsed cat r := by
      simpa [filtersPlan, List.foldr] using h
    simp only [Plan.execUsed, List.mem_filter] at h'
    exact ih r x u h'.1

/-- Every row of a rewriting's plan used the source of every step. -/
theorem rewriting_used (cat : Catalog) (req : Requirement) (rw : Rewriting) {x : Row}
    {u : List Nat} (h : (x, u) ∈ (rw.toPlan req).runUsed cat) : u = rw.steps.map (·.src) := by
  unfold Plan.runUsed Rewriting.toPlan at h
  simp only [Plan.execUsed, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨⟨y, v⟩, hy, _, rfl⟩ := h
  exact chain_used cat _ _ _ _ (filters_used cat _ req.filters _ y v hy)

/-- A row of a rewriting's plan is marked if and only if the rewriting
uses an `approximate` source. -/
theorem rewriting_run_approx {cat : Catalog} {req : Requirement} {rw : Rewriting} {x : Row}
    (hx : x ∈ (rw.toPlan req).run cat) : x.approx = rw.approx cat := by
  have hx' : x ∈ ((rw.toPlan req).runUsed cat).map Prod.fst := by
    unfold Plan.runUsed Plan.run at *
    rw [execUsed_rows]; exact hx
  obtain ⟨⟨x', u⟩, hmem, hfst⟩ := List.mem_map.mp hx'
  simp only at hfst
  subst hfst
  have hu := rewriting_used cat req rw hmem
  have ha := (execUsed_approx cat _ _ x' u hmem).2
  rw [ha, hu]
  show (false || _) = _
  rw [Bool.false_or, Rewriting.approx, List.any_map]
  rfl

end L4Factoidal.Planner
