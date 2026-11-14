/-
L4Factoidal.XForms.Theorems — theorems about XForms recalculation
(XForms 1.1 §4.3.2, Appendix C), at the level of the dependency graph
of `XForms/DepGraph.lean`: any vertex type, any evaluation function
that reads only its declared dependencies.

What links these to the engine: `XForms/Model.lean` takes its
recalculation order from `DepGraph.topoSort` and reports a cycle
(`xforms-compute-exception`) exactly when `topoSort` answers `none`.
That the engine's XPath evaluation reads only the nodes in the read set
it records (`DepGraph.Local` for the engine's graph) is NOT proved: the
XPath 1.0 function library is reached through `XPath.Full.evalExpr`,
a `partial def` the kernel cannot unfold.
-/
import L4Factoidal.XForms.DepGraph

namespace L4Factoidal.XForms.DepGraph

variable {V : Type} [DecidableEq V] {α : Type}

theorem length_filter_ne_lt (v : V) :
    ∀ (l : List V), v ∈ l → (l.filter (fun x => x != v)).length < l.length
  | [], h => nomatch h
  | a :: l, h => by
      by_cases hav : a = v
      · subst hav
        have hle : (l.filter (fun x => x != a)).length ≤ l.length := List.length_filter_le _ _
        have hf : (a :: l).filter (fun x => x != a) = l.filter (fun x => x != a) := by
          simp
        rw [hf]; simp; omega
      · have hv : v ∈ l := by
          rcases List.mem_cons.mp h with e | e
          · exact absurd e.symm hav
          · exact e
        have ih := length_filter_ne_lt v l hv
        have hf : (a :: l).filter (fun x => x != v) = a :: l.filter (fun x => x != v) := by
          simp [hav]
        rw [hf]; simp; omega

theorem topoLoop_sound (deps : V → List V) :
    ∀ (n : Nat) (rem acc o : List V), topoLoop deps n rem acc = some o →
      ∃ o', o = acc.reverse ++ o' ∧ Topo deps o' ∧ (∀ x, x ∈ o' ↔ x ∈ rem) := by
  intro n
  induction n with
  | zero =>
    intro rem acc o h
    unfold topoLoop at h
    by_cases he : rem.isEmpty = true
    · rw [if_pos he] at h
      have hr : rem = [] := List.isEmpty_iff.mp he
      subst hr
      exact ⟨[], by simpa using (Option.some.inj h).symm, trivial, fun x => Iff.rfl⟩
    · rw [if_neg he] at h; exact absurd h (by simp)
  | succ n ih =>
    intro rem acc o h
    unfold topoLoop at h
    by_cases he : rem.isEmpty = true
    · rw [if_pos he] at h
      have hr : rem = [] := List.isEmpty_iff.mp he
      subst hr
      exact ⟨[], by simpa using (Option.some.inj h).symm, trivial, fun x => Iff.rfl⟩
    · rw [if_neg he] at h
      split at h
      · exact absurd h (by simp)
      · rename_i v hf
        obtain ⟨o', ho, ht, hm⟩ := ih _ _ _ h
        have hv : v ∈ rem := List.mem_of_find?_eq_some hf
        have hr : ready deps rem v = true := List.find?_some hf
        have hnot : ∀ u, u ∈ deps v → u ∉ rem := by
          intro u hu
          unfold ready at hr
          have := List.all_eq_true.mp hr u hu
          simpa using this
        refine ⟨v :: o', ?_, ⟨?_, ?_, ht⟩, ?_⟩
        · rw [ho]; simp
        · intro u hu
          refine ⟨fun e => hnot u hu (e ▸ hv), fun hmem => hnot u hu ?_⟩
          exact (List.mem_filter.mp ((hm u).mp hmem)).1
        · intro hmem
          have h2 := (List.mem_filter.mp ((hm v).mp hmem)).2
          simp at h2
        · intro x
          constructor
          · intro hx
            rcases List.mem_cons.mp hx with e | hx
            · exact e ▸ hv
            · exact (List.mem_filter.mp ((hm x).mp hx)).1
          · intro hx
            by_cases hxv : x = v
            · exact hxv ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _
                ((hm x).mpr (List.mem_filter.mpr ⟨hx, by simpa using hxv⟩))

theorem topoLoop_none (deps : V → List V) :
    ∀ (n : Nat) (rem acc : List V), rem.length ≤ n → topoLoop deps n rem acc = none →
      ∃ S, CyclicCore deps S ∧ ∀ x, x ∈ S → x ∈ rem := by
  intro n
  induction n with
  | zero =>
    intro rem acc hl h
    have hr : rem = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst hr
    unfold topoLoop at h
    simp at h
  | succ n ih =>
    intro rem acc hl h
    unfold topoLoop at h
    by_cases he : rem.isEmpty = true
    · rw [if_pos he] at h; exact absurd h (by simp)
    · rw [if_neg he] at h
      split at h
      · rename_i hf
        have hnr := List.find?_eq_none.mp hf
        refine ⟨rem, ⟨fun e => he (by simp [e]), ?_⟩, fun x hx => hx⟩
        intro v hv
        apply Classical.byContradiction
        intro hcon
        apply hnr v hv
        unfold ready
        apply List.all_eq_true.mpr
        intro u hu
        simp
        intro hmem
        exact hcon ⟨u, hu, hmem⟩
      · rename_i v hf
        have hv : v ∈ rem := List.mem_of_find?_eq_some hf
        have hlt := length_filter_ne_lt v rem hv
        obtain ⟨S, hS, hsub⟩ := ih _ _ (by omega) h
        exact ⟨S, hS, fun x hx => (List.mem_filter.mp (hsub x hx)).1⟩

/-- Kind: correctness of an algorithm (soundness).
    Says: when `topoSort` answers an order, that order is a topological
    order of the dependency graph (no vertex twice, no vertex before
    something it reads) and it holds exactly the given vertices. The
    engine recalculates in this order.
    Does not say: that the dependency lists the engine builds are the
    true read sets of its expressions; that is the evaluator's job and
    is only tested. -/
theorem topoSort_topological (deps : V → List V) (vs o : List V)
    (h : topoSort deps vs = some o) :
    Topo deps o ∧ ∀ x, x ∈ o ↔ x ∈ vs := by
  obtain ⟨o', ho, ht, hm⟩ := topoLoop_sound deps _ _ _ _ h
  have : o = o' := by simpa using ho
  exact this ▸ ⟨ht, hm⟩

/-- Kind: structural lemma.
    Says: a list that is a topological order holds no cyclic core.
    Does not say: anything about lists that are not topological. -/
theorem topo_no_cycle (deps : V → List V) :
    ∀ (o : List V), Topo deps o → ∀ S, CyclicCore deps S → ¬ (∀ x, x ∈ S → x ∈ o)
  | [], _, S, hS, hsub => by
      cases S with
      | nil => exact hS.1 rfl
      | cons a _ => exact nomatch (hsub a List.mem_cons_self)
  | v :: rest, ht, S, hS, hsub => by
      obtain ⟨hd, _, hr⟩ := ht
      by_cases hv : v ∈ S
      · obtain ⟨u, hu, huS⟩ := hS.2 v hv
        obtain ⟨h1, h2⟩ := hd u hu
        rcases List.mem_cons.mp (hsub u huS) with e | e
        · exact h1 e
        · exact h2 e
      · apply topo_no_cycle deps rest hr S hS
        intro x hx
        rcases List.mem_cons.mp (hsub x hx) with e | e
        · exact absurd (e ▸ hx) hv
        · exact e

/-- Kind: correctness of an algorithm (soundness and completeness).
    Says: `topoSort` reports failure (`none`; the engine then raises
    `xforms-compute-exception`) if and only if the dependency graph
    restricted to the given vertices has a cyclic core, that is a
    non-empty set of vertices each reading a member of the set, which
    for a finite graph is the same as having a directed cycle.
    Does not say: which cycle; nor that the equivalence between a
    cyclic core and a directed cycle is itself proved here. -/
theorem topoSort_none_iff_cycle (deps : V → List V) (vs : List V) :
    topoSort deps vs = none ↔ ∃ S, CyclicCore deps S ∧ ∀ x, x ∈ S → x ∈ vs := by
  constructor
  · intro h
    exact topoLoop_none deps _ _ _ (Nat.le_refl _) h
  · intro ⟨S, hS, hsub⟩
    cases h : topoSort deps vs with
    | none => rfl
    | some o =>
      obtain ⟨ht, hm⟩ := topoSort_topological deps vs o h
      exact absurd (fun x hx => (hm x).mpr (hsub x hx)) (topo_no_cycle deps o ht S hS)

/-- Kind: invariant of recalculation.
    Says: after recalculating in a topological order, every vertex
    outside the order keeps its value and every vertex in the order
    holds the value of its own expression in the final state (the
    final state solves the equations).
    Does not say: anything when the evaluation reads outside `deps`
    (hypothesis `Local`) or when the order is not topological. -/
theorem recalc_solves {deps : V → List V} {ev : V → (V → α) → α} (hl : Local deps ev) :
    ∀ (o : List V), Topo deps o → ∀ σ : V → α,
      (∀ u, u ∉ o → recalc ev o σ u = σ u) ∧
      (∀ v, v ∈ o → recalc ev o σ v = ev v (recalc ev o σ))
  | [], _, _ => ⟨fun _ _ => rfl, fun _ h => nomatch h⟩
  | v :: rest, ht, σ => by
      obtain ⟨hd, hv, hr⟩ := ht
      obtain ⟨ih1, ih2⟩ := recalc_solves hl rest hr (update σ v (ev v σ))
      constructor
      · intro u hu
        have hu1 : u ≠ v := fun e => hu (e ▸ List.mem_cons_self)
        have hu2 : u ∉ rest := fun h => hu (List.mem_cons_of_mem _ h)
        show recalc ev rest (update σ v (ev v σ)) u = σ u
        rw [ih1 u hu2]; simp [update, hu1]
      · intro w hw
        show recalc ev rest (update σ v (ev v σ)) w
              = ev w (recalc ev rest (update σ v (ev v σ)))
        rcases List.mem_cons.mp hw with e | hw
        · subst e
          rw [ih1 w hv]
          have hself : update σ w (ev w σ) w = ev w σ := by simp [update]
          rw [hself]
          apply hl
          intro u hu
          obtain ⟨h1, h2⟩ := hd u hu
          rw [ih1 u h2]; simp [update, h1]
        · exact ih2 w hw

/-- Kind: uniqueness.
    Says: for a topological order, two states that agree outside the
    order and both solve the equations on it are equal everywhere.
    Does not say: that a solution exists (`recalc_solves` does). -/
theorem solution_unique {deps : V → List V} {ev : V → (V → α) → α} (hl : Local deps ev) :
    ∀ (o : List V), Topo deps o → ∀ σ1 σ2 : V → α,
      (∀ u, u ∉ o → σ1 u = σ2 u) → (∀ v, v ∈ o → σ1 v = ev v σ1) →
      (∀ v, v ∈ o → σ2 v = ev v σ2) → ∀ x, σ1 x = σ2 x
  | [], _, _, _, h, _, _ => fun x => h x (fun hx => nomatch hx)
  | v :: rest, ht, σ1, σ2, h, s1, s2 => by
      obtain ⟨hd, _, hr⟩ := ht
      have hvv : σ1 v = σ2 v :=
        calc σ1 v = ev v σ1 := s1 v List.mem_cons_self
          _ = ev v σ2 := hl v σ1 σ2 (fun u hu => h u (fun hmem => by
                obtain ⟨h1, h2⟩ := hd u hu
                rcases List.mem_cons.mp hmem with e | e
                · exact h1 e
                · exact h2 e))
          _ = σ2 v := (s2 v List.mem_cons_self).symm
      apply solution_unique hl rest hr σ1 σ2
      · intro u hu
        by_cases e : u = v
        · rw [e]; exact hvv
        · apply h; intro hmem
          rcases List.mem_cons.mp hmem with e' | e'
          · exact e e'
          · exact hu e'
      · intro w hw; exact s1 w (List.mem_cons_of_mem _ hw)
      · intro w hw; exact s2 w (List.mem_cons_of_mem _ hw)

/-- Kind: confluence (order independence).
    Says: any two topological orders of the same vertices give the
    same state after recalculation, so a bind's computed properties do
    not depend on which topological order the engine picked.
    Does not say: anything for an evaluation that reads outside its
    declared dependencies. -/
theorem recalc_order_independent {deps : V → List V} {ev : V → (V → α) → α}
    (hl : Local deps ev) (o1 o2 : List V) (h1 : Topo deps o1) (h2 : Topo deps o2)
    (hm : ∀ x, x ∈ o1 ↔ x ∈ o2) (σ : V → α) :
    recalc ev o1 σ = recalc ev o2 σ := by
  funext x
  obtain ⟨a1, b1⟩ := recalc_solves hl o1 h1 σ
  obtain ⟨a2, b2⟩ := recalc_solves hl o2 h2 σ
  apply solution_unique hl o1 h1
  · intro u hu; rw [a1 u hu, a2 u (fun h => hu ((hm u).mpr h))]
  · exact b1
  · intro v hv; exact b2 v ((hm v).mp hv)

/-- Kind: idempotence (fixed point).
    Says: recalculating a second time in the same topological order
    changes nothing.
    Does not say: that one pass reaches a fixed point when the graph
    has a cycle (then there is no topological order). -/
theorem recalc_fixed_point {deps : V → List V} {ev : V → (V → α) → α}
    (hl : Local deps ev) (o : List V) (h : Topo deps o) (σ : V → α) :
    recalc ev o (recalc ev o σ) = recalc ev o σ := by
  funext x
  obtain ⟨_, b1⟩ := recalc_solves hl o h σ
  obtain ⟨a2, b2⟩ := recalc_solves hl o h (recalc ev o σ)
  exact solution_unique hl o h _ _ (fun u hu => a2 u hu) b2 b1 x

/-- Kind: structural lemma.
    Says: keeping only some vertices of a topological order leaves a
    topological order.
    Does not say: that the kept vertices are closed under anything. -/
theorem topo_filter {deps : V → List V} (p : V → Bool) :
    ∀ (o : List V), Topo deps o → Topo deps (o.filter p)
  | [], _ => trivial
  | v :: rest, ht => by
      obtain ⟨hd, hv, hr⟩ := ht
      have ih := topo_filter p rest hr
      by_cases hp : p v = true
      · rw [List.filter_cons_of_pos hp]
        exact ⟨fun u hu => ⟨(hd u hu).1, fun hm => (hd u hu).2 (List.mem_filter.mp hm).1⟩,
               fun hm => hv (List.mem_filter.mp hm).1, ih⟩
      · rw [List.filter_cons_of_neg hp]; exact ih

/-- Kind: equivalence of two procedures (incremental equals full).
    Says: let `σ₀` be a state in which every computed vertex is up to
    date, and `σ` a state that differs from it only on inputs. Let `R`
    mark a set of computed vertices such that an unmarked vertex reads
    nothing that changed and nothing that is marked (so `R` contains
    everything reachable from the changed inputs). Then recalculating
    only the marked vertices gives the same state as recalculating all.
    Does not say: how `R` is computed; the engine recalculates all
    vertices and does not yet use the incremental form. -/
theorem recalc_incremental {deps : V → List V} {ev : V → (V → α) → α}
    (hl : Local deps ev) (o : List V) (ht : Topo deps o) (R : V → Bool) (σ₀ σ : V → α)
    (hfix : ∀ v, v ∈ o → σ₀ v = ev v σ₀)
    (hsame : ∀ v, v ∈ o → σ v = σ₀ v)
    (hclosed : ∀ v, v ∈ o → R v = false →
      ∀ u, u ∈ deps v → σ u = σ₀ u ∧ (u ∈ o → R u = false)) :
    recalc ev (o.filter R) σ = recalc ev o σ := by
  funext x
  have htf := topo_filter (deps := deps) R o ht
  obtain ⟨a1, b1⟩ := recalc_solves hl (o.filter R) htf σ
  obtain ⟨a2, b2⟩ := recalc_solves hl o ht σ
  refine solution_unique hl o ht _ _ ?_ ?_ b2 x
  · intro u hu
    rw [a2 u hu, a1 u (fun h => hu (List.mem_filter.mp h).1)]
  · intro v hv
    by_cases hR : R v = true
    · exact b1 v (List.mem_filter.mpr ⟨hv, hR⟩)
    · have hRf : R v = false := by simpa using hR
      have hnot : v ∉ o.filter R := fun h => hR (List.mem_filter.mp h).2
      rw [a1 v hnot, hsame v hv, hfix v hv]
      apply hl
      intro u hu
      obtain ⟨c1, c2⟩ := hclosed v hv hRf u hu
      have hun : u ∉ o.filter R := by
        intro h
        have h' := List.mem_filter.mp h
        rw [c2 h'.1] at h'
        exact absurd h'.2 (by simp)
      rw [a1 u hun, c1]

end L4Factoidal.XForms.DepGraph
