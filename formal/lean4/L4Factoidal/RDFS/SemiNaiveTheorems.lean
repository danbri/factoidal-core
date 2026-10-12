/-
L4Factoidal.RDFS.SemiNaiveTheorems — the semi-naive RDFS closure
(`RDFS.SemiNaive`) against the rule relation `Derives`, and against the
naive closure `closureFix`.

Issue: https://github.com/danbri/factoidal/issues/756, order item 1
(RDFS; OWL RL is item 2). Owner, 2026-10-10, verbatim: "Instead of
proving that both implementations return identical results after every
round, prove that they compute equivalent saturated closures".

## What is proved

The proof target of the issue is `t ∈ C g ↔ Derives g t` for each
closure algorithm `C`. `Derives` (`RdfsCore.lean`) is the inductive rule
relation, so it is the least set that contains `g` and is closed under
the six rows. As in `ClosureTheorems.lean`, the two directions use
different membership relations: list membership `∈` for soundness, and
the engine's `Graph.mem` (equality up to `Triple.eqb`) for completeness.
`ClosureTheorems.lean`'s header gives the reason: `Graph.add` skips a
triple that is `Triple.eqb`-equal to one already present.

1. **Soundness**, `semiNaive_sound`: `t ∈ semiNaive g → Derives g t`.
   With explicit fuel: `semiNaiveLoop_sound`. A delta term applies a row
   to SUBSETS of the current graph (`delta ⊆ g` is a loop invariant), so
   every delta conclusion is a `stepConclusions` conclusion
   (`mem_stepConclusions_of_mem_deltaConclusions`), and
   `stepConclusions_sound` with `Derives.cut` does the rest.
2. **Saturation at termination**. The invariant is `RoundInv P S Δ`,
   with `P` the graph before the last round, `S` the graph after it and
   `Δ` the delta:
   * `Δ ⊆ S`;
   * every triple of `S` is in `Δ` or in `P`;
   * every conclusion of `stepConclusions P` is in `S` (every rule
     instance whose premises are all in `S(k-1)` has its conclusion in
     `S(k)`).
   `RoundInv.next` proves that one round preserves it. The argument per
   rule instance with first premise `d` and second premise `u` in `S`:
   if `d ∈ Δ`, the left delta term `Δ.flatMap (row S)` covers it; if
   `u ∈ Δ`, the right term `S.flatMap (row Δ)` covers it; otherwise both
   premises are in `P`, and the third clause of the invariant puts the
   conclusion in `S` already. This needs each row to draw its second
   premise from ONE triple of the searched graph: `RowAdditive`, proved
   for all six rows (`rdfsCoreRows_additive`). The loop stops by a test
   in two ways, and each gives saturation (`Saturated h`: every
   conclusion of `stepConclusions h` is in `h`, equivalently
   `step h = h` by `saturated_iff_step_eq`): an empty delta
   (`RoundInv.saturated_of_nil`) and a round that adds nothing
   (`RoundInv.saturated_of_next_eq`).
   `semiNaiveLoop_saturated_of_stopsByTest` states it for a loop that
   stopped by a test; `semiNaiveLoopStopsByTest` mirrors the loop's
   control flow and says which way it stopped.
   `semiNaiveLoop_saturated_or_underfueled` is the fuel dichotomy in
   the form of `ClosureTheorems.closure_saturated_or_underfueled`:
   the result is saturated, or the graph grew by one triple or more for
   each unit of fuel.
3. **Least fixed point**, `semiNaive_complete_of_saturated`: from 2 and
   `complete_of_saturated`, `Derives g t → Graph.mem t (semiNaive g)`
   when `semiNaive g` is saturated. Then
   `semiNaive_mem_eq_closureFix`: the two closures have the same
   members (by `Graph.mem`) when both are saturated.
4. **The checked entry**, `closureSemiNaiveChecked_mem_eq_closureFix`:
   `closureSemiNaiveChecked g` and `closureFix g` have the same members
   whenever `closureFix g` is saturated. This holds for every fuel of
   the delta loop, because of the run-time check and the fallback.
   `closureSemiNaiveChecked_sound` holds with no hypothesis.
5. **The compiled code** (section 7). `closureSemiNaiveCheckedFast_eq`:
   the checked entry equals, as a list and with no hypothesis, a twin
   that runs round 1 as one indexed naive round
   (`addAll_deltaConclusions_self`), runs the indexed delta loop of
   `RDFS.SemiNaive` (`semiNaiveLoop_eq_fast`), and runs the naive
   check round only when the loop used up its fuel. The proof uses
   item 2: a loop that stopped by a test returns a saturated graph, so
   the check would answer `true`. Both twins are `@[csimp]`.

## Open obligation: fuel adequacy (issue 756, item 4)

NOT PROVED: `∀ g, Saturated (semiNaive g)`, i.e. that
`closureFuelBound g` rounds are enough for the delta loop. The same
obligation is open for the naive loop (`ClosureTheorems.lean` header,
T4). The semi-naive loop makes the same rounds as the naive loop
(round k of each adds exactly the conclusions of `stepConclusions` on
the graph of round k-1), so one proof would serve both. Until it is
proved, `closureSemiNaiveChecked` keeps its run-time check
(`isNaiveFixpoint`) and its fallback to `closureFix`.

The expected-failure record is the row `semiNaive_saturated` in
`Harness/ProofObligations.lean`, which `lake build` elaborates: it
prints `XFAIL` with the issue URL while the theorem is absent, and it
FAILS the build when a theorem of that name appears, so that the
run-time check and the record are removed in the same commit.

A finding for that proof: the counting argument in the doc comment of
`Closure.closureFuelBound` does not give the bound it states. It
counts `n` subjects, `n + 1` predicates and `n` objects for an
`n`-triple graph. But rdfs3 makes an OBJECT of `g` the subject of its
conclusion, and rdfs7 makes the object `q` of `p rdfs:subPropertyOf q`
the PREDICATE of its conclusion. The components of closure triples are
therefore up to `2n` subjects, `2n + 1` predicates and `n` objects,
which bounds the closure by `2n * (2n + 1) * n` triples, about four
times `closureFuelBound g`. This is not a counterexample: each round
grows the graph by every conclusion one step deeper, not by one
triple. A proof of item 4 needs either the corrected count or a bound
on the derivation depth.
-/
import L4Factoidal.RDFS.SemiNaive
import L4Factoidal.RDFS.ClosureTheorems

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Section 1 — rows that draw their second premise from one triple

Every row `R` of `RDFS.Closure` has the shape `Graph → Triple → List
Triple`: `R G d` reads `d` as the first premise and searches `G` for
the second. The delta argument needs one fact about that search: each
conclusion comes from ONE triple of `G`. That is `RowAdditive`. It gives
monotonicity in `G` (`RowAdditive.mono`) and the case split on where the
second premise lies (`RoundInv.next`). The six proofs below are the
only row-specific part of this module. -/

/-- A conclusion of `R G d` is a conclusion of `R [u] d` for one triple
`u` of `G`, and conversely. -/
def RowAdditive (R : Graph → Triple → List Triple) : Prop :=
  ∀ (G : Graph) (d t : Triple), t ∈ R G d ↔ ∃ u, u ∈ G ∧ t ∈ R [u] d

theorem rdfs7For_additive : RowAdditive rdfs7For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  cases ds <;> cases dob <;> simp [rdfs7For, triplesWithPredicate, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

theorem rdfs2For_additive : RowAdditive rdfs2For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  cases ds <;> simp [rdfs2For, triplesWithPredicate, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

theorem rdfs3For_additive : RowAdditive rdfs3For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  cases ds <;> simp [rdfs3For, triplesWithPredicate, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

theorem rdfs9For_additive : RowAdditive rdfs9For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  cases dob <;> simp [rdfs9For, objectsOf, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

theorem rdfs11For_additive : RowAdditive rdfs11For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  rcases hs : dob.toSubject? with _ | bsub <;> simp [rdfs11For, objectsOf, hs, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

theorem rdfs5For_additive : RowAdditive rdfs5For := by
  intro G d t
  obtain ⟨ds, dp, dob⟩ := d
  rcases hs : dob.toSubject? with _ | bsub <;> simp [rdfs5For, objectsOf, hs, and_assoc]
  all_goals first
    | rfl
    | exact ⟨fun ⟨hA, a, ha, h⟩ => ⟨a, ha, hA, h⟩, fun ⟨a, ha, hA, h⟩ => ⟨hA, a, ha, h⟩⟩

/-- The six rows, in the order `stepConclusions` and `deltaConclusions`
apply them. -/
def rdfsCoreRows : List (Graph → Triple → List Triple) :=
  [rdfs7For, rdfs2For, rdfs3For, rdfs9For, rdfs11For, rdfs5For]

theorem rdfsCoreRows_additive : ∀ R, R ∈ rdfsCoreRows → RowAdditive R := by
  intro R hR
  simp only [rdfsCoreRows, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfs7For_additive
  · exact rdfs2For_additive
  · exact rdfs3For_additive
  · exact rdfs9For_additive
  · exact rdfs11For_additive
  · exact rdfs5For_additive

/-- A row searching a smaller graph concludes less. -/
theorem RowAdditive.mono {R : Graph → Triple → List Triple} (hR : RowAdditive R)
    {H G : Graph} (hsub : ∀ u, u ∈ H → u ∈ G) {d t : Triple} (h : t ∈ R H d) :
    t ∈ R G d := by
  obtain ⟨u, hu, ht⟩ := (hR H d t).mp h
  exact (hR G d t).mpr ⟨u, hsub u hu, ht⟩

/-! ## Section 2 — one naive round and one delta round, row by row -/

theorem mem_stepConclusions_iff {g : Graph} {t : Triple} :
    t ∈ stepConclusions g ↔ ∃ R, R ∈ rdfsCoreRows ∧ ∃ d, d ∈ g ∧ t ∈ R g d := by
  simp only [stepConclusions, rdfsCoreRows, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, or_assoc]

theorem mem_deltaConclusions_iff {Δ g : Graph} {t : Triple} :
    t ∈ deltaConclusions Δ g ↔ ∃ R, R ∈ rdfsCoreRows ∧ t ∈ rowDelta R Δ g := by
  simp only [deltaConclusions, rdfsCoreRows, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, or_assoc]

/-- When the delta is part of the graph, a delta round concludes nothing
that a naive round on the same graph does not. -/
theorem mem_stepConclusions_of_mem_deltaConclusions {Δ g : Graph} {t : Triple}
    (hΔ : ∀ u, u ∈ Δ → u ∈ g) (h : t ∈ deltaConclusions Δ g) : t ∈ stepConclusions g := by
  obtain ⟨R, hR, ht⟩ := mem_deltaConclusions_iff.mp h
  refine mem_stepConclusions_iff.mpr ⟨R, hR, ?_⟩
  simp only [rowDelta, List.mem_append, List.mem_flatMap] at ht
  rcases ht with ⟨d, hd, ht⟩ | ⟨d, hd, ht⟩
  · exact ⟨d, hΔ d hd, ht⟩
  · exact ⟨d, hd, (rdfsCoreRows_additive R hR).mono hΔ ht⟩

theorem mem_graphDiff {newG oldG : Graph} {u : Triple} :
    u ∈ graphDiff newG oldG ↔ u ∈ newG ∧ Graph.mem u oldG = false := by
  simp [graphDiff, graphMem_eq_any]

/-! ## Section 3 — soundness -/

/-- **Soundness, explicit fuel.** If the delta is part of the graph and
every triple of the graph is derivable from `g0`, every triple of the
loop's result is derivable from `g0`. -/
theorem semiNaiveLoop_sound (g0 : Graph) (n : Nat) :
    ∀ (S Δ : Graph), (∀ u, u ∈ Δ → u ∈ S) → (∀ u, u ∈ S → Derives g0 u) →
    ∀ {t : Triple}, t ∈ semiNaiveLoop S Δ n → Derives g0 t := by
  induction n with
  | zero => intro S Δ _ hS t h; exact hS t h
  | succ n ih =>
    intro S Δ hΔ hS t h
    simp only [semiNaiveLoop] at h
    split at h
    · exact hS t h
    · split at h
      · exact hS t h
      · refine ih _ _ (fun u hu => (mem_graphDiff.mp hu).1) ?_ h
        intro u hu
        rcases mem_addAll_cases _ S hu with hu' | hu'
        · exact hS u hu'
        · exact Derives.cut hS
            (stepConclusions_sound (mem_stepConclusions_of_mem_deltaConclusions hΔ hu'))

/-- **Soundness.** Every triple of the delta closure has a derivation in
the rule relation. No hypothesis. -/
theorem semiNaive_sound {g : Graph} {t : Triple} (h : t ∈ semiNaive g) : Derives g t :=
  semiNaiveLoop_sound g _ g g (fun _ hu => hu) (fun _ hu => Derives.base hu) h

/-! ## Section 4 — saturation -/

/-- A triple in `addAll g ts` that is not in `g` was not in `g` up to
`Triple.eqb` either: `Graph.add` appends only a triple that `g` does not
hold. -/
theorem mem_addAll_new (ts : List Triple) :
    ∀ (g : Graph) {u : Triple}, u ∈ addAll g ts → u ∈ g ∨ Graph.mem u g = false := by
  induction ts with
  | nil => intro g u h; exact Or.inl h
  | cons t ts ih =>
    intro g u h
    simp only [addAll] at h
    rcases ih (g.add t) h with h1 | h1
    · unfold Graph.add at h1
      split at h1
      · exact Or.inl h1
      · rename_i hm
        rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · rw [List.mem_singleton.mp h2]
          exact Or.inr (by simpa using hm)
    · right
      cases hm : Graph.mem u g with
      | false => rfl
      | true =>
        have := Graph.mem_add_of_mem g t u hm
        rw [h1] at this
        exact absurd this (by decide)

/-- Adding triples the graph already holds changes nothing. -/
theorem addAll_eq_self (ts : List Triple) :
    ∀ (g : Graph), (∀ t, t ∈ ts → Graph.mem t g = true) → addAll g ts = g := by
  induction ts with
  | nil => intro g _; rfl
  | cons t ts ih =>
    intro g h
    have ht : g.add t = g := by simp [Graph.add, h t (List.mem_cons_self ..)]
    simp only [addAll, ht]
    exact ih g (fun u hu => h u (List.mem_cons_of_mem _ hu))

/-- `h` is closed under the six rows: every conclusion of one naive
round on `h` is already in `h`. -/
def Saturated (h : Graph) : Prop :=
  ∀ t, t ∈ stepConclusions h → Graph.mem t h = true

theorem step_eq_of_saturated {h : Graph} (hs : Saturated h) : step h = h :=
  addAll_eq_self _ h hs

theorem saturated_of_step_eq {h : Graph} (he : step h = h) : Saturated h := by
  intro t ht
  have := graphMem_step_of_mem_conclusions ht
  rwa [he] at this

/-- `Saturated` is the hypothesis of `complete_of_saturated`. -/
theorem saturated_iff_step_eq (h : Graph) : Saturated h ↔ step h = h :=
  ⟨step_eq_of_saturated, saturated_of_step_eq⟩

/-- The run-time check of `closureSemiNaiveChecked` decides `Saturated`. -/
theorem isNaiveFixpoint_iff (h : Graph) : isNaiveFixpoint h = true ↔ Saturated h := by
  simp [isNaiveFixpoint, Saturated, graphMem_eq_any]

/-- **The round invariant.** `P` is the graph before the last round, `S`
the graph after it, `Δ` the triples the round added. -/
structure RoundInv (P S Δ : Graph) : Prop where
  /-- The delta is part of the current graph. -/
  delta_sub : ∀ u, u ∈ Δ → u ∈ S
  /-- A triple of the current graph is new or was there before. -/
  new_or_old : ∀ u, u ∈ S → u ∈ Δ ∨ u ∈ P
  /-- Every rule instance with all premises in `P` has its conclusion in
  `S`. -/
  closed : ∀ t, t ∈ stepConclusions P → Graph.mem t S = true

/-- `semiNaive g` starts as if from the empty graph, with all of `g` as
the delta. -/
theorem roundInv_init (g : Graph) : RoundInv [] g g where
  delta_sub := fun _ h => h
  new_or_old := fun _ h => Or.inl h
  closed := by intro t ht; simp [stepConclusions] at ht

/-- The graph after one delta round. -/
def nextGraph (S Δ : Graph) : Graph := addAll S (deltaConclusions Δ S)

/-- **One round preserves the invariant.** -/
theorem RoundInv.next {P S Δ : Graph} (inv : RoundInv P S Δ) :
    RoundInv S (nextGraph S Δ) (graphDiff (nextGraph S Δ) S) where
  delta_sub := fun _ hu => (mem_graphDiff.mp hu).1
  new_or_old := by
    intro u hu
    cases hm : Graph.mem u S with
    | false => exact Or.inl (mem_graphDiff.mpr ⟨hu, hm⟩)
    | true =>
      rcases mem_addAll_new _ S hu with h | h
      · exact Or.inr h
      · rw [hm] at h; exact absurd h (by decide)
  closed := by
    intro t ht
    obtain ⟨R, hR, d, hd, htR⟩ := mem_stepConclusions_iff.mp ht
    have hadd := rdfsCoreRows_additive R hR
    have fromDelta : t ∈ rowDelta R Δ S → Graph.mem t (nextGraph S Δ) = true := by
      intro h
      exact graphMem_addAll_of_mem_list _ S (mem_deltaConclusions_iff.mpr ⟨R, hR, h⟩)
    rcases inv.new_or_old d hd with hdΔ | hdP
    · -- first premise new: the left delta term
      exact fromDelta (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hdΔ, htR⟩))
    · obtain ⟨u, hu, htu⟩ := (hadd S d t).mp htR
      rcases inv.new_or_old u hu with huΔ | huP
      · -- second premise new: the right delta term
        exact fromDelta (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨d, hd, (hadd Δ d t).mpr ⟨u, huΔ, htu⟩⟩))
      · -- both premises old: covered the round before
        have htP : t ∈ R P d := (hadd P d t).mpr ⟨u, huP, htu⟩
        exact graphMem_addAll_of_graphMem _ S
          (inv.closed t (mem_stepConclusions_iff.mpr ⟨R, hR, d, hdP, htP⟩))

/-- An empty delta means the graph is closed. -/
theorem RoundInv.saturated_of_nil {P S : Graph} (inv : RoundInv P S []) : Saturated S := by
  intro t ht
  obtain ⟨R, hR, d, hd, htR⟩ := mem_stepConclusions_iff.mp ht
  have hSP : ∀ u, u ∈ S → u ∈ P := by
    intro u hu
    rcases inv.new_or_old u hu with h | h
    · cases h
    · exact h
  exact inv.closed t (mem_stepConclusions_iff.mpr
    ⟨R, hR, d, hSP d hd, (rdfsCoreRows_additive R hR).mono hSP htR⟩)

/-- A round that adds nothing means the graph is closed. -/
theorem RoundInv.saturated_of_next_eq {P S Δ : Graph} (inv : RoundInv P S Δ)
    (he : nextGraph S Δ = S) : Saturated S := by
  intro t ht
  have := inv.next.closed t ht
  rwa [he] at this

/-- Did `semiNaiveLoop g delta n` return through one of its two tests
(empty delta, or a round that added nothing), and not because the fuel
ran out? Same control flow as `semiNaiveLoop`; used by the theorems
and the guards below, not by callers. -/
def semiNaiveLoopStopsByTest (g delta : Graph) : Nat → Bool
  | 0     => false
  | n + 1 =>
      if delta.isEmpty then true
      else
        let g' := addAll g (deltaConclusions delta g)
        if g'.length = g.length then true
        else semiNaiveLoopStopsByTest g' (graphDiff g' g) n

/-- **Saturation at termination, explicit fuel.** A loop that stops by
one of its tests returns a saturated graph. -/
theorem semiNaiveLoop_saturated_of_stopsByTest (n : Nat) :
    ∀ (P S Δ : Graph), RoundInv P S Δ → semiNaiveLoopStopsByTest S Δ n = true →
      Saturated (semiNaiveLoop S Δ n) := by
  induction n with
  | zero => intro P S Δ _ h; simp [semiNaiveLoopStopsByTest] at h
  | succ n ih =>
    intro P S Δ inv hstop
    simp only [semiNaiveLoop]
    simp only [semiNaiveLoopStopsByTest] at hstop
    split
    · rename_i hnil
      have hΔ : Δ = [] := List.isEmpty_iff.mp hnil
      subst hΔ
      exact inv.saturated_of_nil
    · rename_i hnil
      simp only [hnil, Bool.false_eq_true, if_false] at hstop
      split
      · rename_i hlen
        exact inv.saturated_of_next_eq (addAll_eq_of_length_eq _ S hlen)
      · rename_i hlen
        simp only [hlen, if_false] at hstop
        exact ih S _ _ inv.next hstop

/-- **The fuel dichotomy, explicit fuel.** The result is saturated, or
the graph grew by one triple or more for each unit of fuel. -/
theorem semiNaiveLoop_saturated_or_underfueled (n : Nat) :
    ∀ (P S Δ : Graph), RoundInv P S Δ →
      Saturated (semiNaiveLoop S Δ n) ∨ S.length + n ≤ (semiNaiveLoop S Δ n).length := by
  induction n with
  | zero => intro P S Δ _; exact Or.inr (by simp [semiNaiveLoop])
  | succ n ih =>
    intro P S Δ inv
    simp only [semiNaiveLoop]
    split
    · rename_i hnil
      have hΔ : Δ = [] := List.isEmpty_iff.mp hnil
      subst hΔ
      exact Or.inl inv.saturated_of_nil
    · split
      · rename_i hlen
        exact Or.inl (inv.saturated_of_next_eq (addAll_eq_of_length_eq _ S hlen))
      · rename_i _ hlen
        rcases ih S _ _ inv.next with h | h
        · exact Or.inl h
        · have h1 : S.length ≤ (nextGraph S Δ).length := length_le_addAll _ S
          have h2 : (nextGraph S Δ).length ≠ S.length := hlen
          exact Or.inr (by simp only [nextGraph] at h1 h2 h ⊢; omega)

/-- **The fuel dichotomy** for `semiNaive`. -/
theorem semiNaive_saturated_or_underfueled (g : Graph) :
    Saturated (semiNaive g) ∨ g.length + closureFuelBound g ≤ (semiNaive g).length :=
  semiNaiveLoop_saturated_or_underfueled _ [] g g (roundInv_init g)

/-- **Saturation at termination** for `semiNaive`. -/
theorem semiNaive_saturated_of_stopsByTest {g : Graph}
    (h : semiNaiveLoopStopsByTest g g (closureFuelBound g) = true) :
    Saturated (semiNaive g) :=
  semiNaiveLoop_saturated_of_stopsByTest _ [] g g (roundInv_init g) h

/-! ## Section 5 — least fixed point, and the two closures compared -/

/-- The loop never loses a triple. -/
theorem semiNaiveLoop_extensive (n : Nat) :
    ∀ (S Δ : Graph) {t : Triple}, t ∈ S → t ∈ semiNaiveLoop S Δ n := by
  induction n with
  | zero => intro S Δ t h; exact h
  | succ n ih =>
    intro S Δ t h
    simp only [semiNaiveLoop]
    split
    · exact h
    · split
      · exact h
      · exact ih _ _ (mem_addAll_of_mem _ S h)

/-- **Least fixed point.** A saturated delta closure holds everything
`g` derives. -/
theorem semiNaive_complete_of_saturated {g : Graph} (hs : Saturated (semiNaive g))
    {t : Triple} (h : Derives g t) : Graph.mem t (semiNaive g) = true :=
  complete_of_saturated (step_eq_of_saturated hs)
    (fun _ hu => graphMem_of_mem (semiNaiveLoop_extensive _ g g hu)) h

/-- Two graphs that are each sound and complete for `Derives g` have the
same members. Stated once, used for both closures. -/
theorem graphMem_eq_of_sound_complete {g A B : Graph}
    (sA : ∀ u, u ∈ A → Derives g u) (cA : ∀ u, Derives g u → Graph.mem u A = true)
    (sB : ∀ u, u ∈ B → Derives g u) (cB : ∀ u, Derives g u → Graph.mem u B = true)
    (t : Triple) : Graph.mem t A = Graph.mem t B := by
  have move : ∀ {X Y : Graph}, (∀ u, u ∈ X → Derives g u) →
      (∀ u, Derives g u → Graph.mem u Y = true) →
      Graph.mem t X = true → Graph.mem t Y = true := by
    intro X Y sX cY h
    obtain ⟨u, hu, he⟩ := exists_of_graphMem h
    exact graphMem_of_graphMem_eqb (cY u (sX u hu)) he
  exact Bool.eq_iff_iff.mpr ⟨move sA cB, move sB cA⟩

/-- **The two saturated closures are equal as sets.** -/
theorem semiNaive_mem_eq_closureFix {g : Graph} (hs : Saturated (semiNaive g))
    (hc : step (closureFix g) = closureFix g) (t : Triple) :
    Graph.mem t (semiNaive g) = Graph.mem t (closureFix g) :=
  graphMem_eq_of_sound_complete
    (fun _ hu => semiNaive_sound hu)
    (fun _ hu => semiNaive_complete_of_saturated hs hu)
    (fun _ hu => closure_sound _ g hu)
    (fun _ hu => closure_complete_of_saturated hc hu) t

/-! ## Section 6 — the checked entry -/

/-- The checked entry is sound with no hypothesis. -/
theorem closureSemiNaiveChecked_sound {g : Graph} {t : Triple}
    (h : t ∈ closureSemiNaiveChecked g) : Derives g t := by
  simp only [closureSemiNaiveChecked] at h
  split at h
  · exact semiNaive_sound h
  · exact closure_sound _ g h

/-- **The checked entry has the members of `closureFix g`** whenever
`closureFix g` is saturated, for every outcome of the delta loop. -/
theorem closureSemiNaiveChecked_mem_eq_closureFix {g : Graph}
    (hc : step (closureFix g) = closureFix g) (t : Triple) :
    Graph.mem t (closureSemiNaiveChecked g) = Graph.mem t (closureFix g) := by
  simp only [closureSemiNaiveChecked]
  split
  · rename_i hfix
    exact semiNaive_mem_eq_closureFix ((isNaiveFixpoint_iff _).mp hfix) hc t
  · rfl

/-- The checked entry is complete whenever `closureFix g` is saturated. -/
theorem closureSemiNaiveChecked_complete {g : Graph}
    (hc : step (closureFix g) = closureFix g) {t : Triple} (h : Derives g t) :
    Graph.mem t (closureSemiNaiveChecked g) = true := by
  rw [closureSemiNaiveChecked_mem_eq_closureFix hc]
  exact closure_complete_of_saturated hc h

/-! ## Section 7 — the checked entry without the redundant naive round

`closureSemiNaiveChecked` applies one full naive round
(`isNaiveFixpoint`) to the result of the delta loop. Section 4 proves
that round redundant whenever the loop stopped by one of its tests:
`semiNaive_saturated_of_stopsByTest` gives the answer the round would
compute. So the compiled code only needs the round when the loop used
up its fuel, which is the case the open obligation (item 4 of issue
https://github.com/danbri/factoidal/issues/756) is about.

The first delta round of `semiNaive g` has the whole graph as its
delta, so its two delta terms per row are the same list, and the round
is exactly one naive round (`addAll_deltaConclusions_self`). The
compiled code runs that round as `stepFast`.

`closureSemiNaiveCheckedFast` does both. `closureSemiNaiveCheckedFast_eq`
proves it equal to `closureSemiNaiveChecked` as a LIST, with no
hypothesis, and `@[csimp]` makes every caller compiled after this module
run it. The definition `closureSemiNaiveChecked`, with its run-time
check, is unchanged. -/

theorem addAll_append (a b : List Triple) :
    ∀ g : Graph, addAll g (a ++ b) = addAll (addAll g a) b := by
  induction a with
  | nil => intro g; rfl
  | cons t a ih => intro g; exact ih (g.add t)

theorem addAll_twice (g : Graph) (c : List Triple) : addAll (addAll g c) c = addAll g c :=
  addAll_eq_self c _ (fun _ ht => graphMem_addAll_of_mem_list c g ht)

/-- Round 1 of `semiNaive g` is one naive round. -/
theorem addAll_deltaConclusions_self (g : Graph) :
    addAll g (deltaConclusions g g) = step g := by
  simp only [deltaConclusions, rowDelta, step, stepConclusions, addAll_append, addAll_twice]

/-- The indexed delta loop, also returning whether it stopped by one of
its tests. -/
def semiNaiveLoopFlagFast (g delta : Graph) : Nat → Graph × Bool
  | 0     => (g, false)
  | n + 1 =>
      if delta.isEmpty then (g, true)
      else
        let g' := ((FastGraph.ofGraph g).addAll (deltaConclusionsIx delta g)).toGraph
        if g'.length = g.length then (g, true)
        else semiNaiveLoopFlagFast g' (g'.drop g.length) n

theorem semiNaiveLoopFlagFast_eq (n : Nat) :
    ∀ g delta : Graph, semiNaiveLoopFlagFast g delta n =
      (semiNaiveLoop g delta n, semiNaiveLoopStopsByTest g delta n) := by
  induction n with
  | zero => intro g delta; rfl
  | succ n ih =>
    intro g delta
    have hstep : ((FastGraph.ofGraph g).addAll (deltaConclusionsIx delta g)).toGraph
        = addAll g (deltaConclusions delta g) := by
      rw [FastGraph.addAll_toGraph _ _ (FastGraph.ofGraph_inv g), FastGraph.ofGraph_toGraph,
        deltaConclusionsIx_eq, addAll_eq_graphAddAll]
    simp only [semiNaiveLoopFlagFast, semiNaiveLoop, semiNaiveLoopStopsByTest, hstep]
    by_cases hd : delta.isEmpty = true
    · simp only [hd, if_true]
    · simp only [hd, Bool.false_eq_true, if_false]
      by_cases hl : (addAll g (deltaConclusions delta g)).length = g.length
      · simp only [hl, if_true]
      · simp only [hl, if_false]
        rw [ih, graphDiff_addAll]

/-- The delta closure with its stopping reason: round 1 as one indexed
naive round, then the indexed delta loop. -/
def semiNaiveRunFast (g : Graph) : Nat → Graph × Bool
  | 0     => (g, false)
  | n + 1 =>
      if g.isEmpty then (g, true)
      else
        let g' := stepFast g
        if g'.length = g.length then (g, true)
        else semiNaiveLoopFlagFast g' (g'.drop g.length) n

theorem semiNaiveRunFast_eq (g : Graph) (n : Nat) :
    semiNaiveRunFast g n = (semiNaiveLoop g g n, semiNaiveLoopStopsByTest g g n) := by
  rw [← semiNaiveLoopFlagFast_eq]
  cases n with
  | zero => rfl
  | succ n =>
    have h1 : ((FastGraph.ofGraph g).addAll (deltaConclusionsIx g g)).toGraph = stepFast g := by
      rw [FastGraph.addAll_toGraph _ _ (FastGraph.ofGraph_inv g), FastGraph.ofGraph_toGraph,
        deltaConclusionsIx_eq, ← addAll_eq_graphAddAll, addAll_deltaConclusions_self,
        stepFast_eq]
    simp only [semiNaiveRunFast, semiNaiveLoopFlagFast, h1]

/-- `semiNaive` through `semiNaiveRunFast`. -/
def semiNaiveFast (g : Graph) : Graph := (semiNaiveRunFast g (closureFuelBound g)).1

@[csimp] theorem semiNaive_eq_fast : @semiNaive = @semiNaiveFast := by
  funext g
  simp only [semiNaiveFast, semiNaiveRunFast_eq, semiNaive]

/-- `closureSemiNaiveChecked`, with the naive round run only when the
delta loop used up its fuel. -/
def closureSemiNaiveCheckedFast (g : Graph) : Graph :=
  let r := semiNaiveRunFast g (closureFuelBound g)
  if r.2 then r.1
  else if isNaiveFixpoint r.1 then r.1 else closureFix g

/-- **The fast checked entry is the checked entry**, as a list, with no
hypothesis. The proof is where saturation at termination
(`semiNaive_saturated_of_stopsByTest`) is used. -/
theorem closureSemiNaiveCheckedFast_eq (g : Graph) :
    closureSemiNaiveCheckedFast g = closureSemiNaiveChecked g := by
  simp only [closureSemiNaiveCheckedFast, closureSemiNaiveChecked, semiNaiveRunFast_eq]
  by_cases hs : semiNaiveLoopStopsByTest g g (closureFuelBound g) = true
  · have hfix : isNaiveFixpoint (semiNaive g) = true :=
      (isNaiveFixpoint_iff _).mpr (semiNaive_saturated_of_stopsByTest hs)
    simp only [semiNaive] at hfix
    simp only [hs, hfix, if_true, semiNaive]
  · simp only [hs, Bool.false_eq_true, if_false, semiNaive]
    rfl

/-- The compiler emits `closureSemiNaiveCheckedFast` for every call of
`closureSemiNaiveChecked` compiled after this module. -/
@[csimp] theorem closureSemiNaiveChecked_eq_fast :
    @closureSemiNaiveChecked = @closureSemiNaiveCheckedFast := by
  funext g
  exact (closureSemiNaiveCheckedFast_eq g).symm

/-! ## Build-time checks

The hypotheses of the theorems above are satisfiable on real inputs:
the delta loop stops by a test on the four graphs of `RDFS.SemiNaive`,
so `semiNaive_saturated_of_stopsByTest` applies to them. -/

#guard semiNaiveLoopStopsByTest chain chain (closureFuelBound chain)
#guard semiNaiveLoopStopsByTest schema schema (closureFuelBound schema)
#guard semiNaiveLoopStopsByTest cyc cyc (closureFuelBound cyc)
#guard semiNaiveLoopStopsByTest [] [] (closureFuelBound [])

/- Negative cases. With one unit of fuel the chain is not finished:
the loop does NOT stop by a test, and its result is NOT saturated. A
`semiNaiveLoopStopsByTest` that answered `true` everywhere fails here. -/
#guard !semiNaiveLoopStopsByTest chain chain 1
#guard !isNaiveFixpoint (semiNaiveLoop chain chain 1)

/- The invariant hypothesis is needed. Started with an empty delta, the
loop stops by its first test at once, and the result (the input chain)
is not saturated. `RoundInv P chain []` holds for no `P`: it needs
`chain ⊆ P`, and then `stepConclusions P` contains the conclusions of
`stepConclusions chain`, which the chain lacks. -/
#guard semiNaiveLoopStopsByTest chain [] 5
#guard !isNaiveFixpoint (semiNaiveLoop chain [] 5)

/- `RowAdditive` on concrete rows: the conclusions of a row over a graph
are the conclusions over its single triples, for every first premise of
`schema` and `chain`. -/
#guard schema.all (fun d => rdfsCoreRows.all (fun R =>
  sameGraph (R schema d) (schema.flatMap (fun u => R [u] d))))
#guard chain.all (fun d => rdfsCoreRows.all (fun R =>
  sameGraph (R chain d) (chain.flatMap (fun u => R [u] d))))

/-! ## Axiom audit

Only `propext`, `Classical.choice` and `Quot.sound`. Output of the build
on 2026-10-12 is recorded beside each line. -/

-- 'L4Factoidal.RDFS.semiNaive_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_sound
-- 'L4Factoidal.RDFS.semiNaiveLoop_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaiveLoop_sound
-- 'L4Factoidal.RDFS.RoundInv.next' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.RoundInv.next
-- 'L4Factoidal.RDFS.semiNaiveLoop_saturated_of_stopsByTest' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaiveLoop_saturated_of_stopsByTest
-- 'L4Factoidal.RDFS.semiNaiveLoop_saturated_or_underfueled' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaiveLoop_saturated_or_underfueled
-- 'L4Factoidal.RDFS.semiNaive_saturated_of_stopsByTest' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_saturated_of_stopsByTest
-- 'L4Factoidal.RDFS.semiNaive_saturated_or_underfueled' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_saturated_or_underfueled
-- 'L4Factoidal.RDFS.semiNaive_complete_of_saturated' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_complete_of_saturated
-- 'L4Factoidal.RDFS.semiNaive_mem_eq_closureFix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_mem_eq_closureFix
-- 'L4Factoidal.RDFS.closureSemiNaiveChecked_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.closureSemiNaiveChecked_sound
-- 'L4Factoidal.RDFS.closureSemiNaiveChecked_mem_eq_closureFix' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.closureSemiNaiveChecked_mem_eq_closureFix
-- 'L4Factoidal.RDFS.closureSemiNaiveChecked_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.closureSemiNaiveChecked_complete
-- 'L4Factoidal.RDFS.semiNaiveLoop_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaiveLoop_eq_fast
-- 'L4Factoidal.RDFS.isNaiveFixpoint_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.isNaiveFixpoint_eq_fast
-- 'L4Factoidal.RDFS.addAll_deltaConclusions_self' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.addAll_deltaConclusions_self
-- 'L4Factoidal.RDFS.semiNaiveRunFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaiveRunFast_eq
-- 'L4Factoidal.RDFS.semiNaive_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.semiNaive_eq_fast
-- 'L4Factoidal.RDFS.closureSemiNaiveCheckedFast_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.closureSemiNaiveCheckedFast_eq
-- 'L4Factoidal.RDFS.closureSemiNaiveChecked_eq_fast' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms L4Factoidal.RDFS.closureSemiNaiveChecked_eq_fast

end L4Factoidal.RDFS
