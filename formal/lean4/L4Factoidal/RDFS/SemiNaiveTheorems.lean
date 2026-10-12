/-
L4Factoidal.RDFS.SemiNaiveTheorems — scratch
-/
import L4Factoidal.RDFS.SemiNaive
import L4Factoidal.RDFS.ClosureTheorems

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

theorem graphMem_eq_any (t : Triple) (g : Graph) :
    Graph.mem t g = g.any (fun u => u.eqb t) := by
  induction g with
  | nil => rfl
  | cons hd tl ih => simp [Graph.mem, List.any_cons, ih]

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

def rows : List (Graph → Triple → List Triple) :=
  [rdfs7For, rdfs2For, rdfs3For, rdfs9For, rdfs11For, rdfs5For]

theorem rows_additive : ∀ R, R ∈ rows → RowAdditive R := by
  intro R hR
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rdfs7For_additive
  · exact rdfs2For_additive
  · exact rdfs3For_additive
  · exact rdfs9For_additive
  · exact rdfs11For_additive
  · exact rdfs5For_additive

theorem RowAdditive.mono {R : Graph → Triple → List Triple} (hR : RowAdditive R)
    {H G : Graph} (hsub : ∀ u, u ∈ H → u ∈ G) {d t : Triple} (h : t ∈ R H d) :
    t ∈ R G d := by
  obtain ⟨u, hu, ht⟩ := (hR H d t).mp h
  exact (hR G d t).mpr ⟨u, hsub u hu, ht⟩

theorem mem_stepConclusions_iff {g : Graph} {t : Triple} :
    t ∈ stepConclusions g ↔ ∃ R, R ∈ rows ∧ ∃ d, d ∈ g ∧ t ∈ R g d := by
  simp only [stepConclusions, rows, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, or_assoc]

theorem mem_deltaConclusions_iff {Δ g : Graph} {t : Triple} :
    t ∈ deltaConclusions Δ g ↔ ∃ R, R ∈ rows ∧ t ∈ rowDelta R Δ g := by
  simp only [deltaConclusions, rows, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, or_assoc]

theorem mem_stepConclusions_of_mem_deltaConclusions {Δ g : Graph} {t : Triple}
    (hΔ : ∀ u, u ∈ Δ → u ∈ g) (h : t ∈ deltaConclusions Δ g) : t ∈ stepConclusions g := by
  obtain ⟨R, hR, ht⟩ := mem_deltaConclusions_iff.mp h
  refine mem_stepConclusions_iff.mpr ⟨R, hR, ?_⟩
  simp only [rowDelta, List.mem_append, List.mem_flatMap] at ht
  rcases ht with ⟨d, hd, ht⟩ | ⟨d, hd, ht⟩
  · exact ⟨d, hΔ d hd, ht⟩
  · exact ⟨d, hd, (rows_additive R hR).mono hΔ ht⟩

theorem mem_graphDiff {newG oldG : Graph} {u : Triple} :
    u ∈ graphDiff newG oldG ↔ u ∈ newG ∧ Graph.mem u oldG = false := by
  simp [graphDiff, graphMem_eq_any]

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

theorem semiNaive_sound {g : Graph} {t : Triple} (h : t ∈ semiNaive g) : Derives g t :=
  semiNaiveLoop_sound g _ g g (fun _ hu => hu) (fun _ hu => Derives.base hu) h

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

theorem addAll_eq_self (ts : List Triple) :
    ∀ (g : Graph), (∀ t, t ∈ ts → Graph.mem t g = true) → addAll g ts = g := by
  induction ts with
  | nil => intro g _; rfl
  | cons t ts ih =>
    intro g h
    have ht : g.add t = g := by simp [Graph.add, h t (List.mem_cons_self ..)]
    simp only [addAll, ht]
    exact ih g (fun u hu => h u (List.mem_cons_of_mem _ hu))

def Saturated (h : Graph) : Prop :=
  ∀ t, t ∈ stepConclusions h → Graph.mem t h = true

theorem step_eq_of_saturated {h : Graph} (hs : Saturated h) : step h = h :=
  addAll_eq_self _ h hs

theorem saturated_of_step_eq {h : Graph} (he : step h = h) : Saturated h := by
  intro t ht
  have := graphMem_step_of_mem_conclusions ht
  rwa [he] at this

theorem saturated_iff_step_eq (h : Graph) : Saturated h ↔ step h = h :=
  ⟨step_eq_of_saturated, saturated_of_step_eq⟩

theorem isNaiveFixpoint_iff (h : Graph) : isNaiveFixpoint h = true ↔ Saturated h := by
  simp [isNaiveFixpoint, Saturated, graphMem_eq_any]

structure RoundInv (P S Δ : Graph) : Prop where
  delta_sub : ∀ u, u ∈ Δ → u ∈ S
  new_or_old : ∀ u, u ∈ S → u ∈ Δ ∨ u ∈ P
  closed : ∀ t, t ∈ stepConclusions P → Graph.mem t S = true

theorem roundInv_init (g : Graph) : RoundInv [] g g where
  delta_sub := fun _ h => h
  new_or_old := fun _ h => Or.inl h
  closed := by intro t ht; simp [stepConclusions] at ht

def nextGraph (S Δ : Graph) : Graph := addAll S (deltaConclusions Δ S)

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
    have hadd := rows_additive R hR
    have fromDelta : t ∈ rowDelta R Δ S → Graph.mem t (nextGraph S Δ) = true := by
      intro h
      exact graphMem_addAll_of_mem_list _ S (mem_deltaConclusions_iff.mpr ⟨R, hR, h⟩)
    rcases inv.new_or_old d hd with hdΔ | hdP
    · exact fromDelta (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hdΔ, htR⟩))
    · obtain ⟨u, hu, htu⟩ := (hadd S d t).mp htR
      rcases inv.new_or_old u hu with huΔ | huP
      · exact fromDelta (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨d, hd, (hadd Δ d t).mpr ⟨u, huΔ, htu⟩⟩))
      · have htP : t ∈ R P d := (hadd P d t).mpr ⟨u, huP, htu⟩
        exact graphMem_addAll_of_graphMem _ S
          (inv.closed t (mem_stepConclusions_iff.mpr ⟨R, hR, d, hdP, htP⟩))

theorem RoundInv.saturated_of_nil {P S : Graph} (inv : RoundInv P S []) : Saturated S := by
  intro t ht
  obtain ⟨R, hR, d, hd, htR⟩ := mem_stepConclusions_iff.mp ht
  have hSP : ∀ u, u ∈ S → u ∈ P := by
    intro u hu
    rcases inv.new_or_old u hu with h | h
    · cases h
    · exact h
  exact inv.closed t (mem_stepConclusions_iff.mpr
    ⟨R, hR, d, hSP d hd, (rows_additive R hR).mono hSP htR⟩)

theorem RoundInv.saturated_of_next_eq {P S Δ : Graph} (inv : RoundInv P S Δ)
    (he : nextGraph S Δ = S) : Saturated S := by
  intro t ht
  have := inv.next.closed t ht
  rwa [he] at this

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

def semiNaiveLoopStopsByTest (g delta : Graph) : Nat → Bool
  | 0     => false
  | n + 1 =>
      if delta.isEmpty then true
      else
        let g' := addAll g (deltaConclusions delta g)
        if g'.length = g.length then true
        else semiNaiveLoopStopsByTest g' (graphDiff g' g) n

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

theorem semiNaive_saturated_or_underfueled (g : Graph) :
    Saturated (semiNaive g) ∨ g.length + closureFuelBound g ≤ (semiNaive g).length :=
  semiNaiveLoop_saturated_or_underfueled _ [] g g (roundInv_init g)

theorem semiNaive_saturated_of_stopsByTest {g : Graph}
    (h : semiNaiveLoopStopsByTest g g (closureFuelBound g) = true) :
    Saturated (semiNaive g) :=
  semiNaiveLoop_saturated_of_stopsByTest _ [] g g (roundInv_init g) h

theorem semiNaive_complete_of_saturated {g : Graph} (hs : Saturated (semiNaive g))
    {t : Triple} (h : Derives g t) : Graph.mem t (semiNaive g) = true :=
  complete_of_saturated (step_eq_of_saturated hs)
    (fun _ hu => graphMem_of_mem (semiNaiveLoop_extensive _ g g hu)) h

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

theorem semiNaive_mem_eq_closureFix {g : Graph} (hs : Saturated (semiNaive g))
    (hc : step (closureFix g) = closureFix g) (t : Triple) :
    Graph.mem t (semiNaive g) = Graph.mem t (closureFix g) :=
  graphMem_eq_of_sound_complete
    (fun _ hu => semiNaive_sound hu)
    (fun _ hu => semiNaive_complete_of_saturated hs hu)
    (fun _ hu => closure_sound _ g hu)
    (fun _ hu => closure_complete_of_saturated hc hu) t

theorem closureSemiNaiveChecked_sound {g : Graph} {t : Triple}
    (h : t ∈ closureSemiNaiveChecked g) : Derives g t := by
  simp only [closureSemiNaiveChecked] at h
  split at h
  · exact semiNaive_sound h
  · exact closure_sound _ g h

theorem closureSemiNaiveChecked_mem_eq_closureFix {g : Graph}
    (hc : step (closureFix g) = closureFix g) (t : Triple) :
    Graph.mem t (closureSemiNaiveChecked g) = Graph.mem t (closureFix g) := by
  simp only [closureSemiNaiveChecked]
  split
  · rename_i hfix
    exact semiNaive_mem_eq_closureFix ((isNaiveFixpoint_iff _).mp hfix) hc t
  · rfl

theorem closureSemiNaiveChecked_complete {g : Graph}
    (hc : step (closureFix g) = closureFix g) {t : Triple} (h : Derives g t) :
    Graph.mem t (closureSemiNaiveChecked g) = true := by
  rw [closureSemiNaiveChecked_mem_eq_closureFix hc]
  exact closure_complete_of_saturated hc h

end L4Factoidal.RDFS
