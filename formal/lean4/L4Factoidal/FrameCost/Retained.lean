import Init

/-! # Partial compile: what a frame compiles (`NativeSVG.compileRetained`)

A frame's primitives are compiled again only where the key at an index differs from the
key at that index in the last frame. `recompiled` counts such indices for the first `n`
primitives. The lemmas say what this cost model gives: no change compiles nothing, and
primitives added to the page that do not change cost nothing. That the engine compiles
exactly these primitives is not proved: the counters (`frameWork.recompiled`) are compared
in `partial_frame_test.ts`, which also compares the bytes with the plain compile. -/
namespace L4Factoidal.FrameCost

variable {κ : Type}

/-- How many of the first `n` primitives are compiled again: those where `same` is false
for the key of the last frame (`old i`) and of this frame (`new i`). -/
def recompiled (same : κ → κ → Bool) (old new : Nat → κ) : Nat → Nat
  | 0 => 0
  | n+1 => recompiled same old new n + (if same (old n) (new n) then 0 else 1)

/-- No key differs: nothing is compiled, whatever the size of the page. -/
theorem recompiled_of_same (same : κ → κ → Bool) (old new : Nat → κ) (n : Nat)
    (h : ∀ i < n, same (old i) (new i) = true) : recompiled same old new n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    simp [recompiled, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), hn]

/-- A frame identical to the last one compiles nothing (`same` is reflexive on its keys). -/
theorem no_change_no_compile (same : κ → κ → Bool) (keys : Nat → κ) (n : Nat)
    (refl : ∀ i, same (keys i) (keys i) = true) : recompiled same keys keys n = 0 :=
  recompiled_of_same same keys keys n fun i _ => refl i

/-- Primitives added after index `n` that are the same in both frames cost nothing: the cost
of a change depends on the primitives changed, not on the size of the page. -/
theorem recompiled_add_same (same : κ → κ → Bool) (old new : Nat → κ) (n m : Nat)
    (h : ∀ i, n ≤ i → i < n+m → same (old i) (new i) = true) :
    recompiled same old new (n+m) = recompiled same old new n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm := h (n+m) (Nat.le_add_right _ _) (by omega)
    rw [show n+(m+1) = (n+m)+1 from rfl, recompiled]
    simp only [hm, if_true, Nat.add_zero]
    exact ih fun i hi hlt => h i hi (by omega)

/-- Each index counts at most once, so the cost is at most the number of primitives. -/
theorem recompiled_le (same : κ → κ → Bool) (old new : Nat → κ) (n : Nat) :
    recompiled same old new n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [recompiled]
    split <;> omega

end L4Factoidal.FrameCost
