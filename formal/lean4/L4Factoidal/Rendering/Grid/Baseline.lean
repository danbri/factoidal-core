import L4Factoidal.Rendering.Grid.Placement

/-!
L4Factoidal.Rendering.Grid.Baseline — baseline alignment of grid items in their rows
(CSS Grid Layout 2 §11.6, CSS Box Alignment 3 §9.3).

The items of one row with `align-self: baseline` that span that row alone form a
baseline-sharing group: each is moved down by the difference between the group's
largest baseline and its own, so that their baselines line up. The shift adds to what
the item asks of its row (§12.5: "baseline-shim").

An aligned item is `(row, baseline)`: its row, and its baseline in layout units from the
top of its margin box. Only the aligned items are given, so a grid with none costs
nothing.
-/
namespace L4Factoidal.Rendering.Grid

/-- The largest baseline of the aligned items of row `r` (0 when there are none). -/
def rowBaseline (aligned : List (Nat × Nat)) (r : Nat) : Nat :=
  aligned.foldl (fun m p => max m (if p.1 = r then p.2 else 0)) 0

/-- How far an aligned item of row `row` with baseline `b` moves down. -/
def baselineShift (aligned : List (Nat × Nat)) (row b : Nat) : Nat := rowBaseline aligned row - b

/-- Kind: conformance (CSS Box Alignment 3 §9.3). Says: an aligned item's baseline is at
most its row's largest, so after its shift it is exactly there. -/
theorem baselineShift_spec (aligned : List (Nat × Nat)) (row b : Nat) (h : (row, b) ∈ aligned) :
    baselineShift aligned row b + b = rowBaseline aligned row := by
  have hle : b ≤ rowBaseline aligned row := by
    have := foldl_max_mem (fun p => if p.1 = row then p.2 else 0) aligned 0 (row, b) h
    simpa [rowBaseline] using this
  unfold baselineShift; omega

/-- Kind: conformance (CSS Box Alignment 3 §9.3: the items of a baseline-sharing group
have their baselines aligned). Says: two aligned items of one row end with their
baselines at the same place. -/
theorem baselineShift_aligned (aligned : List (Nat × Nat)) (row b₁ b₂ : Nat)
    (h₁ : (row, b₁) ∈ aligned) (h₂ : (row, b₂) ∈ aligned) :
    baselineShift aligned row b₁ + b₁ = baselineShift aligned row b₂ + b₂ := by
  rw [baselineShift_spec aligned row b₁ h₁, baselineShift_spec aligned row b₂ h₂]

/-! ### Examples -/

#guard baselineShift [(0, 10), (0, 25), (1, 5)] 0 10 == 15
#guard baselineShift [(0, 10), (0, 25), (1, 5)] 0 25 == 0
#guard baselineShift [(0, 10), (0, 25), (1, 5)] 1 5 == 0
#guard rowBaseline [] 3 == 0

end L4Factoidal.Rendering.Grid
