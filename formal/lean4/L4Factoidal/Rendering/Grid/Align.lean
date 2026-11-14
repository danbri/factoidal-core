/-
L4Factoidal.Rendering.Grid.Align — where tracks and items go once the tracks are sized
(CSS Grid Layout 2 §11, CSS Box Alignment 3 §4 to §6).

* `contentOffsets`: the free space of an axis shared out by `justify-content` or
  `align-content`: an offset before the first track and an addition to every gap.
* `trackStarts`: the start of every track; `spanExtent`: the start and size of the area
  of a span of tracks.
* `selfOffset`: where an item sits in its area by `justify-self` or `align-self`.

Sizes are whole layout units; offsets are integers (an item or a grid larger than its
room starts before it when centred or end-aligned).

Proved here: the distributed space never exceeds the free space, so the tracks stay
inside the container (`contentOffsets_within`); an item no larger than its area lies inside
the area under every alignment (`selfOffset_inside`).
-/
import Std

namespace L4Factoidal.Rendering.Grid

/-- How free space is distributed among tracks (`justify-content`, `align-content`;
`normal` and `stretch` leave the tracks at the start: stretching auto tracks is part of
track sizing, §12.8). -/
inductive Distribution where
  | start | end_ | center | spaceBetween | spaceAround | spaceEvenly
  deriving Repr, BEq, Inhabited

/-- Positive free space `free` among `n` tracks: the offset of the first track and the
addition to each gap. With one track, `space-between` is `start` and `space-around` is
`center` (the fallback alignments of CSS Box Alignment 3 §4.3). -/
def contentOffsets (d : Distribution) (free n : Nat) : Nat × Nat :=
  match d with
  | .start => (0, 0)
  | .end_ => (free, 0)
  | .center => (free / 2, 0)
  | .spaceBetween => if n ≤ 1 then (0, 0) else (0, free / (n - 1))
  | .spaceAround => if n = 0 then (0, 0) else (free / (2 * n), free / n)
  | .spaceEvenly => (free / (n + 1), free / (n + 1))

/-- Kind: bound. Says: the offset before the first track plus the additions to the
`n − 1` gaps is at most the free space, so with non-negative free space the last track
ends inside the container. Does not say: that the space left over is split evenly at
both ends (whole units: up to `n` units stay at the end). -/
theorem contentOffsets_within (d : Distribution) (free n : Nat) :
    (contentOffsets d free n).1 + (n - 1) * (contentOffsets d free n).2 ≤ free := by
  cases d
  · simp [contentOffsets]
  · simp [contentOffsets]
  · simp only [contentOffsets, Nat.mul_zero, Nat.add_zero]; exact Nat.div_le_self _ _
  · simp only [contentOffsets]
    split
    · simp
    · simp only [Nat.zero_add]
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  · simp only [contentOffsets]
    split
    · simp
    · rename_i hn
      cases n with
      | zero => exact absurd rfl hn
      | succ m =>
        have h1 : (m + 1) * (free / (m + 1)) ≤ free := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
        have h2 : (m + 1) * (free / (m + 1)) = m * (free / (m + 1)) + free / (m + 1) := Nat.succ_mul _ _
        have h3 : free / (2 * (m + 1)) ≤ free / (m + 1) :=
          Nat.div_le_div_left (by omega) (by omega)
        simp only [Nat.add_sub_cancel]
        omega
  · simp only [contentOffsets]
    cases n with
    | zero => simp
    | succ m =>
      have h1 : (m + 1 + 1) * (free / (m + 1 + 1)) ≤ free := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
      have h2 : (m + 1 + 1) * (free / (m + 1 + 1)) = (m + 1) * (free / (m + 1 + 1)) + free / (m + 1 + 1) :=
        Nat.succ_mul _ _
      have h3 : (m + 1) * (free / (m + 1 + 1)) = m * (free / (m + 1 + 1)) + free / (m + 1 + 1) := Nat.succ_mul _ _
      simp only [Nat.add_sub_cancel]
      generalize free / (m + 1 + 1) = q at h1 h2 h3 ⊢
      omega

/-- The offset of the first track and the addition to each gap for any free space: with
none or less than none, `end` and `center` still move the tracks (they overflow at the
start or at both ends); the space distributions fall back to `start`. -/
def contentOffsetsInt (d : Distribution) (free : Int) (n : Nat) : Int × Int :=
  if 0 ≤ free then
    let r := contentOffsets d free.toNat n
    ((r.1 : Int), (r.2 : Int))
  else match d with
    | .end_ => (free, 0)
    | .center => (free / 2, 0)
    | _ => (0, 0)

/-- The start of every track: the first at `offset`, each next one after the track
before it, the gap and `between`. -/
def trackStarts (sizes : Array Nat) (gap : Nat) (offset between : Int) : Array Int :=
  (sizes.foldl (fun (acc : Array Int × Int) (s : Nat) => (acc.1.push acc.2, acc.2 + Int.ofNat s + Int.ofNat gap + between))
    (#[], offset)).1

/-- The start and the size of the area of the tracks `start` up to `start + span`:
from the start of the first to the end of the last, the gaps between them included. -/
def spanExtent (starts : Array Int) (sizes : Array Nat) (start span : Nat) : Int × Nat :=
  let s := starts.getD start 0
  let last := start + span - 1
  (s, (starts.getD last 0 + Int.ofNat (sizes.getD last 0) - s).toNat)

/-- `justify-self` and `align-self` as the layout uses them (`normal` and `stretch`
start at the start edge; the size of a stretched item is set by the layout). -/
inductive SelfAlign where
  | start | end_ | center | stretch
  deriving Repr, BEq, Inhabited

/-- The offset of an item's margin box of `size` from the start of its area of `area`. -/
def selfOffset (a : SelfAlign) (area size : Nat) : Int :=
  match a with
  | .start | .stretch => 0
  | .end_ => (area : Int) - (size : Int)
  | .center => ((area : Int) - (size : Int)) / 2

/-- Kind: containment ("every item lies inside its grid area"). Says: an item whose
margin box is no larger than its area starts at or after the start of the area and ends
at or before its end, under every alignment. Does not say: anything of an item larger
than its area (it overflows: at the end for `start`, at the start for `end`, at both
for `center`), or of positioned or transformed items. -/
theorem selfOffset_inside (a : SelfAlign) (area size : Nat) (h : size ≤ area) :
    0 ≤ selfOffset a area size ∧ selfOffset a area size + (size : Int) ≤ (area : Int) := by
  cases a <;> simp only [selfOffset] <;> omega

/-! ### Examples -/

#guard (trackStarts #[100, 200, 300] 10 0 0).toList == [0, 110, 320]
#guard (trackStarts #[100, 200] 0 50 25).toList == [50, 175]
#guard spanExtent (trackStarts #[100, 200, 300] 10 0 0) #[100, 200, 300] 1 2 == (110, 510)
#guard contentOffsets .spaceBetween 100 3 == (0, 50)
#guard contentOffsets .spaceAround 120 3 == (20, 40)
#guard contentOffsets .spaceEvenly 120 3 == (30, 30)
#guard contentOffsets .center 100 3 == (50, 0)
#guard contentOffsetsInt .center (-100) 3 == (-50, 0)
#guard contentOffsetsInt .spaceBetween (-100) 3 == (0, 0)
#guard selfOffset .center 100 40 == 30
#guard selfOffset .end_ 100 40 == 60

end L4Factoidal.Rendering.Grid
