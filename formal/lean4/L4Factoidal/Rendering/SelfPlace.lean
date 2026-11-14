/-! Where an absolutely positioned box sits in its inset-modified containing block (CSS
Positioned Layout 3 §4.2 and §4.3, CSS Box Alignment 3 §6.1.2 and §6.2.2), on one axis and
in layout units. This module has no import from the engine. -/
namespace L4Factoidal.Rendering.SelfPlace

/-- Self-alignment on one axis, as the placement reads it: `stretch` (also `normal` and
`auto`: a box with an automatic size fills the room), or the box keeps its own size and
goes to the start, the centre or the end. -/
inductive Place where
  | stretch | start | center | end_
  deriving Repr, BEq, DecidableEq

/-- The offset of the box's margin edge from the start of the room, for a box whose outer
size is `outer` in a room of `room`. Free space goes to the auto margins first (to both
in halves, or all of it to the one), and with none by the alignment. With no free space
the box is at the start, whatever the alignment: it overflows the end, not the start. -/
def offset (room outer : Int) (autoStart autoEnd : Bool) (place : Place) : Int :=
  let free := room - outer
  if free ≤ 0 then 0
  else if autoStart && autoEnd then free / 2
  else if autoStart then free
  else if autoEnd then 0
  else match place with
    | .center => free / 2
    | .end_ => free
    | _ => 0

/-- Containment. Says: the box is never placed before the start of the room, and a box
that fits ends inside it. -/
theorem offset_within (room outer : Int) (autoStart autoEnd : Bool) (place : Place) :
    0 ≤ offset room outer autoStart autoEnd place ∧
    (outer ≤ room → offset room outer autoStart autoEnd place + outer ≤ room) := by
  unfold offset
  simp only
  split
  · omega
  · rename_i h
    have hf : 0 < room - outer := by omega
    have h2 := Int.ediv_nonneg (Int.le_of_lt hf) (by omega : (0 : Int) ≤ 2)
    have h3 := Int.ediv_le_self 2 (Int.le_of_lt hf)
    split
    · omega
    · split
      · omega
      · split
        · omega
        · cases place <;> simp only <;> omega

/-- Says: a box as large as the room, or larger, is at the start. -/
theorem offset_full (room outer : Int) (autoStart autoEnd : Bool) (place : Place) (h : room ≤ outer) :
    offset room outer autoStart autoEnd place = 0 := by
  unfold offset
  simp only
  have : room - outer ≤ 0 := by omega
  simp [this]

/-- Says: two auto margins centre the box whatever its alignment. -/
theorem offset_auto_both (room outer : Int) (place : Place) (h : outer < room) :
    offset room outer true true place = (room - outer) / 2 := by
  unfold offset
  simp only
  have : ¬ (room - outer ≤ 0) := by omega
  simp [this]

#guard offset 100 20 false false .center == 40
#guard offset 100 20 false false .end_ == 80
#guard offset 100 20 false false .start == 0
#guard offset 100 20 true false .center == 80
#guard offset 100 20 false true .end_ == 0
#guard offset 100 120 false false .center == 0

end L4Factoidal.Rendering.SelfPlace
