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

/-! ### Which physical side `start` is on (CSS Writing Modes 4 §6; CSS Box Alignment 3 §4)

`start` and `end` are sides of a writing mode: of the alignment container's for `start`,
`end` and the baselines, of the box's own for `self-start` and `self-end`. On a physical
axis (the horizontal one or the vertical one) a writing mode starts at the left or top,
or at the right or bottom (`startsAtEnd`). -/

/-- Whether the writing mode starts the physical axis at its right or bottom end.
`horizontalAxis`: the axis is the horizontal one. `vertical`: the writing mode is a
vertical one, so the vertical axis is its inline axis. `blockAtEnd`: its block axis
starts at the right (`vertical-rl`). `inlineAtEnd`: its inline axis starts at the right or
bottom (`direction: rtl`). -/
def startsAtEnd (horizontalAxis vertical blockAtEnd inlineAtEnd : Bool) : Bool :=
  if horizontalAxis != vertical then inlineAtEnd else vertical && blockAtEnd

/-- The placement on a physical axis of a placement by `start` and `end` in a writing
mode that starts the axis at its far end when `flip`. -/
def Place.physical (place : Place) (flip : Bool) : Place :=
  match place with
  | .start => if flip then .end_ else .start
  | .end_ => if flip then .start else .end_
  | other => other

/-- Says: a writing mode that starts an axis at the left or top changes nothing. -/
theorem Place.physical_same (place : Place) : place.physical false = place := by
  cases place <;> rfl

/-- Says: turning a placement round twice gives it back: `start` of a flipped mode is
`end` of the other, and the reverse. -/
theorem Place.physical_twice (place : Place) (flip : Bool) : (place.physical flip).physical flip = place := by
  cases place <;> cases flip <;> rfl

/-- Says: `stretch` and `center` do not depend on the writing mode. -/
theorem Place.physical_middle (flip : Bool) :
    Place.stretch.physical flip = .stretch ∧ Place.center.physical flip = .center := ⟨rfl, rfl⟩

/-- Says: in a horizontal writing mode the horizontal axis follows the direction and the
vertical axis starts at the top. -/
theorem startsAtEnd_horizontal (blockAtEnd inlineAtEnd : Bool) :
    startsAtEnd true false blockAtEnd inlineAtEnd = inlineAtEnd ∧
      startsAtEnd false false blockAtEnd inlineAtEnd = false := by
  cases blockAtEnd <;> cases inlineAtEnd <;> exact ⟨rfl, rfl⟩

/-- Says: in a vertical writing mode the vertical axis follows the direction and the
horizontal axis starts where the blocks start. -/
theorem startsAtEnd_vertical (blockAtEnd inlineAtEnd : Bool) :
    startsAtEnd false true blockAtEnd inlineAtEnd = inlineAtEnd ∧
      startsAtEnd true true blockAtEnd inlineAtEnd = blockAtEnd := by
  cases blockAtEnd <;> cases inlineAtEnd <;> exact ⟨rfl, rfl⟩

#guard Place.start.physical true == .end_
#guard Place.end_.physical true == .start
#guard startsAtEnd true false false true == true
#guard startsAtEnd true true true false == true
#guard startsAtEnd false true true false == false
#guard offset 100 20 false false .center == 40
#guard offset 100 20 false false .end_ == 80
#guard offset 100 20 false false .start == 0
#guard offset 100 20 true false .center == 80
#guard offset 100 20 false true .end_ == 0
#guard offset 100 120 false false .center == 0

end L4Factoidal.Rendering.SelfPlace
