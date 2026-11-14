/-
L4Factoidal.WebDriver.Touch: the touch points of a page (Touch Events, W3C Recommendation
2013 and Level 2 draft) as the touch pointers of the user drive them.

A touch pointer that goes down starts a touch point at the element under it: `touchstart`
is fired there. While it is down its moves are `touchmove` and its release `touchend`,
all at the element where it started, wherever it is now (the touch point's target does
not change, §5.2). Every touch event carries three lists: `touches` (every touch point
now on the surface), `targetTouches` (those that started on the event's target) and
`changedTouches` (the touch points this event is about). A released or cancelled touch
point is in `changedTouches` only.

This module keeps the touch points and decides the lists and the event init; the
dispatch is `Hosts.PageEvents.lowPointer`, for a pointer of type `touch` only.

Proved: `start_mem` and `start_unique` (a started touch is on the surface once),
`finish_removes` (after `touchend` or `touchcancel` a touch is no longer on the surface),
`move_target` (a move keeps the touch's target), `targetTouches_sub` (`targetTouches`
is part of `touches`).
Tested: `#guard`s below.
-/
import L4Factoidal.WebDriver.Actions

namespace L4Factoidal.WebDriver.Touch
open L4Factoidal.JSON
open L4Factoidal.WebDriver.Actions

/-- A touch point: its identifier (the pointer's id), the element it started on, where it
is in the viewport (CSS pixels). -/
structure Point where
  id : Nat
  target : Nat
  x : Int
  y : Int
  deriving DecidableEq, Repr, Inhabited

/-- The touch points on the surface, in the order they started. -/
structure Surface where
  points : List Point := []
  deriving DecidableEq, Repr, Inhabited

def Surface.find? (s : Surface) (id : Nat) : Option Point := s.points.find? (·.id == id)

/-- A touch starts: the point joins the surface (a point of the same id is replaced). -/
def Surface.start (s : Surface) (p : Point) : Surface := { points := s.points.filter (·.id != p.id) ++ [p] }

/-- A touch moves: its point moves and keeps its target; `none` when no such touch is down. -/
def Surface.move (s : Surface) (id : Nat) (x y : Int) : Option (Surface × Point) :=
  match s.find? id with
  | some p =>
    let q := { p with x, y }
    some ({ points := s.points.map fun r => if r.id == id then q else r }, q)
  | none => none

/-- A touch ends or is cancelled: its point (at the release position) leaves the surface. -/
def Surface.finish (s : Surface) (id : Nat) (x y : Int) : Option (Surface × Point) :=
  match s.find? id with
  | some p => some ({ points := s.points.filter (·.id != id) }, { p with x, y })
  | none => none

private def num (i : Int) : Json := .number (toString i)
private def nat (n : Nat) : Json := .number (toString n)

/-- A touch point as the page's glue reads it: `node` is its target. -/
def Point.toJson (p : Point) : Json :=
  .object [("identifier", nat p.id), ("node", nat p.target), ("clientX", num p.x), ("clientY", num p.y),
    ("screenX", num p.x), ("screenY", num p.y), ("pageX", num p.x), ("pageY", num p.y),
    ("radiusX", nat 1), ("radiusY", nat 1), ("rotationAngle", nat 0), ("force", .number "1")]

/-- The touch points that started on `target`. -/
def Surface.targetTouches (s : Surface) (target : Nat) : List Point := s.points.filter (·.target == target)

/-- The init of a touch event at `target` about `changed`, after the surface became `s`. -/
def init (s : Surface) (target : Nat) (changed : Point) (mods : Mods) : String :=
  (Json.object [("touches", .array (s.points.map Point.toJson)),
    ("targetTouches", .array ((s.targetTouches target).map Point.toJson)),
    ("changedTouches", .array [changed.toJson]),
    ("ctrlKey", .bool mods.ctrl), ("shiftKey", .bool mods.shift), ("altKey", .bool mods.alt),
    ("metaKey", .bool mods.cmd)]).toString

/-! ## Theorems -/

/-- Started. Says: a touch that starts is on the surface. -/
theorem start_mem (s : Surface) (p : Point) : p ∈ (s.start p).points := by
  simp [Surface.start]

/-- Once. Says: after a start there is exactly one point with its identifier. -/
theorem start_unique (s : Surface) (p : Point) :
    ((s.start p).points.filter (·.id == p.id)).length = 1 := by
  simp [Surface.start, List.filter_append, List.filter_filter]

/-- Ended. Says: after `touchend` or `touchcancel` no point with that identifier is on the
surface, so no later event lists it. -/
theorem finish_removes (s s' : Surface) (id : Nat) (x y : Int) (q : Point)
    (h : s.finish id x y = some (s', q)) : ∀ r ∈ s'.points, r.id ≠ id := by
  unfold Surface.finish at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro r hr
    simp only [List.mem_filter, bne_iff_ne, ne_eq] at hr
    exact hr.2
  · cases h

/-- The target stays. Says: a moved touch keeps the target it started on. -/
theorem move_target (s s' : Surface) (id : Nat) (x y : Int) (q : Point)
    (h : s.move id x y = some (s', q)) : ∃ p, s.find? id = some p ∧ q.target = p.target := by
  unfold Surface.move at h
  split at h
  · rename_i p hp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨p, hp, by rw [← h.2]⟩
  · cases h

/-- Sublist. Says: every point of `targetTouches` is a point of `touches`. -/
theorem targetTouches_sub (s : Surface) (target : Nat) : ∀ p ∈ s.targetTouches target, p ∈ s.points := by
  intro p hp
  simp only [Surface.targetTouches, List.mem_filter] at hp
  exact hp.1

/-! ## Tests (the two-finger sequence of `touch-events/multi-touch-interfaces.html`) -/

private def a : Point := { id := 2, target := 10, x := 5, y := 5 }
private def b : Point := { id := 3, target := 10, x := 8, y := 5 }
#guard ((Surface.start {} a).start b).points.length == 2
#guard (((Surface.start {} a).start b).move 2 5 60).map (·.2.target) == some 10
#guard (((Surface.start {} a).start b).finish 2 5 60).map (·.1.points.length) == some 1
#guard ((Surface.start {} a).move 7 0 0).isNone
#guard ((Surface.start {} a).start b).targetTouches 11 == []

end L4Factoidal.WebDriver.Touch
