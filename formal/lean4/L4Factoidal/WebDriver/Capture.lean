/-
L4Factoidal.WebDriver.Capture: pointer capture (Pointer Events 3 §10).

`setPointerCapture` sets a pointer's pending capture target override, `releasePointerCapture`
clears it, and `hasPointerCapture` reads it. Before the next pointer event of that pointer
the override takes the pending value ("process pending pointer capture", §10.3): when it
changes, `lostpointercapture` is fired at the old element and `gotpointercapture` at the
new. While a pointer is captured its events are fired at the capture target, not at the
element under it. After `pointerup` or `pointercancel` the capture is released implicitly
(§10.4): the pending override is cleared and processed, so `lostpointercapture` follows.

A pointer is active while it can make events: the mouse always (pointer 1), any other pointer
from its press to its release. Capture needs the pointer in the active buttons state (§10.1:
otherwise `setPointerCapture` does nothing).

Proved: `set_has` (after a set the element has the capture), `release_has` (after a release
no element has it), `process_current` (processing makes the override the pending value),
`process_again` (processing twice fires nothing the second time), `implicit_none` (after the
implicit release the pointer is captured by nothing), `target_free` and `target_captured`.
Tested: `#guard`s below.
-/

namespace L4Factoidal.WebDriver.Capture

/-- Each pointer's pending capture target override and its capture target override. -/
structure State where
  pending : List (Nat × Nat) := []
  current : List (Nat × Nat) := []
  deriving DecidableEq, Repr, Inhabited

def lookup (xs : List (Nat × Nat)) (id : Nat) : Option Nat := (xs.find? (·.1 == id)).map (·.2)

def put (xs : List (Nat × Nat)) (id : Nat) (el : Option Nat) : List (Nat × Nat) :=
  let rest := xs.filter (·.1 != id)
  match el with
  | some e => (id, e) :: rest
  | none => rest

/-- `setPointerCapture(id)` on `el` (the checks that throw are the caller's). -/
def State.set (c : State) (id el : Nat) : State := { c with pending := put c.pending id (some el) }

/-- `releasePointerCapture(id)` on `el`: only the element that has the capture releases it. -/
def State.release (c : State) (id el : Nat) : State :=
  if lookup c.pending id == some el then { c with pending := put c.pending id none } else c

def State.has (c : State) (id el : Nat) : Bool := lookup c.pending id == some el

/-- Process pending pointer capture: the events to fire (type, target) and the new state. -/
def State.process (c : State) (id : Nat) : State × List (String × Nat) :=
  let old := lookup c.current id
  let new := lookup c.pending id
  if old == new then (c, []) else
  let lost := match old with
    | some o => [("lostpointercapture", o)]
    | none => []
  let got := match new with
    | some n => [("gotpointercapture", n)]
    | none => []
  ({ c with current := put c.current id new }, lost ++ got)

/-- Implicit release after `pointerup` or `pointercancel`. -/
def State.implicit (c : State) (id : Nat) : State × List (String × Nat) :=
  State.process { c with pending := put c.pending id none } id

/-- The target of a pointer's event: its capture target, else the element under it. -/
def State.target (c : State) (id hit : Nat) : Nat := (lookup c.current id).getD hit

/-! ## Theorems -/

theorem lookup_put_same (xs : List (Nat × Nat)) (id : Nat) (el : Option Nat) :
    lookup (put xs id el) id = el := by
  cases el with
  | none =>
    simp only [put, lookup]
    have : (List.filter (fun x => x.1 != id) xs).find? (fun x => x.1 == id) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at hx
      simp [hx.2]
    simp [this]
  | some e => simp [put, lookup]

theorem set_has (c : State) (id el : Nat) : (c.set id el).has id el = true := by
  simp [State.set, State.has, lookup_put_same]

theorem release_has (c : State) (id el : Nat) (h : c.has id el = true) :
    (c.release id el).has id el = false := by
  simp only [State.has] at h
  simp [State.release, State.has, h, lookup_put_same]

theorem process_current (c : State) (id : Nat) : lookup (c.process id).1.current id = lookup c.pending id := by
  by_cases h : lookup c.current id = lookup c.pending id
  · simp [State.process, h]
  · simp [State.process, h, lookup_put_same]

theorem process_same (c : State) (id : Nat) (h : lookup c.current id = lookup c.pending id) :
    (c.process id).2 = [] := by
  simp [State.process, h]

theorem process_pending (c : State) (id : Nat) : (c.process id).1.pending = c.pending := by
  by_cases h : lookup c.current id = lookup c.pending id <;> simp [State.process, h]

theorem process_again (c : State) (id : Nat) : ((c.process id).1.process id).2 = [] :=
  process_same _ _ (by rw [process_pending]; exact process_current c id)

theorem implicit_none (c : State) (id : Nat) : lookup (c.implicit id).1.current id = none := by
  simp [State.implicit, process_current, lookup_put_same]

theorem target_free (c : State) (id hit : Nat) (h : lookup c.current id = none) : c.target id hit = hit := by
  simp [State.target, h]

theorem target_captured (c : State) (id hit el : Nat) (h : lookup c.current id = some el) :
    c.target id hit = el := by
  simp [State.target, h]

/-! ## Tests (`pointerevents/pointerevent_setpointercapture_*`) -/

#guard ((({} : State).set 1 7).process 1).2 == [("gotpointercapture", 7)]
#guard (((({} : State).set 1 7).process 1).1.implicit 1).2 == [("lostpointercapture", 7)]
#guard (((({} : State).set 1 7).process 1).1.set 1 9 |>.process 1).2 == [("lostpointercapture", 7), ("gotpointercapture", 9)]
#guard ((({} : State).set 1 7).release 1 8).has 1 7
#guard !((({} : State).set 1 7).release 1 7).has 1 7

end L4Factoidal.WebDriver.Capture
