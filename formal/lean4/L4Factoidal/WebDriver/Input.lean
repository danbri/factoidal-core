/-
L4Factoidal.WebDriver.Input: what the engine needs to turn the low-level events of
`WebDriver.Actions` into DOM events, as pure functions of data the engine gives.

- `hitOf`, `pointerTarget`: the target of a pointer event is the element that captures
  the pointer, else the topmost element of the layout's hit test at the point: the same
  answer `document.elementFromPoint` gets (measure op 35 of the layout reads). There is
  one hit test in the engine; input does not have its own.
- `boundary`: the over, out, enter and leave events of a pointer that goes from one
  element to another (UI Events §5.3, Pointer Events 3 §4.2), as a list of event type,
  target and related target.
- `clickCount`: the `detail` of a press: 1, or one more than the press before when it
  follows within 500 ms at the same point with the same button.
- `clickType`: which event a release makes: `click` for the primary button, `auxclick`
  for another.
- `keypressChar`: the character of a `keypress` event of a key, if it has one.
- `pointerInit`, `wheelInit`, `keyInit`: the init of the events as JSON (the prelude
  reads it with `node_query` op 16).
- `resolvePath`: the node of a tree path from the document, the element reference of the
  WPT test driver (`path:` and child indices; `s` enters a shadow root).
- `afterCancelable`: a default action runs only when its event was not cancelled.
- `Trusted`: the state of trusted input a session holds (keys and buttons held, the
  time of the last user activation, the error of the last Perform Actions). A session
  keeps it outside the script realm's heap, so no script and no import reaches it
  (`Hosts.LeanJS.Session.run_trusted`).

Proved: `pointerTarget_free` and `pointerTarget_captured` (hit testing and capture),
`boundary_same` (no boundary event when the element does not change), `boundary_leave`
and `boundary_enter` (an element gets `leave` only if the pointer is no longer inside it,
`enter` only if it was not inside it before), `afterCancelable_cancelled` (no default
action after a cancelled event), `clickCount_pos`, `keypressChar_modified` (no `keypress`
with Control or Meta held).
-/
import L4Factoidal.WebDriver.Actions

namespace L4Factoidal.WebDriver.Input
open L4Factoidal.JSON
open L4Factoidal.WebDriver.Actions

/-! ## Hit testing and capture -/

/-- The topmost element of a hit test answer (measure op 35: node numbers separated by
spaces, topmost first; "" when no box holds the point). -/
def hitOf (answer : String) : Option Nat :=
  ((answer.splitOn " ").head?).bind String.toNat?

/-- The target of a pointer event: the element that captures the pointer, else what the
layout's hit test gives. -/
def pointerTarget (capture hit : Option Nat) : Option Nat :=
  match capture with
  | some c => some c
  | none => hit

/-! ## Boundary events -/

/-- One event of a plan: its type, its target, and its related target. -/
abbrev Planned := String × Nat × Option Nat

/-- The boundary events of a pointer that was over the element with chain `prev` (the
element first, then its ancestors) and is now over the element with chain `next`; `none`
is no element. `pfx` is "pointer" or "mouse". In order: `out` at the old element, `leave`
at the old element and each ancestor the pointer is no longer inside (inner first),
`over` at the new element, `enter` at each ancestor the pointer was not inside and at the
new element (outer first). -/
def boundary (pfx : String) (prev next : Option (List Nat)) : List Planned :=
  let p := prev.getD []
  let n := next.getD []
  if p.head? == n.head? then [] else
  let out : List Planned := match p.head? with
    | some o => [(pfx ++ "out", o, n.head?)]
    | none => []
  let leave : List Planned := (p.filter (!n.contains ·)).map fun a => (pfx ++ "leave", a, n.head?)
  let over : List Planned := match n.head? with
    | some o => [(pfx ++ "over", o, p.head?)]
    | none => []
  let enter : List Planned := ((n.filter (!p.contains ·)).reverse).map fun a => (pfx ++ "enter", a, p.head?)
  out ++ leave ++ over ++ enter

/-! ## Clicks -/

/-- The press before: when, where, which button, and its count. -/
structure LastPress where
  time : Nat
  x : Int
  y : Int
  button : Nat
  count : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The `detail` of a press at `now` (ms): one more than the press before when that was at
most 500 ms ago, at the same point, with the same button; else 1. -/
def clickCount (last : Option LastPress) (now : Nat) (x y : Int) (button : Nat) : Nat :=
  match last with
  | some l => if now - l.time ≤ 500 && l.x == x && l.y == y && l.button == button then l.count + 1 else 1
  | none => 1

/-- The event a release of `button` makes at the common ancestor of the press and the
release (UI Events §3.5): `click` for the primary button, `auxclick` for any other. -/
def clickType (button : Nat) : String := if button == 0 then "click" else "auxclick"

/-! ## Keys -/

/-- The character of the `keypress` event of a key (UI Events, legacy `keypress`): a key
whose value is one character, or Enter (U+000D); none while Control or Meta is held. -/
def keypressChar (key : String) (mods : Mods) : Option Nat :=
  if mods.ctrl || mods.cmd then none
  else if key == "Enter" then some 13
  else match key.toList with
    | [c] => some c.toNat
    | _ => none

/-- A default action after a cancelable event: nothing when a listener cancelled the
event, else the action. The engine passes every default action of a key, a press and a
release through this function (`Hosts.PageEvents`). -/
def afterCancelable {σ : Type} (cancelled : Bool) (default : σ → σ) (s : σ) : σ :=
  if cancelled then s else default s

/-! ## Event inits -/

private def num (i : Int) : Json := .number (toString i)
private def nat (n : Nat) : Json := .number (toString n)

def modFields (m : Mods) : List (String × Json) :=
  [("shiftKey", .bool m.shift), ("ctrlKey", .bool m.ctrl), ("altKey", .bool m.alt), ("metaKey", .bool m.cmd)]

/-- The init of a pointer or mouse event at a viewport point (the page does not scroll, so
page and client coordinates are the same). `pressure` is 0.5 while a button is held and 0
otherwise unless the action gave one (Pointer Events 3 §4.1.1). -/
def pointerInit (type : PointerType) (pointerId : Nat) (x y : Int) (button : Int) (buttons : Nat)
    (mods : Mods) (props : Props) (detail : Nat := 0) (related : Option Nat := none) : String :=
  let given := props.map fun (k, v) => (k, Json.number v)
  let pressure : List (String × Json) :=
    if props.any (·.1 == "pressure") then [] else [("pressure", .number (if buttons == 0 then "0" else "0.5"))]
  (Json.object ([("clientX", num x), ("clientY", num y), ("screenX", num x), ("screenY", num y),
      ("pageX", num x), ("pageY", num y), ("button", num button), ("buttons", nat buttons),
      ("pointerId", nat pointerId), ("pointerType", .string type.name), ("isPrimary", .bool true),
      ("detail", nat detail)] ++ modFields mods ++ given ++ pressure ++
      (match related with | some r => [("relatedNode", nat r)] | none => []))).toString

def wheelInit (x y dx dy : Int) (mods : Mods) : String :=
  (Json.object ([("clientX", num x), ("clientY", num y), ("screenX", num x), ("screenY", num y),
      ("pageX", num x), ("pageY", num y), ("button", num 0), ("buttons", nat 0),
      ("deltaX", num dx), ("deltaY", num dy), ("deltaZ", num 0), ("deltaMode", nat 0)] ++ modFields mods)).toString

/-- The init of a keyboard event; `char`: the character of a `keypress` (its `charCode`,
`keyCode` and `which`). -/
def keyInit (data : Keys.KeyData) (mods : Mods) (again : Bool) (char : Option Nat := none) : String :=
  let code := (char.getD data.keyCode)
  (Json.object ([("key", .string data.key), ("code", .string data.code), ("location", nat data.location),
      ("repeat", .bool again), ("keyCode", nat code), ("which", nat code),
      ("charCode", nat (char.getD 0))] ++ modFields mods)).toString

/-! ## Element references of the test driver -/

/-- The node of a tree path from document `doc`: steps separated by "/", a number is a
child index, "s" the shadow root of the element. "" is the document. `kids` and `shadow`
read the arena. -/
def resolvePath (kids : Nat → Array Nat) (shadow : Nat → Option Nat) (doc : Nat) (path : String) : Option Nat :=
  if path.isEmpty then some doc else
  (path.splitOn "/").foldl (init := some doc) fun cur step =>
    match cur with
    | none => none
    | some n =>
      if step == "s" then shadow n
      else match step.toNat? with
        | some i => (kids n)[i]?
        | none => none

/-- The numbers of a layout answer ("x y w h ...", measure op 17) rounded to whole CSS
pixels. -/
def boxOf (answer : String) : Option (Int × Int × Int × Int) :=
  match (answer.splitOn " ").map roundOf with
  | some x :: some y :: some w :: some h :: _ => some (x, y, w, h)
  | _ => none

/-! ## Trusted input state -/

/-- The trusted input state of a session. -/
structure Trusted where
  /-- The input state of WebDriver's actions. -/
  actions : Actions.State := {}
  /-- The time (the event loop's clock, ms) of the last input that gives user activation
  (HTML §6.4.1: a key down, a mouse press, a touch release). -/
  activated : Option Nat := none
  /-- The error of the last Perform Actions, for the turn's answer. -/
  error : Option Error := none
  deriving Inhabited

/-- The low-level events that give user activation (HTML §6.4.1 "activation triggering
input event"): a key down other than Escape, a press of a mouse or pen, a release of a
touch. -/
def activates : Low → Bool
  | .key true data _ _ => data.key != "Escape"
  | .pointer .down type _ _ _ _ _ _ _ => type != .touch
  | .pointer .up type _ _ _ _ _ _ _ => type == .touch
  | _ => false

/-! ## Theorems -/

/-- No capture. Says: with no element capturing the pointer, the target of a pointer
event is exactly the answer of the layout's hit test. Does not say: that the hit test is
right (it is the one `elementFromPoint` uses, `WebHit.target`). -/
theorem pointerTarget_free (hit : Option Nat) : pointerTarget none hit = hit := rfl

/-- Capture. Says: while an element captures the pointer, it is the target wherever the
pointer is. Does not say: when capture starts or ends. -/
theorem pointerTarget_captured (c : Nat) (hit : Option Nat) : pointerTarget (some c) hit = some c := rfl

/-- Same element. Says: a pointer that stays over the same element makes no boundary
event. Does not say: anything about `pointermove`. -/
theorem boundary_same (pfx : String) (c : Option (List Nat)) : boundary pfx c c = [] := by
  simp [boundary]

/-- Leave. Says: every `leave` event of a plan is at an element of the old chain that is
not in the new chain: an element the pointer is still inside never gets `leave`. Does not
say: the order of the events (inner first, by the definition). -/
theorem boundary_leave (pfx : String) (prev next : Option (List Nat)) (t : Nat) (r : Option Nat)
    (hpfx : pfx = "pointer" ∨ pfx = "mouse")
    (h : (pfx ++ "leave", t, r) ∈ boundary pfx prev next) :
    t ∈ prev.getD [] ∧ t ∉ next.getD [] := by
  simp only [boundary] at h
  split at h
  · simp at h
  · rcases hpfx with rfl | rfl <;>
    · simp only [List.mem_append, List.mem_map, List.mem_filter, Prod.mk.injEq] at h
      rcases h with ((h | h) | h) | h
      · cases hp : (prev.getD []).head? <;> simp [hp] at h
      · obtain ⟨a, ⟨ha, hn⟩, _, rfl, _⟩ := h
        exact ⟨ha, by simpa using hn⟩
      · cases hn : (next.getD []).head? <;> simp [hn] at h
      · obtain ⟨a, _, hbad, _, _⟩ := h
        exact absurd hbad (by decide)

/-- Enter. Says: every `enter` event of a plan is at an element of the new chain that is
not in the old chain: an element the pointer was already inside never gets `enter`. Does
not say: the order of the events (outer first, by the definition). -/
theorem boundary_enter (pfx : String) (prev next : Option (List Nat)) (t : Nat) (r : Option Nat)
    (hpfx : pfx = "pointer" ∨ pfx = "mouse")
    (h : (pfx ++ "enter", t, r) ∈ boundary pfx prev next) :
    t ∈ next.getD [] ∧ t ∉ prev.getD [] := by
  simp only [boundary] at h
  split at h
  · simp at h
  · rcases hpfx with rfl | rfl <;>
    · simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_reverse, Prod.mk.injEq] at h
      rcases h with ((h | h) | h) | h
      · cases hp : (prev.getD []).head? <;> simp [hp] at h
      · obtain ⟨a, _, hbad, _, _⟩ := h
        exact absurd hbad (by decide)
      · cases hn : (next.getD []).head? <;> simp [hn] at h
      · obtain ⟨a, ⟨ha, hn⟩, _, rfl, _⟩ := h
        exact ⟨ha, by simpa using hn⟩

/-- Cancelled. Says: after a cancelled event the default action does not run: the state
is the one the event's listeners left. Does not say: which actions the engine passes
through this function (every default action of `Hosts.PageEvents.key`, `lowPointer` and
`lowWheel`; read there). -/
theorem afterCancelable_cancelled {σ : Type} (default : σ → σ) (s : σ) :
    afterCancelable true default s = s := rfl

/-- Not cancelled. Says: when no listener cancelled the event the default action runs
once. Does not say: what the action is. -/
theorem afterCancelable_run {σ : Type} (default : σ → σ) (s : σ) :
    afterCancelable false default s = default s := rfl

/-- Count. Says: a press always counts at least 1. Does not say: an upper bound (a run of
fast presses counts on). -/
theorem clickCount_pos (last : Option LastPress) (now : Nat) (x y : Int) (button : Nat) :
    1 ≤ clickCount last now x y button := by
  unfold clickCount
  cases last with
  | none => simp
  | some l =>
    simp only
    split <;> omega

/-- Modified keys. Says: with Control or Meta held a key makes no `keypress` (and so no
text). Does not say: what the key does then (a format command in an editing host,
`DOM.Editing.keyCommand`). -/
theorem keypressChar_modified (key : String) (mods : Mods) (h : mods.ctrl = true ∨ mods.cmd = true) :
    keypressChar key mods = none := by
  rcases h with h | h <;> simp [keypressChar, h]

/-! ## Tests -/

#guard hitOf "12 7 3" == some 12 && hitOf "" == none && hitOf "5" == some 5
-- from a child (5, in 3, in 1) to its sibling (6, in 3, in 1): out, leave at 5 only, over, enter at 6 only
#guard boundary "mouse" (some [5, 3, 1]) (some [6, 3, 1]) ==
  [("mouseout", 5, some 6), ("mouseleave", 5, some 6), ("mouseover", 6, some 5), ("mouseenter", 6, some 5)]
-- from a parent into its child: no leave; enter at the child
#guard boundary "pointer" (some [3, 1]) (some [5, 3, 1]) ==
  [("pointerout", 3, some 5), ("pointerover", 5, some 3), ("pointerenter", 5, some 3)]
-- the first move of a pointer: enter from the root down
#guard boundary "pointer" none (some [5, 3, 1]) ==
  [("pointerover", 5, none), ("pointerenter", 1, none), ("pointerenter", 3, none), ("pointerenter", 5, none)]
-- a touch pointer is removed: out and leave, inner first
#guard boundary "pointer" (some [5, 3, 1]) none ==
  [("pointerout", 5, none), ("pointerleave", 5, none), ("pointerleave", 3, none), ("pointerleave", 1, none)]
#guard clickCount none 0 1 1 0 == 1
#guard clickCount (some { time := 100, x := 1, y := 1, button := 0, count := 1 }) 300 1 1 0 == 2
#guard clickCount (some { time := 100, x := 1, y := 1, button := 0, count := 1 }) 700 1 1 0 == 1
#guard clickCount (some { time := 100, x := 1, y := 1, button := 0, count := 1 }) 300 2 1 0 == 1
#guard keypressChar "a" {} == some 97 && keypressChar "Enter" {} == some 13 && keypressChar "Shift" {} == none
#guard keypressChar "a" { ctrl := true } == none
private def tree : Nat → Array Nat := fun n => if n == 0 then #[1] else if n == 1 then #[2, 3] else if n == 9 then #[10] else #[]
#guard resolvePath tree (fun n => if n == 3 then some 9 else none) 0 "0/1" == some 3
#guard resolvePath tree (fun n => if n == 3 then some 9 else none) 0 "0/1/s/0" == some 10
#guard resolvePath tree (fun _ => none) 0 "0/5" == none && resolvePath tree (fun _ => none) 0 "" == some 0
#guard boxOf "10 20.5 100 50 1 1 98 48" == some (10, 21, 100, 50)
#guard pointerInit .mouse 1 5 6 0 1 { shift := true } [] 1 ==
  "{\"clientX\":5,\"clientY\":6,\"screenX\":5,\"screenY\":6,\"pageX\":5,\"pageY\":6,\"button\":0,\"buttons\":1,\"pointerId\":1,\"pointerType\":\"mouse\",\"isPrimary\":true,\"detail\":1,\"shiftKey\":true,\"ctrlKey\":false,\"altKey\":false,\"metaKey\":false,\"pressure\":0.5}"
#guard keyInit (Keys.ofRaw 'a') {} false (some 97) ==
  "{\"key\":\"a\",\"code\":\"KeyA\",\"location\":0,\"repeat\":false,\"keyCode\":97,\"which\":97,\"charCode\":97,\"shiftKey\":false,\"ctrlKey\":false,\"altKey\":false,\"metaKey\":false}"
#guard activates (.key true (Keys.ofRaw 'a') {} false) && !activates (.key false (Keys.ofRaw 'a') {} false)
#guard activates (.pointer .down .mouse 1 0 0 0 1 {} []) && !activates (.pointer .down .touch 2 0 0 0 1 {} [])
#guard activates (.pointer .up .touch 2 0 0 0 0 {} []) && !activates (.pointer .move .mouse 1 0 0 (-1) 0 {} [])

end L4Factoidal.WebDriver.Input
