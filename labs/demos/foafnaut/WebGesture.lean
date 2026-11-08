import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize

/-! Back and forward gestures. Lean is the only implementation: the hosts send what the
finger or the trackpad did and do what the answer says. An engine without the op `gesture` has no swipe gestures.

Two conventions, both in CSS pixels:

* **Touch edge swipe** (iOS `UINavigationController`, Android gesture navigation). One
  finger that starts within `edgeZone` (20 px) of the left edge and goes right, mostly
  across (`along > 2·|dy|`), is back; from the right edge going left, forward. It goes
  back on release when it travelled `commitPercent` (30 %) of the width and is not
  thrown back faster than `flingSpeed` (500 px/s), or when it is thrown on at
  `flingSpeed` or faster after more than the tap slop. Until the finger has gone
  `tapSlop` (10 px) it may still be a tap; a touch that starts anywhere else, a mostly
  vertical drag, two fingers (a pinch) are not gestures.
* **Trackpad horizontal swipe** (macOS two-finger "swipe between pages"). The horizontal
  wheel deltas of one trackpad gesture, added up in the DOM sign (`deltaX > 0` scrolls
  right, the content moves left), mostly across as above: content moving right is back,
  content moving left is forward, when the gesture ends past `wheelCommit` (140 px).
  Firefox on macOS draws its arrow over about the same distance.

* **Long press** (iOS `UILongPressGestureRecognizer`, Android `onLongPress`). A finger or
  a button held for `holdMs` (500 ms) within the tap slop of where it went down, and not
  lifted, is a long press. The host asks once when the time has passed; Lean says `hold`,
  or `other` if the finger moved off or lifted. A tap (lifted, or held for less) is never
  a long press, nor is a touch that moved past the tap slop.

While a swipe is under way, `hint` (−100 .. 100 in steps of 10, negative for back) is the
value the hosts put in the shell (`WebShell.Shell.swipe`): WebShell draws the arrow, the
host draws nothing. Steps of 10 bound the frames one swipe asks for to about twenty.

Theorems at the end, for every input: a touch that starts away from both edges, a mostly
vertical movement (a scroll or a fling), a tap, and two fingers never navigate; a wheel
gesture that is mostly vertical never navigates; and back and forward are mirror images
(the touch and the wheel mirrored about the vertical axis give the mirrored answer). -/
namespace WebGesture
open L4Factoidal

/-! ### Thresholds, CSS pixels and milliseconds -/

/-- How near the left or right edge a touch must start (iOS: about 20 pt). -/
def edgeZone : Int := 20
/-- A finger that has moved less than this is still a tap (as the Hub's tap slop). -/
def tapSlop : Int := 10
/-- A swipe that has gone this share of the width goes back on release (percent). -/
def commitPercent : Int := 30
/-- A release this fast in the swipe direction goes back at any distance past the tap slop;
this fast the other way cancels (CSS px per second). -/
def flingSpeed : Int := 500
/-- A trackpad swipe goes back past this much horizontal content movement. -/
def wheelCommit : Int := 140
/-- Movement across must be more than this times the movement down. -/
def dominance : Int := 2
/-- A press held this long without moving is a long press (iOS and Android: 500 ms). -/
def holdMs : Int := 500

inductive Direction where
  | back
  | forward
  deriving Repr, BEq, DecidableEq

def Direction.mirror : Direction → Direction
  | .back => .forward
  | .forward => .back

def Direction.name : Direction → String
  | .back => "back"
  | .forward => "forward"

/-- What the host does with the input now. -/
inductive Phase where
  /-- Within the tap slop at an edge: it may be a tap or a swipe; the host waits. -/
  | pending
  /-- A back or forward swipe: the host neither scrolls nor clicks for it. -/
  | swipe
  /-- Not a navigation gesture: scrolling, tapping and pinching go on as usual. -/
  | other
  deriving Repr, BEq, DecidableEq

def Phase.name : Phase → String
  | .pending => "pending"
  | .swipe => "swipe"
  | .other => "other"

structure Decision where
  phase : Phase
  direction : Option Direction := none
  /-- How far towards going back or forward, 0 .. 100. -/
  progress : Nat := 0
  /-- Go back or forward now (only at the end of the gesture). -/
  navigate : Bool := false
  deriving Repr, BEq, DecidableEq

def Decision.mirror (d : Decision) : Decision := {d with direction := d.direction.map Direction.mirror}

/-- The other answer. -/
def other : Decision := {phase := .other}

/-- Movement in the direction's sense: rightwards for back, leftwards for forward. -/
def along : Direction → Int → Int
  | .back, d => d
  | .forward, d => -d

/-- `distance` of `goal` in percent, 0 .. 100. -/
def progressOf (distance goal : Int) : Nat :=
  if goal ≤ 0 then 100 else (min 100 (distance * 100 / goal)).toNat

/-- Mostly across: `a > dominance·|dy|`. -/
def across (a dy : Int) : Prop := a > dominance * dy ∧ a > -(dominance * dy)
instance (a dy : Int) : Decidable (across a dy) := by unfold across; infer_instance

/-! ### Touch -/

structure Touch where
  /-- The width of the window, CSS px. -/
  width : Int
  startX : Int
  startY : Int
  x : Int
  y : Int
  /-- The velocity across at the lift, CSS px per second, positive rightwards. -/
  vx : Int := 0
  fingers : Nat := 1
  ended : Bool := false
  deriving Repr, BEq

def Touch.dx (t : Touch) : Int := t.x - t.startX
def Touch.dy (t : Touch) : Int := t.y - t.startY

/-- The touch seen in a mirror about the window's vertical axis. -/
def Touch.mirror (t : Touch) : Touch :=
  {t with startX := t.width - t.startX, x := t.width - t.x, vx := -t.vx}

/-- The edge a touch starts at: the left one is back, the right one forward. A window so
narrow that a touch is near both has no edge swipe. -/
def side (t : Touch) : Option Direction :=
  if t.startX < edgeZone then (if t.width - t.startX < edgeZone then none else some .back)
  else if t.width - t.startX < edgeZone then some .forward else none

/-- A one-finger touch from the edge of `d`: `a` the movement across in its sense, `v` the
release velocity in its sense, `dy` the movement down. -/
def fromEdge (d : Direction) (a v dy width : Int) (ended : Bool) : Decision :=
  if a < tapSlop ∧ -a < tapSlop ∧ dy < tapSlop ∧ -dy < tapSlop then {phase := .pending, direction := some d}
  else if across a dy then
    let far := a * 100 ≥ width * commitPercent ∧ v > -flingSpeed
    let thrown := v ≥ flingSpeed
    let goes := decide (a ≥ tapSlop ∧ (far ∨ thrown))
    {phase := .swipe, direction := some d, progress := progressOf a (width * commitPercent / 100),
     navigate := ended && goes}
  else other

/-- What a touch means (Hub, and any host with a touch screen). -/
def touch (t : Touch) : Decision :=
  if t.fingers ≠ 1 then other else
  match side t with
  | none => other
  | some d => fromEdge d (along d t.dx) (along d t.vx) t.dy t.width t.ended

/-! ### Trackpad -/

structure Wheel where
  /-- Horizontal and vertical wheel deltas of one gesture added up, CSS px, DOM sign. -/
  dx : Int
  dy : Int
  ended : Bool := false
  deriving Repr, BEq

def Wheel.mirror (w : Wheel) : Wheel := {w with dx := -w.dx}

/-- A horizontal trackpad gesture whose content moved `a` in the sense of `d`. -/
def sideways (d : Direction) (a dy : Int) (ended : Bool) : Decision :=
  if across a dy then
    if a < tapSlop then {phase := .pending, direction := some d}
    else {phase := .swipe, direction := some d, progress := progressOf a wheelCommit,
          navigate := ended && decide (a ≥ wheelCommit)}
  else other

/-- What a trackpad gesture means (the native window; the Hub, whose page keeps wheel
events from the host browser). Content moving right (`dx < 0`) is back. -/
def wheel (w : Wheel) : Decision :=
  if w.dx < 0 then sideways .back (along .back (-w.dx)) w.dy w.ended
  else if w.dx > 0 then sideways .forward (along .forward (-w.dx)) w.dy w.ended
  else other

/-! ### Long press -/

structure Hold where
  startX : Int
  startY : Int
  /-- Where the finger or pointer is now. -/
  x : Int
  y : Int
  /-- Milliseconds since it went down. -/
  elapsed : Int
  /-- It has been lifted (the press ended). -/
  lifted : Bool := false
  deriving Repr, BEq

/-- Within the tap slop of the start: the distance is under `tapSlop`, as the Hub measures
a tap (`Math.hypot`), in integers. -/
def Hold.still (h : Hold) : Bool :=
  decide ((h.x-h.startX)*(h.x-h.startX)+(h.y-h.startY)*(h.y-h.startY) < tapSlop*tapSlop)

/-- What a press held so far means: `pending`, it may still become a long press; `hold`, it
is one; `other`, it is a tap, a drag, or over. -/
inductive HoldPhase where
  | pending
  | hold
  | other
  deriving Repr, BEq, DecidableEq

def HoldPhase.name : HoldPhase → String
  | .pending => "pending"
  | .hold => "hold"
  | .other => "other"

def hold (h : Hold) : HoldPhase :=
  if h.lifted || !h.still then .other
  else if h.elapsed ≥ holdMs then .hold
  else .pending

/-- A tap never becomes a long press: a press held less than `holdMs` is not one, whatever
else is true of it. -/
theorem tap_never_holds (h : Hold) (short : h.elapsed < holdMs) : hold h ≠ .hold := by
  unfold hold
  split
  · simp
  · split
    · omega
    · simp

/-- A lifted press is not a long press: the host asks while the finger is down. -/
theorem lifted_never_holds (h : Hold) (up : h.lifted = true) : hold h = .other := by
  simp [hold, up]

/-- A touch that moved past the tap slop (a scroll, a drag, a swipe) is not a long press. -/
theorem moved_never_holds (h : Hold) (moved : h.still = false) : hold h = .other := by
  simp [hold, moved]

/-- A long press is still, down and at least `holdMs` old. -/
theorem hold_iff (h : Hold) : hold h = .hold ↔ h.lifted = false ∧ h.still = true ∧ h.elapsed ≥ holdMs := by
  unfold hold
  cases hl : h.lifted <;> cases hs : h.still <;> simp

/-! ### The shell's hint and the op -/

/-- The value of `WebShell.Shell.swipe`: −100 .. 100 in steps of 10, negative for back. -/
def hint (d : Decision) : Int :=
  if d.phase != .swipe then 0 else
  let step := Int.ofNat (d.progress / 10 * 10)
  match d.direction with
  | some .back => -step
  | some .forward => step
  | none => 0

private def int (j : JSON.Json) (key : String) : Int :=
  match j.field? key with
  | some (.number value) => match value.toInt? with
    | some n => n
    -- A host may send 12.5: the whole part.
    | none => ((value.splitOn ".").headD "").toInt?.getD 0
  | _ => 0
private def flag (j : JSON.Json) (key : String) : Bool :=
  match j.field? key with | some (.bool value) => value | _ => false

private def number (n : Int) : JSON.Json := .number (toString n)

def Decision.json (d : Decision) : JSON.Json :=
  .object [("phase",.string d.phase.name),
    ("direction",match d.direction with | some x => .string x.name | none => .null),
    ("progress",number d.progress),("navigate",.bool d.navigate),("hint",number (hint d))]

/-- The thresholds, for a host that asks first whether this engine has the op. -/
def info : JSON.Json :=
  .object [("actions",.array [.string "touch",.string "wheel",.string "hold"]),("edgeZone",number edgeZone),("holdMs",number holdMs),
    ("tapSlop",number tapSlop),("commitPercent",number commitPercent),("flingSpeed",number flingSpeed),
    ("wheelCommit",number wheelCommit),("dominance",number dominance)]

/-- The op `gesture`. `action` "info" gives the thresholds; "touch" takes `width`,
`startX`, `startY`, `x`, `y`, `vx`, `fingers`, `ended`; "wheel" takes `dx`, `dy`, `ended`;
"hold" takes `startX`, `startY`, `x`, `y`, `elapsed`, `lifted` and answers `phase`. -/
def op (name : String) (request : JSON.Json) : Except String (Option String) := do
  if name != "gesture" then return none
  match request.field? "action" with
  | some (.string "info") => return some info.toString
  | some (.string "touch") =>
    let fingers := match request.field? "fingers" with
      | some (.number n) => n.toNat?.getD 1 | _ => 1
    let t : Touch := {
      width := int request "width"
      startX := int request "startX"
      startY := int request "startY"
      x := int request "x"
      y := int request "y"
      vx := int request "vx"
      fingers := fingers
      ended := flag request "ended" }
    return some (touch t).json.toString
  | some (.string "wheel") =>
    let w : Wheel := {dx := int request "dx", dy := int request "dy", ended := flag request "ended"}
    return some (wheel w).json.toString
  | some (.string "hold") =>
    let h : Hold := {
      startX := int request "startX"
      startY := int request "startY"
      x := int request "x"
      y := int request "y"
      elapsed := int request "elapsed"
      lifted := flag request "lifted" }
    return some (JSON.Json.object [("phase",.string (hold h).name)]).toString
  | _ => throw "gesture: action must be info, touch, wheel or hold"

/-! ### Theorems -/

theorem fromEdge_navigates {d : Direction} {a v dy w : Int} {e : Bool}
    (h : (fromEdge d a v dy w e).navigate = true) : a ≥ tapSlop ∧ across a dy := by
  unfold fromEdge at h
  split at h
  · simp at h
  · split at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.2.1, by assumption⟩
    · simp [other] at h

/-- A touch that starts away from both edges never navigates (and is never a swipe). -/
theorem away_from_edges_never_navigates (t : Touch)
    (left : edgeZone ≤ t.startX) (right : edgeZone ≤ t.width - t.startX) :
    touch t = other := by
  unfold touch side
  split
  · rfl
  · have h1 : ¬ t.startX < edgeZone := by omega
    have h2 : ¬ t.width - t.startX < edgeZone := by omega
    simp [h1, h2]

/-- A mostly vertical movement (`|dx| ≤ |dy|`: a scroll, or a fling) never navigates, whatever
its velocity. -/
theorem vertical_never_navigates (t : Touch) (h : t.dx.natAbs ≤ t.dy.natAbs) :
    (touch t).navigate = false := by
  unfold touch
  split
  · rfl
  · split
    · rfl
    · rename_i d _
      cases hn : (fromEdge d (along d t.dx) (along d t.vx) t.dy t.width t.ended).navigate
      · rfl
      · have ⟨_, a⟩ := fromEdge_navigates hn
        unfold across dominance at a
        cases d <;> simp only [along] at a <;> omega

/-- A tap (the finger moved across less than the tap slop of 10 px) never navigates. -/
theorem tap_never_navigates (t : Touch) (h : t.dx.natAbs < 10) :
    (touch t).navigate = false := by
  unfold touch
  split
  · rfl
  · split
    · rfl
    · rename_i d _
      cases hn : (fromEdge d (along d t.dx) (along d t.vx) t.dy t.width t.ended).navigate
      · rfl
      · have ⟨s, _⟩ := fromEdge_navigates hn
        unfold tapSlop at s
        cases d <;> simp only [along] at s <;> omega

/-- Two fingers (a pinch) or none never navigate. -/
theorem pinch_never_navigates (t : Touch) (h : t.fingers ≠ 1) : touch t = other := by
  simp [touch, h]

theorem side_mirror (t : Touch) : side t.mirror = (side t).map Direction.mirror := by
  unfold side Touch.mirror
  simp only
  have e : t.width - (t.width - t.startX) = t.startX := by omega
  rw [e]
  by_cases a : t.startX < edgeZone <;> by_cases b : t.width - t.startX < edgeZone <;>
    simp [a, b, Direction.mirror]

theorem fromEdge_mirror (d : Direction) (a v dy w : Int) (e : Bool) :
    fromEdge d.mirror a v dy w e = (fromEdge d a v dy w e).mirror := by
  unfold fromEdge
  split <;> (try split) <;> simp [Decision.mirror, other]

/-- Back and forward are mirror images: the touch mirrored about the vertical axis gets the
same answer with back and forward swapped. -/
theorem touch_mirror (t : Touch) : touch t.mirror = (touch t).mirror := by
  unfold touch
  have f : t.mirror.fingers = t.fingers := rfl
  rw [f, side_mirror]
  by_cases h : t.fingers ≠ 1
  · simp [h, Decision.mirror, other]
  · simp only [h, if_false]
    cases s : side t with
    | none => simp [Decision.mirror, other]
    | some d =>
      simp only [Option.map]
      have dx : along d.mirror t.mirror.dx = along d t.dx := by
        cases d <;> simp [along, Direction.mirror, Touch.mirror, Touch.dx] <;> omega
      have vx : along d.mirror t.mirror.vx = along d t.vx := by
        cases d <;> simp [along, Direction.mirror, Touch.mirror]
      have dy : t.mirror.dy = t.dy := rfl
      have w : t.mirror.width = t.width := rfl
      have e : t.mirror.ended = t.ended := rfl
      rw [dx, vx, dy, w, e, fromEdge_mirror]

theorem sideways_navigates {d : Direction} {a dy : Int} {e : Bool}
    (h : (sideways d a dy e).navigate = true) : a ≥ wheelCommit ∧ across a dy := by
  unfold sideways at h
  split at h
  · split at h
    · simp at h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.2, by assumption⟩
  · simp [other] at h

/-- The content movement of a wheel gesture in the sense of its direction. -/
theorem wheel_navigates (w : Wheel) (h : (wheel w).navigate = true) :
    w.dx.natAbs ≥ wheelCommit.toNat ∧ w.dx.natAbs > 2 * w.dy.natAbs := by
  unfold wheel at h
  split at h
  · have ⟨c, a⟩ := sideways_navigates h
    unfold across dominance at a; unfold wheelCommit at c ⊢; simp only [along] at a c; omega
  · split at h
    · have ⟨c, a⟩ := sideways_navigates h
      unfold across dominance at a; unfold wheelCommit at c ⊢; simp only [along] at a c; omega
    · simp [other] at h

/-- A wheel gesture that is mostly vertical never navigates. -/
theorem wheel_vertical_never_navigates (w : Wheel) (h : w.dx.natAbs ≤ w.dy.natAbs) :
    (wheel w).navigate = false := by
  cases hn : (wheel w).navigate
  · rfl
  · have := wheel_navigates w hn; omega

/-- A wheel gesture under the tap slop never navigates. -/
theorem wheel_small_never_navigates (w : Wheel) (h : w.dx.natAbs < 10) :
    (wheel w).navigate = false := by
  cases hn : (wheel w).navigate
  · rfl
  · have := wheel_navigates w hn; unfold wheelCommit at this; omega

theorem sideways_mirror (d : Direction) (a dy : Int) (e : Bool) :
    sideways d.mirror a dy e = (sideways d a dy e).mirror := by
  unfold sideways
  split <;> (try split) <;> simp [Decision.mirror, other]

/-- Back and forward are mirror images for the trackpad too. -/
theorem wheel_mirror (w : Wheel) : wheel w.mirror = (wheel w).mirror := by
  unfold wheel Wheel.mirror
  simp only
  by_cases a : w.dx < 0
  · have b : ¬ -w.dx < 0 := by omega
    have c : -w.dx > 0 := by omega
    simp only [a, b, c, if_true, if_false]
    have := sideways_mirror .back (along .back (-w.dx)) w.dy w.ended
    simp only [Direction.mirror, along] at this ⊢
    rw [← this]; congr 1; omega
  · by_cases z : w.dx > 0
    · have b : -w.dx < 0 := by omega
      simp only [a, z, b, if_true, if_false]
      have := sideways_mirror .forward (along .forward (-w.dx)) w.dy w.ended
      simp only [Direction.mirror, along] at this ⊢
      rw [← this]
    · have b : ¬ -w.dx < 0 := by omega
      have c : ¬ -w.dx > 0 := by omega
      simp [a, z, Decision.mirror, other]

/-! ### Cases -/

private def at_ (startX x : Int) (y : Int := 300) (ended := true) (vx : Int := 0) : Touch :=
  {width := 400, startX, startY := 300, x, y, vx, ended}
-- From the left edge past 30 % of 400 px: back.
#guard (touch (at_ 5 140)) == {phase := .swipe, direction := some .back, progress := 100, navigate := true}
-- Not as far, slow: no.
#guard (touch (at_ 5 80)).navigate == false && (touch (at_ 5 80)).phase == .swipe
-- Not as far, thrown on: yes; thrown back: no.
#guard (touch (at_ 5 80 (vx := 900))).navigate && !(touch (at_ 5 140 (vx := -900))).navigate
-- From the right edge going left: forward.
#guard (touch (at_ 395 260)).direction == some .forward && (touch (at_ 395 260)).navigate
-- Away from the edges; vertical; a tap; two fingers.
#guard (touch (at_ 100 300)).navigate == false && (touch (at_ 100 300)).phase == .other
#guard (touch (at_ 5 60 (y := 500))).phase == .other
#guard (touch (at_ 5 12 (y := 305) (ended := false))).phase == .pending
#guard (touch {at_ 5 200 with fingers := 2}).navigate == false
-- The hint while moving: back at 60 %.
#guard hint (touch (at_ 5 77 (ended := false))) == -60
#guard hint (touch (at_ 395 323 (ended := false))) == 60
-- A trackpad: content right (dx < 0) past 140 px is back; left is forward; vertical is nothing.
#guard (wheel {dx := -150, dy := 20, ended := true}) == {phase := .swipe, direction := some .back, progress := 100, navigate := true}
#guard (wheel {dx := 150, dy := 0, ended := true}).direction == some .forward
#guard (wheel {dx := -150, dy := 100, ended := true}).phase == .other
#guard (wheel {dx := -100, dy := 0, ended := true}).navigate == false && hint (wheel {dx := -100, dy := 0}) == -70
-- A long press: held 500 ms within 10 px; sooner, moved, or lifted is not one.
#guard hold {startX := 100, startY := 40, x := 106, y := 46, elapsed := 520} == .hold
#guard hold {startX := 100, startY := 40, x := 108, y := 46, elapsed := 520} == .other
#guard hold {startX := 100, startY := 40, x := 100, y := 40, elapsed := 300} == .pending
#guard hold {startX := 100, startY := 40, x := 100, y := 40, elapsed := 900, lifted := true} == .other

end WebGesture
