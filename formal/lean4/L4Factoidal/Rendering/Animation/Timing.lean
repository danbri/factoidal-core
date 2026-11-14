/-
L4Factoidal.Rendering.Animation.Timing: the timing of an animation effect (Web
Animations 1 §4.6 to §4.10): from a local time and the effect's timing properties, the
phase, the active time, the overall and simple iteration progress, the current
iteration, the directed progress and the transformed progress.

Times are `Animation.Fix` numbers of milliseconds; a count or a duration may be infinite
(`Ext`). Each definition names its section; the arithmetic is exact, so the ranges the
specification states are theorems: the simple iteration progress and the directed
progress are in [0, 1] (`simple_range`, `directed_range`), an effect with no local time
has no progress (`at_idle`), and an effect in its before phase with fill `none` or
`forwards` has none (`before_no_fill`).
-/
import L4Factoidal.Rendering.Animation.Easing

namespace L4Factoidal.Rendering.Animation
open Fix (one scale)

inductive Fill where
  | none | forwards | backwards | both | auto
  deriving DecidableEq, Repr, Inhabited

inductive Direction where
  | normal | reverse | alternate | alternateReverse
  deriving DecidableEq, Repr, Inhabited

/-- A number that may be positive infinity. -/
inductive Ext where
  | fin (x : Int)
  | inf
  deriving DecidableEq, Repr, Inhabited

namespace Ext
def add : Ext → Int → Ext
  | .fin x, y => .fin (x + y)
  | .inf, _ => .inf
def minInt (x : Int) : Ext → Int
  | .fin y => min x y
  | .inf => x
def min : Ext → Ext → Ext
  | .fin x, .fin y => .fin (Min.min x y)
  | .fin x, .inf => .fin x
  | .inf, e => e
def maxInt (x : Int) : Ext → Ext
  | .fin y => .fin (max x y)
  | .inf => .inf
/-- `x < e`. -/
def gtInt (e : Ext) (x : Int) : Bool := match e with | .fin y => decide (x < y) | .inf => true
def isZero : Ext → Bool
  | .fin x => x == 0
  | .inf => false
end Ext

/-- The timing properties of an effect (Web Animations 1 §4.6; `EffectTiming`). -/
structure Timing where
  delay : Int := 0
  endDelay : Int := 0
  fill : Fill := .auto
  iterationStart : Int := 0
  iterations : Ext := .fin one
  /-- none: `auto`. -/
  duration : Option Ext := none
  direction : Direction := .normal
  easing : Easing := .linear
  deriving DecidableEq, Repr, Inhabited

inductive Phase where
  | before | active | after | idle
  deriving DecidableEq, Repr, Inhabited

namespace Timing

/-- §4.7.1 iteration duration: `auto` is 0 for a keyframe effect. -/
def iterationDuration (t : Timing) : Ext := t.duration.getD (.fin 0)

/-- §4.8.3.1 active duration: iteration duration × iteration count, 0 when either is 0. -/
def activeDuration (t : Timing) : Ext :=
  match t.iterationDuration, t.iterations with
  | .fin d, .fin n => .fin (Fix.mul d n)
  | d, n => if d.isZero || n.isZero then .fin 0 else .inf

/-- §4.6.4 end time: max(start delay + active duration + end delay, 0). -/
def endTime (t : Timing) : Ext := ((t.activeDuration.add t.delay).add t.endDelay).maxInt 0

/-- §4.6.5: the fill mode in effect; `auto` is `none` for a keyframe effect. -/
def fillOf (t : Timing) : Fill := if t.fill == .auto then .none else t.fill

/-- §4.6.5 before-active boundary time. -/
def beforeActive (t : Timing) : Int := max (t.endTime.minInt t.delay) 0

/-- §4.6.5 active-after boundary time. -/
def activeAfter (t : Timing) : Ext := (Ext.min (t.activeDuration.add t.delay) t.endTime).maxInt 0

/-- §4.6.5 the phase of an effect at a local time; `backwards` is the animation
direction (a negative playback rate). -/
def phase (t : Timing) (localTime : Option Int) (backwards : Bool) : Phase :=
  match localTime with
  | none => .idle
  | some lt =>
    if lt < t.beforeActive || (backwards && lt == t.beforeActive) then .before
    else match t.activeAfter with
      | .fin aa => if lt > aa || (!backwards && lt == aa) then .after else .active
      | .inf => .active

/-- §4.8.3.1 active time. -/
def activeTime (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Int :=
  match localTime with
  | none => none
  | some lt =>
    match t.phase (some lt) backwards with
    | .before => if t.fillOf == .backwards || t.fillOf == .both then some (max (lt - t.delay) 0) else none
    | .active => some (lt - t.delay)
    | .after =>
      if t.fillOf == .forwards || t.fillOf == .both then some (max (t.activeDuration.minInt (lt - t.delay)) 0) else none
    | .idle => none

/-- §4.8.3.2 overall progress. -/
def overallProgress (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Ext :=
  match t.activeTime localTime backwards with
  | none => none
  | some at_ =>
    let base : Ext := match t.iterationDuration with
      | .fin d =>
        if d == 0 then (if t.phase localTime backwards == .before then .fin 0 else t.iterations)
        else .fin ((Fix.div at_ d).getD 0)
      | .inf => .fin 0
    some (base.add t.iterationStart)

/-- The fractional part of a number: in [0, 1). -/
def frac (x : Int) : Int := x % scale

/-- §4.8.3.3 simple iteration progress. -/
def simpleProgress (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Int :=
  match t.overallProgress localTime backwards with
  | none => none
  | some overall =>
    let s := match overall with
      | .inf => frac t.iterationStart
      | .fin o => frac o
    let ph := t.phase localTime backwards
    if s == 0 && (ph == .active || ph == .after)
        && (t.activeTime localTime backwards).map Ext.fin == some t.activeDuration
        && !t.iterations.isZero then some one
    else some s

/-- §4.9.1 current iteration, a whole number or infinity. -/
def currentIteration (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Ext :=
  match t.activeTime localTime backwards, t.overallProgress localTime backwards with
  | some _, some overall =>
    if t.phase localTime backwards == .after && t.iterations == .inf then some .inf
    else match overall with
      | .inf => some .inf
      | .fin o =>
        if t.simpleProgress localTime backwards == some one then some (.fin (o / scale - 1))
        else some (.fin (o / scale))
  | _, _ => none

/-- §4.9.2: whether the current direction is forwards. -/
def forwardsNow (t : Timing) (localTime : Option Int) (backwards : Bool) : Bool :=
  match t.direction with
  | .normal => true
  | .reverse => false
  | .alternate | .alternateReverse =>
    match t.currentIteration localTime backwards with
    | some (.fin d) =>
      let d := if t.direction == .alternateReverse then d + 1 else d
      d % 2 == 0
    | _ => true

/-- §4.9.2 directed progress. -/
def directedProgress (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Int :=
  match t.simpleProgress localTime backwards with
  | none => none
  | some s => some (if t.forwardsNow localTime backwards then s else one - s)

/-- §4.10.1 transformed progress: the effect's easing of the directed progress, with the
before flag. -/
def progress (t : Timing) (localTime : Option Int) (backwards : Bool) : Option Int :=
  match t.directedProgress localTime backwards with
  | none => none
  | some d =>
    let ph := t.phase localTime backwards
    let fwd := t.forwardsNow localTime backwards
    let before := (ph == .before && fwd) || (ph == .after && !fwd)
    some (t.easing.eval d before)

/-! ## Theorems -/

/-- Kind: range. Says: a fractional part is in [0, 1). Does not say: more. -/
theorem frac_range (x : Int) : 0 ≤ frac x ∧ frac x < one := by
  simp only [frac, one, scale]; omega

/-- Kind: totality of the idle case (Web Animations 1 §4.6.5). Says: an effect with no
local time is idle and has no active time and no progress, whatever its timing. Does not
say: anything of an effect with a local time. -/
theorem at_idle (t : Timing) (backwards : Bool) :
    t.phase none backwards = .idle ∧ t.activeTime none backwards = none ∧ t.progress none backwards = none := by
  simp [phase, activeTime, progress, directedProgress, simpleProgress, overallProgress]

/-- Kind: fill (Web Animations 1 §4.8.3.1). Says: in the before phase an effect whose
fill is `none` or `forwards` (or `auto`) has no active time. Does not say: anything of
the other phases. -/
theorem before_no_fill (t : Timing) (lt : Int) (backwards : Bool)
    (hp : t.phase (some lt) backwards = .before) (hf : t.fillOf ≠ .backwards ∧ t.fillOf ≠ .both) :
    t.activeTime (some lt) backwards = none := by
  simp [activeTime, hp, hf.1, hf.2]

/-- Kind: fill. Says: in the after phase an effect whose fill is `none` or `backwards`
(or `auto`) has no active time. Does not say: anything of the other phases. -/
theorem after_no_fill (t : Timing) (lt : Int) (backwards : Bool)
    (hp : t.phase (some lt) backwards = .after) (hf : t.fillOf ≠ .forwards ∧ t.fillOf ≠ .both) :
    t.activeTime (some lt) backwards = none := by
  simp [activeTime, hp, hf.1, hf.2]

/-- Kind: range (Web Animations 1 §4.8.3.3). Says: a simple iteration progress, when
there is one, is in [0, 1]. Does not say: which end it takes at an iteration boundary. -/
theorem simple_range (t : Timing) (localTime : Option Int) (backwards : Bool) (s : Int)
    (h : t.simpleProgress localTime backwards = some s) : 0 ≤ s ∧ s ≤ one := by
  have key : ∀ x : Int, 0 ≤ frac x ∧ frac x ≤ one := fun x => by have := frac_range x; omega
  have hone : (0 : Int) ≤ one ∧ one ≤ one := by simp [one, scale]
  unfold simpleProgress at h
  split at h
  · simp at h
  · rename_i overall _
    cases overall with
    | fin o =>
      simp only at h
      split at h
      · injection h with h; subst h; exact hone
      · injection h with h; subst h; exact key o
    | inf =>
      simp only at h
      split at h
      · injection h with h; subst h; exact hone
      · injection h with h; subst h; exact key t.iterationStart

/-- Kind: range (Web Animations 1 §4.9.2). Says: a directed progress, when there is one,
is in [0, 1]. Does not say: this of the transformed progress, which an easing function
may take outside [0, 1]. -/
theorem directed_range (t : Timing) (localTime : Option Int) (backwards : Bool) (d : Int)
    (h : t.directedProgress localTime backwards = some d) : 0 ≤ d ∧ d ≤ one := by
  unfold directedProgress at h
  split at h
  · simp at h
  · rename_i s hs
    have := simple_range t localTime backwards s hs
    simp at h
    subst h
    split <;> omega

/-! ## Tests -/

private def ms (n : Int) : Int := Fix.ofInt n
private def t100 : Timing := { duration := some (.fin (ms 100000)), fill := .forwards }

-- the interpolation tests: 100 s, at 50 s the progress is the easing at 0.5
#guard t100.progress (some (ms 50000)) false == some Fix.half
#guard ({ t100 with easing := .steps 1 .start }).progress (some (ms 50000)) false == some one
#guard ({ t100 with easing := .steps 1 .end_ }).progress (some (ms 50000)) false == some 0
#guard t100.phase (some (ms 100000)) false == .after
#guard t100.progress (some (ms 100000)) false == some one
#guard t100.progress (some (ms 200000)) false == some one
#guard ({ t100 with fill := .none }).progress (some (ms 100000)) false == none
#guard ({ t100 with fill := .none }).progress (some (ms (-1))) false == none
#guard ({ t100 with fill := .backwards }).progress (some (ms (-1))) false == some 0
-- CSS: a delay of -50 s on 100 s, at animation time 0
#guard ({ t100 with delay := ms (-50000) }).progress (some 0) false == some Fix.half
#guard t100.endTime == .fin (ms 100000)
#guard ({ t100 with iterations := .inf }).endTime == .inf
#guard ({ t100 with iterations := .inf }).phase (some (ms 1000000)) false == .active
#guard ({ t100 with iterations := .fin (ms 2), direction := .alternate }).progress (some (ms 150000)) false == some Fix.half
#guard ({ t100 with iterations := .fin (ms 2), direction := .alternate }).progress (some (ms 125000)) false == some 750000000
#guard ({ t100 with iterations := .fin (ms 2) }).currentIteration (some (ms 150000)) false == some (.fin 1)
#guard ({ t100 with iterations := .fin (ms 2) }).currentIteration (some (ms 200000)) false == some (.fin 1)
#guard ({ t100 with direction := .reverse }).progress (some (ms 25000)) false == some 750000000
#guard ({ t100 with iterationStart := Fix.half }).progress (some 0) false == some Fix.half
-- zero duration: after phase at once, progress 1 with fill forwards
#guard ({ fill := .forwards } : Timing).progress (some 0) false == some one
#guard ({ fill := .forwards } : Timing).phase (some 0) false == .after
#guard ({ fill := .forwards } : Timing).phase (some 0) true == .before
#guard ({} : Timing).progress (some 0) false == none
#guard ({ duration := some .inf, fill := .both } : Timing).progress (some (ms 5)) false == some 0

end Timing
end L4Factoidal.Rendering.Animation
