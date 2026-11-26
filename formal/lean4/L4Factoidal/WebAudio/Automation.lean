/-
  Web Audio API, `AudioParam` automation: the automation event list.

  Specification: https://webaudio.github.io/web-audio-api/ , interface
  `AudioParam`: the introduction "automation event list" rules, the methods
  `setValueAtTime`, `linearRampToValueAtTime`, `exponentialRampToValueAtTime`,
  `setTargetAtTime`, `setValueCurveAtTime`, `cancelScheduledValues`,
  `cancelAndHoldAtTime`, and the section "Computation of Value"
  (`#computation-of-value`).

  Tracking: https://github.com/danbri/factoidal-core/issues/1169 (audio in
  Foafnaut), stage B. Plan: `docs/designissues/2026-11-26-foafnaut-audio-plan.md`,
  section 4.

  Scope. The file defines the event list, the insertion rules with their
  errors, the two cancellation operations, the value at a time, and a
  block-fill loop. Times are exact rationals converted from the page's doubles
  by `ofDouble`, so every order comparison is exact and provable. Values stay
  `Float`; Lean's `Float` is opaque to the kernel, so properties of a value
  are proved over `Rat` (`linearValue`) and the `Float` code is tested against
  that definition with `#guard`.

  Times. Stored times are exact values of binary64 numbers (every time is a
  value `ofDouble` returns), so comparisons of stored times are exact and equal
  the IEEE comparison of the doubles. Sums, products and frame conversion are
  rounded to binary64 as the page and other engines compute them: `addTimes`
  (for example the curve end `T + D`), the ramp and curve fractions, and
  `frameOf` / `frameTime`. Callers store only times that came from `ofDouble`.

  Theorems proved (`#print axioms` shows only `propext`, `Classical.choice`,
  `Quot.sound`):
    `insert_sorted`, `insertAfterEqual_spec`, `insert_after_equal`,
    `cancelScheduledValues_spec`, `curve_overlap_refused`,
    `linearValue_end`, `linearValue_mono`.
  Properties of `Float` values (the shape of `valueAt`, `cancelAndHold`) are a
  `#guard` battery, not theorems.

  Deviations and gaps are listed at the end of the file (section "Not done").
-/

namespace L4Factoidal.WebAudio.Automation

/-! ## Exact conversion of times -/

/-- Exact value of a finite double as a rational, from the IEEE 754 binary64
    fields (sign, 11-bit exponent, 52-bit mantissa). `none` for NaN and the
    infinities. -/
def ofDouble (x : Float) : Option Rat :=
  let bits := x.toBits
  let negative := (bits >>> 63) != 0
  let ex := ((bits >>> 52) &&& 0x7FF).toNat
  let mant := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if ex == 0x7FF then none
  else
    let m : Nat := if ex == 0 then mant else mant + 2 ^ 52
    let e : Int := if ex == 0 then -1074 else (ex : Int) - 1075
    let mag : Rat :=
      if 0 ≤ e then ((m * 2 ^ e.toNat : Nat) : Rat) else mkRat m (2 ^ (-e).toNat)
    some (if negative then -mag else mag)

/-- Nearest-double conversion of a rational, for values computed from exact
    times. Large numerators or denominators round twice; the tests state the
    tolerance. -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- The double that a stored time is the exact value of: the inverse of
    `ofDouble` on its image. The denominator of such a time is a power of two,
    so scaling is exact. -/
def timeToFloat (q : Rat) : Float :=
  Float.scaleB (Float.ofInt q.num) (-(Nat.log2 q.den : Int))

/-- Sum of two stored times computed in binary64 and converted back exactly,
    as the page and other engines add times (for example the end `T + D` of a
    curve). The result is again the exact value of a double. A sum that
    overflows to infinity gives 0. -/
def addTimes (a b : Rat) : Rat :=
  (ofDouble (timeToFloat a + timeToFloat b)).getD 0

/-- Time of a frame: `frame / sampleRate` divided in binary64. -/
def frameTime (frame : Nat) (sampleRate : Float) : Rat :=
  (ofDouble (Float.ofNat frame / sampleRate)).getD 0

/-- First frame at or after time `t`: `ceil (t * sampleRate)` with the product
    rounded to binary64. Convention of the AudioParam tests: WPT
    `webaudio/resources/audioparam-testing.js`, `getStartEndFrames`, whose
    comment reads "Start frame is the ceiling of the start time because the
    ramp starts at or after the sample frame", used by
    `createLinearRampArray`, `createExponentialRampArray` and
    `createExponentialApproachArray`. The specification says an event takes
    effect at its time; a frame is rendered at `frame / sampleRate`, so the
    first frame that sees the event is the first whose time is at or after it.
    The other WPT convention, `timeToSampleFrame` in
    `webaudio/resources/audit-util.js` (`floor (0.5 + t * sampleRate)`, rounding
    to nearest), is used for buffer and render lengths and for comparing
    segments in `audioparam-testing.js` (`createConstantArray`,
    `comparePartialSignals`); it is not used here. -/
def frameOf (t : Rat) (sampleRate : Float) : Nat :=
  (Float.ceil (timeToFloat t * sampleRate)).toUInt64.toNat

/-! ## Types -/

/-- The five event types of the specification ("SetValue", "LinearRampToValue",
    "ExponentialRampToValue", "SetTarget", "SetValueCurve").
    `setValueCurve` carries the curve values, its duration, and `heldAt`:
    `none` for a curve as inserted; `some tc` after `cancelAndHold` cut it at
    `tc` (the curve is still sampled with the original duration, as the
    specification requires: "not a true replacement"). -/
inductive Kind where
  | setValue
  | linearRamp
  | exponentialRamp
  | setTarget (timeConstant : Float)
  | setValueCurve (values : Array Float) (duration : Rat) (heldAt : Option Rat)

/-- `time` is the start time (setValue, setTarget, setValueCurve) or the end
    time (the two ramps). `value` is the value, the ramp end value, or the
    target; it is unused by a curve. -/
structure Event where
  kind : Kind
  time : Rat
  value : Float

/-- Events sorted by time; events with equal times are in insertion order. -/
structure Timeline where
  events : List Event

/-- The four exception types of the specification. -/
inductive Error where
  | notSupported (msg : String)
  | range (msg : String)
  | invalidState (msg : String)
  | type (msg : String)

/-- Event times are sorted. -/
def Sorted (es : List Event) : Prop := List.Pairwise (fun a b => a.time ≤ b.time) es

/-- A double given as a time. Non-finite doubles are a `TypeError`, as in the
    Web IDL conversion that WPT `audioparam-exceptional-values.html`
    ("test value") checks. -/
def eventTime (x : Float) : Except Error Rat :=
  match ofDouble x with
  | some q => .ok q
  | none => .error (.type "time is not a finite number")

/-- Where an event stops acting: the end of a curve (its cut time if cut),
    the event time for every other type. -/
def spanEnd (e : Event) : Rat :=
  match e.kind with
  | .setValueCurve _ d h => h.getD (addTimes e.time d)
  | _ => e.time

def isCurve (e : Event) : Bool :=
  match e.kind with
  | .setValueCurve .. => true
  | _ => false

def isRamp (e : Event) : Bool :=
  match e.kind with
  | .linearRamp => true
  | .exponentialRamp => true
  | _ => false

/-! ## Value of one event -/

/-- Value of curve `vs` (start `t0`, duration `d`) at time `t`: for
    `t0 ≤ t < t0 + d`, `k = floor ((N-1)/d * (t - t0))` and linear interpolation
    between `V[k]` and `V[k+1]`; from `t0 + d` on, the last value
    (`setValueCurveAtTime`). -/
def curveValue (vs : Array Float) (t0 d t : Rat) : Float :=
  let n := vs.size
  if addTimes t0 d ≤ t then vs.getD (n - 1) 0
  else
    let r : Float := ((Float.ofNat (n - 1) / timeToFloat d)) * (timeToFloat t - timeToFloat t0)
    if r < 0 then vs.getD 0 0
    else
      let kf := Float.floor r
      let k := kf.toUInt64.toNat
      let x : Float := r - kf
      let a := vs.getD k 0
      let b := vs.getD (k + 1) a
      a + (b - a) * x

/-- The value of event `e` at time `t ≥ e.time`, ignoring any later event.
    `vBefore` is the value of the parameter just before `e` (used by
    `setTarget` as `V0`). setTarget: `v(t) = V1 + (V0 - V1) e^(-(t-T0)/tau)`,
    and a time constant of 0 jumps to the target (`setTargetAtTime`). -/
def ownValue (e : Event) (vBefore : Float) (t : Rat) : Float :=
  match e.kind with
  | .setValue => e.value
  | .linearRamp => e.value
  | .exponentialRamp => e.value
  | .setTarget tc =>
      if tc == 0 then e.value
      else e.value + (vBefore - e.value) * Float.exp (-((timeToFloat t - timeToFloat e.time) / tc))
  | .setValueCurve vs d h =>
      curveValue vs e.time d (match h with | some h' => if t < h' then t else h' | none => t)

/-- An event with the value of the parameter just before it. -/
structure Cur where
  e : Event
  vBefore : Float

/-- Where a following ramp starts, as (time, value). A setTarget is replaced
    by the ramp, so the ramp starts at the setTarget's start time with the value
    before it (`linearRampToValueAtTime`, "If the preceding event is a SetTarget
    event"). A curve ends at its end time with its last value (the implicit
    `setValueAtTime` of `setValueCurveAtTime`). -/
def endPoint (c : Cur) : Rat × Float :=
  match c.e.kind with
  | .setTarget _ => (c.e.time, c.vBefore)
  | .setValueCurve vs d h =>
      let fin := h.getD (addTimes c.e.time d)
      (fin, curveValue vs c.e.time d fin)
  | _ => (c.e.time, c.e.value)

/-- Ramp value between start point `(tp, v0)` and end `(t1, v1)` at `t` with
    `tp ≤ t < t1`.
    Linear: `v0 + (v1 - v0) (t - tp)/(t1 - tp)`.
    Exponential: `v0 (v1/v0)^((t - tp)/(t1 - tp))`, and `v0` when `v0` is zero
    or `v0` and `v1` have opposite signs. -/
def rampValue (expo : Bool) (tp : Rat) (v0 : Float) (t1 : Rat) (v1 : Float) (t : Rat) : Float :=
  let f := (timeToFloat t - timeToFloat tp) / (timeToFloat t1 - timeToFloat tp)
  if expo then
    if v0 == 0 || (v0 < 0 && 0 < v1) || (0 < v0 && v1 < 0) then v0
    else v0 * Float.pow (v1 / v0) f
  else v0 + (v1 - v0) * f

/-- One left-to-right pass: the last event with time `≤ t` (with its value
    before it, computed from the event before) and the first event after `t`.
    Structural, tail-recursive. -/
def walk (d : Float) (t : Rat) (cur : Option Cur) : List Event → Option Cur × Option Event
  | [] => (cur, none)
  | e :: es =>
    if e.time ≤ t then
      let vb := match cur with
        | none => d
        | some c => ownValue c.e c.vBefore e.time
      walk d t (some ⟨e, vb⟩) es
    else (cur, some e)

/-- "Computation of Value": `paramIntrinsicValue` at time `t`. `defaultValue`
    is the value before the first event. For `t` in a ramp's interval
    `[tp, T1)` the ramp formula; otherwise the value of the last event at or
    before `t`; after the last event the value stays at its final value. -/
def valueAt (tl : Timeline) (defaultValue : Float) (t : Rat) : Float :=
  match walk defaultValue t none tl.events with
  | (none, _) => defaultValue
  | (some c, next) =>
    let (tp, vp) := endPoint c
    match next with
    | some n =>
      if isRamp n && tp ≤ t then
        rampValue (match n.kind with | .exponentialRamp => true | _ => false) tp vp n.time n.value t
      else ownValue c.e c.vBefore t
    | none => ownValue c.e c.vBefore t

/-- a-rate values for frames `startFrame .. startFrame + n - 1`, at time
    `frameTime frame sampleRate` (`frame / sampleRate` in binary64). A loop
    with an accumulator. `frameOf` is the inverse used to find the first frame
    of an event; the tests check that the two agree (frame `frameOf T` has
    time at or after `T`, the frame before it has an earlier time).

    This is the specification of `fill`: exact rationals, `valueAt` per frame.
    The renderer calls `fill`, which gives the same values faster (below). -/
def fillSpec (tl : Timeline) (defaultValue : Float) (startFrame n : Nat) (sampleRate : Float) :
    Array Float := Id.run do
  let mut out : Array Float := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (valueAt tl defaultValue (frameTime (startFrame + i) sampleRate))
  return out

/-! ## The fast form of `fill`

`fill` computes the same values as `fillSpec` without rationals. A stored time is the exact value of
a binary64 number (see "Times"), so `timeToFloat` recovers that number and the order of two stored
times is the IEEE order of the numbers; the time of a frame is `frame / sampleRate` in binary64,
converted to a rational and back without change when it is finite (`frameTime` reads a non-finite
time as 0). The events are converted once per call, and the value of the parameter before each
event (`vBefore` in `walk`) does not depend on the frame, so it is computed once per call too. The
frames increase, so the event under the cursor only moves forward.

Not proved: this relates `Float` operations, which the kernel does not unfold. The `#guard`s at the
end of the file compare `fill` and `fillSpec` on every kind of event, the empty list, equal times,
frames before, inside and after each event, and a sample rate of 0. A list with a curve event uses
`fillSpec`. -/

/-- An event with its time as a binary64 number. `kind`: 0 setValue, 1 linear ramp, 2 exponential
ramp, 3 setTarget (time constant in `tc`). -/
structure FEvent where
  kind : Nat
  time : Float
  value : Float
  tc : Float

/-- The `FEvent` of an event, or `none` for a curve. -/
def FEvent.ofEvent (e : Event) : Option FEvent :=
  match e.kind with
  | .setValue => some ⟨0, timeToFloat e.time, e.value, 0.0⟩
  | .linearRamp => some ⟨1, timeToFloat e.time, e.value, 0.0⟩
  | .exponentialRamp => some ⟨2, timeToFloat e.time, e.value, 0.0⟩
  | .setTarget tc => some ⟨3, timeToFloat e.time, e.value, tc⟩
  | .setValueCurve .. => none

/-- `ownValue` at the time `t` (a binary64 number). -/
def FEvent.own (e : FEvent) (vBefore t : Float) : Float :=
  if e.kind == 3 then
    if e.tc == 0.0 then e.value
    else e.value + (vBefore - e.value) * Float.exp (-((t - e.time) / e.tc))
  else e.value

/-- `rampValue` with times as binary64 numbers. -/
def fRamp (expo : Bool) (tp : Float) (v0 : Float) (t1 : Float) (v1 : Float) (t : Float) : Float :=
  let f := (t - tp) / (t1 - tp)
  if expo then
    if v0 == 0 || (v0 < 0 && 0 < v1) || (0 < v0 && v1 < 0) then v0
    else v0 * Float.pow (v1 / v0) f
  else v0 + (v1 - v0) * f

/-- The value of the parameter before each event: element 0 is the default value and element `j`
is `ownValue` of event `j - 1` at the time of event `j`. -/
def fBefore (d : Float) (es : Array FEvent) : Array Float := Id.run do
  let mut out : Array Float := Array.mkEmpty es.size
  let mut v := d
  for j in [0:es.size] do
    match es[j]? with
    | none => pure ()
    | some e =>
      if j == 0 then v := d
      else v := (es.getD (j - 1) e).own v e.time
      out := out.push v
  return out

/-- The value at time `t` when the first `j` events are at or before `t`. -/
def fValueAt (d : Float) (es : Array FEvent) (vb : Array Float) (j : Nat) (t : Float) : Float :=
  if j == 0 then d
  else
    match es[j - 1]? with
    | none => d
    | some c =>
      let v := vb.getD (j - 1) d
      let (tp, vp) := if c.kind == 3 then (c.time, v) else (c.time, c.value)
      match es[j]? with
      | some n =>
        if (n.kind == 1 || n.kind == 2) && tp ≤ t then fRamp (n.kind == 2) tp vp n.time n.value t
        else c.own v t
      | none => c.own v t

/-- The time of frame `f` as a binary64 number, as `timeToFloat (frameTime f sampleRate)`. -/
def fFrameTime (f : Nat) (sampleRate : Float) : Float :=
  let x := f.toUInt64.toFloat / sampleRate
  if x.isFinite then x + 0.0 else 0.0

/-- The number of leading events at or before `t`, counted from `j` (the cursor only moves
forward); a loop on the fuel `k`. -/
def advance (es : Array FEvent) (t : Float) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j =>
    match es[j]? with
    | some e => if e.time ≤ t then advance es t k (j + 1) else j
    | none => j

/-- Fast `fill`; the events are all of the four non-curve kinds. -/
def fillFast (es : Array FEvent) (defaultValue : Float) (startFrame n : Nat) (sampleRate : Float) :
    Array Float := Id.run do
  let vb := fBefore defaultValue es
  let mut out : Array Float := Array.mkEmpty n
  let mut j := 0
  for i in [0:n] do
    let t := fFrameTime (startFrame + i) sampleRate
    j := advance es t es.size j
    out := out.push (fValueAt defaultValue es vb j t)
  return out

/-- The value of the parameter at every frame from `startFrame` on, when there is one: the default
value for an empty list, the value of the last event when no event is a curve or a `setTarget` and
every event is at or before the time of `startFrame`. Then `fill` gives that value at every frame
(`fillConst_spec` is a `#guard` battery below). -/
def fillConst (tl : Timeline) (defaultValue : Float) (startFrame : Nat) (sampleRate : Float) :
    Option Float :=
  match tl.events with
  | [] => some defaultValue
  | evs =>
    match evs.mapM FEvent.ofEvent with
    | none => none
    | some es =>
      let t0 := fFrameTime startFrame sampleRate
      match es.getLast? with
      | some l => if l.kind != 3 && es.all (fun e => e.time ≤ t0) then some l.value else none
      | none => some defaultValue

/-- a-rate values for frames `startFrame .. startFrame + n - 1`: the same values as `fillSpec`. -/
def fill (tl : Timeline) (defaultValue : Float) (startFrame n : Nat) (sampleRate : Float) :
    Array Float :=
  match tl.events with
  | [] => Array.replicate n defaultValue
  | evs =>
    match evs.mapM FEvent.ofEvent with
    | some es => fillFast es.toArray defaultValue startFrame n sampleRate
    | none => fillSpec tl defaultValue startFrame n sampleRate

/-! ## Insertion -/

/-- Place `e` after every event with time `≤ e.time` and before the first
    event with a later time ("placed in the list after them, but before events
    whose times are after the event"). -/
def insertAfterEqual (es : List Event) (e : Event) : List Event :=
  match es with
  | [] => [e]
  | x :: xs => if e.time < x.time then e :: x :: xs else x :: insertAfterEqual xs e

/-- `insertAfterEqual` as a loop: the events kept before `e`, in reverse order, in `acc`.
    One stack frame for any number of events on the timeline (issue 1172). -/
def insertAfterEqualGo (e : Event) : List Event → List Event → List Event
  | [], acc => acc.reverseAux [e]
  | x :: xs, acc => if e.time < x.time then acc.reverseAux (e :: x :: xs) else insertAfterEqualGo e xs (x :: acc)

theorem insertAfterEqualGo_eq (e : Event) :
    ∀ (es acc : List Event), insertAfterEqualGo e es acc = acc.reverse ++ insertAfterEqual es e
  | [], acc => by simp [insertAfterEqualGo, insertAfterEqual, List.reverseAux_eq]
  | x :: xs, acc => by
    by_cases h : e.time < x.time
    · simp [insertAfterEqualGo, insertAfterEqual, h, List.reverseAux_eq]
    · simp [insertAfterEqualGo, insertAfterEqual, h, insertAfterEqualGo_eq e xs]

/-- `insertAfterEqual` through the loop (`insertAfterEqual_eq_loop` is the `@[csimp]` equation). -/
def insertAfterEqualLoop (es : List Event) (e : Event) : List Event := insertAfterEqualGo e es []

/-- Kind: equivalence. Says: the compiled code runs the loop, which gives the same list as
    `insertAfterEqual` for every timeline and event. Does not say: anything about time cost. -/
@[csimp] theorem insertAfterEqual_eq_loop : @insertAfterEqual = @insertAfterEqualLoop := by
  funext es e; simp [insertAfterEqualLoop, insertAfterEqualGo_eq]

/-- The argument checks of the five methods. `none` when the event is valid.
    - negative time: RangeError (non-finite times are rejected by `eventTime`);
    - non-finite value, target, time constant or curve element: TypeError;
    - exponential ramp to 0: RangeError. The IDL type is `float` (binary32),
      so a value that rounds to 0 in binary32 (magnitude at most 2^-150) is 0;
      WPT `audioparam-exceptional-values.html` "special cases 2" uses 1e-100;
    - negative time constant: RangeError;
    - curve with fewer than 2 values: InvalidStateError;
    - curve duration not strictly positive: RangeError. -/
def validate (e : Event) : Option Error :=
  if e.time < 0 then some (.range "time is negative")
  else match e.kind with
    | .setValue | .linearRamp =>
        if e.value.isFinite then none else some (.type "value is not finite")
    | .exponentialRamp =>
        if !e.value.isFinite then some (.type "value is not finite")
        else if e.value.abs ≤ 7.006492321624085e-46 then some (.range "exponential ramp to 0")
        else none
    | .setTarget tc =>
        if !e.value.isFinite || !tc.isFinite then some (.type "value is not finite")
        else if tc < 0 then some (.range "negative time constant")
        else none
    | .setValueCurve vs d _ =>
        if !(vs.all Float.isFinite) then some (.type "curve element is not finite")
        else if vs.size < 2 then some (.invalidState "curve has fewer than 2 values")
        else if d ≤ 0 then some (.range "curve duration is not positive")
        else none

/-- "If startTime is less than currentTime, it is clamped to currentTime." -/
def clampTime (e : Event) (currentTime : Rat) : Event :=
  if e.time < currentTime then { e with time := currentTime } else e

/-- The two NotSupportedError rules: a new curve at `T` with duration `D`
    when an event has time strictly in `(T, T + D)`; and any new event at a
    time in `[T, T + D)` of an existing curve. -/
def overlapsCurve (es : List Event) (e : Event) : Bool :=
  (match e.kind with
    | .setValueCurve _ d _ => es.any (fun x => e.time < x.time && x.time < addTimes e.time d)
    | _ => false)
  || es.any (fun x => isCurve x && x.time ≤ e.time && e.time < spanEnd x)

/-- The implicit events that a ramp needs before it is placed.
    - No event at or before the ramp: the ramp "behaves as if
      `setValueAtTime(value, currentTime)` were called" with the current value.
    - The event before the ramp is a setTarget that has already started
      (`T0 ≤ currentTime`): `T0` and `V0` are the current time and the
      setTarget value then, so a `setValue` at `currentTime` with that value
      ends the setTarget.
    Other kinds of event add nothing. -/
def prepare (es : List Event) (e : Event) (currentTime : Rat) (currentValue : Float) :
    List Event :=
  if !isRamp e then es
  else
    match (es.filter (fun x => x.time ≤ e.time)).getLast? with
    | none => insertAfterEqual es ⟨.setValue, currentTime, currentValue⟩
    | some s =>
      match s.kind with
      | .setTarget _ =>
          if s.time ≤ currentTime then
            insertAfterEqual es
              ⟨.setValue, currentTime, valueAt ⟨es⟩ currentValue currentTime⟩
          else es
      | _ => es

/-- Add an event to the list: validate, clamp the time to `currentTime`, refuse
    a value-curve overlap, add the implicit events of a ramp, and place the
    event after events with the same time. -/
def insert (tl : Timeline) (e : Event) (currentTime : Rat) (currentValue : Float) :
    Except Error Timeline :=
  match validate e with
  | some err => .error err
  | none =>
    let e' := clampTime e currentTime
    if overlapsCurve tl.events e' then
      .error (.notSupported "event overlaps a value curve")
    else
      .ok ⟨insertAfterEqual (prepare tl.events e' currentTime currentValue) e'⟩

/-! ## Cancellation -/

/-- `cancelTime` from a double: non-finite is a `TypeError` (WPT
    `cancel-scheduled-values.html` "cancel-time"), negative is a `RangeError`,
    below `currentTime` is clamped to `currentTime`. -/
def cancelTimeOfDouble (x : Float) (currentTime : Rat) : Except Error Rat :=
  match ofDouble x with
  | none => .error (.type "cancelTime is not a finite number")
  | some q =>
    if q < 0 then .error (.range "cancelTime is negative")
    else .ok (if q < currentTime then currentTime else q)

/-- An event that `cancelScheduledValues(c)` removes: time `≥ c`, or a value
    curve with `T0 ≤ c ≤ T0 + TD` (an active curve is removed). -/
def cancelled (c : Rat) (x : Event) : Bool :=
  !(x.time < c) || (isCurve x && c ≤ spanEnd x)

/-- `cancelScheduledValues`. -/
def cancelScheduledValues (tl : Timeline) (cancelTime : Rat) : Timeline :=
  ⟨tl.events.filter (fun x => !(cancelled cancelTime x))⟩

/-- `cancelAndHoldAtTime`, following the numbered steps of the specification
    with `t_c = tc`.
    Steps 1 and 2: `E1` is the last event with time `≤ tc`; `E2` is the first
    event with time `> tc`.
    Step 3: if `E2` is a ramp, it becomes the same ramp ending at `tc` with the
    value the original ramp has at `tc`; go to step 5.
    Step 4: if `E1` is a setTarget, add a setValue at `tc` with the setTarget's
    value at `tc`. If `E1` is a curve with `tc` before its end, cut it at `tc`
    (`heldAt`), keeping the original sampling.
    Step 5: remove events with time `> tc`.
    Deviation (WPT `audioparam-cancel-and-hold.html`, "cancel setValueCurve
    now"): a curve that starts exactly at `tc` is removed and the value
    before it is held; the text of the specification would hold `V[0]`. -/
def cancelAndHold (tl : Timeline) (tc : Rat) (defaultValue : Float) : Timeline :=
  let es := tl.events
  let kept := es.filter (fun x => x.time ≤ tc)
  match es.find? (fun x => tc < x.time) with
  | some r2 =>
    if isRamp r2 then
      ⟨kept ++ [{ r2 with time := tc, value := valueAt tl defaultValue tc }]⟩
    else ⟨step4 es kept tc defaultValue⟩
  | none => ⟨step4 es kept tc defaultValue⟩
where
  /-- Step 4 and the result of step 5. -/
  step4 (es kept : List Event) (tc : Rat) (defaultValue : Float) : List Event :=
    match kept.getLast? with
    | none => kept
    | some s =>
      match s.kind with
      | .setTarget _ =>
          insertAfterEqual kept ⟨.setValue, tc, valueAt ⟨es⟩ defaultValue tc⟩
      | .setValueCurve vs d _ =>
          if spanEnd s < tc then kept
          else if s.time == tc then
            insertAfterEqual kept.dropLast
              ⟨.setValue, tc, valueAt ⟨kept.dropLast⟩ defaultValue tc⟩
          else kept.dropLast ++ [{ s with kind := .setValueCurve vs d (some tc) }]
      | _ => kept

/-! ## Theorems on structure -/

theorem mem_insertAfterEqual (es : List Event) (e x : Event) :
    x ∈ insertAfterEqual es e ↔ x = e ∨ x ∈ es := by
  induction es with
  | nil => simp [insertAfterEqual]
  | cons y ys ih =>
    unfold insertAfterEqual
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

private theorem rat_lt_of_lt_of_le {a b c : Rat} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rw [← Rat.not_le]
  intro h3
  exact (Rat.not_le.mpr h1) (Rat.le_trans h2 h3)

/-- Says: placing any event into a time-sorted list gives a time-sorted list.
    Does not say: which position the event takes (see `insertAfterEqual_spec`),
    or anything about the values of events. -/
theorem sorted_insertAfterEqual (es : List Event) (e : Event) (hs : Sorted es) :
    Sorted (insertAfterEqual es e) := by
  induction es with
  | nil => simp [insertAfterEqual, Sorted]
  | cons x xs ih =>
    unfold Sorted at hs ⊢
    unfold insertAfterEqual
    rw [List.pairwise_cons] at hs
    obtain ⟨hx, hxs⟩ := hs
    split
    · next h =>
      rw [List.pairwise_cons]
      refine ⟨?_, List.pairwise_cons.mpr ⟨hx, hxs⟩⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Rat.le_of_lt h
      · exact Rat.le_of_lt (rat_lt_of_lt_of_le h (hx y hy))
    · next h =>
      rw [List.pairwise_cons]
      refine ⟨?_, ih hxs⟩
      intro y hy
      rcases (mem_insertAfterEqual xs e y).mp hy with rfl | hy
      · exact Rat.not_lt.mp h
      · exact hx y hy

/-- Says: in a time-sorted list, `insertAfterEqual` splits the list into a
    prefix `pre` and a suffix `post` and puts the new event between them; every
    event of `pre` has a time at most the new time (so all events with an equal
    time are in `pre`: the new event comes after them) and every event of
    `post` has a strictly later time.
    Does not say: that the list is sorted afterwards (`sorted_insertAfterEqual`)
    or which events `insert` adds besides the new one. -/
theorem insertAfterEqual_spec (es : List Event) (e : Event) (hs : Sorted es) :
    ∃ pre post, es = pre ++ post ∧ insertAfterEqual es e = pre ++ e :: post ∧
      (∀ x ∈ pre, x.time ≤ e.time) ∧ (∀ x ∈ post, e.time < x.time) := by
  induction es with
  | nil => exact ⟨[], [], rfl, rfl, by simp, by simp⟩
  | cons x xs ih =>
    unfold Sorted at hs
    rw [List.pairwise_cons] at hs
    obtain ⟨hx, hxs⟩ := hs
    unfold insertAfterEqual
    split
    · next h =>
      refine ⟨[], x :: xs, rfl, rfl, by simp, ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h
      · exact rat_lt_of_lt_of_le h (hx y hy)
    · next h =>
      obtain ⟨pre, post, h1, h2, h3, h4⟩ := ih hxs
      refine ⟨x :: pre, post, by simp [h1], by simp [h2], ?_, h4⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact Rat.not_lt.mp h
      · exact h3 y hy

theorem sorted_prepare (es : List Event) (e : Event) (ct : Rat) (cv : Float)
    (hs : Sorted es) : Sorted (prepare es e ct cv) := by
  unfold prepare
  split
  · exact hs
  · split
    · exact sorted_insertAfterEqual _ _ hs
    · next s =>
      split
      · split
        · exact sorted_insertAfterEqual _ _ hs
        · exact hs
      · exact hs

/-- Says: if the list is sorted by time and `insert` accepts the event, the new
    list is sorted by time (including the implicit events a ramp adds).
    Does not say: that `insert` accepts any particular event; the checks can
    refuse it. -/
theorem insert_sorted (tl : Timeline) (e : Event) (ct : Rat) (cv : Float) (tl' : Timeline)
    (hs : Sorted tl.events) (h : insert tl e ct cv = .ok tl') : Sorted tl'.events := by
  unfold insert at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      exact sorted_insertAfterEqual _ _ (sorted_prepare _ _ _ _ hs)

/-- Says: when `insert` accepts an event, the stored list is
    `pre ++ e' :: post`, where `e'` is the event with its time clamped to
    `currentTime`, every event of `pre` has a time at most `e'.time`, and every
    event of `post` has a time strictly after `e'.time`. So the event comes after
    all events with the same time and before events with later times.
    Does not say: that `pre` and `post` are the original list split in two
    (a ramp may add an implicit setValue), or that the list is sorted. -/
theorem insert_after_equal (tl : Timeline) (e : Event) (ct : Rat) (cv : Float) (tl' : Timeline)
    (hs : Sorted tl.events) (h : insert tl e ct cv = .ok tl') :
    ∃ pre post, tl'.events = pre ++ clampTime e ct :: post ∧
      (∀ x ∈ pre, x.time ≤ (clampTime e ct).time) ∧
      (∀ x ∈ post, (clampTime e ct).time < x.time) := by
  unfold insert at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h
      obtain ⟨pre, post, _, h2, h3, h4⟩ :=
        insertAfterEqual_spec (prepare tl.events (clampTime e ct) ct cv) (clampTime e ct)
          (sorted_prepare _ _ _ _ hs)
      exact ⟨pre, post, h2, h3, h4⟩

/-- Says: the events that `cancelScheduledValues c` leaves all have a time
    before `c`; every event of the input with a time before `c` that is not an
    active value curve (a curve with `c ≤ T0 + TD`) is still there; and the
    result is the input with some events removed, in the same order, so a sorted
    input gives a sorted result.
    Does not say: what value the parameter has after the call (the value stays
    at what it was before; `valueAt` computes it from the remaining events). -/
theorem cancelScheduledValues_spec (tl : Timeline) (c : Rat) :
    (∀ x ∈ (cancelScheduledValues tl c).events, x.time < c) ∧
    (∀ x ∈ tl.events, x.time < c → (isCurve x && c ≤ spanEnd x) = false →
        x ∈ (cancelScheduledValues tl c).events) ∧
    List.Sublist (cancelScheduledValues tl c).events tl.events ∧
    (Sorted tl.events → Sorted (cancelScheduledValues tl c).events) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [cancelScheduledValues, List.mem_filter, cancelled] at hx
    obtain ⟨_, h⟩ := hx
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    exact decide_eq_true_iff.mp h.1
  · intro x hx h1 h2
    simp only [cancelScheduledValues, List.mem_filter, cancelled]
    refine ⟨hx, ?_⟩
    simp [h1, h2]
  · exact List.filter_sublist
  · intro hs
    exact List.Pairwise.sublist List.filter_sublist hs

/-- Says: a value curve with start `T` (not before `currentTime`) and a valid
    duration `D` and valid values is refused with `NotSupportedError` when the
    list has an event with time strictly between `T` and `T + D`.
    Does not say: that a curve is accepted when there is no such event (an
    existing curve that contains `T` also refuses it), or that an event exactly
    at `T` or at `T + D` is refused (it is not). -/
theorem curve_overlap_refused (tl : Timeline) (vs : Array Float) (T D : Rat)
    (ct : Rat) (cv : Float) (v : Float)
    (hct : ct ≤ T) (hvalid : validate ⟨.setValueCurve vs D none, T, v⟩ = none)
    (hx : ∃ x ∈ tl.events, T < x.time ∧ x.time < addTimes T D) :
    ∃ msg, insert tl ⟨.setValueCurve vs D none, T, v⟩ ct cv = .error (.notSupported msg) := by
  refine ⟨"event overlaps a value curve", ?_⟩
  have hclamp : clampTime ⟨.setValueCurve vs D none, T, v⟩ ct = ⟨.setValueCurve vs D none, T, v⟩ := by
    unfold clampTime
    simp [Rat.not_lt.mpr hct]
  unfold insert
  rw [hvalid]
  simp only [hclamp]
  have hov : overlapsCurve tl.events ⟨.setValueCurve vs D none, T, v⟩ = true := by
    obtain ⟨x, hxm, h1, h2⟩ := hx
    unfold overlapsCurve
    simp only [Bool.or_eq_true]
    left
    simp only [List.any_eq_true]
    exact ⟨x, hxm, by simp [h1, h2]⟩
  simp [hov]

/-! ## Linear interpolation over the rationals -/

/-- The linear-ramp formula `v0 + (v1 - v0) (t - t0)/(t1 - t0)` over `Rat`
    ("linearRampToValueAtTime"). -/
def linearValue (t0 v0 t1 v1 t : Rat) : Rat := v0 + (v1 - v0) * ((t - t0) / (t1 - t0))

/-- Says: a linear ramp reaches its end value exactly at its end time.
    Does not say: that `valueAt` returns `v1` at `t1` in `Float` (the `Float`
    code is tested against `linearValue` with `#guard`). -/
theorem linearValue_end (t0 v0 t1 v1 : Rat) (h : t0 ≠ t1) :
    linearValue t0 v0 t1 v1 t1 = v1 := by
  have hne : t1 - t0 ≠ 0 := by
    intro h0
    apply h
    have := congrArg (· + t0) h0
    simp only [Rat.sub_add_cancel, Rat.zero_add] at this
    exact this.symm
  unfold linearValue
  rw [Rat.div_def, Rat.mul_inv_cancel _ hne, Rat.mul_one]
  rw [Rat.add_comm, Rat.sub_add_cancel]

private theorem rat_div_le_div {a b d : Rat} (hd : 0 < d) (h : a ≤ b) : a / d ≤ b / d := by
  rw [Rat.div_def, Rat.div_def]
  have hinv : 0 ≤ d⁻¹ := by
    by_cases hz : d = 0
    · subst hz; exact absurd hd Rat.lt_irrefl
    · have h1 : d * d⁻¹ = 1 := Rat.mul_inv_cancel _ hz
      rcases Rat.le_total (a := 0) (b := d⁻¹) with h0 | h0
      · exact h0
      · exfalso
        have h2 : d * d⁻¹ ≤ 0 := by
          have := Rat.mul_le_mul_of_nonneg_left h0 (Rat.le_of_lt hd)
          simpa using this
        rw [h1] at h2
        exact (Rat.not_le.mpr (by decide : (0 : Rat) < 1)) h2
  exact Rat.mul_le_mul_of_nonneg_right h hinv

/-- Says: for `t0 < t1` and `v0 ≤ v1`, the linear ramp does not decrease in `t`
    (so it does not decrease on `[t0, t1]`, the interval where the
    specification applies the formula).
    Does not say: that the parameter is monotone between events (a later event
    can end the ramp), a statement for `v0 > v1`, or a property of the `Float`
    implementation. -/
theorem linearValue_mono (t0 v0 t1 v1 ta tb : Rat) (h01 : t0 < t1) (hv : v0 ≤ v1)
    (hab : ta ≤ tb) :
    linearValue t0 v0 t1 v1 ta ≤ linearValue t0 v0 t1 v1 tb := by
  unfold linearValue
  have hd : 0 < t1 - t0 := (Rat.lt_iff_sub_pos _ _).mp h01
  have hsub : ta - t0 ≤ tb - t0 := by
    have h := @Rat.add_le_add_right (ta - t0) (tb - t0) t0
    rw [Rat.sub_add_cancel, Rat.sub_add_cancel] at h
    exact h.mp hab
  have hf : (ta - t0) / (t1 - t0) ≤ (tb - t0) / (t1 - t0) := rat_div_le_div hd hsub
  have hs : 0 ≤ v1 - v0 := (Rat.le_iff_sub_nonneg _ _).mp hv
  exact Rat.add_le_add_left.mpr (Rat.mul_le_mul_of_nonneg_left hf hs)

/-! ## Tests

  Each `#guard` is checked when the file is compiled. Cases marked "WPT" follow
  the web-platform-tests files under
  `webaudio/the-audio-api/the-audioparam-interface/` and
  `webaudio/resources/audioparam-testing.js`; their times are the page's
  doubles, converted exactly. -/

private def q (x : Float) : Rat := (ofDouble x).getD 0
private def sv (v : Float) (t : Rat) : Event := ⟨.setValue, t, v⟩
private def lin (v : Float) (t : Rat) : Event := ⟨.linearRamp, t, v⟩
private def expo (v : Float) (t : Rat) : Event := ⟨.exponentialRamp, t, v⟩
private def tgt (v : Float) (t : Rat) (tc : Float) : Event := ⟨.setTarget tc, t, v⟩
private def crv (vs : Array Float) (t d : Rat) : Event := ⟨.setValueCurve vs d none, t, 0⟩

private def build (es : List Event) (ct : Rat := 0) (cv : Float := 1) : Except Error Timeline :=
  es.foldlM (fun tl e => insert tl e ct cv) ⟨[]⟩

private def kindOf : Except Error Timeline → String
  | .ok _ => "ok"
  | .error (.notSupported _) => "notSupported"
  | .error (.range _) => "range"
  | .error (.invalidState _) => "invalidState"
  | .error (.type _) => "type"

private def val (r : Except Error Timeline) (d : Float) (t : Rat) : Float :=
  match r with
  | .ok tl => valueAt tl d t
  | .error _ => 0.0 / 0.0

private def times (r : Except Error Timeline) : List Rat :=
  match r with
  | .ok tl => tl.events.map (·.time)
  | .error _ => []

private def approx (a b : Float) (tol : Float := 1e-9) : Bool := (a - b).abs ≤ tol

private def nan : Float := 0.0 / 0.0
private def inf : Float := 1.0 / 0.0

private def withTl (r : Except Error Timeline) (f : Timeline → Timeline) : Except Error Timeline :=
  match r with
  | .ok tl => .ok (f tl)
  | .error e => .error e

-- Exact conversion of doubles.
#guard ofDouble 0.5 == some (1 / 2 : Rat)
#guard ofDouble (-0.75) == some (-3 / 4 : Rat)
#guard ofDouble 0.1 == some (mkRat 3602879701896397 36028797018963968)
#guard ofDouble nan == none && ofDouble inf == none && ofDouble (-inf) == none
#guard ofDouble 5e-324 == some (mkRat 1 (2 ^ 1074))
#guard ofDouble 0.0 == some 0 && ofDouble 1e300 != none

-- Placement: after equal times, before later times (`setValueAtTime` etc.).
#guard times (build [sv 1 1, sv 3 3, sv 2 2]) == [1, 2, 3]
#guard val (build [sv 1 1, sv 2 1]) 0 1 == 2.0
#guard val (build [sv 1 1, sv 2 1]) 0 0 == 0.0
-- A time before currentTime is clamped to currentTime.
#guard times (build [sv 1 1] (ct := 2)) == [2]

-- Argument errors. WPT `audioparam-exceptional-values.html`.
#guard kindOf (build [sv 1 (-1)]) == "range"
#guard kindOf (build [sv nan 1]) == "type" && kindOf (build [lin inf 1]) == "type"
#guard kindOf (build [tgt nan 1 1]) == "type" && kindOf (build [tgt 1 1 inf]) == "type"
#guard kindOf (build [sv 1 1, expo 0 2]) == "range"
#guard kindOf (build [sv 1 1, expo (-1e-100) 2]) == "range"
#guard kindOf (build [sv 1 1, expo 1e-100 2]) == "range"
#guard kindOf (build [tgt 1 1 (-1)]) == "range"
#guard kindOf (build [crv #[0, 0, 0] 1 0]) == "range"
#guard kindOf (build [crv #[0, 0, 0] 1 (-1)]) == "range"
#guard kindOf (build [crv #[1, 2, inf, 3] 1 1]) == "type"
#guard kindOf (build [crv #[1, nan, 2, 3] 1 1]) == "type"
-- WPT `audioparam-setValueCurve-exceptions.html` "curve lengths".
#guard kindOf (build [crv #[] 0 (q 0.01)]) == "invalidState"
#guard kindOf (build [crv #[1] 0 (q 0.01)]) == "invalidState"
#guard kindOf (build [crv #[1, 2] 0 (q 0.01)]) == "ok"
-- Non-finite times (`eventTime`) and `cancelTime`.
#guard (match eventTime nan with | .error (.type _) => true | _ => false)
#guard (match cancelTimeOfDouble (-1) 0 with | .error (.range _) => true | _ => false)
#guard (match cancelTimeOfDouble nan 0 with | .error (.type _) => true | _ => false)
#guard (match cancelTimeOfDouble inf 0 with | .error (.type _) => true | _ => false)
#guard (match cancelTimeOfDouble 1 2 with | .ok c => c == 2 | _ => false)

-- Curve overlap. WPT `audioparam-setValueCurve-exceptions.html`.
-- "setValueCurve": curve over [1, 2) with events inside it, and after it.
#guard kindOf (build [crv #[0, 0] 1 1, sv 1 (3 / 2)]) == "notSupported"
#guard kindOf (build [crv #[0, 0] 1 1, lin 1 (3 / 2)]) == "notSupported"
#guard kindOf (build [crv #[0, 0] 1 1, expo 1 (3 / 2)]) == "notSupported"
#guard kindOf (build [crv #[0, 0] 1 1, tgt 1 (3 / 2) 1]) == "notSupported"
#guard kindOf (build [crv #[0, 0] 1 1, sv 1 (q 2.1)]) == "ok"
-- "value setter": a setValue at the curve start.
#guard kindOf (build [crv #[0, 0] 0 (q 0.2), sv 0 0]) == "notSupported"
-- "automations" (times from the page: interval 0.125 / 10).
private def autos : List Event :=
  [lin 1 (q 0.0125), expo 1 (q 0.025), tgt 1 (q 0.0375) 0.1, crv #[0, 0] (q 0.05) (q 0.1)]
#guard kindOf (build autos) == "ok"
#guard kindOf (build (autos ++ [crv #[0, 0] (q 0.00625) (q 0.01)])) == "notSupported"
#guard kindOf (build (autos ++ [crv #[0, 0] (q 0.01875) (q 0.01)])) == "notSupported"
#guard kindOf (build (autos ++ [crv #[0, 0] (q 0.03125) (q 0.01)])) == "notSupported"
#guard kindOf (build (autos ++ [crv #[0, 0] (q 0.04375) (q 0.01)])) == "notSupported"
-- "start-end": the page's own doubles, accumulated in binary64 as the page does
-- (`time += timeInterval`, `time += 2 * timeInterval`).
private def startEnd : List Event :=
  let iv : Float := 0.125 / 50
  let t1 := 0.0 + iv
  let t3 := t1 + 2 * iv
  let t4 := t3 + iv
  let t5 := t4 + iv
  let t6 := t5 + iv
  [sv 1 0, lin 0 (q t1), crv #[0, 0] (q t1) (q iv), expo 1 (q t3), crv #[0, 0] (q t3) (q iv),
   crv #[0, 0] (q t4) (q iv), sv 0 (q t5), crv #[0, 0] (q t5) (q iv), tgt 1 (q t6) 1]
#guard kindOf (build startEnd) == "ok"
-- "curve overlap": a curve over [5, 15) and six overlapping curves, then an event at its end.
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] 5 10]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] 5 5]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] (5 / 2) 10]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] 10 10]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] 6 9]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, crv #[1, 2, 3] 4 11]) == "notSupported"
#guard kindOf (build [crv #[1, 2, 3] 5 10, sv 1 15]) == "ok"
-- "catch-exception": a refused event leaves the earlier timeline as it was.
#guard (match insert ⟨[sv 1 0]⟩ (crv #[0, nan] (q 0.01) (1 / 2)) 0 1 with
        | .error (.type _) => true
        | _ => false)

-- Implicit setValue of a ramp with no earlier event: `setValueAtTime(currentValue, currentTime)`.
#guard times (build [lin 1 2] (ct := 0) (cv := 0.5)) == [0, 2]
#guard val (build [lin 1 2] (ct := 0) (cv := 0.5)) 0 1 == 0.75
#guard val (build [lin 1 2] (ct := 1) (cv := 0.5)) 0 0 == 0.0

-- Linear ramp. WPT `audioparam-testing.js` `createLinearRampArray`; `audioparam-cancel-and-hold.html`
-- `linearRampTest` (0 to 1 over [0, 0.01], then 1 to 0 ending at 0.5).
#guard approx (val (build [sv 0 0, lin 1 (q 0.01), lin 0 (q 0.5)]) 0 (q 0.255)) (1 - (0.255 - 0.01) / 0.49)
#guard val (build [sv 0 0, lin 1 1]) 0 1 == 1.0
#guard val (build [sv 0 0, lin 1 1]) 0 5 == 1.0
#guard val (build [sv 0 0, lin 1 1]) 0 (1 / 2) == 0.5
-- The `Float` code against the `Rat` formula `linearValue`.
#guard approx (val (build [sv 2 1, lin 8 5]) 0 3) (ratToFloat (linearValue 1 2 5 8 3)) 1e-12
#guard approx (val (build [sv 2 1, lin (-8) 5]) 0 (q 2.3333333333333335)) (ratToFloat (linearValue 1 2 5 (-8) (q 2.3333333333333335))) 1e-12
#guard approx (val (build [sv 0 0, lin 1 (q 0.01)]) 0 (q 0.007)) (ratToFloat (linearValue 0 0 (q 0.01) 1 (q 0.007))) 1e-12

-- Exponential ramp: `v0 (v1/v0)^((t-T0)/(T1-T0))`; opposite signs or zero start hold `v0`.
#guard approx (val (build [sv 1 0, expo 4 2]) 0 1) 2.0 1e-12
#guard val (build [sv 1 0, expo 4 2]) 0 2 == 4.0
#guard val (build [sv (-1) 0, expo 1 1]) 0 (1 / 2) == -1.0
#guard val (build [sv 0 0, expo 1 1]) 0 (1 / 2) == 0.0
#guard approx (val (build [sv 0.001 0, expo 2 1]) 0 (1 / 2)) (Float.sqrt (0.001 * 2)) 1e-12

-- setTarget: `v1 + (v0 - v1) e^(-(t-T0)/tau)`; tau 0 jumps; the next event ends it.
#guard approx (val (build [sv 1 0, tgt 0 1 0.5]) 0 (3 / 2)) (Float.exp (-1.0)) 1e-12
#guard val (build [sv 1 0, tgt 0 1 0.5]) 0 1 == 1.0
#guard val (build [sv 1 0, tgt 0 1 0]) 0 1 == 0.0
#guard val (build [sv 1 0, tgt 0 1 1, sv 5 2]) 0 2 == 5.0
#guard approx (val (build [sv 1 0, tgt 0 1 1, sv 5 2]) 0 (q 1.99)) (Float.exp (-0.99)) 1e-12
-- WPT `audioparam-cancel-and-hold.html` "initial setTarget": no earlier event, default 1.
#guard approx (val (build [tgt 0 0 0.1]) 1 (q 0.1)) (Float.exp (-1.0)) 1e-12
-- A ramp after a setTarget replaces it; the curve is continuous.
#guard approx (val (build [sv 1 0, tgt 0 1 1, lin 3 3]) 0 2) 2.0 1e-12
-- A ramp after a setTarget that has started: an implicit setValue at currentTime.
private def started : Except Error Timeline :=
  build [sv 1 0, tgt 0 1 1] >>= fun tl => insert tl (lin 2 3) (3 / 2) 1
#guard times started == [0, 1, 3 / 2, 3]
#guard approx (val started 0 (3 / 2)) (Float.exp (-0.5)) 1e-12
#guard val started 0 3 == 2.0

-- Value curve: interpolation, last value held. `setValueCurveAtTime`.
#guard val (build [crv #[0, 1, 0] 1 2]) 7 1 == 0.0
#guard val (build [crv #[0, 1, 0] 1 2]) 7 (3 / 2) == 0.5
#guard val (build [crv #[0, 1, 0] 1 2]) 7 2 == 1.0
#guard val (build [crv #[0, 1, 0] 1 2]) 7 (5 / 2) == 0.5
#guard val (build [crv #[0, 1, 0] 1 2]) 7 3 == 0.0
#guard val (build [crv #[0, 1, 0] 1 2]) 7 0 == 7.0
-- A ramp after a curve starts at the curve end with its last value.
#guard val (build [crv #[0, 1] 0 1, lin 3 2]) 0 (3 / 2) == 2.0
#guard val (build [crv #[0, 1] 0 1, lin 3 2]) 0 (1 / 2) == 0.5

-- cancelScheduledValues. WPT `cancel-scheduled-values.html` "cancel1".
private def cancel1 : Except Error Timeline :=
  build [sv 0.5 0, sv 1.5 (1 / 4), crv #[1, -1] (1 / 4) (1 / 4), sv 99 (1 / 2)]
private def cancel1At (c : Rat) : Except Error Timeline :=
  withTl cancel1 (fun tl => cancelScheduledValues tl c)
#guard times (cancel1At (q 0.3)) == [0, 1 / 4]
#guard val (cancel1At (q 0.3)) 0 (q 0.3) == 1.5
#guard times (cancel1At (q 0.3) >>= fun tl => insert tl (sv 3 (q 0.375)) 0 1) == [0, 1 / 4, q 0.375]
#guard val (cancel1At (q 0.3) >>= fun tl => insert tl (sv 3 (q 0.375)) 0 1) 0 (q 0.4) == 3.0
-- At the end of the curve the curve and the later event are removed; after the end they stay.
#guard times (cancel1At (1 / 2)) == [0, 1 / 4]
#guard times (cancel1At (q 0.6)) == [0, 1 / 4, 1 / 4, 1 / 2]

-- cancelAndHold. WPT `audioparam-cancel-and-hold.html`.
private def hold (r : Except Error Timeline) (c : Rat) : Except Error Timeline :=
  withTl r (fun tl => cancelAndHold tl c 1)
-- "cancel setTarget now" and "cancel future setTarget".
#guard val (hold (build [sv 0.5 0, tgt 0 (1 / 4) 0.1]) (1 / 4)) 1 1 == 0.5
#guard val (hold (build [sv 0.5 0, tgt 0 (3 / 8) 0.1]) (1 / 4)) 1 1 == 0.5
#guard times (hold (build [sv 0.5 0, tgt 0 (3 / 8) 0.1]) (1 / 4)) == [0]
-- "cancel future setValueCurve" and "cancel setValueCurve now".
#guard val (hold (build [sv 0.5 0, crv #[-1, 1] (3 / 8) (q 0.1)]) (1 / 4)) 1 1 == 0.5
#guard val (hold (build [sv 0.5 0, crv #[-1, 1] (1 / 4) (q 0.1)]) (1 / 4)) 1 1 == 0.5
-- Linear ramp cancelled mid-ramp: the hold value is the ramp value at the cancel time.
private def ramp2 : Except Error Timeline := build [sv 0 0, lin 1 (q 0.01), lin 0 (q 0.5)]
#guard approx (val (hold ramp2 (1 / 4)) 0 1) (1 - (0.25 - 0.01) / 0.49)
#guard approx (val (hold ramp2 (1 / 4)) 0 (q 0.1)) (val ramp2 0 (q 0.1))
#guard approx (val (hold ramp2 (1 / 4)) 0 (1 / 4)) (1 - (0.25 - 0.01) / 0.49)
-- Cancelled twice.
#guard approx (val (hold (hold ramp2 (1 / 4)) (3 / 8)) 0 1) (1 - (0.25 - 0.01) / 0.49)
-- setTarget cancelled after a ramp.
private def tgt2 : Except Error Timeline := build [sv 0 0, lin 1 (q 0.01), tgt 0 (q 0.01) 0.05]
#guard approx (val (hold tgt2 (1 / 4)) 0 1) (Float.exp (-(0.25 - 0.01) / 0.05)) 1e-12
-- Curve cancelled in the middle: held at the value of the original sampling.
private def curve2 : Except Error Timeline :=
  build [sv 0 0, lin 1 (q 0.01), crv #[1, 0] (q 0.01) (q 0.49)]
#guard approx (val (hold curve2 (1 / 4)) 0 1) (1 - 0.24 / 0.49) 1e-12
#guard approx (val (hold curve2 (1 / 4)) 0 (q 0.1)) (val curve2 0 (q 0.1)) 1e-12
-- Cancel after the end of the curve changes nothing.
#guard val (hold curve2 (q 0.6)) 0 1 == 0.0

-- Binary64 sums and frames. A stored time converts back exactly.
#guard timeToFloat (q 0.1) == 0.1 && timeToFloat (q 1e300) == 1e300 && timeToFloat (q 5e-324) == 5e-324
#guard timeToFloat (q (-0.75)) == -0.75 && timeToFloat 0 == 0.0 && timeToFloat 3 == 3.0
#guard ofDouble (timeToFloat (q 0.0125)) == some (q 0.0125)
-- The exact sum differs from the binary64 sum: 0.1 + 0.2 is 0.30000000000000004 in binary64.
#guard addTimes (q 0.1) (q 0.2) == q 0.30000000000000004 && q 0.1 + q 0.2 != q 0.30000000000000004
-- Event at the double 0.1, 44100 Hz: binary64 `0.1 * 44100` is exactly 4410.0, so the first frame is
-- 4410; in exact arithmetic it would be 4411 (4410 / 44100 is below the stored time).
#guard frameOf (q 0.1) 44100 == 4410
#guard -((-(q 0.1 * 44100)).floor) == 4411
#guard frameTime 4410 44100 == q 0.1
#guard q 0.1 ≤ frameTime (frameOf (q 0.1) 44100) 44100
-- The frame before the first frame has an earlier time.
#guard frameTime (frameOf (q 0.0125) 48000 - 1) 48000 < q 0.0125 && frameOf (q 0.0125) 48000 == 600
-- Block fill: a-rate values at `frame / sampleRate`.
private def fillTl : Timeline := ⟨[sv 0 0, lin 1 1]⟩
#guard fill fillTl 0 0 5 4.0 == #[0.0, 0.25, 0.5, 0.75, 1.0]
#guard fill fillTl 0 2 3 4.0 == #[0.5, 0.75, 1.0]
#guard (fill fillTl 0 0 100000 48000.0).size == 100000
#guard (fill fillTl 0 0 3 0.0).size == 3

-- `fillConst`: when it answers, every value of `fill` over later frames is that value (bit equal).
private def constOk (es : List Event) (d : Float) : Bool :=
  [0, 10, 300, 5000, 60000].all fun f =>
    match fillConst ⟨es⟩ d f 48000.0 with
    | none => true
    | some v => (fill ⟨es⟩ d f 700 48000.0).all (fun x => x.toBits == v.toBits)
#guard constOk [] 0.7 && constOk [sv 2 (q 0.001)] 0.7 && constOk [sv 2 (q 0.001), lin 3 (q 0.002)] 0.7
#guard constOk [tgt 1 0 0.002] 0.25 && constOk [sv 0 0, expo 1 (q 0.01)] 0.0
#guard constOk [sv 1 (q 0.001), crv #[0, 1, 0, 2] (q 0.002) (q 0.01)] 0.5
#guard fillConst ⟨[]⟩ 0.7 0 48000.0 == some 0.7
#guard fillConst ⟨[sv 2 (q 0.001)]⟩ 0.7 0 48000.0 == none
#guard fillConst ⟨[sv 2 (q 0.001)]⟩ 0.7 5000 48000.0 == some 2.0
#guard fillConst ⟨[tgt 1 0 0.002]⟩ 0.25 5000 48000.0 == none

-- `fill` against `fillSpec`: every kind of event, empty list, equal times, frames before, inside
-- and after each event, a sample rate of 0, a curve (which uses `fillSpec`).
private def diffTl (es : List Event) (d : Float) (start n : Nat) (sr : Float) : Bool :=
  fill ⟨es⟩ d start n sr == fillSpec ⟨es⟩ d start n sr
private def diffAll (es : List Event) (d : Float) : Bool :=
  diffTl es d 0 200 48000.0 && diffTl es d 37 500 48000.0 && diffTl es d 5000 300 48000.0
    && diffTl es d 0 40 100.0 && diffTl es d 0 5 0.0 && diffTl es d 0 0 48000.0
#guard diffAll [] 0.7
#guard diffAll [sv 2 (q 0.001)] 0.7
#guard diffAll [sv 2 (q 0.001), sv 3 (q 0.001), sv 5 (q 0.002)] 0.7
#guard diffAll [sv 0 0, lin 1 (q 0.01)] 0.0
#guard diffAll [sv 1 0, expo 0.0001 (q 0.01)] 0.0
#guard diffAll [sv 0 0, expo 1 (q 0.01)] 0.0
#guard diffAll [sv (-1) 0, expo 1 (q 0.01)] 0.0
#guard diffAll [tgt 1 0 0.002, lin 3 (q 0.01)] 0.25
#guard diffAll [tgt 1 (q 0.001) 0.003, tgt 0.2 (q 0.004) 0.001, expo 4 (q 0.02)] 0.25
#guard diffAll [tgt 1 (q 0.001) 0.0, sv 7 (q 0.004)] 0.25
#guard diffAll [sv 0.0001 (q 0.002), lin 0.1 (q 0.0125), expo 0.0001 (q 0.0125), sv 3 (q 0.03)] 0.0
#guard diffAll [sv 1 (q 0.005), lin 2 (q 0.005), lin 3 (q 0.005)] 0.0
#guard diffAll [sv 1 (q 0.001), crv #[0, 1, 0, 2] (q 0.002) (q 0.01), lin 5 (q 0.02)] 0.5

/-! ## Not done

  - Values are binary64 `Float`. The IDL type of a value is binary32; the page
    layer must round to binary32 before calling `insert`. Only the
    exponential-ramp zero test accounts for it (`validate`).
  - Clamping to the nominal range (`minValue`, `maxValue`) is not here
    ("Computation of Value": automation runs unclamped, clamping applies to
    the output).
  - `paramComputedValue` (sum with the input buffer, NaN to default) and
    k-rate sampling are not here; `fill` is the a-rate case.
  - The `value` attribute setter is `insert` of a `setValue` at `currentTime`;
    it refuses inside a curve (guard "value setter").
  - `cancelScheduledValues` and `cancelAndHold` take an already clamped time;
    `cancelTimeOfDouble` does the clamp and the errors.
  - `cancelAndHold` on a ramp whose cancel time lies inside a curve that ends
    before the ramp starts rewrites the ramp at that time, as the text of the
    specification does; no WPT case covers it.
  - A curve that starts exactly at the cancel time of `cancelAndHold` is
    removed (WPT "cancel setValueCurve now"); the specification text would
    hold its first value.
  - `valueAt` scans the list for each query: `fill` costs O(frames x events).
    A cursor over the list is a later change; the semantics stay `valueAt`.
  - No theorem relates the `Float` code to `linearValue`; the `#guard`s do.
-/

end L4Factoidal.WebAudio.Automation
