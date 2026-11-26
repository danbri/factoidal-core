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

  Theorems proved (no `sorry`, no axiom beyond `propext`, `Classical.choice`,
  `Quot.sound` where `omega`/`simp` use them):
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
  | .setValueCurve _ d h => h.getD (e.time + d)
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
  if t0 + d ≤ t then vs.getD (n - 1) 0
  else
    let r : Rat := (((n - 1 : Nat) : Rat) / d) * (t - t0)
    if r < 0 then vs.getD 0 0
    else
      let k := r.floor.toNat
      let x : Rat := r - (k : Rat)
      let a := vs.getD k 0
      let b := vs.getD (k + 1) a
      a + (b - a) * ratToFloat x

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
      else e.value + (vBefore - e.value) * Float.exp (-(ratToFloat (t - e.time) / tc))
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
      let fin := h.getD (c.e.time + d)
      (fin, curveValue vs c.e.time d fin)
  | _ => (c.e.time, c.e.value)

/-- Ramp value between start point `(tp, v0)` and end `(t1, v1)` at `t` with
    `tp ≤ t < t1`.
    Linear: `v0 + (v1 - v0) (t - tp)/(t1 - tp)`.
    Exponential: `v0 (v1/v0)^((t - tp)/(t1 - tp))`, and `v0` when `v0` is zero
    or `v0` and `v1` have opposite signs. -/
def rampValue (expo : Bool) (tp : Rat) (v0 : Float) (t1 : Rat) (v1 : Float) (t : Rat) : Float :=
  let f := ratToFloat ((t - tp) / (t1 - tp))
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
    `frame / sampleRate`. A loop with an accumulator. -/
def fill (tl : Timeline) (defaultValue : Float) (startFrame n : Nat) (sampleRate : Rat) :
    Array Float := Id.run do
  let mut out : Array Float := Array.mkEmpty n
  for i in [0:n] do
    out := out.push (valueAt tl defaultValue (((startFrame + i : Nat) : Rat) / sampleRate))
  return out

/-! ## Insertion -/

/-- Place `e` after every event with time `≤ e.time` and before the first
    event with a later time ("placed in the list after them, but before events
    whose times are after the event"). -/
def insertAfterEqual (es : List Event) (e : Event) : List Event :=
  match es with
  | [] => [e]
  | x :: xs => if e.time < x.time then e :: x :: xs else x :: insertAfterEqual xs e

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
    | .setValueCurve _ d _ => es.any (fun x => e.time < x.time && x.time < e.time + d)
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
    (hx : ∃ x ∈ tl.events, T < x.time ∧ x.time < T + D) :
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

end L4Factoidal.WebAudio.Automation
