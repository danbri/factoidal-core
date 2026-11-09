import L4Factoidal.Rendering.Style

/-! # SVG declarative animation: timing and values (SMIL Animation)

The timing that SVG animation elements (`animate`, `animateTransform`) use, from SMIL
Animation (W3C Recommendation 2001-09-04, §3.6) as SVG 1.1 §19.2 takes it, and the
animation function over numbers (§3.2). Times are whole milliseconds of the page clock
(the document's begin is 0). Record: `docs/designissues/2026-10-28-smil-timing-engine.md`
(the design; this is its first slice).

Profile:

* `begin`: a list of offsets (`0s`, `2.5s`) and `click` events (on the target, or
  `id.click` on another element), each with an optional offset; `indefinite`. The
  interval that runs at a time is that of the latest begin instance at or before it
  (`restart="always"`, the default);
* `dur` a clock value (`indefinite` and `media`: no animation); `repeatCount` (a
  number or `indefinite`) and `repeatDur`, whose minimum gives the active duration;
* `fill`: `remove` or `freeze`;
* values: `values` with optional `keyTimes`, or `from`/`to`/`by`; `calcMode` `linear`
  (also for `paced` and `spline`, which are read as linear) and `discrete`;
* `additive` `replace` or `sum`. `accumulate` is not read.

Theorems: the phase is `before` until the begin; in the active phase the time in the
iteration is less than the simple duration; at and after the end of a finite active
duration the phase is `frozen` or `removed` (`fill`). -/
namespace L4Factoidal.Rendering.Smil

private def trim (s : String) := s.trimAscii.toString

/-- A decimal number of the form `d+[.d+]` as thousandths, rounded down. -/
private def thousandths (s : String) : Option Nat := do
  let (whole,frac) := match s.splitOn "." with
    | [w] => (w,"")
    | [w,f] => (w,f)
    | _ => ("x","")
  if whole.isEmpty && frac.isEmpty then none
  let w ← if whole.isEmpty then some 0 else whole.toNat?
  if !frac.all Char.isDigit then none
  let f := ((frac.take 3).toString ++ "000").take 3 |>.toString
  let fv ← f.toNat?
  some (w*1000+fv)

/-- SMIL clock value (SMIL Animation §3.6.7) in milliseconds: `hh:mm:ss[.f]`,
`mm:ss[.f]`, or a timecount with a metric `h`, `min`, `s`, `ms` (none: seconds). -/
def clockValue (source : String) : Option Nat := do
  let s := trim source
  if s.isEmpty then none
  match s.splitOn ":" with
  | [h,m,sec] =>
    let h ← h.toNat?; let m ← m.toNat?; let sec ← thousandths sec
    if m ≥ 60 || sec ≥ 60000 then none
    some (h*3600000+m*60000+sec)
  | [m,sec] =>
    let m ← m.toNat?; let sec ← thousandths sec
    if m ≥ 60 || sec ≥ 60000 then none
    some (m*60000+sec)
  | [_] =>
    if s.endsWith "ms" then (thousandths (s.dropEnd 2).toString).map (·/1000)
    else if s.endsWith "min" then (thousandths (s.dropEnd 3).toString).map (·*60)
    else if s.endsWith "h" then (thousandths (s.dropEnd 1).toString).map (·*3600)
    else if s.endsWith "s" then thousandths (s.dropEnd 1).toString
    else thousandths s
  | _ => none

/-- One item of a `begin` list (SMIL Animation §3.6.7, begin-value). -/
inductive Begin where
  /-- An offset from the document begin. -/
  | offset (ms : Nat)
  /-- A `click` on an element (`none`: the target element), then `delay` ms. -/
  | click (element : Option String) (delay : Nat)
  deriving Repr, BEq, Inhabited

/-- An offset with an optional sign: a negative offset begins at 0 here (the interval
started before the document; the part before 0 is not seen). -/
private def signedOffset (s : String) : Option Nat :=
  let s := trim s
  if s.startsWith "-" then (clockValue (s.drop 1).toString).map fun _ => 0
  else clockValue (if s.startsWith "+" then (s.drop 1).toString else s)

/-- A `begin` value list. `indefinite` and values this profile does not read (syncbase,
`accessKey`, wallclock, other events) give no instance. -/
def beginList (source : String) : List Begin :=
  (source.splitOn ";").filterMap fun item =>
    let item := trim item
    if item.isEmpty then (if source.isEmpty then some (.offset 0) else none) else
    match signedOffset item with
    | some ms => some (.offset ms)
    | none =>
      -- `[id.]click[+-offset]`
      let (event,delay) := match item.splitOn "+" with
        | [e,d] => (trim e,clockValue d)
        | [e] => match e.splitOn "-" with
          | [e',_] => (trim e',some 0)
          | _ => (trim e,some 0)
        | _ => ("",none)
      match delay with
      | none => none
      | some d =>
        if event == "click" then some (.click none d)
        else if event.endsWith ".click" then some (.click (some (event.dropEnd 6).toString) d)
        else none

/-- The begin of the interval that runs at `now`: the latest instance at or before it.
`clicks e` are the times of clicks on the element of item `e`, in any order. -/
def beginAt (begins : List Begin) (clicks : Option String → List Nat) (now : Nat) : Option Nat :=
  begins.foldl (fun acc b =>
    let instances := match b with
      | .offset ms => [ms]
      | .click e d => (clicks e).map (·+d)
    instances.foldl (fun acc t => if t ≤ now then (match acc with
      | some a => some (max a t)
      | none => some t) else acc) acc) none

/-- The phase of an element at a time (SMIL Animation §3.6.8). -/
inductive Phase where
  | before
  /-- In iteration `iteration`, at `at_` ms of a simple duration of `dur` ms. -/
  | active (iteration at_ : Nat)
  /-- After the active duration with `fill="freeze"`: the value of simple time `at_`
  of iteration `iteration` (`at_` may equal the simple duration: its end). -/
  | frozen (iteration at_ : Nat)
  | removed
  deriving Repr, BEq, Inhabited

/-- The phase at `now` for an interval that begins at `start`, with simple duration
`dur` (more than 0), active duration `active` (`none`: indefinite) and `freeze`. -/
def phase (start dur : Nat) (active : Option Nat) (freeze : Bool) (now : Nat) : Phase :=
  if now < start || dur == 0 then .before else
  let e := now-start
  match active with
  | some ad =>
    if ad ≤ e then
      if !freeze then .removed
      -- §3.6.8: frozen at the value of the end of the active duration; an end at the end
      -- of an iteration is the end of the simple duration, not the start of the next.
      else if ad % dur == 0 && ad > 0 then .frozen (ad/dur-1) dur
      else .frozen (ad/dur) (ad%dur)
    else .active (e/dur) (e%dur)
  | none => .active (e/dur) (e%dur)

theorem phase_before (start dur : Nat) (active : Option Nat) (freeze : Bool) (now : Nat) (h : now < start) :
    phase start dur active freeze now = .before := by
  simp [phase, h]

/-- In the active phase the time in the iteration is less than the simple duration. -/
theorem phase_active_lt (start dur : Nat) (active : Option Nat) (freeze : Bool) (now i t : Nat)
    (h : phase start dur active freeze now = .active i t) : t < dur := by
  unfold phase at h
  by_cases h1 : now < start
  · simp [h1] at h
  by_cases h2 : dur = 0
  · simp [h2] at h
  have hp : 0 < dur := Nat.pos_of_ne_zero h2
  cases active with
  | none =>
    simp [h1, h2] at h
    rw [← h.2]; exact Nat.mod_lt _ hp
  | some ad =>
    simp only [h1, h2, decide_false, Bool.false_or, beq_iff_eq] at h
    by_cases h3 : ad ≤ now - start
    · simp only [h3, if_true] at h
      split at h <;> (try split at h) <;> (try split at h) <;> simp at h
    · simp only [h3, if_false, Phase.active.injEq] at h
      rw [← h.2]; exact Nat.mod_lt _ hp

/-- At and after the end of a finite active duration the element is not active. -/
theorem phase_after_end (start dur ad : Nat) (freeze : Bool) (now : Nat) (hd : 0 < dur)
    (h : start+ad ≤ now) :
    phase start dur (some ad) freeze now = (if !freeze then .removed
      else if ad % dur == 0 && ad > 0 then .frozen (ad/dur-1) dur else .frozen (ad/dur) (ad%dur)) := by
  have h1 : ¬ now < start := by omega
  have h2 : ¬ dur = 0 := by omega
  have h3 : ad ≤ now-start := by omega
  simp [phase, h1, h2, h3]

/-- The active duration (§3.6.4): the minimum of `dur` times `repeatCount` (in
thousandths) and `repeatDur`, each when given; `dur` alone with neither; `none`
(indefinite) when both are indefinite or only an indefinite one is given. -/
def activeDuration (dur : Nat) (repeatCount : Option (Option Nat)) (repeatDur : Option (Option Nat)) : Option Nat :=
  let byCount : Option (Option Nat) := repeatCount.map (·.map fun k => dur*k/1000)
  match byCount, repeatDur with
  | none, none => some dur
  | some a, none => a
  | none, some b => b
  | some (some a), some (some b) => some (min a b)
  | some (some a), some none => some a
  | some none, some (some b) => some b
  | some none, some none => none

/-! ### The animation function (§3.2) -/

/-- Linear interpolation of two number lists of one length (shorter: the first). -/
def lerp (a b : Array Float) (t : Float) : Array Float :=
  if a.size != b.size then a else (a.zip b).map fun (x,y) => x+(y-x)*t

/-- The value of `values` at simple-time fraction `f` (0 to 1), with `keyTimes` (same
length as `values`, from 0 to 1) or with equal intervals. Discrete: the value of the
interval that holds `f`. -/
def valueAt (values : Array (Array Float)) (keyTimes : Option (Array Float)) (discrete : Bool) (f : Float) :
    Option (Array Float) := do
  let n := values.size
  if n == 0 then none
  if n == 1 then return values[0]!
  let times : Array Float := match keyTimes with
    | some k => if k.size == n then k else
        (Array.range n).map fun i => Float.ofNat i/Float.ofNat (if discrete then n else n-1)
    | none => (Array.range n).map fun i => Float.ofNat i/Float.ofNat (if discrete then n else n-1)
  if discrete then
    let i := (List.range n).foldl (fun acc i => if times[i]! ≤ f then i else acc) 0
    return values[i]!
  if f ≥ 1 then return values[n-1]!
  let i := (List.range (n-1)).foldl (fun acc i => if times[i]! ≤ f then i else acc) 0
  let span : Float := times[i+1]!-times[i]!
  let t : Float := if span ≤ 0 then 0 else (f-times[i]!)/span
  return lerp values[i]! values[i+1]! (max 0 (min 1 t))

/-- A list of numbers separated by white space or commas. -/
def numbers (source : String) : Option (Array Float) := do
  let items := ((source.replace "," " ").splitOn " ").filter (!·.isEmpty)
  let out ← items.mapM fun s => (CSS.number s).toOption
  some out.toArray

/-- The `values` list (`;`-separated values), or `from`/`to`/`by` (§3.2.3): `to`
alone animates from the base value `base`; `by` adds to `from` (or to `base`). -/
def valueList (values fromV toV byV : Option String) (base : Array Float) : Option (Array (Array Float)) := do
  match values with
  | some v =>
    let items := ((v.splitOn ";").map trim).filter (!·.isEmpty)
    let out ← items.mapM numbers
    if out.isEmpty then none else some out.toArray
  | none =>
    let f := (fromV.bind numbers).getD base
    match toV.bind numbers, byV.bind numbers with
    | some t, _ => some #[f,t]
    | none, some b => some #[f,(f.zip b).map fun (x,y) => x+y]
    | none, none => none

/-! ### `animateTransform` values (SVG 1.1 §19.2.14) -/

def degrees (a : Float) : Float := a*3.141592653589793/180

/-- The matrix of one `animateTransform` value of type `kind`: `translate tx [ty]`,
`scale sx [sy]`, `rotate a [cx cy]`, `skewX a`, `skewY a`. -/
def transformValue (kind : String) (v : Array Float) : Option Transform :=
  let g := fun (i : Nat) (d : Float) => v.getD i d
  let translate := fun (x y : Float) => (⟨1,0,0,1,x,y⟩ : Transform)
  match kind with
  | "translate" => if v.size == 0 then none else some (translate (g 0 0) (g 1 0))
  | "scale" => if v.size == 0 then none else some ⟨g 0 1,0,0,g 1 (g 0 1),0,0⟩
  | "rotate" =>
    if v.size == 0 then none else
    let a := degrees (g 0 0)
    let r : Transform := ⟨a.cos,a.sin,-a.sin,a.cos,0,0⟩
    let cx := g 1 0
    let cy := g 2 0
    some (Math.Affine2.compose .float (Math.Affine2.compose .float (translate cx cy) r) (translate (-cx) (-cy)))
  | "skewX" => if v.size == 0 then none else some ⟨1,0,(degrees (g 0 0)).tan,1,0,0⟩
  | "skewY" => if v.size == 0 then none else some ⟨1,(degrees (g 0 0)).tan,0,1,0,0⟩
  | _ => none

end L4Factoidal.Rendering.Smil
