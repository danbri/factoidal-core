import L4Factoidal.WebAudio.Kernels

/-!
# PannerNode kernel (equal-power panning, distance and cone gains) and the AudioListener geometry

Web Audio API sections "The PannerNode Interface" and "The AudioListener Interface"
(issue https://github.com/danbri/factoidal-core/issues/1169, stage F).

`process` turns one input of 1 or 2 channels into 2 output channels: the equal-power panned input,
times the distance gain, times the cone gain, frame by frame.

## What `process` does not read

`Settings.panningModel` is not read here. The `HRTF` model is refused by the page op before this
kernel runs (it needs the measured impulse responses, a later step); this kernel is the
`equalpower` model whatever the field says.

## Block or frame geometry

The azimuth, the distance and the cone angle are computed once per block when every parameter array
and every listener channel is constant over the block (`isConst`: at most one value, or `n` values
that all equal the first), and once per frame otherwise. Both paths run the same per-frame
function `geoAt`; the constant path evaluates it at frame 0 only. A guard compares the two paths.

## Conventions chosen where the specification or the reference scripts leave a gap

* `normalize` of a zero vector is the zero vector (as in Chromium), so a source straight above or
  below the listener has azimuth 0, and a source at the listener's position has cone angle 90.
* The argument of `acos` is clamped to [-1, 1].
* Distance gain: when `refDistance` is 0 and the distance is 0 (every model), the gain is 1; the
  gain at distance `refDistance` is 1 in every model.
* Linear model: as WPT `panner-formulas.js` (`dref = min(ref, max)`, `dmax = max(ref, max)`,
  `dref = dmax` gives `1 - rolloff`, rolloff clamped to [0, 1]).

## What is tested only with `#guard`

Every statement about a `Float` value.
-/

namespace L4Factoidal.WebAudio.Panner

open L4Factoidal.WebAudio.Kernels (Block iter getF paramAt IsBlock)

/-! ## Models and settings -/

inductive PanningModel where
  | equalpower
  | hrtf
  deriving DecidableEq, Repr, Inhabited

inductive DistanceModel where
  | linear
  | inverse
  | exponential
  deriving DecidableEq, Repr, Inhabited

def PanningModel.text : PanningModel → String
  | .equalpower => "equalpower"
  | .hrtf => "HRTF"

def PanningModel.ofString? : String → Option PanningModel
  | "equalpower" => some .equalpower
  | "HRTF" => some .hrtf
  | _ => none

def DistanceModel.text : DistanceModel → String
  | .linear => "linear"
  | .inverse => "inverse"
  | .exponential => "exponential"

def DistanceModel.ofString? : String → Option DistanceModel
  | "linear" => some .linear
  | "inverse" => some .inverse
  | "exponential" => some .exponential
  | _ => none

/-- Says: reading the text of a panning model gives the model back. Does not say: that other
strings are refused (a guard shows one). -/
theorem PanningModel.ofString_text (m : PanningModel) : PanningModel.ofString? m.text = some m := by
  cases m <;> rfl

/-- Says: reading the text of a distance model gives the model back. Does not say: that other
strings are refused (a guard shows one). -/
theorem DistanceModel.ofString_text (m : DistanceModel) :
    DistanceModel.ofString? m.text = some m := by
  cases m <;> rfl

/-- The attributes of a PannerNode (specification defaults). -/
structure Settings where
  panningModel : PanningModel := .equalpower
  distanceModel : DistanceModel := .inverse
  refDistance : Float := 1.0
  maxDistance : Float := 10000.0
  rolloffFactor : Float := 1.0
  coneInnerAngle : Float := 360.0
  coneOuterAngle : Float := 360.0
  coneOuterGain : Float := 0.0
  deriving Inhabited, Repr

/-- `refDistance` setter: a negative value is a RangeError. Zero is allowed. -/
def setRefDistance (s : Settings) (v : Float) : Except String Settings :=
  if v < 0.0 then .error ("RangeError: " ++ "refDistance must not be negative")
  else .ok { s with refDistance := v }

/-- `maxDistance` setter: zero or a negative value is a RangeError. -/
def setMaxDistance (s : Settings) (v : Float) : Except String Settings :=
  if v ≤ 0.0 then .error ("RangeError: " ++ "maxDistance must be greater than 0")
  else .ok { s with maxDistance := v }

/-- `rolloffFactor` setter: a negative value is a RangeError. -/
def setRolloffFactor (s : Settings) (v : Float) : Except String Settings :=
  if v < 0.0 then .error ("RangeError: " ++ "rolloffFactor must not be negative")
  else .ok { s with rolloffFactor := v }

/-- `coneOuterGain` setter: a value outside [0, 1] is an InvalidStateError. -/
def setConeOuterGain (s : Settings) (v : Float) : Except String Settings :=
  if v < 0.0 ∨ 1.0 < v then
    .error ("InvalidStateError: " ++ "coneOuterGain must be in [0, 1]")
  else .ok { s with coneOuterGain := v }

/-- `coneInnerAngle` setter (no check). -/
def setConeInnerAngle (s : Settings) (v : Float) : Settings := { s with coneInnerAngle := v }

/-- `coneOuterAngle` setter (no check). -/
def setConeOuterAngle (s : Settings) (v : Float) : Settings := { s with coneOuterAngle := v }

/-- Says: a negative `refDistance` is refused with a RangeError text. Does not say: anything about
NaN (the page refuses non-finite values before this setter). -/
theorem setRefDistance_error (s : Settings) (v : Float) (h : v < 0.0) :
    ∃ d, setRefDistance s v = .error ("RangeError: " ++ d) :=
  ⟨"refDistance must not be negative", by simp only [setRefDistance, if_pos h]⟩

/-- Says: a `refDistance` that is not negative (0 included) is accepted and stored. Does not say:
anything about NaN. -/
theorem setRefDistance_ok (s : Settings) (v : Float) (h : ¬ v < 0.0) :
    setRefDistance s v = .ok { s with refDistance := v } := by
  simp only [setRefDistance, if_neg h]

/-- Says: a `maxDistance` of 0 or less is refused with a RangeError text. Does not say: anything
about NaN. -/
theorem setMaxDistance_error (s : Settings) (v : Float) (h : v ≤ 0.0) :
    ∃ d, setMaxDistance s v = .error ("RangeError: " ++ d) :=
  ⟨"maxDistance must be greater than 0", by simp only [setMaxDistance, if_pos h]⟩

/-- Says: a `maxDistance` above 0 is accepted and stored. Does not say: anything about NaN. -/
theorem setMaxDistance_ok (s : Settings) (v : Float) (h : ¬ v ≤ 0.0) :
    setMaxDistance s v = .ok { s with maxDistance := v } := by
  simp only [setMaxDistance, if_neg h]

/-- Says: a negative `rolloffFactor` is refused with a RangeError text. Does not say: anything
about NaN. -/
theorem setRolloffFactor_error (s : Settings) (v : Float) (h : v < 0.0) :
    ∃ d, setRolloffFactor s v = .error ("RangeError: " ++ d) :=
  ⟨"rolloffFactor must not be negative", by simp only [setRolloffFactor, if_pos h]⟩

/-- Says: a `rolloffFactor` that is not negative is accepted and stored. Does not say: anything
about NaN. -/
theorem setRolloffFactor_ok (s : Settings) (v : Float) (h : ¬ v < 0.0) :
    setRolloffFactor s v = .ok { s with rolloffFactor := v } := by
  simp only [setRolloffFactor, if_neg h]

/-- Says: a `coneOuterGain` below 0 or above 1 is refused with an InvalidStateError text.
Does not say: anything about NaN. -/
theorem setConeOuterGain_error (s : Settings) (v : Float) (h : v < 0.0 ∨ 1.0 < v) :
    ∃ d, setConeOuterGain s v = .error ("InvalidStateError: " ++ d) :=
  ⟨"coneOuterGain must be in [0, 1]", by simp only [setConeOuterGain, if_pos h]⟩

/-- Says: a `coneOuterGain` inside [0, 1] is accepted and stored. Does not say: anything about
NaN. -/
theorem setConeOuterGain_ok (s : Settings) (v : Float) (h : ¬ (v < 0.0 ∨ 1.0 < v)) :
    setConeOuterGain s v = .ok { s with coneOuterGain := v } := by
  simp only [setConeOuterGain, if_neg h]

/-! ## Vectors and listener geometry -/

structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Inhabited, Repr

namespace Vec3

def sub (a b : Vec3) : Vec3 := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩
def dot (a b : Vec3) : Float := a.x * b.x + a.y * b.y + a.z * b.z
def cross (u v : Vec3) : Vec3 :=
  ⟨u.y * v.z - u.z * v.y, u.z * v.x - u.x * v.z, u.x * v.y - u.y * v.x⟩
def scale (k : Float) (a : Vec3) : Vec3 := ⟨k * a.x, k * a.y, k * a.z⟩
def norm (a : Vec3) : Float := Float.sqrt (dot a a)
def isZero (a : Vec3) : Bool := a.x == 0.0 && a.y == 0.0 && a.z == 0.0
/-- The vector divided by its length; the zero vector stays the zero vector. -/
def normalize (a : Vec3) : Vec3 :=
  let m := norm a
  if m == 0.0 then a else ⟨a.x / m, a.y / m, a.z / m⟩

end Vec3

open Vec3 in
/-- `acos` in degrees, the argument clamped to [-1, 1]. -/
def acosDeg (c : Float) : Float :=
  let c' := if c < -1.0 then -1.0 else if 1.0 < c then 1.0 else c
  180.0 * Float.acos c' / Kernels.pi

open Vec3 in
/-- Listener basis: (right, forward normalised, up) as in the specification's azimuth algorithm. -/
def listenerBasis (lisFwd lisUp : Vec3) : Vec3 × Vec3 × Vec3 :=
  let right := normalize (cross lisFwd lisUp)
  let fwd := normalize lisFwd
  (right, fwd, cross right fwd)

open Vec3 in
/-- Azimuth in degrees, in (-180, 180]: 0 in front of the listener, 90 to the right. -/
def azimuth (src lisPos lisFwd lisUp : Vec3) : Float :=
  let sl := sub src lisPos
  if isZero sl then 0.0 else
  let sln := normalize sl
  let (right, fwd, up) := listenerBasis lisFwd lisUp
  let projected := normalize (sub sln (scale (dot sln up) up))
  let a0 := acosDeg (dot projected right)
  let a1 := if dot projected fwd < 0.0 then 360.0 - a0 else a0
  if 0.0 ≤ a1 ∧ a1 ≤ 270.0 then 90.0 - a1 else 450.0 - a1

open Vec3 in
/-- Elevation in degrees, in [-90, 90]. -/
def elevation (src lisPos lisFwd lisUp : Vec3) : Float :=
  let sl := sub src lisPos
  if isZero sl then 0.0 else
  let sln := normalize sl
  let (_, _, up) := listenerBasis lisFwd lisUp
  let e := 90.0 - acosDeg (dot sln up)
  if e > 90.0 then 180.0 - e else if e < -90.0 then -180.0 - e else e

/-- Azimuth and elevation of the source seen from the listener. -/
def azimuthElevation (src lisPos lisFwd lisUp : Vec3) : Float × Float :=
  (azimuth src lisPos lisFwd lisUp, elevation src lisPos lisFwd lisUp)

/-! ## Equal-power panning, distance gain, cone gain -/

/-- Left and right gain of the equal-power model for an azimuth in degrees.
The azimuth is clamped to [-180, 180] and folded into [-90, 90]. -/
def equalPowerGains (az : Float) (stereoInput : Bool) : Float × Float :=
  let c := if az < -180.0 then -180.0 else if 180.0 < az then 180.0 else az
  let f := if c < -90.0 then -180.0 - c else if 90.0 < c then 180.0 - c else c
  let x := if stereoInput then (if f ≤ 0.0 then (f + 90.0) / 90.0 else f / 90.0)
           else (f + 90.0) / 180.0
  (Float.cos (x * Kernels.pi / 2.0), Float.sin (x * Kernels.pi / 2.0))

private def fmin (a b : Float) : Float := if a < b then a else b
private def fmax (a b : Float) : Float := if a < b then b else a

/-- Distance gain for a distance `d` between source and listener. -/
def distanceGain (s : Settings) (d : Float) : Float :=
  let r := s.refDistance
  let ro := s.rolloffFactor
  match s.distanceModel with
  | .linear =>
    let dref := fmin r s.maxDistance
    let dmax := fmax r s.maxDistance
    let d' := fmax (fmin d dmax) dref
    let f := fmax (fmin ro 1.0) 0.0
    if dref == dmax then 1.0 - f else 1.0 - f * (d' - dref) / (dmax - dref)
  | .inverse =>
    let dm := fmax d r
    let den := r + ro * (dm - r)
    if den == 0.0 then 1.0 else r / den
  | .exponential =>
    let dm := fmax d r
    if dm == r then 1.0 else Float.pow (dm / r) (-ro)

open Vec3 in
/-- Cone gain of a directional source. -/
def coneGain (s : Settings) (srcPos srcOrient lisPos : Vec3) : Float :=
  if isZero srcOrient || (s.coneInnerAngle == 360.0 && s.coneOuterAngle == 360.0) then 1.0 else
  let angle := acosDeg (dot (normalize (sub lisPos srcPos)) (normalize srcOrient))
  let inner := Float.abs s.coneInnerAngle / 2.0
  let outer := Float.abs s.coneOuterAngle / 2.0
  if angle ≤ inner then 1.0
  else if angle ≥ outer then s.coneOuterGain
  else
    let x := (angle - inner) / (outer - inner)
    (1.0 - x) + s.coneOuterGain * x

/-! ## The kernel -/

/-- The geometry of one frame: the two equal-power gains, the product of the distance and cone
gains, and which branch the stereo formula takes (azimuth at most 0). -/
structure Geo where
  gl : Float
  gr : Float
  gain : Float
  leftBranch : Bool

/-- A parameter value at frame `i`; an absent (empty) array reads as the default `d`. -/
def pAt (a : FloatArray) (d : Float) (i : Nat) : Float :=
  if a.size = 0 then d else paramAt a i

/-- All values over the first `n` frames equal the first (an array of at most one value always
is). -/
def isConst (n : Nat) (a : FloatArray) : Bool :=
  if a.size ≤ 1 then true
  else iter (fun i (ok : Bool) => ok && getF a i == getF a 0) n 0 true

/-- The listener channel `k` (0 to 8) at frame `i`; an absent channel reads as `d`. -/
def lisAt (listener : Block) (k : Nat) (d : Float) (i : Nat) : Float :=
  pAt (listener.getD k ⟨#[]⟩) d i

def geoAt (s : Settings) (stereo : Bool) (listener : Block) (params : Array FloatArray)
    (i : Nat) : Geo :=
  let p (k : Nat) (d : Float) : Float := pAt (params.getD k ⟨#[]⟩) d i
  let l (k : Nat) (d : Float) : Float := lisAt listener k d i
  let src : Vec3 := ⟨p 0 0.0, p 1 0.0, p 2 0.0⟩
  let srcOr : Vec3 := ⟨p 3 1.0, p 4 0.0, p 5 0.0⟩
  let lisPos : Vec3 := ⟨l 0 0.0, l 1 0.0, l 2 0.0⟩
  let lisFwd : Vec3 := ⟨l 3 0.0, l 4 0.0, l 5 (-1.0)⟩
  let lisUp : Vec3 := ⟨l 6 0.0, l 7 1.0, l 8 0.0⟩
  let az := azimuth src lisPos lisFwd lisUp
  let (gl, gr) := equalPowerGains az stereo
  { gl := gl, gr := gr
    gain := distanceGain s (Vec3.norm (Vec3.sub src lisPos)) * coneGain s src srcOr lisPos
    leftBranch := decide (az ≤ 0.0) }

/-- One output frame (left, right) from the input frames `a` (channel 0) and `b` (channel 1). -/
def frameOut (stereo : Bool) (a b : FloatArray) (geo : Nat → Geo) (i : Nat) : Float × Float :=
  let g := geo i
  let l := getF a i
  if stereo then
    let r := getF b i
    if g.leftBranch then ((l + r * g.gl) * g.gain, r * g.gr * g.gain)
    else (l * g.gl * g.gain, (r + l * g.gr) * g.gain)
  else (l * g.gl * g.gain, l * g.gr * g.gain)

def push2 (f : Nat → Float × Float) (j : Nat) (p : FloatArray × FloatArray) :
    FloatArray × FloatArray :=
  let o := f j
  (p.1.push o.1, p.2.push o.2)

theorem iter_push2_size (f : Nat → Float × Float) (k i : Nat) (a b : FloatArray) :
    (iter (push2 f) k i (a, b)).1.size = a.size + k ∧
    (iter (push2 f) k i (a, b)).2.size = b.size + k := by
  induction k generalizing i a b with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter, push2]
    have := ih (i + 1) (a.push (f i).1) (b.push (f i).2)
    rw [Kernels.size_push, Kernels.size_push] at this
    omega

def render (n : Nat) (stereo : Bool) (a b : FloatArray) (geo : Nat → Geo) : Block :=
  let r := iter (push2 (frameOut stereo a b geo)) n 0 (⟨#[]⟩, ⟨#[]⟩)
  #[r.1, r.2]

theorem render_shape (n : Nat) (stereo : Bool) (a b : FloatArray) (geo : Nat → Geo) :
    (render n stereo a b geo).size = 2 ∧ IsBlock n (render n stereo a b geo) := by
  have h := iter_push2_size (frameOut stereo a b geo) n 0 ⟨#[]⟩ ⟨#[]⟩
  have e : (FloatArray.mk #[]).size = 0 := rfl
  rw [e] at h
  refine ⟨by simp [render], ?_⟩
  intro c hc
  simp only [render, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · omega
  · omega

/-- The PannerNode kernel. `input`: 1 or 2 channels of `n` frames (more: the first two; none: one
channel of silence). `listener`: the 9 AudioListener channels (positionX/Y/Z, forwardX/Y/Z,
upX/Y/Z); an absent one reads as its default. `params`: positionX/Y/Z, orientationX/Y/Z of the
node. Output: 2 channels of `n` frames. -/
def process (n : Nat) (s : Settings) (input : Block) (listener : Block)
    (params : Array FloatArray) : Block :=
  let stereo := decide (2 ≤ input.size)
  let a := input.getD 0 ⟨#[]⟩
  let b := input.getD 1 ⟨#[]⟩
  let constant := (listener.all (isConst n)) && (params.all (isConst n))
  if constant then
    let g := geoAt s stereo listener params 0
    render n stereo a b (fun _ => g)
  else render n stereo a b (geoAt s stereo listener params)

/-- Says: the output has 2 channels of `n` frames each, for any settings, input, listener and
parameters. Does not say: anything about the values. -/
theorem process_shape (n : Nat) (s : Settings) (input listener : Block)
    (params : Array FloatArray) :
    (process n s input listener params).size = 2 ∧
    IsBlock n (process n s input listener params) := by
  unfold process
  dsimp only
  split <;> exact render_shape _ _ _ _ _

/-! ## Tests (Web Platform Tests expectations named at each guard) -/

section Tests

private def approx (a b : Float) : Bool := Float.abs (a - b) ≤ 1e-9
private def approxL (a b : List Float) : Bool :=
  a.length == b.length && (List.zip a b).all fun (x, y) => approx x y
private def v (x y z : Float) : Vec3 := ⟨x, y, z⟩
private def o3 : Vec3 := v 0.0 0.0 0.0
private def lf : Vec3 := v 0.0 0.0 (-1.0)
private def lu : Vec3 := v 0.0 1.0 0.0
private def az (p : Vec3) : Float := azimuth p o3 lf lu
private def el (p : Vec3) : Float := elevation p o3 lf lu
private def ch (xs : List Float) : FloatArray := ⟨xs.toArray⟩
private def gl (a : Float) (st : Bool) : Float := (equalPowerGains a st).1
private def gr (a : Float) (st : Bool) : Float := (equalPowerGains a st).2

-- Azimuth with the default listener (panner-azimuth.html: right 90, left -90, front 0, back 180
-- read as -180 by the algorithm, which then folds it to 0 in the equal-power model).
#guard approx (az (v 1.0 0.0 0.0)) 90.0
#guard approx (az (v (-1.0) 0.0 0.0)) (-90.0)
#guard approx (az (v 0.0 0.0 (-1.0))) 0.0
#guard approx (az (v 0.0 0.0 1.0)) (-180.0)
#guard approx (az (v 1.0 0.0 (-1.0))) 45.0
#guard approx (az (v 1.0 0.0 1.0)) 135.0
#guard approx (az (v (-1.0) 0.0 1.0)) (-135.0)
-- directly above: the projection is the zero vector, azimuth 0 (zero stays zero)
#guard approx (az (v 0.0 1.0 0.0)) 0.0
#guard approx (az o3) 0.0
-- Elevation
#guard approx (el (v 0.0 1.0 0.0)) 90.0
#guard approx (el (v 0.0 (-1.0) 0.0)) (-90.0)
#guard approx (el (v 1.0 0.0 0.0)) 0.0
#guard approx (el (v 0.0 1.0 (-1.0))) 45.0
#guard approx (el (v 1.0 (-1.0) 0.0)) (-45.0)
#guard approx (el o3) 0.0
-- A rotated listener (forward +x, up +y): the source on +x is in front, on +z is to the right.
#guard approx (azimuth (v 1.0 0.0 0.0) o3 (v 1.0 0.0 0.0) lu) 0.0
#guard approx (azimuth (v 0.0 0.0 1.0) o3 (v 1.0 0.0 0.0) lu) 90.0
-- A listener not at the origin
#guard approx (azimuth (v 6.0 5.0 5.0) (v 5.0 5.0 5.0) lf lu) 90.0

-- Equal-power gains (panner-equalpower.html, panner-equalpower-stereo.html), mono then stereo
#guard approxL [gl (-90.0) false, gr (-90.0) false] [1.0, 0.0]
#guard approxL [gl 0.0 false, gr 0.0 false] [0.7071067811865476, 0.7071067811865476]
#guard approxL [gl 90.0 false, gr 90.0 false] [0.0, 1.0]
#guard approxL [gl (-90.0) true, gr (-90.0) true] [1.0, 0.0]
#guard approxL [gl 0.0 true, gr 0.0 true] [0.0, 1.0]
#guard approxL [gl 90.0 true, gr 90.0 true] [0.0, 1.0]
-- folding: behind the listener equals the mirror position in front; the angle is clamped
#guard approxL [gl 180.0 false, gr 180.0 false] [0.7071067811865476, 0.7071067811865476]
#guard approxL [gl (-135.0) false, gr (-135.0) false] [gl (-45.0) false, gr (-45.0) false]
#guard approxL [gl 400.0 true, gr 400.0 true] [gl 180.0 true, gr 180.0 true]

-- Distance models: distance-model-testing.js (positions refDistance + k step on the z axis,
-- 100 nodes, refDistance 1, maxDistance 10000, rolloff 1).
private def dmSettings (m : DistanceModel) : Settings := { distanceModel := m }
private def dmPos (k : Nat) : Float := 1.0 + (10000.0 - 1.0) / 100.0 * k.toFloat
#guard (List.range 100).all fun k =>
  approx (distanceGain (dmSettings .linear) (dmPos k))
    (1.0 - 1.0 * (fmin (dmPos k) 10000.0 - 1.0) / (10000.0 - 1.0))
#guard (List.range 100).all fun k =>
  approx (distanceGain (dmSettings .inverse) (dmPos k)) (1.0 / (1.0 + 1.0 * (dmPos k - 1.0)))
#guard (List.range 100).all fun k =>
  approx (distanceGain (dmSettings .exponential) (dmPos k)) (Float.pow (dmPos k / 1.0) (-1.0))

-- panner-distance-clamping.html: the gain at a distance outside [ref, max] equals the gain at the
-- clamped distance (all models clamp below to ref; only linear clamps above to max); rolloff 0.5.
private def clampCase (m : DistanceModel) (d ref mx : Float) : Bool :=
  let s : Settings := { distanceModel := m, refDistance := ref, maxDistance := mx,
                        rolloffFactor := 0.5 }
  let x := fmax d ref
  let x := if m == .linear then fmin x mx else x
  distanceGain s d == distanceGain s x
#guard clampCase .linear 0.01 1.0 10000.0
#guard clampCase .exponential 0.01 1.0 10000.0
#guard clampCase .inverse 0.01 1.0 10000.0
#guard clampCase .linear 2.0 10.0 1000.0
#guard clampCase .exponential 2.0 10.0 1000.0
#guard clampCase .inverse 2.0 10.0 1000.0
#guard clampCase .linear 20000.0 1.0 10000.0
#guard clampCase .exponential 21000.0 1.0 10000.0
#guard clampCase .inverse 23000.0 1.0 10000.0
#guard clampCase .linear 5000.0 10.0 1000.0
#guard clampCase .exponential 5000.0 10.0 1000.0
#guard clampCase .inverse 5000.0 10.0 1000.0
-- the clamped linear gains are not trivially equal: gain at max is 1 - rolloff
#guard approx (distanceGain { distanceModel := .linear, rolloffFactor := 0.5 } 20000.0) 0.5
-- panner-rolloff-clamping.html: linear, rolloff 2 gives the output of rolloff 1 (position 5000)
#guard distanceGain { distanceModel := .linear, rolloffFactor := 2.0 } 5000.0
  == distanceGain { distanceModel := .linear, rolloffFactor := 1.0 } 5000.0
-- Edge cases written for this kernel (no WPT expectation): at distance refDistance the gain is 1;
-- refDistance 0 with distance 0 is 1; rolloff 0 is 1.
#guard [DistanceModel.linear, .inverse, .exponential].all fun m =>
  distanceGain { distanceModel := m, refDistance := 0.0 } 0.0 == 1.0
#guard [DistanceModel.linear, .inverse, .exponential].all fun m =>
  distanceGain { distanceModel := m, refDistance := 3.0 } 3.0 == 1.0
#guard [DistanceModel.linear, .inverse, .exponential].all fun m =>
  distanceGain { distanceModel := m, rolloffFactor := 0.0 } 500.0 == 1.0
#guard [DistanceModel.linear, .inverse, .exponential].all fun m =>
  distanceGain { distanceModel := m, refDistance := 0.0, rolloffFactor := 0.0 } 7.0 == 1.0
-- refDistance 0 with a positive distance: inverse and exponential give 0
#guard distanceGain { distanceModel := .inverse, refDistance := 0.0 } 7.0 == 0.0
#guard distanceGain { distanceModel := .exponential, refDistance := 0.0 } 7.0 == 0.0
-- linear with ref = max: 1 - rolloff (panner-formulas.js)
private def refEqMax : Settings :=
  { distanceModel := .linear, refDistance := 5.0, maxDistance := 5.0, rolloffFactor := 0.25 }
#guard distanceGain refEqMax 9.0 == 0.75

-- Cone gain (panner-orientation-cone-gain-changes.html: source at (1,0,0), listener at origin,
-- inner 60, outer 120, outer gain 0; orientation (-1,0,0) full gain, (1,0,0) outer gain)
private def coneS : Settings :=
  { coneInnerAngle := 60.0, coneOuterAngle := 120.0, coneOuterGain := 0.0 }
#guard coneGain coneS (v 1.0 0.0 0.0) (v (-1.0) 0.0 0.0) o3 == 1.0
#guard coneGain coneS (v 1.0 0.0 0.0) (v 1.0 0.0 0.0) o3 == 0.0
-- between the cones: angle 90 (orientation (0,1,0)), inner 30, outer 150: x = 0.5,
-- gain = (1 - 0.5) + 0.5 * 0.5 = 0.75
#guard approx (coneGain { coneInnerAngle := 60.0, coneOuterAngle := 300.0, coneOuterGain := 0.5 }
  (v 1.0 0.0 0.0) (v 0.0 1.0 0.0) o3) 0.75
-- default cone (360, 360) and a zero orientation: 1
#guard coneGain { coneOuterGain := 0.3 } (v 1.0 0.0 0.0) (v 1.0 0.0 0.0) o3 == 1.0
#guard coneGain coneS (v 1.0 0.0 0.0) o3 o3 == 1.0
-- inside the inner cone / outside the outer cone with another outer gain
#guard coneGain { coneInnerAngle := 90.0, coneOuterAngle := 180.0, coneOuterGain := 0.25 }
  (v 1.0 0.0 0.0) (v (-1.0) 0.0 0.0) o3 == 1.0
#guard coneGain { coneInnerAngle := 90.0, coneOuterAngle := 180.0, coneOuterGain := 0.25 }
  (v 1.0 0.0 0.0) (v 1.0 0.0 0.0) o3 == 0.25

-- Setters (panner-distance-clamping.html: -1 throws RangeError, 0 allowed for refDistance and
-- refused for maxDistance, the least positive double allowed)
#guard (match setRefDistance {} (-1.0) with | .error m => m.startsWith "RangeError:" | _ => false)
#guard (match setRefDistance {} 0.0 with | .ok _ => true | _ => false)
#guard (match setRefDistance {} 4.9406564584124654e-324 with | .ok _ => true | _ => false)
#guard (match setMaxDistance {} (-1.0) with | .error m => m.startsWith "RangeError:" | _ => false)
#guard (match setMaxDistance {} 0.0 with | .error m => m.startsWith "RangeError:" | _ => false)
#guard (match setMaxDistance {} 4.9406564584124654e-324 with | .ok _ => true | _ => false)
#guard (match setRolloffFactor {} (-0.5) with | .error m => m.startsWith "RangeError:" | _ => false)
#guard (match setRolloffFactor {} 0.0 with | .ok _ => true | _ => false)
#guard (match setConeOuterGain {} 1.5 with
  | .error m => m.startsWith "InvalidStateError:" | _ => false)
#guard (match setConeOuterGain {} (-0.1) with
  | .error m => m.startsWith "InvalidStateError:" | _ => false)
#guard (match setConeOuterGain {} 1.0 with | .ok _ => true | _ => false)
#guard (match setConeOuterGain {} 0.0 with | .ok _ => true | _ => false)
#guard PanningModel.ofString? "equal" == none
#guard DistanceModel.ofString? "Linear" == none

-- whole `process`, equal-power rows of panner-model-testing.js: 101 sources at
-- (cos a, 0, sin a), linear distance model, impulse 1 (mono) or (1, 1) (stereo); the reference
-- gains are equalPowerGain(angle) of that file.
private def refGain (angle : Float) (stereo : Bool) : Float × Float :=
  let azr := 90.0 - angle * 180.0 / Kernels.pi
  if !stereo then
    let pp := (azr + 90.0) / 180.0
    (Float.cos (0.5 * Kernels.pi * pp), Float.sin (0.5 * Kernels.pi * pp))
  else if azr ≤ 0.0 then
    let pp := (azr + 90.0) / 90.0
    (1.0 + Float.cos (0.5 * Kernels.pi * pp), Float.sin (0.5 * Kernels.pi * pp))
  else
    let pp := azr / 90.0
    (Float.cos (0.5 * Kernels.pi * pp), 1.0 + Float.sin (0.5 * Kernels.pi * pp))
private def modelRow (stereo : Bool) (k : Nat) : Bool :=
  let angle := Kernels.pi / 100.0 * k.toFloat
  let input : Block := if stereo then #[ch [1.0], ch [1.0]] else #[ch [1.0]]
  let o := process 1 { distanceModel := .linear } input #[]
    #[ch [Float.cos angle], ch [0.0], ch [Float.sin angle], ch [1.0], ch [0.0], ch [0.0]]
  let r := refGain angle stereo
  approx (o[0]!.get! 0) r.1 && approx (o[1]!.get! 0) r.2
#guard (List.range 101).all (modelRow false)
#guard (List.range 101).all (modelRow true)

-- One whole block against a direct evaluation of panner-formulas.js (calculateAzimuth,
-- applyPanner, distance formulas): panner-automation-position.html, a source moving from (0,0,1)
-- to (20000,30000,10000) in 8 frames (behind the listener, where the reference's equalPowerGain
-- agrees with the specification), 1 and 2 channel input, the three distance models.
private def rv3 (a b : List Float) : List Float := (List.zip a b).map fun (x, y) => x - y
private def rcross (u w : List Float) : List Float :=
  [u[1]! * w[2]! - u[2]! * w[1]!, u[2]! * w[0]! - u[0]! * w[2]!, u[0]! * w[1]! - u[1]! * w[0]!]
private def rdot (u w : List Float) : Float := u[0]! * w[0]! + u[1]! * w[1]! + u[2]! * w[2]!
private def rnorm (u : List Float) : List Float :=
  let m := Float.sqrt (rdot u u)
  u.map (· / m)
private def rAzimuth (src : List Float) : Float :=
  let sl := rnorm (rv3 src [0.0, 0.0, 0.0])
  let right := rnorm (rcross [0.0, 0.0, -1.0] [0.0, 1.0, 0.0])
  let fwd := rnorm [0.0, 0.0, -1.0]
  let up := rcross right fwd
  let proj := rnorm (rv3 sl (up.map (· * rdot sl up)))
  let a := 180.0 / Kernels.pi * Float.acos (rdot proj right)
  let a := if rdot proj fwd < 0.0 then 360.0 - a else a
  if a ≥ 0.0 && a ≤ 270.0 then 90.0 - a else 450.0 - a
private def rEqual (az : Float) (n : Nat) : Float × Float :=
  let az := if az < -90.0 then -180.0 - az else 180.0 - az
  let hp := Kernels.pi / 2.0
  if n == 1 then
    let pp := (az + 90.0) / 180.0
    (Float.cos (hp * pp), Float.sin (hp * pp))
  else
    let pp := if az ≤ 0.0 then (az + 90.0) / 90.0 else az / 90.0
    (Float.cos (hp * pp), Float.sin (hp * pp))
private def rDist (m : DistanceModel) (ro : Float) (p : List Float) : Float :=
  let d := Float.sqrt (rdot p p)
  match m with
  | .linear => 1.0 - fmax (fmin ro 1.0) 0.0 * (fmax (fmin d 10000.0) 1.0 - 1.0) / (10000.0 - 1.0)
  | .inverse => 1.0 / (1.0 + ro * (fmax d 1.0 - 1.0))
  | .exponential => Float.pow (fmax d 1.0 / 1.0) (-ro)
private def mvPos (i : Nat) : List Float :=
  let t := i.toFloat / 8.0
  [20000.0 * t, 30000.0 * t, 1.0 + 9999.0 * t]
private def movingParams : Array FloatArray :=
  #[ch ((List.range 8).map fun i => (mvPos i)[0]!), ch ((List.range 8).map fun i => (mvPos i)[1]!),
    ch ((List.range 8).map fun i => (mvPos i)[2]!), ch [1.0], ch [0.0], ch [0.0]]
private def movingRow (m : DistanceModel) (ro : Float) (nch : Nat) : Bool :=
  let sl := (List.range 8).map fun i => 1.0 + i.toFloat
  let sr := (List.range 8).map fun i => 10.0 + i.toFloat
  let input : Block := if nch == 1 then #[ch sl] else #[ch sl, ch sr]
  let o := process 8 { distanceModel := m, rolloffFactor := ro } input #[] movingParams
  let exp := (List.range 8).map fun i =>
    let p := mvPos i
    let azv := rAzimuth p
    let g := rEqual azv nch
    let dg := rDist m ro p
    let l := sl[i]!
    let r := if nch == 1 then l else sr[i]!
    if nch == 1 then (l * g.1 * dg, r * g.2 * dg)
    else if azv ≤ 0.0 then ((l + r * g.1) * dg, r * g.2 * dg)
    else (l * g.1 * dg, (r + l * g.2) * dg)
  approxL o[0]!.toList (exp.map (·.1)) && approxL o[1]!.toList (exp.map (·.2))
#guard movingRow .inverse 1.0 1
#guard movingRow .inverse 1.0 2
#guard movingRow .exponential 1.5 1
#guard movingRow .exponential 1.5 2
#guard movingRow .linear 1.0 1
#guard movingRow .linear 1.0 2

-- The block path and the frame path give the same values: constant arrays of one value against
-- the same values given as `n` frames (the listener too).
private def sameOut (a b : Block) : Bool :=
  a.size == b.size && (List.zip a.toList b.toList).all fun (x, y) => x.toList == y.toList
private def coneAll : Settings :=
  { distanceModel := .inverse, rolloffFactor := 0.7, coneInnerAngle := 60.0,
    coneOuterAngle := 200.0, coneOuterGain := 0.2, refDistance := 2.0 }
private def inp4 : Block := #[ch [1.0, -2.0, 0.5, 3.0], ch [0.25, 4.0, -1.0, 2.0]]
private def pk : Array FloatArray :=
  #[ch [3.0], ch [-2.0], ch [5.0], ch [0.3], ch [-0.6], ch [0.9]]
private def pf : Array FloatArray := pk.map fun a => ch [a.get! 0, a.get! 0, a.get! 0, a.get! 0]
private def lk : Block := #[ch [0.5], ch [0.1], ch [-0.4], ch [1.0], ch [0.2], ch [-1.0], ch [0.0],
  ch [1.0], ch [0.3]]
private def lf4 : Block := lk.map fun a => ch [a.get! 0, a.get! 0, a.get! 0, a.get! 0]
#guard !(isConst 4 (ch [1.0, 1.0, 1.0, 2.0]))
#guard isConst 4 (ch [1.0, 1.0, 1.0, 1.0]) && isConst 4 (ch [7.0]) && isConst 4 (ch [])
#guard sameOut (process 4 coneAll inp4 lk pk) (process 4 coneAll inp4 lf4 pf)
#guard sameOut (process 4 coneAll inp4 lk pk) (process 4 coneAll inp4 lf4 pk)
#guard sameOut (process 4 coneAll inp4 lk pk) (process 4 coneAll inp4 lk pf)
#guard sameOut (process 4 coneAll #[inp4[0]!] lk pk) (process 4 coneAll #[inp4[0]!] lf4 pf)
-- the output is not trivial: the cone and distance gains are below 1 here
#guard (process 4 coneAll inp4 lk pk)[0]!.get! 0 != (process 4 {} inp4 lk pk)[0]!.get! 0
-- absent listener and parameter channels read as the defaults
#guard sameOut (process 4 {} inp4 #[] #[])
  (process 4 {} inp4
    #[ch [0.0], ch [0.0], ch [0.0], ch [0.0], ch [0.0], ch [-1.0], ch [0.0], ch [1.0], ch [0.0]]
    #[ch [0.0], ch [0.0], ch [0.0], ch [1.0], ch [0.0], ch [0.0]])
-- an empty input gives silence of 2 channels; more than 2 channels use the first two
#guard sameOut (process 3 {} #[] #[] #[]) #[ch [0.0, 0.0, 0.0], ch [0.0, 0.0, 0.0]]
#guard sameOut (process 4 {} #[inp4[0]!, inp4[1]!, ch [9.0, 9.0, 9.0, 9.0]] #[] #[])
  (process 4 {} inp4 #[] #[])
-- default settings, source at the listener's position: azimuth 0, distance 0, gain 1:
-- a mono input of 1 gives cos and sin of 45 degrees
#guard approxL (process 1 {} #[ch [1.0]] #[] #[])[0]!.toList [0.7071067811865476]
-- n = 0
#guard (process 0 {} inp4 #[] #[]).size == 2

end Tests

end L4Factoidal.WebAudio.Panner
