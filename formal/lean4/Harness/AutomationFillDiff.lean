import L4Factoidal.WebAudio.Automation

/-!
Harness/AutomationFillDiff: randomized differential test of `Automation.fill` (binary64, cursor)
against `Automation.fillSpec` (exact rationals), bit for bit (issue
https://github.com/danbri/factoidal-core/issues/1169, plan section 14). Run by `tests/audio/run.sh`:
`lake exe automation-fill-diff [cases [seed]]`; default 20000 cases, seed 20261126. Prints the
first difference with its event list and exits 1.

Each case: a timeline built with `Automation.insert` (so it is valid) from 0 to 9 operations of
any kind (including curves, which take the `fillSpec` route, and `cancelScheduledValues` and
`cancelAndHold`); times drawn on frame times of the sample rate, one ulp above or below them,
multiples of 1/8000, and random doubles; a random start frame, a quantum of 1 (k-rate), 32, 64,
128, 256 or 500; the sample rate 44,100 or 48,000 (rarely 8,000 or 0).
-/
open L4Factoidal.WebAudio
open L4Factoidal.WebAudio.Automation

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x * 2685821657736338717, ⟨x⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  ((x >>> 11).toNat % n, r)

def Rng.unit (r : Rng) : Float × Rng :=
  let (x, r) := r.next
  ((x >>> 11).toFloat / 9007199254740992.0, r)

def ulpUp (x : Float) : Float := Float.ofBits (x.toBits + 1)
def ulpDown (x : Float) : Float := if x.toBits == 0 then 0.0 else Float.ofBits (x.toBits - 1)

/-- A time: on a frame time, one ulp off it, a multiple of 1/8000, or random. -/
def drawTime (r : Rng) (sr : Float) : Float × Rng :=
  let (c, r) := r.below 6
  let (f, r) := r.below 3000
  let (u, r) := r.unit
  let ft := f.toFloat / sr
  match c with
  | 0 => (ft, r)
  | 1 => (ulpUp ft, r)
  | 2 => (ulpDown ft, r)
  | 3 => (f.toFloat / 8000.0, r)
  | 4 => (u * 0.05, r)
  | _ => (ft + 0.0025, r)

def drawValue (r : Rng) : Float × Rng :=
  let (c, r) := r.below 8
  let (u, r) := r.unit
  match c with
  | 0 => (0.0, r)
  | 1 => (0.0001, r)
  | 2 => (-0.0001, r)
  | 3 => (1.0, r)
  | 4 => (-1.0, r)
  | 5 => (u * 4.0 - 2.0, r)
  | 6 => (u * 1e-6, r)
  | _ => (u * 1000.0, r)

def kindName : Kind → String
  | .setValue => "setValue" | .linearRamp => "linear" | .exponentialRamp => "expo"
  | .setTarget tc => s!"target(tc={tc})"
  | .setValueCurve vs d _ => s!"curve({vs.size} values, d={timeToFloat d})"

def showTl (tl : Timeline) : String :=
  String.intercalate "; " (tl.events.map fun e => s!"{kindName e.kind}@{timeToFloat e.time}={e.value}")

/-- One random operation on the timeline. -/
def step (tl : Timeline) (r : Rng) (sr : Float) : Timeline × Rng :=
  let (op, r) := r.below 14
  let (t, r) := drawTime r sr
  let (v, r) := drawValue r
  let (tc, r) := r.below 4
  let tcF := [0.0, 0.0005, 0.002, 0.01].getD tc 0.0
  let (nv, r) := r.below 4
  let ins (k : Kind) : Timeline :=
    match ofDouble t with
    | none => tl
    | some q =>
      match insert tl ⟨k, q, v⟩ 0 1.0 with
      | .ok tl' => tl'
      | .error _ => tl
  match op with
  | 0 | 1 | 2 => (ins .setValue, r)
  | 3 | 4 | 5 => (ins .linearRamp, r)
  | 6 | 7 => (ins .exponentialRamp, r)
  | 8 | 9 | 10 => (ins (.setTarget tcF), r)
  | 11 =>
    (ins (.setValueCurve ((Array.range (nv + 2)).map (fun i => v * i.toFloat))
      ((ofDouble 0.004).getD 0) none), r)
  | 12 => (match ofDouble t with | some q => cancelScheduledValues tl q | none => tl, r)
  | _ => (match ofDouble t with | some q => cancelAndHold tl q 1.0 | none => tl, r)

def bitsEq (a b : Array Float) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => (a.getD i 0.0).toBits == (b.getD i 0.0).toBits

def oneCase (r : Rng) : Option String × Rng := Id.run do
  let (c, r) := r.below 20
  let sr : Float :=
    if c == 0 then 8000.0 else if c == 1 then 0.0 else if c < 11 then 44100.0 else 48000.0
  let (nev, r) := r.below 10
  let mut tl : Timeline := ⟨[]⟩
  let mut r := r
  for _ in [0:nev] do
    let (tl', r') := step tl r sr
    tl := tl'
    r := r'
  let (qi, r1) := r.below 8
  let n := [128, 128, 128, 64, 32, 256, 500, 1].getD qi 128
  let (fs, r2) := r1.below 3
  let (f0, r3) := r2.below 4000
  let startFrame := if fs == 0 then f0 else if fs == 1 then f0 * 3 else 0
  let (dv, r4) := drawValue r3
  let a := fill tl dv startFrame n sr
  let b := fillSpec tl dv startFrame n sr
  if bitsEq a b then return (none, r4)
  let bad := (List.range a.size).find? fun i => (a.getD i 0.0).toBits != (b.getD i 0.0).toBits
  let i := bad.getD 0
  return (some s!"DIFF default={dv} start={startFrame} n={n} sr={sr} frame {startFrame + i}: fill={a.getD i 0.0} spec={b.getD i 0.0}\n  events: {showTl tl}", r4)

def main (args : List String) : IO UInt32 := do
  let cases := (args.getD 0 "20000").toNat!
  let seed := (args.getD 1 "20261126").toNat!.toUInt64
  let mut r : Rng := ⟨seed ^^^ 88172645463325252⟩
  for k in [0:cases] do
    let (res, r') := oneCase r
    r := r'
    match res with
    | some msg =>
      IO.println s!"automation-fill-diff: FAIL at case {k} (seed {seed})\n{msg}"
      return 1
    | none => pure ()
  IO.println s!"automation-fill-diff: {cases} cases (seed {seed}), fill equals fillSpec bit for bit"
  return 0
