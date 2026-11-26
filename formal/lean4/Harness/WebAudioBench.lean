import L4Factoidal.WebAudio.Context

/-!
Harness/WebAudioBench: time of one render quantum of three graphs (issue
https://github.com/danbri/factoidal-core/issues/1169, stage B performance). Run: `lake exe webaudio-bench`.
Prints milliseconds per quantum (median of 5 runs) and a checksum of the output bits.
(a) one sine oscillator into the destination; (b) one `AudioBufferSourceNode` (1 s stereo buffer)
through a gain; (c) a graph with the shape of the sound of `labs/demos/foafnaut/pages/particle-rex.html`.
-/
open L4Factoidal.WebAudio

def ex {α : Type} (r : Except Context.Error α) : IO α :=
  match r with
  | .ok a => pure a
  | .error _ => throw (IO.userError "context call failed")

def sr : Float := 48000.0

def newCtx : IO Context.OfflineContext := ex (Context.OfflineContext.new 2 1000000 sr)

def graphA : IO Context.OfflineContext := do
  let c ← newCtx
  let (c, o) ← ex c.createOscillator
  let c ← ex (c.connect o 0 0 0)
  ex (c.start o 0.0)

def graphB : IO Context.OfflineContext := do
  let c ← newCtx
  let (c, s) ← ex c.createBufferSource
  let (c, g) ← ex c.createGain
  let buf ← ex (c.createBuffer 2 48000 sr)
  let mk (k : Nat) : FloatArray := Id.run do
    let mut a := FloatArray.emptyWithCapacity 48000
    for i in [0:48000] do
      a := a.push (Float.sin (6.283185307179586 * (220.0 + k.toFloat * 110.0) * i.toFloat / 48000.0))
    return a
  let buf := { buf with data := #[mk 0, mk 1] }
  let c ← ex (c.setBuffer s (some buf))
  let c ← ex (c.setLoop s true)
  let c ← ex (c.connect s 0 g 0)
  let c ← ex (c.connect g 0 0 0)
  ex (c.startBuffer s)

/-- Shape of the Particle Rex sound: master gain, feedback delay with wet gain, pad of three
oscillators through gains and a lowpass, three tone oscillators with gain automation. -/
def graphC : IO Context.OfflineContext := do
  let c ← newCtx
  let (c, master) ← ex c.createGain
  let c ← ex (c.setParamValue master 0 0.7)
  let c ← ex (c.connect master 0 0 0)
  let (c, dly) ← ex (c.createDelay 1.0)
  let c ← ex (c.setParamValue dly 0 0.32)
  let (c, fb) ← ex c.createGain
  let c ← ex (c.setParamValue fb 0 0.4)
  let c ← ex (c.connect dly 0 fb 0)
  let c ← ex (c.connect fb 0 dly 0)
  let (c, wet) ← ex c.createGain
  let c ← ex (c.setParamValue wet 0 0.45)
  let c ← ex (c.connect dly 0 wet 0)
  let c ← ex (c.connect wet 0 master 0)
  let (c, pad) ← ex c.createGain
  let c ← ex (c.setParamValue pad 0 0.0)
  let (c, lp) ← ex c.createBiquadFilter
  let c ← ex (c.setParamValue lp 0 650.0)
  let c ← ex (c.connect pad 0 lp 0)
  let c ← ex (c.connect lp 0 master 0)
  let mut c := c
  let types := [Oscillator.OscType.sine, .sine, .triangle]
  let mults := [1.0, 1.5, 2.005]
  let gains := [0.05, 0.03, 0.018]
  for i in [0:3] do
    let (c', o) ← ex c.createOscillator
    let (c', g) ← ex c'.createGain
    c := c'
    c ← ex (c.setOscillatorType o (types.getD i .sine))
    c ← ex (c.setParamValue o 0 (110.0 * mults.getD i 1.0))
    c ← ex (c.setParamValue g 0 (gains.getD i 0.0))
    c ← ex (c.connect o 0 g 0)
    c ← ex (c.connect g 0 pad 0)
    c ← ex (c.start o 0.0)
    c ← ex (c.setTargetAtTime o 0 (55.0 * mults.getD i 1.0) 0.0 0.8)
  c ← ex (c.setTargetAtTime pad 0 1.0 0.0 1.2)
  let tones : List (Oscillator.OscType × Float × Float × Float × Float × Float) :=
    [(.sine, 600.0, 0.3, 0.1, 0.0, 0.0), (.square, 520.0, 0.1, 0.045, 760.0, 0.05),
     (.sawtooth, 110.0, 0.5, 0.2, 28.0, 0.1)]
  for (ty, f, d, v, f2, t) in tones do
    let (c', o) ← ex c.createOscillator
    let (c', g) ← ex c'.createGain
    c := c'
    c ← ex (c.setOscillatorType o ty)
    c ← ex (c.setValueAtTime o 0 f t)
    if f2 > 0.0 then c ← ex (c.exponentialRampToValueAtTime o 0 f2 (t + d))
    c ← ex (c.setValueAtTime g 0 0.0001 t)
    c ← ex (c.linearRampToValueAtTime g 0 v (t + 0.01))
    c ← ex (c.exponentialRampToValueAtTime g 0 0.0001 (t + d))
    c ← ex (c.connect o 0 g 0)
    c ← ex (c.connect g 0 master 0)
    c ← ex (c.connect g 0 dly 0)
    c ← ex (c.start o t)
    c ← ex (c.stop o (t + d + 0.05))
  return c

def checksum (acc : UInt64) (b : Array FloatArray) : UInt64 := Id.run do
  let mut h := acc
  for ch in b do
    for x in ch.data do
      h := (h ^^^ x.toFloat32.toFloat.toBits) * 1099511628211
  return h

def run (c : Context.OfflineContext) (quanta : Nat) : IO (Float × UInt64) := do
  let pl := Render.Plan.of c.state.graph
  let mut st := c.state
  let mut h : UInt64 := 14695981039346656037
  let t0 ← IO.monoNanosNow
  for _ in [0:quanta] do
    let r := Render.renderQuantumWith st pl
    st := r.1
    h := checksum h r.2
  let t1 ← IO.monoNanosNow
  return ((t1 - t0).toFloat / 1.0e6 / quanta.toFloat, h)

def median (xs : Array Float) : Float :=
  let s := xs.qsort (· < ·)
  s.getD (s.size / 2) 0.0

def bench (name : String) (mk : IO Context.OfflineContext) (quanta : Nat) : IO Unit := do
  let c ← mk
  let mut ts : Array Float := #[]
  let mut h : UInt64 := 0
  for _ in [0:5] do
    let (t, h') ← run c quanta
    ts := ts.push t
    h := h'
  IO.println s!"{name}: {median ts} ms/quantum (median of 5, {quanta} quanta) checksum {h}"

def main : IO Unit := do
  bench "a oscillator" graphA 300
  bench "b buffer-gain" graphB 300
  bench "c particle-rex" graphC 300
