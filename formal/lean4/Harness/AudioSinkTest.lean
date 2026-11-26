import L4Factoidal.WebAudio.Sink

/-!
Harness/AudioSinkTest: the audio sink (`ffi/audio_sink.c`, `WebAudio/Sink.lean`) against a WAV file
and the clock (issue https://github.com/danbri/factoidal-core/issues/1169, stage D1). Run by
`tests/audio/run.sh`: `lake exe audio-sink-test`.

Checks: refusals of bad arguments; all-or-nothing writes; pause; one second of a 440 Hz sine
written in render quanta of 128 frames through `wav:PATH` at 48,000 Hz, 2 channels, capacity 8192:
every frame of the file bit-equal to the binary32 rounding of the binary64 value written, in
order, after leading silence; no under-run after the first write while the writer is running; the
time to play all frames 1 s within 15 %. The same run through `null` checks the counters.
Prints `audio-sink: N pass, M fail (out of T)`; exit code 1 on a failure.
-/
open L4Factoidal.WebAudio

structure Tally where
  pass : IO.Ref Nat
  fail : IO.Ref Nat

def check (t : Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then t.pass.modify (· + 1)
  else do
    t.fail.modify (· + 1)
    IO.println s!"FAIL {name} {detail}"

/-- True when `act` fails with a message that contains `needle`. -/
def refuses (act : IO Sink.Sink) (needle : String) : IO (Bool × String) := do
  try
    let s ← act
    Sink.close s
    return (false, "opened")
  catch e =>
    let m := toString e
    return ((m.splitOn needle).length > 1, m)

def pi : Float := 3.14159265358979323846

/-- Frame `n` of the test signal: left `sin`, right half of it. -/
def sample (n : Nat) : Float × Float :=
  let v := Float.sin (2.0 * pi * 440.0 * n.toFloat / 48000.0)
  (v, 0.5 * v)

def quantum (start : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity 256
  for j in [0:128] do
    let (l, r) := sample (start + j)
    a := (a.push l).push r
  return a

def ms (n : Nat) : UInt32 := n.toUInt32

/-- Write one second of sine (375 quanta). Answers (elapsed ms from first write until every frame
was read, counters after the first write, counters when the last quantum was written, counters at
the end). -/
def playSecond (s : Sink.Sink) : IO (Nat × FloatArray × FloatArray × FloatArray) := do
  let mut first : Option FloatArray := none
  let mut t0 := 0
  for q in [0:375] do
    let data := quantum (q * 128)
    -- Wait until the ring has room: the outside event is the consumer taking frames.
    let mut taken ← Sink.write s data
    let mut spins := 0
    while taken == 0 && spins < 5000 do
      IO.sleep 1
      taken ← Sink.write s data
      spins := spins + 1
    if taken != 128 then throw (IO.userError s!"write of quantum {q} took {taken} frames")
    if first.isNone then
      t0 ← IO.monoMsNow
      first := some (← Sink.counters s)
  let atLast ← Sink.counters s
  -- Wait for the consumer to take every written frame (outside event: the consumer thread).
  let mut c ← Sink.counters s
  let mut spins := 0
  while c[1]! < c[0]! && spins < 5000 do
    IO.sleep 1
    c ← Sink.counters s
    spins := spins + 1
  let t1 ← IO.monoMsNow
  return (t1 - t0, first.getD c, atLast, c)

def u32le (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8) ||| (b[i+2]!.toUInt32 <<< 16) ||| (b[i+3]!.toUInt32 <<< 24)

def u16le (b : ByteArray) (i : Nat) : UInt32 := b[i]!.toUInt32 ||| (b[i+1]!.toUInt32 <<< 8)

def tag (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat b[i+k]!.toNat)

def main : IO UInt32 := do
  let t : Tally := ⟨← IO.mkRef 0, ← IO.mkRef 0⟩
  let tmp := (← IO.getEnv "AUDIO_TEST_DIR").getD "/tmp"
  -- Refusals.
  let (ok, m) ← refuses (Sink.«open» "bogus" 48000.0 2 8192) "bad audio sink spec"
  check t "open bogus refused" ok m
  let (ok, m) ← refuses (Sink.«open» "null" 1000.0 2 8192) "sample rate"
  check t "rate 1000 refused" ok m
  let (ok, m) ← refuses (Sink.«open» "null" 48000.0 0 8192) "channels"
  check t "channels 0 refused" ok m
  let (ok, m) ← refuses (Sink.«open» "null" 48000.0 33 8192) "channels"
  check t "channels 33 refused" ok m
  let (ok, m) ← refuses (Sink.«open» "null" 48000.0 2 100) "capacity"
  check t "capacity 100 refused" ok m
  let (ok, m) ← refuses (Sink.«open» "wav:/nonexistent-dir-l4/x.wav" 48000.0 2 8192) "not writable"
  check t "unwritable file refused" ok m
  let (ok, m) ← refuses (Sink.«open» "coreaudio" 48000.0 2 8192) "CoreAudio"
  check t "coreaudio refused in this build" ok m
  let di ← Sink.deviceInfo "null"
  check t "deviceInfo size" (di.size == 2) s!"{di.size}"
  check t "deviceInfo channels" (di[1]! == 2.0)
  -- All or nothing, size checks, pause, close twice.
  let s ← Sink.«open» "null" 48000.0 2 256
  Sink.pause s true
  IO.sleep 20
  let c0 ← Sink.counters s
  check t "counters size" (c0.size == 8)
  check t "no under-run before the first write" (c0[2]! == 0.0)
  check t "counters rate, channels, capacity" (c0[5]! == 48000.0 && c0[6]! == 2.0 && c0[7]! == 256.0)
  let n1 ← Sink.write s (FloatArray.mk (Array.replicate 3 0.5))
  check t "size not a multiple of channels takes nothing" (n1 == 0) s!"{n1}"
  let n2 ← Sink.write s (FloatArray.mk (Array.replicate 400 0.5))
  check t "200 frames taken" (n2 == 200) s!"{n2}"
  let n3 ← Sink.write s (FloatArray.mk (Array.replicate 200 0.5))
  check t "100 frames into 56 free: nothing taken" (n3 == 0) s!"{n3}"
  let n4 ← Sink.write s (FloatArray.mk (Array.replicate 112 0.5))
  check t "56 frames taken" (n4 == 56) s!"{n4}"
  let n5 ← Sink.write s (FloatArray.mk (Array.replicate 2 0.5))
  check t "full ring takes nothing" (n5 == 0) s!"{n5}"
  IO.sleep 60
  let c1 ← Sink.counters s
  check t "paused: nothing read" (c1[1]! == 0.0 && c1[0]! == 256.0) s!"{c1}"
  check t "paused: no under-run counted" (c1[2]! == c0[2]!) s!"{c0[2]!} -> {c1[2]!}"
  Sink.pause s false
  let mut c2 ← Sink.counters s
  let mut spins := 0
  while c2[1]! < 256.0 && spins < 2000 do
    IO.sleep 1
    c2 ← Sink.counters s
    spins := spins + 1
  check t "resumed: all 256 frames read" (c2[1]! == 256.0) s!"{c2}"
  Sink.close s
  Sink.close s
  let n6 ← Sink.write s (FloatArray.mk (Array.replicate 2 0.5))
  check t "closed sink takes nothing" (n6 == 0)
  let c3 ← Sink.counters s
  check t "counters readable after close" (c3.size == 8)
  Sink.close s
  -- One second of sine through `null`: counters only.
  let sn ← Sink.«open» "null" 48000.0 2 8192
  IO.sleep 60
  let cIdle ← Sink.counters sn
  check t "null: no under-run and no frame taken before the first write" (cIdle[2]! == 0.0 && cIdle[1]! == 0.0)
    s!"{cIdle}"
  let (el, firstN, atLast, cEnd) ← playSecond sn
  check t "null: no under-run at the first write" (firstN[2]! == 0.0) s!"{firstN[2]!}"
  Sink.close sn
  check t "null: all frames written" (cEnd[0]! == 48000.0) s!"{cEnd[0]!}"
  check t "null: all frames read" (cEnd[1]! == 48000.0) s!"{cEnd[1]!}"
  check t "null: elapsed 1 s +- 15 %" (el ≥ 850 && el ≤ 1150) s!"{el} ms"
  IO.println s!"audio-sink null: elapsed {el} ms, underruns at last write {atLast[2]!}, at end {cEnd[2]!}"
  -- One second of sine through `wav`: the file.
  let path := s!"{tmp}/audio-sink-test-{← IO.monoNanosNow}.wav"
  let sw ← Sink.«open» s!"wav:{path}" 48000.0 2 8192
  IO.sleep 30
  let (el, first, atLast, cEnd) ← playSecond sw
  Sink.close sw
  Sink.close sw
  check t "wav: all frames read" (cEnd[1]! == 48000.0 && cEnd[0]! == 48000.0) s!"{cEnd}"
  check t "wav: elapsed 1 s +- 15 %" (el ≥ 850 && el ≤ 1150) s!"{el} ms"
  -- No under-run from the first write until the last quantum was written; one more at the end
  -- (the last period holds 128 frames and 128 of silence).
  check t "wav: no under-run from open until the last quantum was written" (atLast[2]! == 0.0) s!"{atLast[2]!}"
  check t "wav: no under-run after the first write, while writing" (atLast[2]! == first[2]!)
    s!"{first[2]!} -> {atLast[2]!}"
  check t "wav: at most one under-run at the end" (cEnd[2]! - first[2]! ≤ 1.0) s!"{first[2]!} -> {cEnd[2]!}"
  let b ← IO.FS.readBinFile path
  IO.FS.removeFile path
  check t "wav: header tags" (tag b 0 == "RIFF" && tag b 8 == "WAVE" && tag b 12 == "fmt " && tag b 38 == "fact" &&
    tag b 50 == "data") (tag b 0)
  check t "wav: format 3, 2 channels, 48000 Hz, 32 bits"
    (u16le b 20 == 3 && u16le b 22 == 2 && u32le b 24 == 48000 && u16le b 34 == 32)
  let dataBytes := (u32le b 54).toNat
  check t "wav: data size matches the file" (dataBytes + 58 == b.size && u32le b 4 == (dataBytes + 50).toUInt32)
    s!"data {dataBytes}, file {b.size}"
  let frames := dataBytes / 8
  check t "wav: fact frames" ((u32le b 46).toNat == frames)
  let bits (i : Nat) : UInt32 := u32le b (58 + 4 * i)
  -- Leading silence: the first sample is (0, 0), so frames before the first non-zero one are all
  -- zero and the first written frame is the last of them.
  let mut lead := 0
  while lead < frames && bits (2 * lead) == 0 && bits (2 * lead + 1) == 0 do
    lead := lead + 1
  let start := if lead == 0 then 0 else lead - 1
  let mut bad := 0
  let mut firstBad := 0
  for n in [0:48000] do
    let (l, r) := sample n
    let i := start + n
    if i < frames then
      if bits (2 * i) != l.toFloat32.toBits || bits (2 * i + 1) != r.toFloat32.toBits then
        if bad == 0 then firstBad := n
        bad := bad + 1
    else
      bad := bad + 1
  check t "wav: 48000 frames bit-equal to binary32 of the written values, in order" (bad == 0)
    s!"{bad} differ, first at {firstBad}; lead {lead}"
  let mut tailBad := 0
  for i in [start + 48000:frames] do
    if bits (2 * i) != 0 || bits (2 * i + 1) != 0 then tailBad := tailBad + 1
  check t "wav: only silence after the last frame" (tailBad == 0 && frames - (start + 48000) ≤ 256)
    s!"{tailBad} not silent; {frames} frames, start {start}"
  IO.println s!"audio-sink wav: {frames} frames in file, {start} of leading silence, {48000 - bad} of 48000 bit-equal, elapsed {el} ms, underruns {first[2]!} -> {atLast[2]!} (while writing) -> {cEnd[2]!}"
  let p ← t.pass.get
  let f ← t.fail.get
  IO.println s!"audio-sink: {p} pass, {f} fail (out of {p + f})"
  return (if f == 0 then 0 else 1)
