import L4Factoidal.WebAudio.Realtime

/-!
Harness/AudioRealtimeTest: a real-time `AudioContext` from the control side to the speaker file
(issue https://github.com/danbri/factoidal-core/issues/1169, step D3; plan
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 13.2 to 13.6). Run by
`tests/audio/run.sh`: `lake exe audio-realtime-test`.

Part 1. The ops a page's `AudioContext` makes (190, 176, 177, 181, 182, then 191 `close`) on the
control side (`Api.op`), moved to the rendering task by the engine's IO functions
(`Realtime.after`), the reports merged back (`Realtime.before`), through the `wav:PATH` sink at
48,000 Hz. Checks: the file's first 48,000 frames equal, bit for bit (binary32), the render of the
same ops by an `OfflineAudioContext` (op 187); the frames after them are 0; no under-run; the
source's `ended` event, then the state `closed` and the confirmed `close()` call reach the page.

Part 2. The autoplay rule (plan 13.7) through the `null` sink: a context made with no activation is
`suspended`; its `resume()` waits; `activate` (the engine's input step) sends it; the rendering side
confirms it and reports the state `running`.

Prints `audio-realtime: N pass, M fail (out of T)` and the measures; exit code 1 on a failure.
-/
open L4Factoidal L4Factoidal.WebAudio

structure Tally where
  pass : IO.Ref Nat
  fail : IO.Ref Nat

def check (t : Tally) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then t.pass.modify (· + 1)
  else do
    t.fail.modify (· + 1)
    IO.println s!"FAIL {name} {detail}"

def d (x : Float) : ByteArray := Api.f64le x
def n (k : Nat) : ByteArray := (toString k).toUTF8
def s (x : String) : ByteArray := x.toUTF8

/-- Run ops on the control side; the answers. A failed op is an error. -/
def ops (st : Api.State) (l : List (Nat × List ByteArray)) : Except String (Api.State × Array ByteArray) :=
  l.foldlM (init := (st, #[])) fun (st, outs) (c, fs) =>
    match Api.op st c fs.toArray with
    | (st', .ok out) => .ok (st', outs.push out)
    | (_, .error e) => .error s!"op {c} answered {e}"

def u32At (b : ByteArray) (i : Nat) : UInt32 := Api.u32At b i

/-- The page's graph: one 440 Hz sine oscillator into the destination, from 0 s to 1 s. -/
def graph (ctx : Nat) : List (Nat × List ByteArray) :=
  [(176, [n ctx, s "oscillator"]), (177, [n ctx, n 1, n 0, n 0, n 0, n 0]),
   (181, [n ctx, n 1, d 0.0]), (182, [n ctx, n 1, d 1.0])]

/-- Wait in steps of 5 ms (at most `limit` steps) until `done` holds of the merged state: the
reports of the rendering task are merged before each check, as before each page action. -/
def pump (tasks : Realtime.Tasks) (sid : Nat) (st : Api.State) (limit : Nat)
    (done : Api.State → Bool) : IO (Realtime.Tasks × Api.State × Bool) := do
  let mut tasks := tasks
  let mut st := st
  let mut ok := false
  let mut clock := 0
  for _ in [0:limit] do
    let (t, a) ← Realtime.before tasks sid st clock
    tasks := t
    st := a
    if done st then
      ok := true
      break
    IO.sleep 5
    clock := clock + 5
  return (tasks, st, ok)

def rtOf (st : Api.State) (id : Nat) : Api.Realtime := (st.realtime[id]?).getD default

def permit : Risk.Accepted .audioWithoutActivation := Risk.dangerouslyAccept .audioWithoutActivation

def part1 (t : Tally) (dir : String) : IO Unit := do
  let path := dir ++ "/realtime.wav"
  let dev : Api.State := { device := some (48000.0, 2), autoplay := some permit }
  -- An offline context first, as a page that renders offline before it plays: the real-time
  -- context is context 2 (its id is not 1 on either side).
  let .ok (st, outs) := ops dev ([(175, [n 2, n 100, d 48000.0]), (190, [s "interactive", ByteArray.empty, n 7])] ++ graph 2)
    | check t "control ops" false; return
  check t "context answer" (String.fromUTF8! outs[1]! == "2 48000 2 suspended") (String.fromUTF8! outs[1]!)
  let t0 ← IO.monoMsNow
  let (tasks, st) ← Realtime.after {} 1 s!"wav:{path}" st
  check t "task started" (tasks.size == 1)
  check t "outbox taken" ((rtOf st 2).outbox.isEmpty)
  -- Until the source has ended and 1.1 s are played.
  let (tasks, st, ended) ← pump tasks 1 st 600 fun a => (rtOf a 2).framesPlayed ≥ 52800
  let t1 ← IO.monoMsNow
  check t "plays 1.1 s" ended s!"framesPlayed {(rtOf st 2).framesPlayed}"
  let evs := (rtOf st 2).events.toList
  check t "ended event" (evs.contains (1, 1)) (toString evs)
  check t "state running reported" (evs.contains (2, 1)) (toString evs)
  check t "callback queued" (st.wakeups.contains 7)
  -- close()
  let .ok (st, outs) := ops st [(191, [n 2, s "close"])] | check t "close op" false; return
  let call := (String.fromUTF8! outs[0]!).toNat!
  let (tasks, st) ← Realtime.after tasks 1 "unused" st
  let (_, st, closed) ← pump tasks 1 st 400 fun a => (rtOf a 2).state == .closed
  check t "closed" closed
  let evs := (rtOf st 2).events.toList
  check t "close confirmed" (evs.contains (3, call) && evs.contains (2, 2)) (toString evs)
  let rt := rtOf st 2
  check t "no under-run" (rt.underruns == 0) s!"underruns {rt.underruns}"
  -- The task ends and closes the file: wait for it.
  for (_, h) in tasks.toList do let _ ← IO.wait h.task
  -- The offline render of the same ops.
  let .ok (off, outs) := ops {} ([(175, [n 2, n 48000, d 48000.0])] ++ graph 1 ++ [(187, [n 1])])
    | check t "offline ops" false; return
  let _ := off
  let r := outs[outs.size - 1]!
  check t "offline shape" (u32At r 0 == 2 && u32At r 4 == 48000)
  let wav ← IO.FS.readBinFile path
  let frames := (wav.size - 58) / 8
  check t "wav frames" (frames ≥ 52800) s!"frames {frames}"
  let mut diff := 0
  let mut firstDiff : Option Nat := none
  for i in [0:48000] do
    for c in [0:2] do
      let w := u32At wav (58 + 8 * i + 4 * c)
      let o := u32At r (8 + 4 * (48000 * c + i))
      if w != o then
        diff := diff + 1
        if firstDiff.isNone then firstDiff := some i
  check t "bit equal to offline render" (diff == 0) s!"{diff} values differ, first frame {firstDiff}"
  let mut loud := 0
  for i in [48000:frames] do
    for c in [0:2] do
      if u32At wav (58 + 8 * i + 4 * c) != 0 then loud := loud + 1
  check t "silence after stop" (loud == 0) s!"{loud} values"
  IO.println s!"audio-realtime measure: wall ms from handover to 1.1 s played {t1 - t0}; frames in file {frames}; underruns {rt.underruns}"

def part2 (t : Tally) : IO Unit := do
  let dev : Api.State := { device := some (48000.0, 2) }
  let .ok (st, outs) := ops dev [(190, [s "interactive", ByteArray.empty, n 9]), (191, [n 1, s "resume"])]
    | check t "part 2 ops" false; return
  check t "suspended without activation" (String.fromUTF8! outs[0]! == "1 48000 2 suspended")
  let call := (String.fromUTF8! outs[1]!).toNat!
  check t "resume waits" ((rtOf st 1).pendingResume.toList == [call])
  -- No page op gives activation; the engine's input step does.
  check t "op 196 is not a page op" ((match (Api.op st 196 #[]).2 with | .error e => e == -2 | .ok _ => false) && !(Api.op st 196 #[]).1.activated)
  let (tasks, st) ← Realtime.after {} 1 "null" st
  let (tasks, st, _) ← pump tasks 1 st 20 fun _ => false
  check t "no state change before activation" (!((rtOf st 1).events.toList.any (·.1 == 2)))
  let st := Api.activate st
  let (tasks, st) ← Realtime.after tasks 1 "null" st
  let (tasks, st, ok) ← pump tasks 1 st 400 fun a => (rtOf a 1).state == .running
  check t "running after activation" ok
  check t "resume confirmed" ((rtOf st 1).events.toList.contains (3, call)) (toString (rtOf st 1).events.toList)
  let .ok (st, _) := ops st [(191, [n 1, s "close"])] | check t "part 2 close" false; return
  let (tasks, st) ← Realtime.after tasks 1 "null" st
  let (tasks, _, closed) ← pump tasks 1 st 400 fun a => (rtOf a 1).state == .closed
  check t "part 2 closed" closed
  for (_, h) in tasks.toList do let _ ← IO.wait h.task

def main : IO UInt32 := do
  let t : Tally := { pass := ← IO.mkRef 0, fail := ← IO.mkRef 0 }
  let dir := (← IO.getEnv "AUDIO_TEST_DIR").getD "/tmp"
  if !(← Realtime.threadsAvailable) then
    IO.println "audio-realtime: no threads for dedicated tasks"; return 1
  part1 t dir
  part2 t
  let p ← t.pass.get
  let f ← t.fail.get
  IO.println s!"audio-realtime: {p} pass, {f} fail (out of {p + f})"
  return if f == 0 then 0 else 1
