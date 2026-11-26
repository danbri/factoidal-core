import L4Factoidal.WebAudio.Ring

/-!
tests/audio/RingReplay: replays a trace of the C ring (tests/audio/ring_trace.c, capacity 7, one
channel) through the Lean model `L4Factoidal.WebAudio.Ring` and exits 1 at the first difference.

  lake env lean --run tests/audio/RingReplay.lean TRACE      (from formal/lean4)

Lines: `w K TAKEN` and `r K GAVE SILENT UNDERRUN`.
-/
open L4Factoidal.WebAudio.Ring

def parseNat (s : String) : Option Nat := s.toNat?

def fail (n : Nat) (line msg : String) : IO UInt32 := do
  IO.eprintln s!"ring-replay: line {n}: {msg}: {line}"
  return 1

def replay (lines : Array String) : IO UInt32 := do
  let mut s := State.empty 7
  let mut n := 0
  for line in lines do
    n := n + 1
    if line.isEmpty then continue
    match (line.splitOn " ").map parseNat with
    | [none, some k, some taken] =>
      -- The tag is the first field, which is not a number: re-read it as a string.
      if (line.splitOn " ").head! != "w" then return ← fail n line "bad tag"
      let (s', t) := write s k
      if t != taken then return ← fail n line s!"the model took {t}"
      s := s'
    | [none, some k, some gave, some silent, some under] =>
      if (line.splitOn " ").head! != "r" then return ← fail n line "bad tag"
      let r := read s k
      if r.frames.length != gave then return ← fail n line s!"the model gave {r.frames.length}"
      if r.silence != silent then return ← fail n line s!"the model gave silence {r.silence}"
      if r.state.underruns - s.underruns != under then return ← fail n line "under-run count differs"
      -- The frames the model gave are the next frames in order.
      if r.frames != List.range' s.read gave then return ← fail n line "frames out of order"
      s := r.state
    | _ => return ← fail n line "cannot parse"
  if !(s.read ≤ s.written ∧ s.written ≤ s.read + s.capacity) then
    return ← fail n "" "invariant broken"
  IO.println s!"ring-replay: {n} operations replayed, the model agrees (final: written {s.written}, read {s.read}, under-runs {s.underruns}, silent {s.silent})"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let text ← IO.FS.readFile path
    replay (text.splitOn "\n").toArray
  | _ =>
    IO.eprintln "usage: RingReplay TRACE"
    return 2
