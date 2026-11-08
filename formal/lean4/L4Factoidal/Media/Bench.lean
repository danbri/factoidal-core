/-
L4Factoidal.Media.Bench: `lake exe media-bench`, from `formal/lean4`
(record: docs/designissues/2026-11-08-media-wasmvm.md).

    media-bench test                        container tests (no decoder modules needed)
    media-bench audio WASMDIR FILE [OUT]    decode the audio of an Ogg or WebM file in
                                            WasmVM; OUT gets a WAV file and OUT.s16 the
                                            raw samples
    media-bench video WASMDIR FILE [N] [OUT]  decode N VP8 frames (default all) of a
                                            WebM file in WasmVM; OUT.ppm gets the first
                                            picture, OUT.i420 the packed I420 of all
    media-bench play WASMDIR FILE           decode, write a WAV file to the temporary
                                            folder and play it with `afplay` (macOS):
                                            the PCM is ours, `afplay` only plays it

WASMDIR holds `opus-wasmvm.wasm`, `vorbis-wasmvm.wasm` and `vp8-wasmvm.wasm` from
`tools/wasmvm/build-media.sh`.
-/
import L4Factoidal.Media.Decode
import L4Factoidal.Media.Tests

namespace L4Factoidal.Media.Bench
open L4Factoidal.Media

def isWebM (b : ByteArray) : Bool :=
  b.size ≥ 4 && b[0]! == 0x1A && b[1]! == 0x45 && b[2]! == 0xDF && b[3]! == 0xA3

def mips (steps ns : Nat) : Nat := if ns == 0 then 0 else steps * 1000 / ns

def ms (ns : Nat) : Nat := ns / 1000000

/-- `x` with two decimals. -/
def fmt2 (x : Float) : String :=
  let n := (x * 100).round.toUInt64.toNat
  s!"{n / 100}.{if n % 100 < 10 then "0" else ""}{n % 100}"

def decodeAudio (dir : System.FilePath) (file : String) : IO Decode.Pcm := do
  let opusW ← IO.FS.readBinFile (dir / "opus-wasmvm.wasm")
  let vorbisW ← IO.FS.readBinFile (dir / "vorbis-wasmvm.wasm")
  let b ← IO.FS.readBinFile file
  if isWebM b then Decode.webmAudio opusW vorbisW (← IO.ofExcept (WebM.demux b))
  else Decode.oggAudio opusW vorbisW b

def audio (dir : System.FilePath) (file : String) (out : Option String) : IO UInt32 := do
  let p ← decodeAudio dir file
  let secs := p.seconds
  let rtf := (p.ns.toFloat / 1e9) / secs
  IO.println s!"{file}: {p.packets} packets, {p.frames} samples per channel at {p.rate} Hz, {p.channels} channels, {fmt2 secs} s"
  IO.println s!"  decode in WasmVM: {ms p.ns} ms, {p.steps} instructions ({mips p.steps p.ns} million per second)"
  IO.println s!"  real-time factor (decode time / clip length): {fmt2 rtf}; {fmt2 (1 / rtf)} times real time"
  if let some o := out then
    IO.FS.writeBinFile o (Decode.wav p)
    IO.FS.writeBinFile (o ++ ".s16") p.samples
    IO.println s!"  wrote {o} and {o}.s16"
  return 0

def play (dir : System.FilePath) (file : String) : IO UInt32 := do
  let p ← decodeAudio dir file
  let tmp := (← IO.getEnv "TMPDIR").getD "/tmp"
  let o := System.FilePath.mk tmp / "media-bench-play.wav"
  IO.FS.writeBinFile o (Decode.wav p)
  IO.println s!"decoded in WasmVM in {ms p.ns} ms; playing {fmt2 p.seconds} s with afplay"
  let r ← IO.Process.output { cmd := "afplay", args := #[o.toString] }
  return r.exitCode

def ppm (p : Decode.Picture) : ByteArray := Id.run do
  let mut out := s!"P6\n{p.width} {p.height}\n255\n".toUTF8
  for i in [0:p.width * p.height] do
    out := out.push p.rgba[4*i]! |>.push p.rgba[4*i+1]! |>.push p.rgba[4*i+2]!
  return out

def video (dir : System.FilePath) (file : String) (limit : Option Nat) (out : Option String) : IO UInt32 := do
  let w ← IO.FS.readBinFile (dir / "vp8-wasmvm.wasm")
  let r ← IO.ofExcept (WebM.demux (← IO.FS.readBinFile file))
  let some t := r.tracks.find? (·.codec == "V_VP8") | IO.println "no VP8 track"; return 1
  let fs := r.framesOf t.number
  let n := limit.getD fs.size
  let v ← Decode.vp8 w fs n out.isSome
  let k := v.pictures.size
  let fps := fun (ns : Nat) => if ns == 0 then 0 else k.toFloat * 1e9 / ns.toFloat
  IO.println s!"{file}: VP8 {t.width}x{t.height}, {fs.size} frames; {k} pictures decoded"
  IO.println s!"  decode: {ms v.decodeNs} ms, {v.decodeSteps / max 1 k} instructions a frame ({mips v.decodeSteps v.decodeNs} million per second), {fmt2 (fps v.decodeNs)} frames per second"
  IO.println s!"  I420 copy out of WasmVM: {ms v.copyNs} ms; I420 to RGBA in Lean: {ms v.convertNs} ms"
  IO.println s!"  the module's own RGBA of the first picture is the same as Lean's: {v.crossCheck}"
  IO.println s!"  decode, copy and convert: {fmt2 (fps (v.decodeNs + v.copyNs + v.convertNs))} frames per second"
  if let some o := out then
    if let some p := v.pictures[0]? then IO.FS.writeBinFile (o ++ ".ppm") (ppm p)
    IO.FS.writeBinFile (o ++ ".i420") (v.i420.foldl (· ++ ·) .empty)
    IO.println s!"  wrote {o}.ppm and {o}.i420"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["test"] => return (if (← Tests.run) then 0 else 1)
  | ["audio", d, f] => audio d f none
  | ["audio", d, f, o] => audio d f (some o)
  | ["play", d, f] => play d f
  | ["video", d, f] => video d f none none
  | ["video", d, f, n] => video d f n.toNat? none
  | ["video", d, f, n, o] => video d f n.toNat? (some o)
  | _ =>
    IO.println "usage: media-bench test | audio WASMDIR FILE [OUT] | play WASMDIR FILE | video WASMDIR FILE [N] [OUT]"
    return 2

end L4Factoidal.Media.Bench

def main (args : List String) : IO UInt32 := L4Factoidal.Media.Bench.main args
