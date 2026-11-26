/-
L4Factoidal.Media.Bench: `lake exe media-bench`, from `formal/lean4`
(record: docs/designissues/2026-11-08-media-wasmvm.md).

    media-bench test                        container tests (no decoder modules needed)
    media-bench audio WASMDIR FILE [OUT]    decode the audio of an Ogg, WebM or MP3 file in
                                            WasmVM; OUT gets a WAV file and OUT.s16 the
                                            raw samples
    media-bench video WASMDIR FILE [N] [OUT]  decode N VP8 frames (default all) of a
                                            WebM file in WasmVM; OUT.ppm gets the first
                                            picture, OUT.i420 the packed I420 of all
    media-bench play WASMDIR FILE           decode, write a WAV file to the temporary
                                            folder and play it with `afplay` (macOS):
                                            the PCM is ours, `afplay` only plays it

    media-bench decode WASMDIR FILE RATE [OUT]  WebAudio.decodeAudioData: sniff, decode to
                                            floats, resample to RATE Hz ("file": the file's own
                                            rate), print channels, rate, frames and the first
                                            samples; OUT gets interleaved 32-bit float samples
                                            (little-endian, as `ffmpeg -f f32le`)

    media-bench check WASMDIR               the pins of `Media.Modules`: size, SHA-256, and
                                            the `mw_abi` version of each module run in WasmVM

WASMDIR holds `opus-wasmvm.wasm`, `vorbis-wasmvm.wasm`, `vp8-wasmvm.wasm` and
`mp3-wasmvm.wasm` from `danbri/factoidal-builds` (`third_party/media-decoders`), fetched by
`tools/fetch-media-decoders.sh`. A module whose bytes are not the pinned ones is refused;
`MEDIA_ANY_MODULE=1` uses it with a warning (to compare a rebuild, never for a result).
-/
import L4Factoidal.Media.Decode
import L4Factoidal.Media.Modules
import L4Factoidal.Media.Tests
import L4Factoidal.WebAudio.Decode

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

/-- A module's bytes after the pin check of `Media.Modules` (size and SHA-256). With
`MEDIA_ANY_MODULE=1` in the environment a module that is not the pinned one is used, with a
warning on standard error. -/
def readModule (dir : System.FilePath) (file : String) : IO ByteArray := do
  let b ← IO.FS.readBinFile (dir / file)
  match Modules.check file b with
  | .ok _ => return b
  | .error e =>
    if (← IO.getEnv "MEDIA_ANY_MODULE") == some "1" then
      IO.eprintln s!"warning: {e}; used because MEDIA_ANY_MODULE=1"
      return b
    throw (IO.userError s!"{e}; MEDIA_ANY_MODULE=1 uses it anyway")

/-- `media-bench check`: every pin, with the interface version the module itself reports. -/
def checkPins (dir : System.FilePath) : IO UInt32 := do
  let mut bad := 0
  for p in Modules.pins do
    let b ← IO.FS.readBinFile (dir / p.file)
    match Modules.check p.file b with
    | .error e =>
      IO.println s!"FAIL {e}"
      bad := bad + 1
    | .ok _ =>
      let m ← Decode.load b
      let (_, abi) ← m.callI32 "mw_abi" #[]
      if abi == p.abi then
        IO.println s!"ok   {p.file}: {p.bytes} bytes, SHA-256 {p.sha256}, mw_abi {abi}"
      else
        IO.println s!"FAIL {p.file}: mw_abi {abi}, pinned {p.abi}"
        bad := bad + 1
  IO.println s!"{Modules.pins.length - bad} of {Modules.pins.length} modules are the pinned ones ({Modules.source})"
  return (if bad == 0 then 0 else 1)

def decodeAudio (dir : System.FilePath) (file : String) : IO Decode.Pcm := do
  let b ← IO.FS.readBinFile file
  if file.endsWith ".mp3" then
    return (← Decode.mp3 (← readModule dir "mp3-wasmvm.wasm") b (← IO.ofExcept (Mp3.read b)))
  let opusW ← readModule dir "opus-wasmvm.wasm"
  let vorbisW ← readModule dir "vorbis-wasmvm.wasm"
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
  let w ← readModule dir "vp8-wasmvm.wasm"
  let r ← IO.ofExcept (WebM.demux (← IO.FS.readBinFile file))
  let some t := r.tracks.find? (·.codec == "V_VP8") | IO.println "no VP8 track"; return 1
  let fs := r.framesOf t.number
  let n := limit.getD fs.size
  let v ← Decode.vp8 w fs n out.isSome
  let k := v.pictures.size
  let fps := fun (ns : Nat) => if ns == 0 then 0 else k.toFloat * 1e9 / ns.toFloat
  IO.println s!"{file}: VP8 {t.width}x{t.height}, {fs.size} frames; {k} pictures decoded"
  IO.println s!"  decode: {ms v.decodeNs} ms, {v.decodeSteps / max 1 k} instructions a frame ({mips v.decodeSteps v.decodeNs} million per second), {fmt2 (fps v.decodeNs)} frames per second"
  WasmVM.Bench.Sample.report "VP8 decode"
  IO.println s!"  I420 copy out of WasmVM: {ms v.copyNs} ms; I420 to RGBA in Lean: {ms v.convertNs} ms"
  IO.println s!"  the module's own RGBA of the first picture is the same as Lean's: {v.crossCheck}"
  IO.println s!"  decode, copy and convert: {fmt2 (fps (v.decodeNs + v.copyNs + v.convertNs))} frames per second"
  if let some o := out then
    if let some p := v.pictures[0]? then IO.FS.writeBinFile (o ++ ".ppm") (ppm p)
    IO.FS.writeBinFile (o ++ ".i420") (v.i420.foldl (· ++ ·) .empty)
    IO.println s!"  wrote {o}.ppm and {o}.i420"
  return 0

/-- Interleaved little-endian binary32 samples of a buffer. -/
def interleaveF32 (b : WebAudio.Buffer.AudioBuffer) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.length * b.numberOfChannels * 4)
  for i in [0:b.length] do
    for c in [0:b.numberOfChannels] do
      let bits := (b.data[c]!.get! i).toFloat32.toBits
      out := out.push bits.toUInt8 |>.push (bits >>> 8).toUInt8 |>.push (bits >>> 16).toUInt8
        |>.push (bits >>> 24).toUInt8
  return out

def decodeCmd (dir : System.FilePath) (file rate : String) (out : Option String) : IO UInt32 := do
  let b ← IO.FS.readBinFile file
  let mut mods : List (String × ByteArray) := []
  for p in Modules.pins do
    if ← (dir / p.file).pathExists then mods := (p.file, ← IO.FS.readBinFile (dir / p.file)) :: mods
  let modules := fun (n : String) => (mods.find? (·.1 == n)).map (·.2)
  let ctx ← match rate with
    | "file" =>
      match ← WebAudio.Decode.decodeRaw b modules with
      | .ok r => pure r.rate.toFloat
      | .error e => IO.println s!"{file}: {e.name}: {e.detail}"; return 1
    | r => match r.toNat? with
      | some n => pure n.toFloat
      | none => IO.eprintln s!"RATE is a number or \"file\": {r}"; return 2
  let t0 ← IO.monoNanosNow
  let res ← WebAudio.Decode.decode b ctx modules
  let t1 ← IO.monoNanosNow
  match res with
  | .error e =>
    IO.println s!"{file}: {e.name}: {e.detail}"
    return 1
  | .ok d =>
    let ab := d.buffer
    IO.println s!"{file}: {d.format}, file {d.sourceRate} Hz {d.sourceFrames} frames -> buffer {ab.numberOfChannels} channels, {ab.sampleRate} Hz, {ab.length} frames, {fmt2 ab.duration} s; {ms (t1 - t0)} ms; {d.nanReplaced} non-finite samples replaced"
    let first := (List.range (min 8 ab.length)).map fun i => ab.data[0]!.get! i
    IO.println s!"  channel 0, first samples: {first}"
    let mid := ab.length / 2
    let m := (List.range (min 4 (ab.length - mid))).map fun i => ab.data[0]!.get! (mid + i)
    IO.println s!"  channel 0 from frame {mid}: {m}"
    if let some o := out then
      IO.FS.writeBinFile o (interleaveF32 ab)
      IO.println s!"  wrote {o} ({ab.length * ab.numberOfChannels * 4} bytes, interleaved f32le)"
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["test"] => return (if (← Tests.run) then 0 else 1)
  | ["check", d] => checkPins d
  | ["audio", d, f] => audio d f none
  | ["audio", d, f, o] => audio d f (some o)
  | ["decode", d, f, r] => decodeCmd d f r none
  | ["decode", d, f, r, o] => decodeCmd d f r (some o)
  | ["play", d, f] => play d f
  | ["video", d, f] => video d f none none
  | ["video", d, f, n] => video d f n.toNat? none
  | ["video", d, f, n, o] => video d f n.toNat? (some o)
  | _ =>
    IO.println "usage: media-bench test | check WASMDIR | decode WASMDIR FILE RATE [OUT] | audio WASMDIR FILE [OUT] | play WASMDIR FILE | video WASMDIR FILE [N] [OUT]"
    return 2

end L4Factoidal.Media.Bench

def main (args : List String) : IO UInt32 := L4Factoidal.Media.Bench.main args
