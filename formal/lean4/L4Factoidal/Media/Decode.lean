/-
L4Factoidal.Media.Decode: audio and video decoders, compiled to WebAssembly, run in
the Lean WasmVM engine (record: docs/designissues/2026-11-08-media-wasmvm.md).

The modules come from `tools/wasmvm/build-media.sh` (libopus, libvorbis, libvpx's VP8
decoder; not in the repository). Their entry points are in `tools/wasmvm/media/`.
The containers are read in Lean (`Media.Ogg`, `Media.WebM`); a module gets one packet
or frame per call and gives PCM samples or a picture. The host browser's decoders
are not used.

Capabilities: the WASI host (`WasmVM.Wasi`) with nothing granted (no files, clock,
randomness, environment or output). The one other import,
`env.emscripten_notify_memory_growth`, does nothing.
-/
import L4Factoidal.WasmVM.WasiIO
import L4Factoidal.WasmVM.Bench.Sample
import L4Factoidal.Media.Ogg
import L4Factoidal.Media.WebM
import L4Factoidal.Media.Yuv

namespace L4Factoidal.Media.Decode
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Wasi

def caps : Caps IO := {}

def extraNames (mo nm : String) : Bool := mo == "env" && nm == "emscripten_notify_memory_growth"

def noExtra : String → String → Array Value → Store → IO (Store × HostResult) :=
  fun _ _ _ st => pure (st, .values #[])

/-- A loaded decoder module, a buffer in its memory for packets, and the
instructions and nanoseconds its calls have used. -/
structure Module where
  store : Store
  inst : Nat
  mem : Nat
  bindings : Array Binding
  buf : Nat := 0
  cap : Nat := 0
  steps : Nat := 0
  ns : Nat := 0

def budget : Budget := { fuel := 1000000000000 }

/-- Run export `name`, counting instructions; host calls go to the WASI host. -/
def Module.call (m : Module) (name : String) (args : Array Value) : IO (Module × Outcome) := do
  let ⟨st, inst, mem, bs, buf, cap, steps, ns⟩ := m
  match st.export? inst name with
  | some (.func fa) =>
    let t0 ← IO.monoNanosNow
    if ← WasmVM.Bench.Sample.enabled then
      let (st, o, n) ← WasmVM.Bench.Sample.runIO st fa args budget (host caps mem bs noExtra)
      let t1 ← IO.monoNanosNow
      return (⟨st, inst, mem, bs, buf, cap, steps + n, ns + (t1 - t0)⟩, o)
    let (st, o, n) := invokeSteps st fa args budget
    let mut st := st
    let mut o := o
    let mut total := n
    for _ in [0:1000000] do
      match o with
      | .hostCall id vs k =>
        let (st', r) ← host caps mem bs noExtra id vs st
        let (st'', o', n') := resumeSteps st' k r budget
        st := st''; o := o'; total := total + n'
      | _ => break
    let t1 ← IO.monoNanosNow
    return (⟨st, inst, mem, bs, buf, cap, steps + total, ns + (t1 - t0)⟩, o)
  | _ => return (⟨st, inst, mem, bs, buf, cap, steps, ns⟩, .trap (.host s!"no export {name}"))

def Module.callI32 (m : Module) (name : String) (args : Array Value) : IO (Module × Int) := do
  let (m, o) ← m.call name args
  match o with
  | .values #[.i32 v] => return (m, if v.toNat ≥ 2147483648 then (v.toNat : Int) - 4294967296 else v.toNat)
  | .values #[] => return (m, 0)
  | o => throw (IO.userError s!"{name}: {o.describe}")

def i32 (n : Nat) : Value := .i32 n.toUInt32

def Module.read (m : Module) (off n : Nat) : IO ByteArray :=
  match m.store.readMem m.mem off n with
  | .ok b => pure b
  | .error e => throw (IO.userError e)

def Module.write (m : Module) (off : Nat) (b : ByteArray) : IO Module := do
  let ⟨st, inst, mem, bs, buf, cap, steps, ns⟩ := m
  match st.writeMem mem off b with
  | .ok st => pure ⟨st, inst, mem, bs, buf, cap, steps, ns⟩
  | .error e => throw (IO.userError e)

/-- Load a module, run `_initialize`, and allocate a packet buffer. -/
def load (bytes : ByteArray) : IO Module := do
  let l ← match ← Wasi.load caps bytes {} extraNames noExtra with
    | .ok l => pure l
    | .error e => throw (IO.userError e)
  let m : Module := { store := l.store, inst := l.inst, mem := l.mem, bindings := l.bindings }
  let m ← match m.store.export? m.inst "_initialize" with
    | some _ => do let (m, _) ← m.callI32 "_initialize" #[]; pure m
    | none => pure m
  let (m, p) ← m.callI32 "mw_alloc" #[i32 65536]
  if p ≤ 0 then throw (IO.userError "mw_alloc gave 0")
  return { m with buf := p.toNat, cap := 65536 }

/-- Copy a packet into the module's buffer (a larger buffer when it does not fit). -/
def Module.put (m : Module) (b : ByteArray) : IO Module := do
  let m ← if b.size ≤ m.cap then pure m else do
    let (m, _) ← m.callI32 "mw_free" #[i32 m.buf]
    let (m, p) ← m.callI32 "mw_alloc" #[i32 b.size]
    if p ≤ 0 then throw (IO.userError "mw_alloc gave 0")
    pure { m with buf := p.toNat, cap := b.size }
  m.write m.buf b

/-! ## Audio -/

/-- Decoded audio: interleaved little-endian 16-bit samples. -/
structure Pcm where
  rate : Nat
  channels : Nat
  samples : ByteArray
  /-- Instructions and nanoseconds of the decode calls. -/
  steps : Nat
  ns : Nat
  packets : Nat

def Pcm.frames (p : Pcm) : Nat := p.samples.size / (2 * max 1 p.channels)
def Pcm.seconds (p : Pcm) : Float := p.frames.toFloat / p.rate.toFloat

/-- Decode Opus packets. `preSkip` samples (per channel, at 48 kHz) are dropped from
the start (RFC 7845 section 4.2); `total`, when given, is the number of samples to
keep after that (from the last granule position, section 4.4). -/
def opus (wasm : ByteArray) (channels preSkip : Nat) (packets : Array ByteArray) (total : Option Nat) :
    IO Pcm := do
  let mut m ← load wasm
  let (m', r) ← m.callI32 "mw_opus_init" #[i32 channels]
  m := m'
  if r != 0 then throw (IO.userError s!"mw_opus_init: {r}")
  let (m', pcm) ← m.callI32 "mw_pcm" #[]
  m := m'
  let s0 := m.steps
  let n0 := m.ns
  let mut out := ByteArray.emptyWithCapacity (packets.size * 960 * 2 * channels)
  for p in packets do
    m ← m.put p
    let (m', n) ← m.callI32 "mw_opus_decode" #[i32 m.buf, i32 p.size]
    m := m'
    if n < 0 then throw (IO.userError s!"mw_opus_decode: {n}")
    out := out ++ (← m.read pcm.toNat (n.toNat * 2 * channels))
  let frame := 2 * channels
  let start := min out.size (preSkip * frame)
  let stop := match total with
    | some t => min out.size (start + t * frame)
    | none => out.size
  return { rate := 48000, channels, samples := out.extract start stop, steps := m.steps - s0,
           ns := m.ns - n0, packets := packets.size }

/-- Decode Vorbis: three header packets, then audio packets. Two channels at most
are kept. -/
def vorbis (wasm : ByteArray) (headers packets : Array ByteArray) (total : Option Nat) : IO Pcm := do
  let mut m ← load wasm
  for i in [0:3] do
    let h := headers[i]?.getD .empty
    m ← m.put h
    let (m', r) ← m.callI32 "mw_vorbis_header" #[i32 m.buf, i32 h.size, i32 i]
    m := m'
    if r != 0 then throw (IO.userError s!"mw_vorbis_header {i}: {r}")
  let (m', rate) ← m.callI32 "mw_vorbis_rate" #[]
  let (m', ch) ← m'.callI32 "mw_vorbis_channels" #[]
  let (m', pcm) ← m'.callI32 "mw_pcm" #[]
  m := m'
  let channels := min 2 ch.toNat
  let s0 := m.steps
  let n0 := m.ns
  let mut out := ByteArray.empty
  for p in packets do
    m ← m.put p
    let (m', n) ← m.callI32 "mw_vorbis_decode" #[i32 m.buf, i32 p.size]
    m := m'
    if n < 0 then throw (IO.userError s!"mw_vorbis_decode: {n}")
    out := out ++ (← m.read pcm.toNat (n.toNat * 2 * channels))
  let stop := match total with
    | some t => min out.size (t * 2 * channels)
    | none => out.size
  return { rate := rate.toNat, channels, samples := out.extract 0 stop, steps := m.steps - s0,
           ns := m.ns - n0, packets := packets.size }

/-- A RIFF WAVE file of 16-bit PCM. -/
def wav (p : Pcm) : ByteArray :=
  let le16 := fun (v : Nat) => ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8]
  let ascii := fun (s : String) => s.toUTF8
  let n := p.samples.size
  ascii "RIFF" ++ le32 (36 + n) ++ ascii "WAVE" ++ ascii "fmt " ++ le32 16 ++ le16 1 ++
    le16 p.channels ++ le32 p.rate ++ le32 (p.rate * p.channels * 2) ++ le16 (p.channels * 2) ++
    le16 16 ++ ascii "data" ++ le32 n ++ p.samples

/-- Samples per channel at 48 kHz in an Opus packet, from its TOC byte and frame
count (RFC 6716 section 3.1). 0 for an empty or malformed packet. -/
def opusSamples (p : ByteArray) : Nat :=
  if p.size == 0 then 0 else
  let toc := p[0]!.toNat
  let config := toc >>> 3
  -- Frame size in units of 2.5 ms (120 samples at 48 kHz).
  let units :=
    if config < 12 then [4, 8, 16, 24][config % 4]!          -- SILK: 10, 20, 40, 60 ms
    else if config < 16 then [4, 8][config % 2]!             -- hybrid: 10, 20 ms
    else [1, 2, 4, 8][config % 4]!                           -- CELT: 2.5, 5, 10, 20 ms
  let frames := match toc &&& 3 with
    | 0 => 1
    | 1 | 2 => 2
    | _ => if p.size < 2 then 0 else p[1]!.toNat &&& 0x3F
  units * 120 * frames

/-- Audio of an Ogg file: the first Opus or Vorbis stream. -/
def oggAudio (opusWasm vorbisWasm : ByteArray) (file : ByteArray) : IO Pcm := do
  let r := Ogg.demux file
  match r.streams.find? (fun s => s.codec == .opus || s.codec == .vorbis) with
  | none => throw (IO.userError "no Opus or Vorbis stream")
  | some s =>
    let pk := s.packets.map (·.data)
    if s.codec == .opus then
      let h ← IO.ofExcept (Ogg.opusHead pk[0]!)
      -- Packet 1 is OpusTags; audio starts at packet 2.
      let total := if s.lastGranule.toNat ≥ h.preSkip then some (s.lastGranule.toNat - h.preSkip) else none
      opus opusWasm h.channels h.preSkip (pk.extract 2 pk.size) total
    else
      vorbis vorbisWasm (pk.extract 0 3) (pk.extract 3 pk.size) (some s.lastGranule.toNat)

/-- Audio of a WebM file: the first Opus or Vorbis track. -/
def webmAudio (opusWasm vorbisWasm : ByteArray) (r : WebM.Result) : IO Pcm := do
  match r.tracks.find? (fun t => t.codec == "A_OPUS" || t.codec == "A_VORBIS") with
  | none => throw (IO.userError "no Opus or Vorbis track")
  | some t =>
    let pk := (r.framesOf t.number).map (·.data)
    if t.codec == "A_OPUS" then
      let h ← IO.ofExcept (Ogg.opusHead t.codecPrivate)
      -- End trimming: the `DiscardPadding` of the frames, in samples at 48 kHz.
      let fs := r.framesOf t.number
      let discard := fs.foldl (fun n f => n + f.discard * 48000 / 1000000000) 0
      let decoded := fs.foldl (fun n f => n + opusSamples f.data) 0
      let total := if discard > 0 && decoded ≥ h.preSkip + discard then some (decoded - h.preSkip - discard) else none
      opus opusWasm h.channels h.preSkip pk total
    else
      vorbis vorbisWasm (← IO.ofExcept (WebM.xiphHeaders t.codecPrivate)) pk none

/-! ## Video -/

/-- One decoded picture: RGBA, rows from the top. -/
structure Picture where
  width : Nat
  height : Nat
  rgba : ByteArray
  time : Int

structure Video where
  pictures : Array Picture
  /-- Packed I420 of each picture, when asked for (for comparison with a reference). -/
  i420 : Array ByteArray
  /-- Instructions and nanoseconds of `mw_vp8_decode` in WasmVM. -/
  decodeSteps : Nat
  decodeNs : Nat
  /-- `mw_vp8_i420` (a copy of the planes, in WasmVM) and reading them out. -/
  copyNs : Nat
  /-- I420 to RGBA in Lean (`Media.Yuv`). -/
  convertNs : Nat
  /-- The first picture: the module's own conversion (`mw_vp8_rgba`) gives the same
  bytes as `Yuv.toRgba`. -/
  crossCheck : Bool

/-- `f ()` and the nanoseconds it took on the host clock. -/
def timedPure {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- Decode the VP8 frames of a WebM track, at most `limit` of them. -/
def vp8 (wasm : ByteArray) (frames : Array WebM.Frame) (limit : Nat) (keepI420 : Bool) : IO Video := do
  let mut m ← load wasm
  let (m', r) ← m.callI32 "mw_vp8_init" #[]
  m := m'
  if r != 0 then throw (IO.userError s!"mw_vp8_init: {r}")
  let mut out : Nat := 0
  let mut outSize : Nat := 0
  let mut pics := #[]
  let mut yuvs := #[]
  let mut ds := 0
  let mut dn := 0
  let mut cpn := 0
  let mut cvn := 0
  let mut cross := true
  for f in frames.extract 0 limit do
    m ← m.put f.data
    let (s0, n0) := (m.steps, m.ns)
    let (m', r) ← m.callI32 "mw_vp8_decode" #[i32 m.buf, i32 f.data.size]
    m := m'
    ds := ds + (m.steps - s0); dn := dn + (m.ns - n0)
    if r < 0 then throw (IO.userError s!"mw_vp8_decode: {r}")
    if r == 1 then continue
    let (m', w) ← m.callI32 "mw_vp8_width" #[]
    let (m', h) ← m'.callI32 "mw_vp8_height" #[]
    m := m'
    let (w, h) := (w.toNat, h.toNat)
    if outSize < w * h * 4 then
      let (m', p) ← m.callI32 "mw_alloc" #[i32 (w * h * 4)]
      if p ≤ 0 then throw (IO.userError "mw_alloc gave 0")
      m := m'; out := p.toNat; outSize := w * h * 4
    let t0 ← IO.monoNanosNow
    let (m', n) ← m.callI32 "mw_vp8_i420" #[i32 out]
    m := m'
    let yuv ← m.read out n.toNat
    let t1 ← IO.monoNanosNow
    cpn := cpn + (t1 - t0)
    let (rgba, ns) ← timedPure fun _ => Yuv.toRgba w h yuv
    cvn := cvn + ns
    if pics.isEmpty then
      let (m', n) ← m.callI32 "mw_vp8_rgba" #[i32 out]
      m := m'
      cross := (← m.read out n.toNat) == rgba
    pics := pics.push { width := w, height := h, rgba, time := f.time }
    if keepI420 then yuvs := yuvs.push yuv
  return { pictures := pics, i420 := yuvs, decodeSteps := ds, decodeNs := dn, copyNs := cpn,
           convertNs := cvn, crossCheck := cross }

end L4Factoidal.Media.Decode
