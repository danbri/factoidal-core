/-
L4Factoidal.Media.WebM: the WebM and Matroska containers (RFC 8794 EBML, RFC 9559
Matroska), read in Lean (record: docs/designissues/2026-11-08-media-wasmvm.md).

The reader knows the few elements that playback needs:

- `EBML` header: `DocType` (`webm` or `matroska`).
- `Segment` → `Info`: `TimestampScale` (nanoseconds per tick, default 1000000), `Duration`.
- `Segment` → `Tracks` → `TrackEntry`: `TrackNumber`, `TrackType`, `CodecID`,
  `CodecPrivate`, `CodecDelay`, `Video` (`PixelWidth`, `PixelHeight`), `Audio`
  (`SamplingFrequency`, `Channels`).
- `Segment` → `Cluster`: `Timestamp`, `SimpleBlock`, `BlockGroup` → `Block`; with
  no lacing, Xiph lacing, fixed-size lacing and EBML lacing (RFC 9559 section 10.3).

Every other element is skipped by its size. The walk is flat: an element that holds
elements the reader needs (`Segment`, `Info`, `Tracks`, `TrackEntry`, `Video`,
`Audio`, `Cluster`, `BlockGroup`) is entered, every other one is stepped over. So an
element of unknown size (a live `Segment` or `Cluster`) needs no special case, and
there is no recursion. Each step moves forward by at least two bytes (an ID and a
size), so a file of `n` bytes takes at most `n / 2 + 1` steps.
-/

namespace L4Factoidal.Media.WebM

/-- A variable-size integer (RFC 8794 section 4) at `off`: its width in bytes, its
value with the marker bit removed, and whether all value bits are 1 (an unknown
size). -/
def vint (b : ByteArray) (off : Nat) : Except String (Nat × Nat × Bool) := do
  unless off < b.size do throw s!"variable-size integer at {off} is past the end"
  let first := b[off]!.toNat
  if first == 0 then throw s!"variable-size integer at {off} is wider than 8 bytes"
  let mut w := 1
  for k in [0:8] do
    if first &&& (0x80 >>> k) != 0 then w := k + 1; break
  unless off + w ≤ b.size do throw s!"variable-size integer at {off} is cut short"
  let mut v := first &&& (0xFF >>> w)
  for i in [1:w] do v := v * 256 + b[off + i]!.toNat
  return (w, v, v == 2 ^ (7 * w) - 1)

/-- An element ID at `off`: its width and its value with the marker bits kept, as
the specifications write IDs. -/
def elementId (b : ByteArray) (off : Nat) : Except String (Nat × Nat) := do
  let (w, _, _) ← vint b off
  if w > 4 then throw s!"element ID at {off} is wider than 4 bytes"
  let mut v := 0
  for i in [0:w] do v := v * 256 + b[off + i]!.toNat
  return (w, v)

def uint (b : ByteArray) (off len : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:len] do v := v * 256 + b[off + i]!.toNat
  return v

/-- A float element: 4 or 8 bytes, big-endian IEEE 754; 0 for any other size. -/
def float (b : ByteArray) (off len : Nat) : Float :=
  if len == 4 then (Float32.ofBits (uint b off 4).toUInt32).toFloat
  else if len == 8 then Float.ofBits (uint b off 8).toUInt64
  else 0

def str (b : ByteArray) (off len : Nat) : String :=
  -- Strings may end with zero bytes (RFC 8794 section 7.4).
  let s := String.fromUTF8? (b.extract off (off + len)) |>.getD ""
  String.ofList (s.toList.takeWhile (· != '\x00'))

/-! Element IDs (RFC 8794, RFC 9559). -/
def idEBML : Nat := 0x1A45DFA3
def idDocType : Nat := 0x4282
def idSegment : Nat := 0x18538067
def idInfo : Nat := 0x1549A966
def idTimestampScale : Nat := 0x2AD7B1
def idDuration : Nat := 0x4489
def idTracks : Nat := 0x1654AE6B
def idTrackEntry : Nat := 0xAE
def idTrackNumber : Nat := 0xD7
def idTrackType : Nat := 0x83
def idCodecID : Nat := 0x86
def idCodecPrivate : Nat := 0x63A2
def idCodecDelay : Nat := 0x56AA
def idVideo : Nat := 0xE0
def idPixelWidth : Nat := 0xB0
def idPixelHeight : Nat := 0xBA
def idAudio : Nat := 0xE1
def idSamplingFrequency : Nat := 0xB5
def idChannels : Nat := 0x9F
def idCluster : Nat := 0x1F43B675
def idTimestamp : Nat := 0xE7
def idSimpleBlock : Nat := 0xA3
def idBlockGroup : Nat := 0xA0
def idBlock : Nat := 0xA1
def idDiscardPadding : Nat := 0x75A2

/-- Elements the walk enters instead of stepping over. -/
def entered : List Nat := [idSegment, idInfo, idTracks, idTrackEntry, idVideo, idAudio, idCluster, idBlockGroup]

structure Track where
  number : Nat := 0
  /-- 1 video, 2 audio, 17 subtitle (RFC 9559 section 5.1.4.1.3). -/
  type : Nat := 0
  codec : String := ""
  codecPrivate : ByteArray := .empty
  /-- Nanoseconds of audio the decoder adds at the start (Opus pre-skip). -/
  codecDelay : Nat := 0
  width : Nat := 0
  height : Nat := 0
  rate : Float := 8000
  channels : Nat := 1
  deriving Inhabited

/-- One frame of one track. `time` is in nanoseconds from the start of the segment. -/
structure Frame where
  track : Nat
  time : Int
  key : Bool
  data : ByteArray
  /-- `DiscardPadding` of the block group: nanoseconds of decoded audio to drop at
  the end of this frame (RFC 9559 section 5.1.3.5.6). -/
  discard : Nat := 0
  deriving Inhabited

structure Result where
  docType : String := ""
  timestampScale : Nat := 1000000
  /-- In ticks of `timestampScale`. -/
  duration : Float := 0
  tracks : Array Track := #[]
  frames : Array Frame := #[]
  deriving Inhabited

/-- The frame sizes of a laced block (RFC 9559 section 10.3). `off` is the byte
after the flags, `stop` the end of the block. The result is the offset of the first
frame and the sizes. -/
def laceSizes (b : ByteArray) (lacing off stop : Nat) : Except String (Nat × Array Nat) := do
  if lacing == 0 then return (off, #[stop - off])
  unless off < stop do throw "laced block is cut short"
  let count := b[off]!.toNat + 1
  let mut pos := off + 1
  let mut sizes : Array Nat := #[]
  if lacing == 1 then
    -- Xiph: each size but the last is a run of 255 bytes and one byte below 255.
    for _ in [0:count - 1] do
      let mut s := 0
      for _ in [0:stop - pos] do
        unless pos < stop do throw "Xiph lacing is cut short"
        let v := b[pos]!.toNat
        pos := pos + 1
        s := s + v
        if v < 255 then break
      sizes := sizes.push s
  else if lacing == 2 then
    -- Fixed size: the rest of the block in `count` equal frames.
    let rest := stop - pos
    unless rest % count == 0 do throw "fixed-size lacing does not divide the block"
    return (pos, Array.replicate count (rest / count))
  else
    -- EBML: the first size as an unsigned integer, the next ones as signed differences.
    let (w, first, _) ← vint b pos
    pos := pos + w
    sizes := sizes.push first
    let mut prev : Int := first
    for _ in [0:count - 2] do
      let (w, raw, _) ← vint b pos
      pos := pos + w
      let s : Int := (raw : Int) - (2 ^ (7 * w - 1) - 1)
      let cur := prev + s
      if cur < 0 then throw "EBML lacing gives a negative size"
      sizes := sizes.push cur.toNat
      prev := cur
  let used := sizes.foldl (· + ·) 0
  unless pos + used ≤ stop do throw "laced frames are larger than the block"
  return (pos, sizes.push (stop - pos - used))

/-- The frames of a `SimpleBlock` or `Block` at `[off, stop)`. -/
def block (b : ByteArray) (off stop : Nat) (clusterTime : Int) (scale : Nat) (simple : Bool) :
    Except String (Array Frame) := do
  let (w, track, _) ← vint b off
  unless off + w + 3 ≤ stop do throw s!"block at {off} is cut short"
  let rel := uint b (off + w) 2
  let rel : Int := if rel ≥ 32768 then (rel : Int) - 65536 else rel
  let flags := b[off + w + 2]!.toNat
  let key := simple && flags &&& 0x80 != 0
  let (start, sizes) ← laceSizes b ((flags >>> 1) &&& 3) (off + w + 3) stop
  let time := (clusterTime + rel) * scale
  let mut pos := start
  let mut out := #[]
  for s in sizes do
    out := out.push { track, time, key, data := b.extract pos (pos + s) }
    pos := pos + s
  return out

/-- Read a WebM or Matroska file. -/
def demux (b : ByteArray) : Except String Result := do
  let mut r : Result := {}
  let mut pos := 0
  let mut clusterTime : Int := 0
  let mut sawHeader := false
  for _ in [0:b.size / 2 + 1] do
    if pos ≥ b.size then break
    let (iw, id) ← elementId b pos
    let (sw, size, unknown) ← vint b (pos + iw)
    let data := pos + iw + sw
    let stop := if unknown then b.size else min b.size (data + size)
    if !unknown && data + size > b.size && !(entered.contains id) then
      -- A cut-short leaf at the end (a partial download): stop here.
      break
    if id == idEBML then
      sawHeader := true
      -- Find DocType inside the header.
      let mut p := data
      for _ in [0:(stop - data) / 2 + 1] do
        if p ≥ stop then break
        let (iw2, id2) ← elementId b p
        let (sw2, size2, _) ← vint b (p + iw2)
        if id2 == idDocType then r := { r with docType := str b (p + iw2 + sw2) size2 }
        p := p + iw2 + sw2 + size2
      pos := stop
    else if entered.contains id then
      if id == idTrackEntry then r := { r with tracks := r.tracks.push {} }
      pos := data
    else
      let leaf := fun (f : Track → Track) =>
        if r.tracks.isEmpty then r else { r with tracks := r.tracks.modify (r.tracks.size - 1) f }
      if id == idTimestampScale then r := { r with timestampScale := uint b data size }
      else if id == idDuration then r := { r with duration := float b data size }
      else if id == idTrackNumber then r := leaf fun t => { t with number := uint b data size }
      else if id == idTrackType then r := leaf fun t => { t with type := uint b data size }
      else if id == idCodecID then r := leaf fun t => { t with codec := str b data size }
      else if id == idCodecPrivate then r := leaf fun t => { t with codecPrivate := b.extract data stop }
      else if id == idCodecDelay then r := leaf fun t => { t with codecDelay := uint b data size }
      else if id == idPixelWidth then r := leaf fun t => { t with width := uint b data size }
      else if id == idPixelHeight then r := leaf fun t => { t with height := uint b data size }
      else if id == idSamplingFrequency then r := leaf fun t => { t with rate := float b data size }
      else if id == idChannels then r := leaf fun t => { t with channels := uint b data size }
      else if id == idTimestamp then clusterTime := uint b data size
      else if id == idDiscardPadding && !r.frames.isEmpty then
        -- A signed integer; a negative value (padding at the start) is not used here.
        let v := uint b data size
        if size > 0 && v < 2 ^ (8 * size - 1) then
          r := { r with frames := r.frames.modify (r.frames.size - 1) fun f => { f with discard := v } }
      else if id == idSimpleBlock || id == idBlock then
        r := { r with frames := r.frames ++ (← block b data stop clusterTime r.timestampScale (id == idSimpleBlock)) }
      pos := stop
  unless sawHeader do throw "no EBML header"
  unless r.docType == "webm" || r.docType == "matroska" do throw s!"DocType {repr r.docType}"
  return r

/-- The three Vorbis header packets of a Matroska `CodecPrivate` (Xiph lacing). -/
def xiphHeaders (p : ByteArray) : Except String (Array ByteArray) := do
  let (start, sizes) ← laceSizes p 1 0 p.size
  let mut pos := start
  let mut out := #[]
  for s in sizes do
    out := out.push (p.extract pos (pos + s))
    pos := pos + s
  return out

def Result.track? (r : Result) (n : Nat) : Option Track := r.tracks.find? (·.number == n)
def Result.framesOf (r : Result) (n : Nat) : Array Frame := r.frames.filter (·.track == n)

end L4Factoidal.Media.WebM
