/-
L4Factoidal.Media.Ogg: the Ogg container (RFC 3533), read in Lean
(record: docs/designissues/2026-11-08-media-wasmvm.md).

`demux` reads every page of a file: the capture pattern `OggS`, the 27-byte header,
the segment table, and the CRC-32 of the page (polynomial 0x04C11DB7, initial value
0, no reflection, no final XOR; the CRC field counts as zero). It joins the segments
into packets for each logical stream (serial number): a lacing value below 255 ends
a packet, and a packet can continue on the next page of its stream. A page whose CRC
does not match is dropped (RFC 3533 section 6), and the reader looks for the next
capture pattern; the count of dropped pages is in the result.

The codec of a stream comes from its first packet: `OpusHead` (RFC 7845), `\x01vorbis`
(Vorbis I section 4.2.2) or `\x80theora`.

Every loop is bounded by the input size: a page is at least 27 bytes, so a file of
`n` bytes has at most `n / 27 + 1` pages.
-/

namespace L4Factoidal.Media.Ogg

/-- CRC-32 table of the Ogg polynomial 0x04C11DB7, most significant bit first. -/
def crcTable : Array UInt32 := Id.run do
  let mut t : Array UInt32 := Array.emptyWithCapacity 256
  for i in [0:256] do
    let mut r : UInt32 := i.toUInt32 <<< 24
    for _ in [0:8] do
      r := if r &&& 0x80000000 != 0 then (r <<< 1) ^^^ 0x04C11DB7 else r <<< 1
    t := t.push r
  return t

/-- The Ogg CRC of `b[start, start+len)`, with bytes 22 to 25 of the page (the CRC
field) counted as zero. -/
def pageCrc (b : ByteArray) (start len : Nat) : UInt32 := Id.run do
  let mut c : UInt32 := 0
  for i in [0:len] do
    let byte : UInt32 := if 22 ≤ i && i < 26 then 0 else (b[start + i]!).toUInt32
    c := (c <<< 8) ^^^ crcTable[(((c >>> 24) ^^^ byte) &&& 0xFF).toNat]!
  return c

def u16le (b : ByteArray) (i : Nat) : Nat := b[i]!.toNat + b[i+1]!.toNat * 256
def u32le (b : ByteArray) (i : Nat) : Nat := u16le b i + u16le b (i + 2) * 65536
def u64le (b : ByteArray) (i : Nat) : UInt64 :=
  (u32le b i).toUInt64 ||| ((u32le b (i + 4)).toUInt64 <<< 32)

/-- One page header. `bodyStart` and `bodyLen` locate the page body in the file. -/
structure Page where
  headerType : Nat
  granule : UInt64
  serial : Nat
  seq : Nat
  lacing : Array Nat
  bodyStart : Nat
  bodyLen : Nat
  deriving Repr, Inhabited

def Page.continued (p : Page) : Bool := p.headerType &&& 1 != 0
def Page.bos (p : Page) : Bool := p.headerType &&& 2 != 0
def Page.eos (p : Page) : Bool := p.headerType &&& 4 != 0
/-- A granule position of all ones means that no packet ends on the page. -/
def Page.hasGranule (p : Page) : Bool := p.granule != 0xFFFFFFFFFFFFFFFF

def isCapture (b : ByteArray) (off : Nat) : Bool :=
  off + 4 ≤ b.size && b[off]! == 0x4F && b[off+1]! == 0x67 && b[off+2]! == 0x67 && b[off+3]! == 0x53

/-- The page at `off`, with its length in bytes. The CRC is checked. -/
def readPage (b : ByteArray) (off : Nat) : Except String (Page × Nat) := do
  unless isCapture b off do throw s!"no capture pattern at {off}"
  unless off + 27 ≤ b.size do throw s!"page header at {off} is cut short"
  unless b[off+4]! == 0 do throw s!"page at {off}: stream structure version {b[off+4]!}"
  let n := b[off+26]!.toNat
  unless off + 27 + n ≤ b.size do throw s!"segment table at {off} is cut short"
  let lacing := (Array.range n).map fun i => b[off + 27 + i]!.toNat
  let bodyLen := lacing.foldl (· + ·) 0
  let total := 27 + n + bodyLen
  unless off + total ≤ b.size do throw s!"page body at {off} is cut short"
  let stated := u32le b (off + 22)
  let got := pageCrc b off total
  unless got.toNat == stated do throw s!"page at {off}: CRC {got.toNat} but the page states {stated}"
  return ({ headerType := b[off+5]!.toNat, granule := u64le b (off + 6), serial := u32le b (off + 14),
            seq := u32le b (off + 18), lacing, bodyStart := off + 27 + n, bodyLen }, total)

inductive Codec where
  | opus | vorbis | theora | unknown
  deriving Repr, BEq, Inhabited

def Codec.name : Codec → String
  | .opus => "opus" | .vorbis => "vorbis" | .theora => "theora" | .unknown => "unknown"

def startsWith (b : ByteArray) (sig : List UInt8) : Bool :=
  sig.length ≤ b.size && (sig.zipIdx.all fun (c, i) => b[i]! == c)

def codecOf (first : ByteArray) : Codec :=
  if startsWith first "OpusHead".toUTF8.toList then .opus
  else if startsWith first ([0x01] ++ "vorbis".toUTF8.toList) then .vorbis
  else if startsWith first ([0x80] ++ "theora".toUTF8.toList) then .theora
  else .unknown

/-- A packet, and the granule position of the page where it ends when it is the last
packet that ends there. -/
structure Packet where
  data : ByteArray
  granule : Option UInt64 := none

instance : Inhabited Packet := ⟨{ data := .empty }⟩

/-- One logical stream. `partial_` holds a packet that continues on a later page. -/
structure Stream where
  serial : Nat
  codec : Codec := .unknown
  packets : Array Packet := #[]
  partial_ : ByteArray := .empty
  lastGranule : UInt64 := 0
  eos : Bool := false
  deriving Inhabited

structure Result where
  streams : Array Stream
  pages : Nat
  /-- Pages dropped: CRC mismatch, a bad header, or bytes between pages. -/
  dropped : Nat
  deriving Inhabited

/-- Add the packets of one page to its stream. -/
def addPage (b : ByteArray) (s : Stream) (p : Page) : Stream := Id.run do
  let mut s := s
  -- A continued packet with nothing pending (the stream was joined mid-packet):
  -- its first segments are dropped, up to the first lacing value below 255.
  let mut skipping := p.continued && s.partial_.size == 0
  -- A page that is not continued while a packet is pending: the pending bytes are
  -- an incomplete packet, and are dropped.
  if !p.continued && s.partial_.size > 0 then s := { s with partial_ := .empty }
  let mut pos := p.bodyStart
  let mut cur := s.partial_
  let mut ended : Array ByteArray := #[]
  for l in p.lacing do
    if !skipping then cur := b.copySlice pos cur cur.size l
    pos := pos + l
    if l < 255 then
      if skipping then skipping := false
      else
        ended := ended.push cur
      cur := .empty
  let mut packets := s.packets
  for i in [0:ended.size] do
    let g := if i + 1 == ended.size && p.hasGranule then some p.granule else none
    packets := packets.push { data := ended[i]!, granule := g }
  let codec := if s.packets.size == 0 && packets.size > 0 then codecOf packets[0]!.data else s.codec
  return { s with packets, partial_ := cur, codec,
                  lastGranule := if p.hasGranule then p.granule else s.lastGranule,
                  eos := s.eos || p.eos }

/-- All pages and packets of a file. -/
def demux (b : ByteArray) : Result := Id.run do
  let mut streams : Array Stream := #[]
  let mut off := 0
  let mut pages := 0
  let mut dropped := 0
  for _ in [0:b.size / 27 + 1] do
    if off + 27 > b.size then break
    match readPage b off with
    | .ok (p, len) =>
      pages := pages + 1
      off := off + len
      match streams.findIdx? (·.serial == p.serial) with
      | some i => streams := streams.modify i (addPage b · p)
      | none => streams := streams.push (addPage b { serial := p.serial } p)
    | .error _ =>
      dropped := dropped + 1
      -- Look for the next capture pattern after this offset.
      let mut next := b.size
      for j in [off+1:b.size] do
        if isCapture b j then next := j; break
      off := next
  return { streams, pages, dropped }

/-! ## Codec headers -/

/-- The Opus identification header (RFC 7845 section 5.1). -/
structure OpusHead where
  channels : Nat
  preSkip : Nat
  inputRate : Nat
  /-- Output gain, Q7.8 dB, as stated (signed 16 bits). -/
  gain : Int
  mapping : Nat
  deriving Repr

def opusHead (p : ByteArray) : Except String OpusHead := do
  unless p.size ≥ 19 && codecOf p == .opus do throw "not an OpusHead packet"
  unless p[8]!.toNat >>> 4 == 0 do throw s!"OpusHead version {p[8]!}"
  let g := u16le p 16
  return { channels := p[9]!.toNat, preSkip := u16le p 10, inputRate := u32le p 12,
           gain := if g ≥ 32768 then (g : Int) - 65536 else g, mapping := p[18]!.toNat }

/-- The Vorbis identification header (Vorbis I section 4.2.2): channels and rate. -/
def vorbisId (p : ByteArray) : Except String (Nat × Nat) := do
  unless p.size ≥ 30 && codecOf p == .vorbis do throw "not a Vorbis identification header"
  return (p[11]!.toNat, u32le p 12)

end L4Factoidal.Media.Ogg
