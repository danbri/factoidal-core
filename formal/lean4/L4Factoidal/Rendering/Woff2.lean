import L4Factoidal.Codec.Brotli
import L4Factoidal.Rendering.Woff

/-!
# WOFF2 to sfnt

WOFF File Format 2.0 (W3C Recommendation): an sfnt font whose tables are stored in one Brotli
stream (RFC 7932), behind a 48-byte header (§3) and a table directory with variable-length
entries (§4.1: a flags byte naming one of 63 known tags or giving the tag, and lengths in
UIntBase128). The `glyf` and `loca` tables may be stored transformed (§5.1 to §5.3: glyph data
split into seven streams, coordinates as triplets, `loca` left out) and the `hmtx` table may be
stored transformed (§5.4: left side bearings equal to the glyph's xMin left out). `toSfnt`
gives back the sfnt that the font reader takes.

The sfnt is laid out as the reference decoder (google/woff2, `woff2_dec.cc`) lays it out: the
table records sorted by tag; the tables in tag order, each at a four-byte boundary, except
that a reconstructed `loca` follows its `glyf` at once; every glyph padded to four bytes; the
simple glyphs written with the reference decoder's flag and coordinate encoding; the table
checksums and the `head` checkSumAdjustment computed. The bytes are the reference decoder's
bytes (checked on 34 WOFF2 files made from twelve fonts, `tools/fonts/woff2_vectors.py`).

Differences from the reference decoder: a glyph whose contour count is negative and not -1,
and a simple glyph whose first contour has no point, are refused (the reference decoder writes
them as they come); a transformation version of `glyf` or `loca` other than 0 and 3, and of
`hmtx` other than 0 and 1, is refused.

Font collections (flavor `ttcf`, §4.2) are refused with a message: the font reader takes one
face.

Font bytes are hostile input. The header's length must be the file's length; the table
directory, the compressed stream, the metadata and the private data must lie in the file in
that order (§3, §6, §7); the Brotli stream must give exactly the bytes the directory gives;
every stream of the transformed `glyf` is read with bounds; the sfnt made may not pass
`maxSfntBytes`. Every loop is a `for` over a count read from the file and checked against the
bytes that remain.
-/
namespace L4Factoidal.Rendering.Woff2

open L4Factoidal.Codec

/-- The largest sfnt made from a WOFF2 file (the WOFF 1.0 limit: 16 MiB). -/
def maxSfntBytes : Nat := Woff.maxSfntBytes

/-- The most tables of a WOFF2 file. -/
def maxTables : Nat := 256

/-- The first four bytes of a WOFF2 file: `wOF2`. -/
def isWoff2 (b : ByteArray) : Bool :=
  b.size ≥ 4 && b.get! 0 == 0x77 && b.get! 1 == 0x4F && b.get! 2 == 0x46 && b.get! 3 == 0x32

/-- The 63 known table tags of §4.1 (Table 2), by their index in the flags byte. -/
def knownTags : Array Nat := #[
  0x636D6170, 0x68656164, 0x68686561, 0x686D7478, 0x6D617870, 0x6E616D65, 0x4F532F32, 0x706F7374,
  0x63767420, 0x6670676D, 0x676C7966, 0x6C6F6361, 0x70726570, 0x43464620, 0x564F5247, 0x45424454,
  0x45424C43, 0x67617370, 0x68646D78, 0x6B65726E, 0x4C545348, 0x50434C54, 0x56444D58, 0x76686561,
  0x766D7478, 0x42415345, 0x47444546, 0x47504F53, 0x47535542, 0x45425343, 0x4A535446, 0x4D415448,
  0x43424454, 0x43424C43, 0x434F4C52, 0x4350414C, 0x53564720, 0x73626978, 0x61636E74, 0x61766172,
  0x62646174, 0x626C6F63, 0x62736C6E, 0x63766172, 0x66647363, 0x66656174, 0x666D7478, 0x66766172,
  0x67766172, 0x68737479, 0x6A757374, 0x6C636172, 0x6D6F7274, 0x6D6F7278, 0x6F706264, 0x70726F70,
  0x7472616B, 0x5A617066, 0x53696C66, 0x476C6174, 0x476C6F63, 0x46656174, 0x53696C6C]

def tagGlyf : Nat := 0x676C7966
def tagLoca : Nat := 0x6C6F6361
def tagHmtx : Nat := 0x686D7478
def tagHhea : Nat := 0x68686561
def tagHead : Nat := 0x68656164

/-! ## Reading -/

/-- A read position in bytes `[pos, lim)` of a buffer (`lim` at most the buffer's size). -/
structure Cur where
  pos : Nat
  lim : Nat
  deriving Inhabited

namespace Cur

def u8 (d : ByteArray) (c : Cur) (what : String) : Except String (Nat × Cur) :=
  if c.pos + 1 ≤ c.lim && c.lim ≤ d.size then .ok ((d.get! c.pos).toNat, { c with pos := c.pos + 1 })
  else .error s!"WOFF2 {what} runs past its end"

def u16 (d : ByteArray) (c : Cur) (what : String) : Except String (Nat × Cur) :=
  if c.pos + 2 ≤ c.lim && c.lim ≤ d.size then
    .ok ((d.get! c.pos).toNat * 256 + (d.get! (c.pos+1)).toNat, { c with pos := c.pos + 2 })
  else .error s!"WOFF2 {what} runs past its end"

def u32 (d : ByteArray) (c : Cur) (what : String) : Except String (Nat × Cur) := do
  let (hi, c) ← c.u16 d what
  let (lo, c) ← c.u16 d what
  return (hi * 65536 + lo, c)

def bytes (d : ByteArray) (c : Cur) (n : Nat) (what : String) : Except String (ByteArray × Cur) :=
  if c.pos + n ≤ c.lim && c.lim ≤ d.size then .ok (d.extract c.pos (c.pos + n), { c with pos := c.pos + n })
  else .error s!"WOFF2 {what} runs past its end"

/-- 255UInt16 (§4.1): one byte, or 253 then two bytes, or 255 or 254 then one byte (plus 253
or 506). -/
def r255 (d : ByteArray) (c : Cur) (what : String) : Except String (Nat × Cur) := do
  let (code, c) ← c.u8 d what
  if code == 253 then c.u16 d what
  else if code == 255 then do let (v, c) ← c.u8 d what; return (v + 253, c)
  else if code == 254 then do let (v, c) ← c.u8 d what; return (v + 506, c)
  else return (code, c)

/-- UIntBase128 (§4.1): at most five bytes, seven bits each, high bit set on all but the
last; no leading zero byte, no value above 2^32 - 1. -/
def base128 (d : ByteArray) (c : Cur) (what : String) : Except String (Nat × Cur) := do
  let mut v := 0
  let mut c := c
  for i in [0:5] do
    let (b, c') ← c.u8 d what
    c := c'
    if i == 0 && b == 0x80 then throw s!"WOFF2 {what}: UIntBase128 has a leading zero"
    if v ≥ 2 ^ 25 then throw s!"WOFF2 {what}: UIntBase128 is larger than 32 bits"
    v := v * 128 + b % 128
    if b < 128 then return (v, c)
  throw s!"WOFF2 {what}: UIntBase128 is longer than five bytes"

end Cur

/-! ## Writing -/

def push16 (out : ByteArray) (v : Nat) : ByteArray :=
  (out.push (v / 256 % 256).toUInt8).push (v % 256).toUInt8
def push32 (out : ByteArray) (v : Nat) : ByteArray :=
  push16 (push16 out (v / 65536 % 65536)) (v % 65536)
/-- A signed value as 16 bits (two's complement, low 16 bits, as `Store16` does). -/
def pushS16 (out : ByteArray) (v : Int) : ByteArray := push16 out (v % 65536).toNat

/-- Zero bytes up to a multiple of four. -/
def pad4 (out : ByteArray) : ByteArray := Id.run do
  let mut o := out
  for _ in [0:Woff.pad4 out.size - out.size] do o := o.push 0
  return o

/-- The sfnt table checksum (OpenType, "Calculating checksums"): the sum of the table's
big-endian 32-bit words, the last one padded with zeros, modulo 2^32. -/
def checksum (t : ByteArray) (start len : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:(len + 3) / 4] do
    let mut w := 0
    for k in [0:4] do
      let j := 4 * i + k
      w := w * 256 + (if j < len then (t.get! (start + j)).toNat else 0)
    s := (s + w) % 4294967296
  return s

/-- The signed 16-bit value of bytes `i, i+1`. -/
def s16At (b : ByteArray) (i : Nat) : Int :=
  let v := (b.get! i).toNat * 256 + (b.get! (i+1)).toNat
  if v ≥ 32768 then Int.ofNat v - 65536 else Int.ofNat v

/-! ## The transformed `glyf` table (§5.1 to §5.3) -/

/-- One point of a simple glyph. -/
structure Point where
  x : Int
  y : Int
  onCurve : Bool
  deriving Inhabited

private def withSign (flag : Nat) (v : Nat) : Int := if flag % 2 == 1 then Int.ofNat v else -Int.ofNat v

/-- The points of a simple glyph from its flags and its triplets (§5.2, "Triplet encoding"),
as `TripletDecode` of the reference decoder. `flagStart` is the first flag byte; `c` reads the
glyph stream. -/
def tripletDecode (d : ByteArray) (flagStart n : Nat) (c : Cur) : Except String (Array Point × Cur) := do
  let mut pts : Array Point := Array.emptyWithCapacity n
  let mut x : Int := 0
  let mut y : Int := 0
  let mut c := c
  for i in [0:n] do
    let f0 := (d.get! (flagStart + i)).toNat
    let onCurve := f0 < 128
    let flag := f0 % 128
    let nb := if flag < 84 then 1 else if flag < 120 then 2 else if flag < 124 then 3 else 4
    let (bs, c') ← c.bytes d nb "glyph stream (point coordinates)"
    c := c'
    let b (k : Nat) : Nat := (bs.get! k).toNat
    let (dx, dy) : Int × Int :=
      if flag < 10 then (0, withSign flag ((flag &&& 14) * 128 + b 0))
      else if flag < 20 then (withSign flag (((flag - 10) &&& 14) * 128 + b 0), 0)
      else if flag < 84 then
        let b0 := flag - 20
        (withSign flag (1 + (b0 &&& 0x30) + b 0 / 16), withSign (flag / 2) (1 + (b0 &&& 0x0c) * 4 + b 0 % 16))
      else if flag < 120 then
        let b0 := flag - 84
        (withSign flag (1 + b0 / 12 * 256 + b 0), withSign (flag / 2) (1 + b0 % 12 / 4 * 256 + b 1))
      else if flag < 124 then
        (withSign flag (b 0 * 16 + b 1 / 16), withSign (flag / 2) (b 1 % 16 * 256 + b 2))
      else
        (withSign flag (b 0 * 256 + b 1), withSign (flag / 2) (b 2 * 256 + b 3))
    x := x + dx
    y := y + dy
    pts := pts.push ⟨x, y, onCurve⟩
  return (pts, c)

/-- The flags and the coordinates of a simple glyph, as `StorePoints` of the reference decoder
writes them: short coordinates where they fit, repeated flags folded. -/
def storePoints (pts : Array Point) (overlap : Bool) : ByteArray := Id.run do
  let mut flags := ByteArray.empty
  let mut xs := ByteArray.empty
  let mut ys := ByteArray.empty
  let mut lastFlag : Int := -1
  let mut rep := 0
  let mut lastX : Int := 0
  let mut lastY : Int := 0
  for i in [0:pts.size] do
    let p := pts[i]!
    let mut flag := if p.onCurve then 1 else 0
    if overlap && i == 0 then flag := flag ||| 0x40
    let dx := p.x - lastX
    let dy := p.y - lastY
    if dx == 0 then flag := flag ||| 0x10
    else if dx > -256 && dx < 256 then
      flag := flag ||| 0x02 ||| (if dx > 0 then 0x10 else 0)
      xs := xs.push dx.natAbs.toUInt8
    else xs := pushS16 xs dx
    if dy == 0 then flag := flag ||| 0x20
    else if dy > -256 && dy < 256 then
      flag := flag ||| 0x04 ||| (if dy > 0 then 0x20 else 0)
      ys := ys.push dy.natAbs.toUInt8
    else ys := pushS16 ys dy
    if Int.ofNat flag == lastFlag && rep != 255 then
      flags := flags.set! (flags.size - 1) (flags.get! (flags.size - 1) ||| 0x08)
      rep := rep + 1
    else
      if rep != 0 then flags := flags.push rep.toUInt8
      flags := flags.push flag.toUInt8
      rep := 0
    lastX := p.x
    lastY := p.y
    lastFlag := Int.ofNat flag
  if rep != 0 then flags := flags.push rep.toUInt8
  return flags ++ xs ++ ys

/-- The bytes of the composite glyph records at the start of `c` (OpenType `glyf`,
"Composite glyph description"), and whether a record has WE_HAVE_INSTRUCTIONS. -/
def compositeSize (d : ByteArray) (c : Cur) : Except String (Nat × Bool × Cur) := do
  let start := c.pos
  let mut c := c
  let mut instr := false
  for _ in [0:(c.lim - c.pos) / 4 + 1] do
    let (flags, c') ← c.u16 d "composite stream"
    c := c'
    if flags &&& 0x0100 != 0 then instr := true
    let argSize := 2 + (if flags &&& 0x0001 != 0 then 4 else 2) +
      (if flags &&& 0x0008 != 0 then 2 else if flags &&& 0x0040 != 0 then 4
       else if flags &&& 0x0080 != 0 then 8 else 0)
    let (_, c') ← c.bytes d argSize "composite stream"
    c := c'
    if flags &&& 0x0020 == 0 then return (c.pos - start, instr, c)
  throw "WOFF2 composite glyph has no last component"

/-- The reconstructed `glyf` and `loca` tables of a transformed `glyf` table in bytes
`[start, start + len)` of the stream, and the xMin of every glyph (0 for an empty glyph).
`locaLength` is the origLength the directory gives for `loca`. -/
def reconstructGlyf (d : ByteArray) (start len locaLength : Nat) :
    Except String (ByteArray × ByteArray × Array Int) := do
  let hdr : Cur := ⟨start, start + len⟩
  let (_, c) ← hdr.u16 d "glyf header"
  let (optionFlags, c) ← c.u16 d "glyf header"
  let (numGlyphs, c) ← c.u16 d "glyf header"
  let (indexFormat, c) ← c.u16 d "glyf header"
  if indexFormat > 1 then throw "WOFF2 glyf indexFormat is not 0 or 1"
  if locaLength != (if indexFormat == 1 then 4 else 2) * (numGlyphs + 1) then
    throw "WOFF2 loca origLength does not match numGlyphs and indexFormat (§5.3)"
  let mut c := c
  let mut sizes : Array Nat := #[]
  for _ in [0:7] do
    let (s, c') ← c.u32 d "glyf header"
    c := c'
    sizes := sizes.push s
  -- the seven streams, one after the other
  let mut at_ := c.pos
  let mut streams : Array Cur := #[]
  for s in sizes do
    if at_ + s > start + len then throw "WOFF2 glyf stream runs past the glyf table"
    streams := streams.push ⟨at_, at_ + s⟩
    at_ := at_ + s
  let overlapStart := at_
  let hasOverlap := optionFlags &&& 1 != 0
  if hasOverlap && overlapStart + (numGlyphs + 7) / 8 > start + len then
    throw "WOFF2 overlapSimpleBitmap runs past the glyf table"
  let mut nContour := streams[0]!
  let mut nPoints := streams[1]!
  let mut flagS := streams[2]!
  let mut glyphS := streams[3]!
  let mut compS := streams[4]!
  let mut bboxS := streams[5]!
  let mut instrS := streams[6]!
  let bboxBitmap := bboxS.pos
  let bitmapLen := (numGlyphs + 31) / 32 * 4
  if bboxS.pos + bitmapLen > bboxS.lim then throw "WOFF2 bboxBitmap runs past the bbox stream"
  bboxS := { bboxS with pos := bboxS.pos + bitmapLen }
  let bitAt (base i : Nat) : Bool := (d.get! (base + i / 8)).toNat &&& (0x80 >>> (i % 8)) != 0
  let mut glyf := ByteArray.empty
  let mut loca : Array Nat := Array.emptyWithCapacity (numGlyphs + 1)
  let mut xMins : Array Int := Array.emptyWithCapacity numGlyphs
  for i in [0:numGlyphs] do
    let haveBbox := bitAt bboxBitmap i
    let (nc, c') ← nContour.u16 d "nContour stream"
    nContour := c'
    let mut g := ByteArray.empty
    if nc == 0xFFFF then
      -- a composite glyph (§5.3): its bbox is always given
      if !haveBbox then throw "WOFF2 composite glyph has no bbox"
      let (size, instr, _) ← compositeSize d compS
      let mut instrLen := 0
      if instr then
        let (n, c') ← glyphS.r255 d "glyph stream"
        glyphS := c'
        instrLen := n
      g := push16 g 0xFFFF
      let (bb, c') ← bboxS.bytes d 8 "bbox stream"
      bboxS := c'
      g := g ++ bb
      let (comp, c') ← compS.bytes d size "composite stream"
      compS := c'
      g := g ++ comp
      if instr then
        let (ins, c') ← instrS.bytes d instrLen "instruction stream"
        instrS := c'
        g := push16 g instrLen ++ ins
    else if nc ≥ 0x8000 then
      throw "WOFF2 glyph has a negative contour count other than -1"
    else if nc > 0 then
      -- a simple glyph
      let mut ends : Array Nat := #[]
      let mut total := 0
      for _ in [0:nc] do
        let (n, c') ← nPoints.r255 d "nPoints stream"
        nPoints := c'
        total := total + n
        if total > 65536 then throw "WOFF2 glyph has more than 65536 points"
        ends := ends.push total
      if flagS.pos + total > flagS.lim then throw "WOFF2 flag stream runs past its end"
      let (pts, c') ← tripletDecode d flagS.pos total glyphS
      glyphS := c'
      flagS := { flagS with pos := flagS.pos + total }
      let (instrLen, c') ← glyphS.r255 d "glyph stream"
      glyphS := c'
      g := push16 g nc
      if haveBbox then
        let (bb, c') ← bboxS.bytes d 8 "bbox stream"
        bboxS := c'
        g := g ++ bb
      else
        let mut xMin : Int := 0
        let mut yMin : Int := 0
        let mut xMax : Int := 0
        let mut yMax : Int := 0
        if h : 0 < pts.size then
          xMin := pts[0].x; xMax := pts[0].x; yMin := pts[0].y; yMax := pts[0].y
        for p in pts do
          xMin := min xMin p.x; xMax := max xMax p.x; yMin := min yMin p.y; yMax := max yMax p.y
        g := pushS16 (pushS16 (pushS16 (pushS16 g xMin) yMin) xMax) yMax
      for e in ends do
        if e == 0 then throw "WOFF2 glyph's first contour has no point"
        g := push16 g (e - 1)
      let (ins, c') ← instrS.bytes d instrLen "instruction stream"
      instrS := c'
      g := push16 g instrLen ++ ins
      let overlap := hasOverlap && bitAt overlapStart i
      g := g ++ storePoints pts overlap
    else
      if haveBbox then throw "WOFF2 empty glyph has a bbox"
    loca := loca.push glyf.size
    xMins := xMins.push (if g.size ≥ 4 then s16At g 2 else 0)
    glyf := pad4 (glyf ++ g)
    if glyf.size > maxSfntBytes then throw s!"WOFF2 font exceeds {maxSfntBytes} bytes"
  loca := loca.push glyf.size
  let mut locaBytes := ByteArray.emptyWithCapacity locaLength
  for v in loca do
    if indexFormat == 1 then locaBytes := push32 locaBytes v
    else
      if v / 2 > 65535 then throw "WOFF2 glyf is too large for a short loca"
      locaBytes := push16 locaBytes (v / 2)
  return (glyf, locaBytes, xMins)

/-! ## The transformed `hmtx` table (§5.4) -/

def reconstructHmtx (d : ByteArray) (start len numHMetrics : Nat) (xMins : Array Int) :
    Except String ByteArray := do
  let numGlyphs := xMins.size
  let c : Cur := ⟨start, start + len⟩
  let (flags, c) ← c.u8 d "hmtx flags"
  if flags &&& 0xFC != 0 then throw "WOFF2 hmtx flags has reserved bits set"
  let hasProp := flags &&& 1 == 0
  let hasMono := flags &&& 2 == 0
  if hasProp && hasMono then throw "WOFF2 hmtx is marked transformed but leaves nothing out"
  if numHMetrics > numGlyphs then throw "WOFF2 hhea numberOfHMetrics is larger than numGlyphs"
  if numHMetrics < 1 then throw "WOFF2 hhea numberOfHMetrics is 0"
  let mut c := c
  let mut adv : Array Nat := #[]
  for _ in [0:numHMetrics] do
    let (a, c') ← c.u16 d "hmtx advanceWidth"
    c := c'
    adv := adv.push a
  let mut lsbs : Array Int := #[]
  for i in [0:numGlyphs] do
    let given := if i < numHMetrics then hasProp else hasMono
    if given then
      let (v, c') ← c.u16 d "hmtx lsb"
      c := c'
      lsbs := lsbs.push (if v ≥ 32768 then Int.ofNat v - 65536 else Int.ofNat v)
    else lsbs := lsbs.push xMins[i]!
  let mut out := ByteArray.emptyWithCapacity (2 * numGlyphs + 2 * numHMetrics)
  for i in [0:numGlyphs] do
    if i < numHMetrics then out := push16 out adv[i]!
    out := pushS16 out lsbs[i]!
  return out

/-! ## The file (§3, §4) -/

/-- One entry of the table directory: the tag, whether the table is transformed, its
origLength, and where its bytes are in the decompressed stream. -/
structure Entry where
  tag : Nat
  transformed : Bool
  origLength : Nat
  srcOffset : Nat
  srcLength : Nat
  deriving Inhabited

/-- The table directory (§4.1), from byte 48. -/
def readDirectory (b : ByteArray) (numTables : Nat) : Except String (Array Entry × Nat) := do
  let mut c : Cur := ⟨48, b.size⟩
  let mut entries : Array Entry := #[]
  let mut src := 0
  for _ in [0:numTables] do
    let (flags, c') ← c.u8 b "table directory"
    c := c'
    let mut tag := 0
    if flags % 64 == 63 then
      let (t, c') ← c.u32 b "table directory"
      c := c'
      tag := t
    else tag := knownTags[flags % 64]!
    let version := flags / 64
    let isGlyfLoca := tag == tagGlyf || tag == tagLoca
    if isGlyfLoca && (version == 1 || version == 2) then
      throw "WOFF2 glyf or loca has a transformation version that is not defined"
    let transformed := if isGlyfLoca then version == 0 else version != 0
    if transformed && !isGlyfLoca && tag != tagHmtx then
      throw "WOFF2 table has a transformation that is not defined"
    if transformed && tag == tagHmtx && version != 1 then
      throw "WOFF2 hmtx has a transformation version that is not defined"
    let (origLength, c') ← c.base128 b "table directory"
    c := c'
    let mut srcLength := origLength
    if transformed then
      let (t, c') ← c.base128 b "table directory"
      c := c'
      srcLength := t
      if tag == tagLoca && t != 0 then throw "WOFF2 transformed loca has a transformLength"
    if entries.any (·.tag == tag) then throw "WOFF2 table directory names a tag twice"
    entries := entries.push ⟨tag, transformed, origLength, src, srcLength⟩
    src := src + srcLength
  return (entries, c.pos)

/-- The sfnt of a WOFF2 file. -/
def toSfnt (b : ByteArray) : Except String ByteArray := do
  if b.size < 48 || !isWoff2 b then throw "not a WOFF2 file"
  let u16 (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i+1)).toNat
  let u32 (i : Nat) : Nat := u16 i * 65536 + u16 (i+2)
  let flavor := u32 4
  if flavor == 0x74746366 then throw "WOFF2 font collections are not read"
  if u32 8 != b.size then throw "WOFF2 header length is not the file's length"
  let numTables := u16 12
  if numTables == 0 || numTables > maxTables then throw "WOFF2 table count is not valid"
  let compLength := u32 20
  let metaOffset := u32 28
  let metaLength := u32 32
  let privOffset := u32 40
  let privLength := u32 44
  let (entries, compOffset) ← readDirectory b numTables
  -- §3: the compressed data, then the metadata, then the private data, each at a four-byte
  -- boundary, and nothing after them.
  let mut next := Woff.pad4 (compOffset + compLength)
  if metaOffset != 0 then
    if metaOffset != next || metaOffset + metaLength > b.size then
      throw "WOFF2 metadata is not where the header says"
    next := Woff.pad4 (metaOffset + metaLength)
  if privOffset != 0 then
    if privOffset != next || privOffset + privLength > b.size then
      throw "WOFF2 private data is not where the header says"
    next := Woff.pad4 (privOffset + privLength)
  if next != Woff.pad4 b.size then throw "WOFF2 file has bytes the header does not account for"
  if compOffset + compLength > b.size then throw "WOFF2 compressed data runs past the end of the file"
  let total := entries.foldl (fun s e => s + e.srcLength) 0
  if total > maxSfntBytes then throw s!"WOFF2 font exceeds {maxSfntBytes} bytes"
  let stream ← Brotli.decompress (b.extract compOffset (compOffset + compLength)) total
  if stream.size != total then throw "WOFF2 compressed data gives another size than the table directory"
  -- glyf and loca: both or neither, both transformed or neither
  let glyfE := entries.find? (·.tag == tagGlyf)
  let locaE := entries.find? (·.tag == tagLoca)
  match glyfE, locaE with
  | some g, some l =>
    if g.transformed != l.transformed then throw "WOFF2 transforms only one of glyf and loca"
  | none, none => pure ()
  | _, _ => throw "WOFF2 font has only one of glyf and loca"
  -- sorted by tag: an insertion sort in loops (at most `maxTables` entries; `Array.qsort`
  -- recurses)
  let mut sorted : Array Entry := Array.emptyWithCapacity entries.size
  for e in entries do
    let mut k := sorted.size
    sorted := sorted.push e
    for _ in [0:sorted.size] do
      if k == 0 || sorted[k-1]!.tag < e.tag then break
      sorted := sorted.set! k sorted[k-1]!
      k := k - 1
    sorted := sorted.set! k e
  -- the tables in output order, with their bytes
  let mut tables : Array (Nat × ByteArray) := #[]
  let mut xMins : Array Int := #[]
  let mut size := 12 + 16 * numTables
  for e in sorted do
    if e.tag == tagLoca && e.transformed then continue
    if e.tag == tagGlyf && e.transformed then
      let locaLength := (locaE.map (·.origLength)).getD 0
      let (glyf, loca, xm) ← reconstructGlyf stream e.srcOffset e.srcLength locaLength
      xMins := xm
      tables := tables.push (tagGlyf, glyf) |>.push (tagLoca, loca)
      size := size + Woff.pad4 glyf.size + Woff.pad4 loca.size
    else if e.tag == tagHmtx && e.transformed then
      if xMins.isEmpty then throw "WOFF2 hmtx is transformed but glyf is not"
      let numHMetrics ← match entries.find? (·.tag == tagHhea) with
        | some h =>
          if h.srcLength < 36 then throw "WOFF2 hhea is too short"
          else pure ((stream.get! (h.srcOffset + 34)).toNat * 256 + (stream.get! (h.srcOffset + 35)).toNat)
        | none => throw "WOFF2 hmtx is transformed but the font has no hhea"
      let t ← reconstructHmtx stream e.srcOffset e.srcLength numHMetrics xMins
      tables := tables.push (tagHmtx, t)
      size := size + Woff.pad4 t.size
    else
      let mut t := stream.extract e.srcOffset (e.srcOffset + e.srcLength)
      if e.tag == tagHead then
        if t.size < 12 then throw "WOFF2 head is too short"
        -- checkSumAdjustment is computed below
        for k in [8:12] do t := t.set! k 0
      tables := tables.push (e.tag, t)
      size := size + Woff.pad4 t.size
    if size > maxSfntBytes then throw s!"WOFF2 font exceeds {maxSfntBytes} bytes"
  -- the offset table, the table records (sorted by tag), the tables
  let (power, exponent) := Woff.searchPower numTables
  let mut out := ByteArray.emptyWithCapacity size
  out := push32 out flavor
  out := push16 out numTables
  out := push16 out (power * 16)
  out := push16 out exponent
  out := push16 out (numTables * 16 - power * 16)
  let mut offsets : Array (Nat × Nat × Nat × Nat) := #[]
  let mut at_ := 12 + 16 * numTables
  for (tag, t) in tables do
    offsets := offsets.push (tag, checksum t 0 t.size, at_, t.size)
    at_ := at_ + Woff.pad4 t.size
  for e in sorted do
    match offsets.find? (·.1 == e.tag) with
    | some (tag, sum, off, len) => out := push32 (push32 (push32 (push32 out tag) sum) off) len
    | none => throw "WOFF2 table was not made"
  for (_, t) in tables do
    out := pad4 (out ++ t)
  if out.size != size then throw "WOFF2 font: the sfnt made has another size than its tables give"
  -- head checkSumAdjustment: 0xB1B0AFBA less the sum of the whole font
  match offsets.find? (·.1 == tagHead) with
  | some (_, _, off, _) =>
    let adj := (0xB1B0AFBA + 4294967296 - checksum out 0 out.size) % 4294967296
    out := out.set! (off + 8) (adj / 16777216).toUInt8 |>.set! (off + 9) (adj / 65536 % 256).toUInt8
      |>.set! (off + 10) (adj / 256 % 256).toUInt8 |>.set! (off + 11) (adj % 256).toUInt8
  | none => pure ()
  return out

/-- Bytes as the font reader takes them: a WOFF2 file or a WOFF 1.0 file as its sfnt,
anything else as it is. -/
def sfntOf (b : ByteArray) : Except String ByteArray :=
  if isWoff2 b then toSfnt b else Woff.sfntOf b

/-- Bytes that are neither WOFF2 nor WOFF 1.0 pass through unchanged. -/
theorem sfntOf_other (b : ByteArray) (h2 : isWoff2 b = false) (h1 : Woff.isWoff b = false) :
    sfntOf b = .ok b := by
  simp [sfntOf, h2, Woff.sfntOf_other b h1]

end L4Factoidal.Rendering.Woff2
