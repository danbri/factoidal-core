/-
L4Factoidal.Codec.Inflate — DEFLATE (RFC 1951): the decoder, and a
writer that uses only stored blocks.

Spec: RFC 1951 "DEFLATE Compressed Data Format Specification version
1.3". A stream is a sequence of blocks; each is stored (3.2.4), or
compressed with the fixed Huffman code (3.2.6) or with a dynamic one
(3.2.7), and a block ends the stream when its BFINAL bit is set.

## The decoder

Canonical Huffman codes are decoded bit by bit against the per-length
counts, as RFC 1951 section 3.2.2 describes them. The decoder is a
total function: every loop is bounded, a truncated stream, an
over-long distance, a bad code and a stored block whose LEN and NLEN
disagree are errors with a message, and the output is capped so a hostile
stream cannot ask for gigabytes.

## The writer

`deflateStored` emits stored blocks, which every inflater reads. It does
not compress; the point of a writer here is a gzip, zip or tar.gz file
that RML-IO can name as a target, and an exporter whose bytes any reader
accepts. A compressing writer can replace it without changing a caller.
-/
import L4Factoidal.Codec.Crc32

namespace L4Factoidal.Codec

structure Bits where
  data : ByteArray
  /-- The next bit to read, counted from the start of `data`; bits are
      read least-significant first (RFC 1951 section 3.1.1). -/
  pos  : Nat

abbrev BitM := StateT Bits (Except String)

def readBit : BitM Nat := do
  let s ← get
  let i := s.pos / 8
  if i < s.data.size then
    set { s with pos := s.pos + 1 }
    pure ((s.data.get! i).toNat >>> (s.pos % 8) % 2)
  else throw "unexpected end of compressed data"

/-- `n` bits as a number, first bit least significant. -/
def readBits (n : Nat) : BitM Nat := do
  let mut v := 0
  for i in [0:n] do
    v := v ||| ((← readBit) <<< i)
  pure v

/-- Skip to the next byte boundary. -/
def alignByte : BitM Unit :=
  modify (fun s => { s with pos := (s.pos + 7) / 8 * 8 })

/-- A canonical Huffman code: how many codes there are of each length,
    and the symbols in code order. -/
structure Huff where
  count  : Array Nat
  symbol : Array Nat

def buildHuff (lengths : Array Nat) : Huff := Id.run do
  let mut count := Array.replicate 16 0
  for l in lengths do
    count := count.modify l (· + 1)
  let mut offs := Array.replicate 17 0
  for len in [1:16] do
    offs := offs.set! (len + 1) (offs[len]! + count[len]!)
  let mut symbol := Array.replicate lengths.size 0
  for sym in [0:lengths.size] do
    let l := lengths[sym]!
    if l != 0 then
      symbol := symbol.set! offs[l]! sym
      offs := offs.modify l (· + 1)
  pure { count := count, symbol := symbol }

/-- Decode one symbol: RFC 1951 section 3.2.2, bit by bit. -/
def decodeSym (h : Huff) : BitM Nat := do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  for len in [1:16] do
    code := code ||| (← readBit)
    let count := h.count[len]!
    if code < first + count then
      return h.symbol[index + (code - first)]!
    index := index + count
    first := (first + count) <<< 1
    code := code <<< 1
  throw "invalid Huffman code"

private def lengthBase : Array Nat :=
  #[3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258]
private def lengthExtra : Array Nat :=
  #[0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0]
private def distBase : Array Nat :=
  #[1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577]
private def distExtra : Array Nat :=
  #[0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13]

/-- The most output one stream may produce (256 MiB). -/
def maxInflated : Nat := 256 * 1024 * 1024

/-- Decode the symbols of one compressed block into `out`. -/
def inflateCodes (lit dist : Huff) (out : ByteArray) : BitM ByteArray := do
  let mut out := out
  for _ in [0:maxInflated] do
    let sym ← decodeSym lit
    if sym < 256 then
      out := out.push sym.toUInt8
    else if sym == 256 then
      return out
    else
      let s := sym - 257
      if s ≥ 29 then throw "invalid length symbol"
      let len := lengthBase[s]! + (← readBits lengthExtra[s]!)
      let ds ← decodeSym dist
      if ds ≥ 30 then throw "invalid distance symbol"
      let d := distBase[ds]! + (← readBits distExtra[ds]!)
      if d > out.size then throw "distance reaches before the start of the output"
      if out.size + len > maxInflated then throw "output too large"
      for _ in [0:len] do
        out := out.push (out.get! (out.size - d))
  throw "output too large"

private def fixedLit : Huff :=
  buildHuff ((Array.replicate 144 8) ++ (Array.replicate 112 9) ++
             (Array.replicate 24 7) ++ (Array.replicate 8 8))
private def fixedDist : Huff := buildHuff (Array.replicate 30 5)

private def clOrder : Array Nat := #[16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15]

/-- RFC 1951 section 3.2.7: the code lengths of a dynamic block, then its
    two codes. -/
def readDynamic : BitM (Huff × Huff) := do
  let nlen := (← readBits 5) + 257
  let ndist := (← readBits 5) + 1
  let ncode := (← readBits 4) + 4
  if nlen > 286 || ndist > 30 then throw "too many length or distance codes"
  let mut cl := Array.replicate 19 0
  for i in [0:ncode] do
    cl := cl.set! clOrder[i]! (← readBits 3)
  let clh := buildHuff cl
  let mut lens : Array Nat := #[]
  for _ in [0:nlen + ndist] do
    if lens.size ≥ nlen + ndist then break
    let sym ← decodeSym clh
    if sym < 16 then
      lens := lens.push sym
    else
      let (v, rep) ←
        if sym == 16 then
          if lens.isEmpty then throw "a repeat with nothing to repeat"
          pure (lens.back!, 3 + (← readBits 2))
        else if sym == 17 then pure (0, 3 + (← readBits 3))
        else pure (0, 11 + (← readBits 7))
      if lens.size + rep > nlen + ndist then throw "a repeat runs past the code lengths"
      for _ in [0:rep] do
        lens := lens.push v
  if lens.size != nlen + ndist then throw "code lengths do not add up"
  pure (buildHuff (lens.extract 0 nlen), buildHuff (lens.extract nlen (nlen + ndist)))

/-- A stored block: LEN, its complement, then the bytes. -/
def inflateStored (out : ByteArray) : BitM ByteArray := do
  alignByte
  let len := (← readBits 16)
  let nlen := (← readBits 16)
  if len ^^^ nlen != 0xFFFF then throw "stored block LEN and NLEN disagree"
  let s ← get
  let start := s.pos / 8
  if start + len > s.data.size then throw "stored block runs past the end of the data"
  set { s with pos := s.pos + 8 * len }
  pure (out ++ s.data.extract start (start + len))

/-- Decode a whole DEFLATE stream starting at byte `start` of `b`. The
    result is the output and the offset of the first byte after the
    stream. -/
def inflateAt (b : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := do
  let act : BitM ByteArray := do
    let mut out := ByteArray.empty
    for _ in [0:b.size * 8 + 1] do
      let final ← readBit
      let typ ← readBits 2
      out ← match typ with
        | 0 => inflateStored out
        | 1 => inflateCodes fixedLit fixedDist out
        | 2 => do
            let (lit, dist) ← readDynamic
            inflateCodes lit dist out
        | _ => throw "invalid block type"
      if final == 1 then break
    pure out
  let (out, st) ← act.run { data := b, pos := start * 8 }
  pure (out, (st.pos + 7) / 8)

def inflate (b : ByteArray) : Except String ByteArray :=
  (inflateAt b 0).map (·.1)

/-- Stored DEFLATE blocks, at most 65535 bytes each. -/
def deflateStored (b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  let n := b.size
  for _ in [0:n / 65535 + 1] do
    let len := min 65535 (n - i)
    let final := i + len ≥ n
    out := out.push (if final then 1 else 0)
    out := out.push (len % 256).toUInt8 |>.push (len / 256).toUInt8
    out := out.push ((65535 - len) % 256).toUInt8 |>.push ((65535 - len) / 256).toUInt8
    out := out ++ b.extract i (i + len)
    i := i + len
  pure out

end L4Factoidal.Codec
