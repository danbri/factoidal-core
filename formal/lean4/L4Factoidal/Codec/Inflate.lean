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

/-! ## Build-time checks

The vectors were produced by `gzip` and `zlib` and are the deflate
bodies only. -/

private def bytes (xs : List Nat) : ByteArray := ByteArray.mk (xs.map UInt8.ofNat).toArray

-- A fixed-Huffman block: "hello hello hello hello" (zlib level 9, raw).
#guard (inflate (bytes [0xcb, 0x48, 0xcd, 0xc9, 0xc9, 0x57, 0xc8, 0x40, 0x27, 0x01])).toOption ==
       some "hello hello hello hello".toUTF8
-- A dynamic-Huffman block (BTYPE=2): 300 words from a twelve-word vocabulary.
private def dynamicVector : ByteArray := bytes
  [
  0x6d, 0x55, 0x5b, 0x8e, 0xc3, 0x30, 0x08, 0xbc, 0x8a, 0xaf, 0xe6, 0xa8, 0xd1, 0xb6, 0x6a, 0xd2,
  0x46, 0xda, 0xec, 0x0f, 0xa7, 0x5f, 0xc7, 0x03, 0x66, 0xc0, 0x91, 0x5a, 0x42, 0xcc, 0xf0, 0x1a,
  0x63, 0x47, 0xd6, 0xb3, 0x96, 0x9f, 0xba, 0xef, 0xb5, 0x5c, 0xda, 0x56, 0xf7, 0xe5, 0x51, 0x4b,
  0xdd, 0x8e, 0x67, 0x2d, 0xcb, 0xb5, 0xf2, 0xfa, 0x9e, 0xaa, 0xc9, 0x25, 0xde, 0xf5, 0x38, 0xcc,
  0xde, 0x4d, 0x8f, 0x75, 0x3b, 0x83, 0x83, 0xfd, 0xfb, 0x0b, 0xac, 0x1e, 0x68, 0x1d, 0x58, 0x04,
  0x22, 0x90, 0xa6, 0xd6, 0x07, 0xe7, 0x81, 0x0e, 0xe9, 0x01, 0x38, 0x71, 0x8f, 0xad, 0x5d, 0x1c,
  0xbf, 0xaf, 0xed, 0xfb, 0x29, 0xde, 0x97, 0x77, 0xa0, 0x21, 0x14, 0xd1, 0xd7, 0x35, 0x1d, 0x90,
  0x04, 0x82, 0x54, 0x2b, 0x52, 0xc9, 0x1a, 0x5a, 0xd9, 0xff, 0x18, 0xcf, 0x95, 0x02, 0x7e, 0x3e,
  0x89, 0xd0, 0xd1, 0x7c, 0x0f, 0x02, 0x13, 0xc0, 0xd0, 0xfb, 0xb2, 0x15, 0x06, 0x7f, 0x94, 0xd4,
  0xb2, 0x10, 0x87, 0x37, 0x0d, 0x90, 0x7f, 0xc3, 0xe2, 0xcd, 0x00, 0xc4, 0x71, 0xdc, 0x02, 0xc4,
  0x16, 0x57, 0xd5, 0x6f, 0x10, 0xaa, 0x65, 0xbb, 0x17, 0x42, 0x09, 0xe7, 0x92, 0xdc, 0x04, 0xeb,
  0x9e, 0xd4, 0x8a, 0xc1, 0x7a, 0xf3, 0xe3, 0xd8, 0xc8, 0xd6, 0x16, 0xdb, 0xcf, 0x80, 0x61, 0x02,
  0xf4, 0x25, 0xf6, 0x75, 0x81, 0x9d, 0x5b, 0xf1, 0x40, 0x44, 0x06, 0xfa, 0x22, 0x06, 0x60, 0xe3,
  0xd9, 0xb1, 0x70, 0x89, 0x69, 0x63, 0x82, 0x1a, 0xc9, 0x24, 0x81, 0xc8, 0xe0, 0x3e, 0x2d, 0x6b,
  0x91, 0x42, 0x95, 0xfa, 0xb0, 0xd3, 0xbc, 0x41, 0x85, 0x0c, 0x27, 0x81, 0x07, 0x9c, 0x09, 0x4e,
  0x73, 0xae, 0x4f, 0xe0, 0x52, 0x2d, 0x92, 0x07, 0x9a, 0xa8, 0x69, 0xf5, 0xd1, 0xce, 0xc6, 0xd3,
  0xd7, 0x6c, 0x9c, 0x37, 0x0f, 0xf1, 0x74, 0xcc, 0x03, 0x2c, 0xd3, 0x4c, 0x67, 0x1c, 0x38, 0x6a,
  0x7e, 0xba, 0x53, 0x96, 0x7c, 0x43, 0xe4, 0x33, 0x7c, 0xef, 0x81, 0xf0, 0x7e, 0x45, 0xc0, 0xcb,
  0x0a, 0x52, 0x8a, 0xc8, 0x55, 0xd2, 0x06, 0x53, 0x17, 0xb3, 0x34, 0xff, 0x25, 0x15, 0x6f, 0x67,
  0x80, 0x66, 0x77, 0x0c, 0x39, 0x95, 0xcd, 0x5c, 0xf8, 0xae, 0xc4, 0x4d, 0xa0, 0x6b, 0x2c, 0x1d,
  0x83, 0x25, 0x65, 0xc8, 0x11, 0xc4, 0xdb, 0xef, 0x26, 0x17, 0x3c, 0x79, 0xcc, 0x0f, 0x74, 0x9f,
  0xf5, 0x31, 0xf8, 0x14, 0x25, 0xde, 0x2a, 0xa8, 0x0e, 0x32, 0x76, 0x1a, 0xaf, 0xac, 0x06, 0x9d,
  0xe8, 0x35, 0x92, 0xe4, 0xe6, 0x9b, 0xf0, 0x0f ]
private def dynamicText : String :=
  "zeta gamma eta lambda alpha beta iota beta zeta kappa alpha iota delta alpha beta eta eta beta delta beta iota eta alpha kappa beta delta lambda lambda kappa alpha kappa kappa eta alpha delta alpha iota gamma epsilon eta gamma iota beta kappa epsilon iota lambda gamma beta kappa kappa lambda delta zeta beta iota mu beta kappa alpha kappa delta theta lambda iota eta zeta theta kappa theta zeta epsilon delta gamma mu delta beta kappa epsilon iota theta zeta mu theta epsilon kappa beta beta iota eta gamma zeta gamma theta eta alpha lambda beta iota kappa zeta zeta mu zeta kappa theta kappa theta beta beta epsilon theta mu lambda beta alpha mu mu epsilon lambda kappa lambda theta epsilon mu eta lambda zeta alpha theta zeta gamma kappa beta theta alpha delta epsilon gamma mu delta eta eta theta beta gamma theta eta iota epsilon gamma eta iota epsilon mu eta zeta lambda eta delta gamma beta gamma gamma delta lambda delta alpha theta kappa gamma epsilon epsilon alpha gamma eta iota zeta kappa kappa zeta gamma mu iota kappa lambda lambda mu alpha theta lambda iota eta eta eta eta beta theta lambda eta alpha delta beta delta theta gamma beta zeta kappa alpha beta alpha kappa gamma iota beta zeta kappa alpha beta delta kappa eta gamma lambda epsilon zeta kappa zeta theta beta beta theta theta theta theta epsilon beta gamma beta mu zeta mu epsilon theta mu gamma iota alpha delta iota zeta gamma mu iota alpha iota epsilon lambda beta mu epsilon iota zeta gamma zeta delta iota iota iota zeta lambda delta kappa delta delta eta mu delta delta iota theta zeta mu alpha alpha epsilon theta epsilon delta mu kappa zeta theta mu zeta zeta beta delta beta"
#guard (dynamicVector.get! 0).toNat / 2 % 4 == 2
#guard (inflate dynamicVector).toOption == some dynamicText.toUTF8
-- A stored block, written by hand: BFINAL=1 BTYPE=00, LEN=3.
#guard (inflate (bytes [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61, 0x62, 0x63])).toOption == some "abc".toUTF8
-- Empty input and an empty stored block.
#guard (inflate (bytes [0x01, 0x00, 0x00, 0xff, 0xff])).toOption == some ByteArray.empty
-- Errors, not guesses: truncation, a bad NLEN, a bad block type.
#guard (inflate (bytes [0x01, 0x03, 0x00, 0xfc, 0xff, 0x61])).toOption.isNone
#guard (inflate (bytes [0x01, 0x03, 0x00, 0xfd, 0xff, 0x61, 0x62, 0x63])).toOption.isNone
#guard (inflate (bytes [0x07])).toOption.isNone
#guard (inflate ByteArray.empty).toOption.isNone
-- The writer's output is read back, for empty, short and multi-block input.
#guard (inflate (deflateStored ByteArray.empty)).toOption == some ByteArray.empty
#guard (inflate (deflateStored "abc".toUTF8)).toOption == some "abc".toUTF8
private def big : ByteArray := ByteArray.mk ((List.range 70000).map (fun i => UInt8.ofNat (i % 251))).toArray
#guard (inflate (deflateStored big)).toOption == some big
#guard (deflateStored big).size == big.size + 2 * 5

end L4Factoidal.Codec
