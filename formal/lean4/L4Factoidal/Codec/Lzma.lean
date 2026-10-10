/-
L4Factoidal.Codec.Lzma — the LZMA decoder and the LZMA2 chunk format that
the xz container carries.

Spec: the LZMA specification (Igor Pavlov, `lzma-specification.txt` in the
LZMA SDK, section "The range decoder" to "LZMA decoding") and the xz file
format specification (Lasse Collin, version 1.0.4, section 5.3.1 "LZMA2").
The names below follow the first: `isMatch`, `isRep`, `isRepG0`..`isRepG2`,
`isRep0Long`, `posSlot`, `align`, the two length decoders.

## Shape

The decoder state is one structure and every step is a function of it in
`StateT Lz (Except String)`. The probability model is one flat `Array
UInt16` with the offsets below, so a bit decode updates it in place when the
state is not shared. Decoding is by `for` loops bounded by the sizes the
chunk header gives; a chunk of `n` output bytes takes at most `n` symbols,
since a symbol is at least one byte.

## LZMA2

A chunk is a control byte and its data. `0x00` ends the stream, `0x01` and
`0x02` are uncompressed chunks (with and without a dictionary reset), and
`0x80` and up are LZMA chunks; their bits 5 and 6 say how much of the
decoder state the chunk resets (nothing, the state, the state and the
properties, all of them and the dictionary). The decoder checks what the
format requires: the first chunk resets the dictionary, an LZMA chunk comes
after the properties are known, `lc + lp` is at most 4, a chunk's range
decoder ends with its code at zero and its input used up, and no distance
reaches before the last dictionary reset.
-/

namespace L4Factoidal.Codec.Lzma

/-! ## Layout of the probability model -/

private def offIsMatch : Nat := 0
private def offIsRep : Nat := 192
private def offIsRepG0 : Nat := 204
private def offIsRepG1 : Nat := 216
private def offIsRepG2 : Nat := 228
private def offIsRep0Long : Nat := 240
private def offPosSlot : Nat := 432
private def offPosDec : Nat := 688
private def offAlign : Nat := 803
private def offLen : Nat := 819
private def offRepLen : Nat := 1333
private def offLiteral : Nat := 1847

/-- The number of probabilities for a literal context of `lc + lp` bits. -/
def numProbs (lc lp : Nat) : Nat := offLiteral + (0x300 <<< (lc + lp))

structure Lz where
  probs     : Array UInt16
  inp       : ByteArray
  inPos     : Nat := 0
  range     : UInt32 := 0xFFFFFFFF
  code      : UInt32 := 0
  out       : ByteArray
  /-- Where in `out` the dictionary starts: the last dictionary reset. -/
  dictStart : Nat := 0
  state     : Nat := 0
  rep0      : Nat := 0
  rep1      : Nat := 0
  rep2      : Nat := 0
  rep3      : Nat := 0
  lc        : Nat := 3
  lp        : Nat := 0
  pb        : Nat := 2

abbrev M := StateT Lz (Except String)

/-- Read one more input byte when the range has dropped below 2^24. Past
    the end of the input the byte is zero; `decodeChunk` finds the overrun
    by comparing the input position with the chunk's size. -/
@[inline] private def norm (s : Lz) : Lz :=
  if s.range < 0x1000000 then
    let b : UInt32 := if h : s.inPos < s.inp.size then (s.inp[s.inPos]).toUInt32 else 0
    { s with range := s.range <<< (8 : UInt32), code := (s.code <<< (8 : UInt32)) ||| b, inPos := s.inPos + 1 }
  else s

/-- Decode one bit with the probability at `i`. -/
private def bit (i : Nat) : M Nat :=
  modifyGet fun s =>
    let p : UInt32 := (s.probs.getD i 1024).toUInt32
    let bound : UInt32 := (s.range >>> (11 : UInt32)) * p
    if s.code < bound then
      (0, norm { s with range := bound, probs := s.probs.set! i (p + ((2048 - p) >>> (5 : UInt32))).toUInt16 })
    else
      (1, norm { s with range := s.range - bound, code := s.code - bound,
                        probs := s.probs.set! i (p - (p >>> (5 : UInt32))).toUInt16 })

/-- `n` bits with probability one half each, most significant first. -/
private def direct (n : Nat) : M Nat := do
  let mut res : Nat := 0
  for _ in [0:n] do
    let b ← modifyGet fun s =>
      let r : UInt32 := s.range >>> (1 : UInt32)
      let c : UInt32 := s.code - r
      let t : UInt32 := 0 - (c >>> (31 : UInt32))
      (((t + 1).toNat), norm { s with range := r, code := c + (r &&& t) })
    res := (res <<< 1) + b
  return res

/-- A bit tree of `numBits` levels at `base`, most significant bit first. -/
private def bitTree (base numBits : Nat) : M Nat := do
  let mut m : Nat := 1
  for _ in [0:numBits] do
    let b ← bit (base + m)
    m := (m <<< 1) + b
  return m - (1 <<< numBits)

/-- A bit tree of `numBits` levels at `base`, least significant bit first. -/
private def bitTreeRev (base numBits : Nat) : M Nat := do
  let mut m : Nat := 1
  let mut sym : Nat := 0
  for i in [0:numBits] do
    let b ← bit (base + m)
    m := (m <<< 1) + b
    sym := sym ||| (b <<< i)
  return sym

/-- A length: the choice bits, then a low, mid or high tree. The result is
    the length minus the minimum match length of 2. -/
private def lenDecode (off posState : Nat) : M Nat := do
  let c ← bit off
  if c == 0 then bitTree (off + 2 + posState * 8) 3
  else
    let c2 ← bit (off + 1)
    if c2 == 0 then return 8 + (← bitTree (off + 130 + posState * 8) 3)
    else return 16 + (← bitTree (off + 258) 8)

/-- A match distance, minus one; `len` is the decoded length minus 2. -/
private def distance (len : Nat) : M Nat := do
  let posSlot ← bitTree (offPosSlot + (min len 3) * 64) 6
  if posSlot < 4 then return posSlot
  else
    let numDirect := (posSlot >>> 1) - 1
    let base := (2 ||| (posSlot &&& 1)) <<< numDirect
    if posSlot < 14 then
      return base + (← bitTreeRev (offPosDec + base - posSlot) numDirect)
    else
      let high ← direct (numDirect - 4)
      let low ← bitTreeRev offAlign 4
      return base + (high <<< 4) + low

/-- A literal byte, by the `lc` bits of the previous byte and the `lp` bits
    of the position; after a match the byte at the last distance steers
    the first bits. -/
private def literal : M Unit := do
  let s ← get
  let pos := s.out.size - s.dictStart
  let prev : Nat := if pos > 0 then (s.out.get! (s.out.size - 1)).toNat else 0
  let litState := ((pos &&& ((1 <<< s.lp) - 1)) <<< s.lc) + (prev >>> (8 - s.lc))
  let base := offLiteral + 0x300 * litState
  let mut symbol : Nat := 1
  if s.state ≥ 7 then
    let mut matchByte : Nat := (s.out.get! (s.out.size - s.rep0 - 1)).toNat
    for _ in [0:8] do
      if symbol ≥ 0x100 then break
      let matchBit := (matchByte >>> 7) &&& 1
      matchByte := (matchByte <<< 1) &&& 0xFF
      let b ← bit (base + ((1 + matchBit) <<< 8) + symbol)
      symbol := (symbol <<< 1) ||| b
      if matchBit != b then break
  for _ in [0:8] do
    if symbol ≥ 0x100 then break
    let b ← bit (base + symbol)
    symbol := (symbol <<< 1) ||| b
  modify fun s => { s with
    out := s.out.push (symbol - 0x100).toUInt8
    state := if s.state < 4 then 0 else if s.state < 10 then s.state - 3 else s.state - 6 }

/-- Copy `len` bytes from `rep0 + 1` back, a byte at a time, so a match may
    overlap its own output. -/
private def copyMatch (len limit : Nat) : M Unit := do
  let s ← get
  let pos := s.out.size - s.dictStart
  if s.rep0 ≥ pos then throw "an LZMA distance reaches before the start of the dictionary"
  if s.out.size + len > limit then throw "an LZMA match runs past the end of its chunk"
  let mut out := s.out
  for _ in [0:len] do
    out := out.push (out.get! (out.size - s.rep0 - 1))
  set { s with out := out }

/-- Decode symbols until the output has `limit` bytes. -/
private def decodeSymbols (limit : Nat) : M Unit := do
  let start := (← get).out.size
  for _ in [0:limit - start] do
    let s ← get
    if s.out.size ≥ limit then break
    let pos := s.out.size - s.dictStart
    let posState := pos &&& ((1 <<< s.pb) - 1)
    let m ← bit (offIsMatch + (s.state <<< 4) + posState)
    if m == 0 then literal
    else
      let r ← bit (offIsRep + s.state)
      if r == 0 then
        modify fun s => { s with rep3 := s.rep2, rep2 := s.rep1, rep1 := s.rep0 }
        let len ← lenDecode offLen posState
        modify fun s => { s with state := if s.state < 7 then 7 else 10 }
        let d ← distance len
        if d == 0xFFFFFFFF then throw "an LZMA end marker inside an LZMA2 chunk"
        modify fun s => { s with rep0 := d }
        copyMatch (len + 2) limit
      else
        if pos == 0 then throw "an LZMA repeat match with an empty dictionary"
        let g0 ← bit (offIsRepG0 + s.state)
        if g0 == 0 then
          let long ← bit (offIsRep0Long + (s.state <<< 4) + posState)
          if long == 0 then
            -- short repeat: one byte from the last distance
            modify fun s => { s with state := if s.state < 7 then 9 else 11 }
            copyMatch 1 limit
          else
            let len ← lenDecode offRepLen posState
            modify fun s => { s with state := if s.state < 7 then 8 else 11 }
            copyMatch (len + 2) limit
        else
          let g1 ← bit (offIsRepG1 + s.state)
          if g1 == 0 then
            modify fun s => { s with rep0 := s.rep1, rep1 := s.rep0 }
          else
            let g2 ← bit (offIsRepG2 + s.state)
            if g2 == 0 then
              modify fun s => { s with rep0 := s.rep2, rep2 := s.rep1, rep1 := s.rep0 }
            else
              modify fun s => { s with rep0 := s.rep3, rep3 := s.rep2, rep2 := s.rep1, rep1 := s.rep0 }
          let len ← lenDecode offRepLen posState
          modify fun s => { s with state := if s.state < 7 then 8 else 11 }
          copyMatch (len + 2) limit

/-! ## One LZMA chunk -/

/-- The decoder state at the start of a stream, for the properties `lc`,
    `lp`, `pb`. -/
def Lz.fresh (lc lp pb : Nat) : Lz :=
  { probs := Array.replicate (numProbs lc lp) 1024, inp := ByteArray.empty,
    out := ByteArray.empty, lc := lc, lp := lp, pb := pb }

/-- Reset the model and the match history, as a state reset does. -/
def Lz.resetState (s : Lz) : Lz :=
  { s with probs := Array.replicate (numProbs s.lc s.lp) 1024, state := 0,
           rep0 := 0, rep1 := 0, rep2 := 0, rep3 := 0 }

/-- Decode the range-coded bytes `inp` into `unc` more bytes of `s.out`. The
    range coder starts afresh (a zero byte, then four code bytes) and must
    end with its code at zero and every input byte used. -/
def decodeChunk (s : Lz) (inp : ByteArray) (unc : Nat) : Except String Lz := do
  if inp.size < 5 then throw "an LZMA chunk is shorter than its range coder header"
  if inp[0]! != 0 then throw "an LZMA chunk does not start with a zero byte"
  let code : UInt32 := ((inp[1]!.toUInt32 <<< (24 : UInt32)) ||| (inp[2]!.toUInt32 <<< (16 : UInt32)) |||
                        (inp[3]!.toUInt32 <<< (8 : UInt32)) ||| inp[4]!.toUInt32)
  let s0 : Lz := { s with inp := inp, inPos := 5, range := 0xFFFFFFFF, code := code }
  let limit := s0.out.size + unc
  let ((), s1) ← (decodeSymbols limit).run s0
  if s1.out.size != limit then throw "an LZMA chunk ended before its uncompressed size"
  if s1.inPos != inp.size then throw "an LZMA chunk did not use all of its input"
  if s1.code != 0 then throw "an LZMA chunk's range coder did not end at zero"
  return s1

/-! ## LZMA2 -/

private def byteAt (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat

/-- Decode the LZMA2 data of one xz block, starting at `start`: the
    uncompressed bytes, and the index after the end marker. -/
def lzma2Decode (data : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := do
  let mut lz : Lz := Lz.fresh 3 0 2
  let mut pos := start
  let mut needDict := true
  let mut needProps := true
  for _ in [0:data.size + 1] do
    if pos ≥ data.size then throw "the LZMA2 data is truncated"
    let c := byteAt data pos
    if c == 0 then return (lz.out, pos + 1)
    else if c == 1 || c == 2 then
      if pos + 3 > data.size then throw "the LZMA2 data is truncated"
      let n := byteAt data (pos + 1) * 256 + byteAt data (pos + 2) + 1
      if pos + 3 + n > data.size then throw "the LZMA2 data is truncated"
      if c == 1 then
        lz := { lz with dictStart := lz.out.size }
        needDict := false
        needProps := true
      else if needDict then throw "the first LZMA2 chunk does not reset the dictionary"
      lz := { lz with out := lz.out ++ data.extract (pos + 3) (pos + 3 + n) }
      pos := pos + 3 + n
    else if c ≥ 0x80 then
      let reset := (c >>> 5) &&& 3
      if needDict && reset < 3 then throw "the first LZMA2 chunk does not reset the dictionary"
      let hdr := if reset ≥ 2 then 6 else 5
      if pos + hdr > data.size then throw "the LZMA2 data is truncated"
      let unc := ((c &&& 0x1F) <<< 16) + byteAt data (pos + 1) * 256 + byteAt data (pos + 2) + 1
      let comp := byteAt data (pos + 3) * 256 + byteAt data (pos + 4) + 1
      if reset == 3 then
        lz := { lz with dictStart := lz.out.size }
        needDict := false
      if reset ≥ 2 then
        let props := byteAt data (pos + 5)
        if props ≥ 225 then throw "the LZMA properties byte is out of range"
        let lc := props % 9
        let lp := (props / 9) % 5
        let pb := props / 45
        if lc + lp > 4 then throw "an LZMA2 chunk has lc + lp above 4"
        lz := { lz with lc := lc, lp := lp, pb := pb }
        needProps := false
      else if needProps then throw "an LZMA2 chunk comes before the properties are known"
      if reset ≥ 1 then lz := lz.resetState
      if pos + hdr + comp > data.size then throw "the LZMA2 data is truncated"
      lz ← decodeChunk lz (data.extract (pos + hdr) (pos + hdr + comp)) unc
      pos := pos + hdr + comp
    else throw s!"the LZMA2 control byte {c} is not defined"
  throw "the LZMA2 data has no end marker"

end L4Factoidal.Codec.Lzma
