import L4Factoidal.Codec.BrotliData
import L4Factoidal.Codec.Zstd

/-!
# Brotli decoding (RFC 7932)

Spec: RFC 7932 "Brotli Compressed Data Format". A stream is a window size (section 9.1) and a
sequence of meta-blocks (section 9.2): metadata blocks (skipped), uncompressed blocks, and
compressed blocks. A compressed block has three block categories (literals, insert-and-copy
lengths, distances), each with block types and block switch commands (section 6); context
maps from (block type, context) to prefix codes (section 7); the prefix codes themselves
(section 3); and the commands (section 5): an insert of literals, then a copy from the
output already made (section 4, distances) or from the static dictionary (section 8, with the
transforms of Appendix B).

`decompress input limit` gives the whole output, or a refusal with a message. Output past
`limit` bytes is refused before it is made.

## Bit reading

Bits are read least-significant first from each byte (RFC 7932 section 1.5.1) at a bit
position held in the state monad. `Zstd.bitsAt` reads up to 56 bits at a bit offset, with
bytes past the end as 0; every read checks the position against the input size first, so a
truncated stream is a refusal, never a read of invented zero bits.

## Prefix codes

A prefix code is canonical (section 3.2): the code lengths give the codes. A symbol is decoded
with a 256-entry table indexed by the next 8 bits, for codes of at most 8 bits, and bit by bit
against the per-length counts (as RFC 1951 section 3.2.2 decoders do) for longer codes. A code
with one symbol uses no bits (section 3.4, NSYM = 1). A complex code (section 3.5) is accepted
only when its code lengths fill the code space exactly, as the reference decoder requires.

## Loops

Every loop is a `for` over a range bounded by a count read from the input and checked
against the input or the output limit first (block counts, code lengths, the bytes of a
meta-block). The command loop of a meta-block is bounded by the meta-block length plus the
input bits: a command either makes output or reads bits, and a stream that does neither is
refused. Buffers are `ByteArray` and `Array`.

## Differences from the reference decoder (google/brotli 1.1.0)

- Data after the end of the stream is refused (`decompress`), so that a container that gives
  the stream's exact length (WOFF2 `totalCompressedSize`) is checked.
- The large-window extension (WBITS above 24, not in RFC 7932) and shared dictionaries are
  not read; a stream that asks for them is refused.
-/
namespace L4Factoidal.Codec.Brotli

/-! ## Data: the dictionary, the transforms, the context table -/

/-- Base64 (RFC 4648 section 4) to bytes; characters outside the alphabet are skipped, padding
ends the data. -/
def base64Decode (s : String) : ByteArray := Id.run do
  let b := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (b.size / 4 * 3)
  let mut acc := 0
  let mut nbits := 0
  for i in [0:b.size] do
    let c := (b.get! i).toNat
    let v :=
      if c ≥ 65 && c ≤ 90 then c - 65
      else if c ≥ 97 && c ≤ 122 then c - 71
      else if c ≥ 48 && c ≤ 57 then c + 4
      else if c == 43 then 62
      else if c == 47 then 63
      else 64
    if c == 61 then break
    if v < 64 then
      acc := (acc % 65536) * 64 + v
      nbits := nbits + 6
      if nbits ≥ 8 then
        nbits := nbits - 8
        out := out.push (acc / 2 ^ nbits % 256).toUInt8
  return out

/-- Hexadecimal digits to bytes. -/
def hexDecode (s : String) : ByteArray := Id.run do
  let b := s.toUTF8
  let digit (c : Nat) : Nat := if c ≤ 57 then c - 48 else if c ≤ 70 then c - 55 else c - 87
  let mut out := ByteArray.emptyWithCapacity (b.size / 2)
  for i in [0:b.size / 2] do
    out := out.push (digit (b.get! (2*i)).toNat * 16 + digit (b.get! (2*i+1)).toNat).toUInt8
  return out

/-- The RFC 7932 Appendix A dictionary (122,784 bytes), decoded on first use. -/
def dictionary : Thunk ByteArray := Thunk.mk fun _ => base64Decode BrotliData.dictionaryBase64

/-- The context lookup table of section 7.1 (2,048 bytes). -/
def contextLut : ByteArray := hexDecode BrotliData.contextLutHex

/-- The transforms of Appendix B: type, prefix bytes, suffix bytes. -/
def transformTable : Array (Nat × ByteArray × ByteArray) :=
  BrotliData.transforms.map fun (t, p, s) => (t, p.toUTF8, s.toUTF8)

/-- NDBITS of section 8: the number of word-index bits of the dictionary words of each length
(0 for lengths with no words). -/
def ndBits : Array Nat := #[0,0,0,0,10,10,11,11,10,10,10,10,10,9,9,8,7,7,8,7,7,6,6,5,5]

/-- DOFFSET of section 8: where the words of each length start in the dictionary. -/
def dOffset : Array Nat := Id.run do
  let mut a := Array.replicate 26 0
  for l in [4:25] do
    a := a.set! (l+1) (a[l]! + l * 2 ^ ndBits[l]!)
  return a

/-! ## Transforms (Appendix B) -/

/-- The uppercase step of Appendix B at byte `i` of `w`: an ASCII lowercase letter is flipped;
the second byte of a two-byte UTF-8 sequence is xored with 32; the third byte of a longer one
with 5. Bytes past the end of the word are not touched. Gives the word and the step length. -/
def upperAt (w : ByteArray) (i : Nat) : ByteArray × Nat :=
  let c := w.get! i
  if c < 0xC0 then
    (if c ≥ 97 && c ≤ 122 then w.set! i (c ^^^ 32) else w, 1)
  else if c < 0xE0 then
    (if i + 1 < w.size then w.set! (i+1) (w.get! (i+1) ^^^ 32) else w, 2)
  else
    (if i + 2 < w.size then w.set! (i+2) (w.get! (i+2) ^^^ 5) else w, 3)

/-- Transform `t` (0 to 120) of a dictionary word: prefix, the word cut or uppercased, suffix. -/
def transformWord (word : ByteArray) (t : Nat) : ByteArray := Id.run do
  let (ty, pre, suf) := transformTable[t]!
  let mut w := word
  if ty ≤ 9 then
    w := word.extract 0 (word.size - ty)
  else if ty ≥ 12 && ty ≤ 20 then
    w := word.extract (ty - 11) word.size
  if ty == 10 && w.size > 0 then
    w := (upperAt w 0).1
  else if ty == 11 then
    let mut i := 0
    for _ in [0:w.size] do
      if i ≥ w.size then break
      let (w', step) := upperAt w i
      w := w'
      i := i + step
  return pre ++ w ++ suf

/-! ## Bit reading -/

/-- The decoder's monad: the bit position, and a refusal. -/
abbrev M := StateT Nat (Except String)

/-- `n` bits (`n ≤ 24`), least significant first. -/
@[inline] def readBits (d : ByteArray) (n : Nat) : M Nat := do
  let p ← get
  if p + n > d.size * 8 then throw "Brotli stream is truncated"
  set (p + n)
  return Zstd.bitsAt d p n

/-- Skip to the next byte boundary; the skipped bits must be zero (RFC 7932 section 9.2). -/
def alignZero (d : ByteArray) : M Unit := do
  let p ← get
  let q := (p + 7) / 8 * 8
  if q > d.size * 8 then throw "Brotli stream is truncated"
  if Zstd.bitsAt d p (q - p) != 0 then throw "Brotli padding bits are not zero"
  set q

/-- The number of bits of `x` (0 for 0): ALPHABET_BITS of section 3.4 is `bitCount (n-1)`. -/
def bitCount (x : Nat) : Nat := Id.run do
  let mut v := x
  let mut n := 0
  for _ in [0:64] do
    if v == 0 then break
    v := v / 2
    n := n + 1
  return n

/-! ## Prefix codes (section 3) -/

/-- A canonical prefix code. -/
structure Huff where
  /-- `count[l]`: how many codes have length `l` (1 to 15). -/
  count : Array Nat
  /-- The symbols in code order (by length, then by symbol). -/
  symbol : Array Nat
  /-- 256 entries indexed by the next 8 bits: `symbol * 16 + length`, or 0 for a code longer
  than 8 bits. -/
  root : Array Nat
  /-- The symbol of a code with one symbol, which uses no bits. -/
  single : Option Nat
  deriving Inhabited

/-- The prefix code with one symbol. -/
def Huff.one (s : Nat) : Huff := ⟨#[], #[], #[], some s⟩

/-- The canonical code of code lengths (each 0 to 15; 0 is no code). The caller has checked
that the lengths fill the code space. -/
def buildHuff (lens : Array Nat) : Huff := Id.run do
  let mut count := Array.replicate 16 0
  for l in lens do
    if l < 16 then count := count.modify l (· + 1)
  count := count.set! 0 0
  -- offsets of each length in the symbol list, and the first code of each length
  let mut offs := Array.replicate 17 0
  let mut next := Array.replicate 17 0
  let mut code := 0
  for l in [1:16] do
    offs := offs.set! (l+1) (offs[l]! + count[l]!)
    code := (code + count[l-1]!) * 2
    next := next.set! l code
  let mut symbol := Array.replicate (offs[16]!) 0
  let mut root := Array.replicate 256 0
  for s in [0:lens.size] do
    let l := lens[s]!
    if l != 0 && l < 16 then
      symbol := symbol.set! offs[l]! s
      offs := offs.modify l (· + 1)
      let c := next[l]!
      next := next.modify l (· + 1)
      if l ≤ 8 then
        -- the code's bits in stream order: its most significant bit is read first
        let mut rev := 0
        for k in [0:l] do
          rev := rev * 2 + (c / 2 ^ k) % 2
        for j in [0:2 ^ (8 - l)] do
          root := root.set! (rev + j * 2 ^ l) (s * 16 + l)
  return ⟨count, symbol, root, none⟩

/-- Decode one symbol. -/
def decodeSym (d : ByteArray) (h : Huff) : M Nat := do
  if let some s := h.single then return s
  let p ← get
  let total := d.size * 8
  let e := h.root[Zstd.bitsAt d p 8]!
  let len := e % 16
  if len != 0 then
    if p + len > total then throw "Brotli stream is truncated"
    set (p + len)
    return e / 16
  -- a code longer than 8 bits (or no code): bit by bit
  let mut code := 0
  let mut first := 0
  let mut index := 0
  let mut pos := p
  for l in [1:16] do
    if pos ≥ total then throw "Brotli stream is truncated"
    code := code + Zstd.bitsAt d pos 1
    pos := pos + 1
    let count := h.count[l]!
    if code < first + count then
      set pos
      return h.symbol[index + (code - first)]!
    index := index + count
    first := (first + count) * 2
    code := code * 2
  throw "Brotli prefix code has no symbol for these bits"

/-- The code of the code length code lengths (section 3.5), indexed by the next 4 bits:
the number of bits and the value. -/
private def clcLen : Array Nat := #[2,2,2,3,2,2,2,4,2,2,2,3,2,2,2,4]
private def clcVal : Array Nat := #[0,4,3,2,0,4,3,1,0,4,3,2,0,4,3,5]
/-- The order of the code length code lengths (section 3.5). -/
private def clcOrder : Array Nat := #[1,2,3,4,0,5,17,6,16,7,8,9,10,11,12,13,14,15]

/-- Read a prefix code over an alphabet of `alphabet` symbols (sections 3.4 and 3.5). -/
def readPrefixCode (d : ByteArray) (alphabet : Nat) : M Huff := do
  let hskip ← readBits d 2
  if hskip == 1 then
    -- simple prefix code (section 3.4)
    let nsym := (← readBits d 2) + 1
    let abits := bitCount (alphabet - 1)
    let mut syms : Array Nat := #[]
    for _ in [0:nsym] do
      let v ← readBits d abits
      if v ≥ alphabet then throw "Brotli simple prefix code names a symbol outside its alphabet"
      if syms.contains v then throw "Brotli simple prefix code names a symbol twice"
      syms := syms.push v
    if nsym == 1 then return Huff.one syms[0]!
    -- the tree-select bit is read only when NSYM is 4 (an action nested in an `if` term
    -- would run before the test)
    let mut lensOf : List Nat := if nsym == 2 then [1,1] else [1,2,2]
    if nsym == 4 then
      let treeSelect ← readBits d 1
      lensOf := if treeSelect == 0 then [2,2,2,2] else [1,2,3,3]
    let mut lens := Array.replicate alphabet 0
    for (s, l) in syms.toList.zip lensOf do
      lens := lens.set! s l
    return buildHuff lens
  -- complex prefix code (section 3.5): first the code length code lengths
  let mut clens := Array.replicate 18 0
  let mut space : Int := 32
  let mut num := 0
  for i in [hskip:18] do
    let p ← get
    let ix := Zstd.bitsAt d p 4
    let l := clcLen[ix]!
    if p + l > d.size * 8 then throw "Brotli stream is truncated"
    set (p + l)
    let v := clcVal[ix]!
    clens := clens.set! clcOrder[i]! v
    if v != 0 then
      space := space - Int.ofNat (32 / 2 ^ v)
      num := num + 1
      if space ≤ 0 then break
  if !(num == 1 || space == 0) then throw "Brotli code length code does not fill its code space"
  let clh : Huff ←
    if num == 1 then
      match (List.range 18).find? (fun s => clens[s]! != 0) with
      | some s => pure (Huff.one s)
      | none => throw "Brotli code length code is empty"
    else pure (buildHuff clens)
  -- then the code lengths of the symbols
  let mut lens := Array.replicate alphabet 0
  let mut sym := 0
  let mut prev := 8
  let mut repeat_ := 0
  let mut repeatLen := 0
  let mut space2 := 32768
  for _ in [0:alphabet] do
    if sym ≥ alphabet || space2 == 0 then break
    let c ← decodeSym d clh
    if c < 16 then
      lens := lens.set! sym c
      sym := sym + 1
      repeat_ := 0
      if c != 0 then
        prev := c
        if 32768 / 2 ^ c > space2 then throw "Brotli code lengths overfill their code space"
        space2 := space2 - 32768 / 2 ^ c
    else
      let extraBits := if c == 16 then 2 else 3
      let newLen := if c == 16 then prev else 0
      let extra ← readBits d extraBits
      if repeatLen != newLen then
        repeat_ := 0
        repeatLen := newLen
      let old := repeat_
      if repeat_ > 0 then repeat_ := (repeat_ - 2) * 2 ^ extraBits
      repeat_ := repeat_ + extra + 3
      let delta := repeat_ - old
      if sym + delta > alphabet then throw "Brotli code length repeat runs past the alphabet"
      if repeatLen != 0 then
        for k in [0:delta] do
          lens := lens.set! (sym + k) repeatLen
        if delta * (32768 / 2 ^ repeatLen) > space2 then
          throw "Brotli code lengths overfill their code space"
        space2 := space2 - delta * (32768 / 2 ^ repeatLen)
      sym := sym + delta
  if space2 != 0 then throw "Brotli code lengths do not fill their code space"
  return buildHuff lens

/-! ## Headers (sections 6, 7 and 9) -/

/-- A number of 1 to 256, less 1 (section 9.2, NBLTYPES and NTREES). -/
def readVarLen8 (d : ByteArray) : M Nat := do
  if (← readBits d 1) == 0 then return 0
  let n ← readBits d 3
  if n == 0 then return 1
  return 2 ^ n + (← readBits d n)

/-- The block count codes of section 6: base and extra bits. -/
private def blockBase : Array Nat :=
  #[1,5,9,13,17,25,33,41,49,65,81,97,113,145,177,209,241,305,369,497,753,1265,2289,4337,8433,16625]
private def blockExtra : Array Nat :=
  #[2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,6,6,7,8,9,10,11,12,13,24]

/-- A block count (section 6). -/
def readBlockLength (d : ByteArray) (h : Huff) : M Nat := do
  let s ← decodeSym d h
  return blockBase[s]! + (← readBits d blockExtra[s]!)

/-- One block category of a meta-block (section 6): the number of block types, the two codes
of its block switch commands, the current and the previous block type, and the count left in
the current block. -/
structure Cat where
  n : Nat
  typeCode : Huff
  lenCode : Huff
  cur : Nat
  prev : Nat
  left : Nat
  deriving Inhabited

/-- NBLTYPES and, if there are two or more, the two codes and the first block count. -/
def readCat (d : ByteArray) : M Cat := do
  let n := (← readVarLen8 d) + 1
  if n < 2 then return ⟨1, default, default, 0, 1, 16777216⟩
  let t ← readPrefixCode d (n + 2)
  let l ← readPrefixCode d 26
  let left ← readBlockLength d l
  return ⟨n, t, l, 0, 1, left⟩

/-- A block switch command (section 6): the new block type and its count. -/
def switchBlock (d : ByteArray) (c : Cat) : M Cat := do
  let s ← decodeSym d c.typeCode
  let len ← readBlockLength d c.lenCode
  let t0 := if s == 0 then c.prev else if s == 1 then c.cur + 1 else s - 2
  let t := if t0 ≥ c.n then t0 - c.n else t0
  return { c with cur := t, prev := c.cur, left := len }

/-- Count one symbol of a category, with a block switch first when its block is used up. -/
def stepCat (d : ByteArray) (c : Cat) : M Cat := do
  if c.n < 2 then return c
  let c ← if c.left == 0 then switchBlock d c else pure c
  if c.left == 0 then throw "Brotli block count is zero"
  return { c with left := c.left - 1 }

/-- A context map of `size` entries over `ntrees` prefix codes (section 7.3). -/
def readContextMap (d : ByteArray) (size ntrees : Nat) : M (Array Nat) := do
  if ntrees < 2 then return Array.replicate size 0
  let useRle ← readBits d 1
  let rleMax ← if useRle == 1 then (· + 1) <$> readBits d 4 else pure 0
  let h ← readPrefixCode d (ntrees + rleMax)
  let mut map : Array Nat := Array.emptyWithCapacity size
  for _ in [0:size] do
    if map.size ≥ size then break
    let c ← decodeSym d h
    if c == 0 then map := map.push 0
    else if c ≤ rleMax then
      let reps := 2 ^ c + (← readBits d c)
      if map.size + reps > size then throw "Brotli context map run is longer than the map"
      for _ in [0:reps] do map := map.push 0
    else map := map.push (c - rleMax)
  if map.size != size then throw "Brotli context map is short"
  if (← readBits d 1) == 1 then
    -- inverse move-to-front (section 7.3)
    let mut mtf := (Array.range 256)
    for i in [0:size] do
      let idx := map[i]!
      let v := mtf[idx]!
      map := map.set! i v
      if idx > 0 then
        let mut m := mtf
        for k in [0:idx] do
          m := m.set! (idx - k) m[idx - k - 1]!
        mtf := m.set! 0 v
  return map

/-! ## Commands (sections 4 and 5) -/

private def insBase : Array Nat :=
  #[0,1,2,3,4,5,6,8,10,14,18,26,34,50,66,98,130,194,322,578,1090,2114,6210,22594]
private def insExtra : Array Nat :=
  #[0,0,0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,7,8,9,10,12,14,24]
private def copyBase : Array Nat :=
  #[2,3,4,5,6,7,8,9,10,12,14,18,22,30,38,54,70,102,134,198,326,582,1094,2118]
private def copyExtra : Array Nat :=
  #[0,0,0,0,0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,7,8,9,10,24]
/-- The cells of the insert-and-copy alphabet (section 5): first insert code, first copy code. -/
private def cellIns : Array Nat := #[0,0,0,0,8,8,0,16,8,16,16]
private def cellCopy : Array Nat := #[0,8,0,8,0,8,16,0,16,8,16]

/-- The decoder state carried across meta-blocks: the output and the last four distances
(`d0` the last). -/
structure St where
  out : ByteArray
  d0 : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat

/-- A distance short code (section 4, codes 0 to 15). -/
def shortDistance (st : St) (code : Nat) : Except String Nat :=
  if code == 0 then .ok st.d0 else if code == 1 then .ok st.d1
  else if code == 2 then .ok st.d2 else if code == 3 then .ok st.d3
  else
    let base : Int := if code < 10 then st.d0 else st.d1
    let k := (if code < 10 then code - 4 else code - 10)
    let delta : Int := if k % 2 == 0 then -Int.ofNat (k / 2 + 1) else Int.ofNat (k / 2 + 1)
    let r := base + delta
    if r ≤ 0 then .error "Brotli distance short code gives a distance below 1"
    else .ok r.toNat

/-- One compressed meta-block of `mlen` bytes (section 9.2 after ISUNCOMPRESSED, and the
decoding algorithm of section 9.3). -/
def compressedBlock (d : ByteArray) (window mlen : Nat) (st0 : St) : M St := do
  let mut st := st0
  let mut catL ← readCat d
  let mut catI ← readCat d
  let mut catD ← readCat d
  let npostfix ← readBits d 2
  let ndirect := (← readBits d 4) * 2 ^ npostfix
  let mut cmodes : Array Nat := #[]
  for _ in [0:catL.n] do cmodes := cmodes.push (← readBits d 2)
  let ntreesL := (← readVarLen8 d) + 1
  let cmapL ← readContextMap d (64 * catL.n) ntreesL
  let ntreesD := (← readVarLen8 d) + 1
  let cmapD ← readContextMap d (4 * catD.n) ntreesD
  let mut litTrees : Array Huff := #[]
  for _ in [0:ntreesL] do litTrees := litTrees.push (← readPrefixCode d 256)
  let mut cmdTrees : Array Huff := #[]
  for _ in [0:catI.n] do cmdTrees := cmdTrees.push (← readPrefixCode d 704)
  let distAlphabet := 16 + ndirect + 48 * 2 ^ npostfix
  let mut distTrees : Array Huff := #[]
  for _ in [0:ntreesD] do distTrees := distTrees.push (← readPrefixCode d distAlphabet)
  let lut := contextLut
  let start := st.out.size
  let fuel := mlen + d.size * 8 + 1
  for _ in [0:fuel] do
    let produced := st.out.size - start
    if produced ≥ mlen then break
    catI ← stepCat d catI
    let cmd ← decodeSym d cmdTrees[catI.cur]!
    let cell := cmd / 64
    let ic := cellIns[cell]! + cmd / 8 % 8
    let cc := cellCopy[cell]! + cmd % 8
    let insLen := insBase[ic]! + (← readBits d insExtra[ic]!)
    let copyLen := copyBase[cc]! + (← readBits d copyExtra[cc]!)
    if produced + insLen > mlen then throw "Brotli insert runs past the meta-block length"
    let mut out := st.out
    for _ in [0:insLen] do
      catL ← stepCat d catL
      let n := out.size
      let p1 := if n ≥ 1 then (out.get! (n-1)).toNat else 0
      let p2 := if n ≥ 2 then (out.get! (n-2)).toNat else 0
      let m := cmodes[catL.cur]! * 512
      let ctx := (lut.get! (m + p1)).toNat ||| (lut.get! (m + 256 + p2)).toNat
      let lit ← decodeSym d litTrees[cmapL[64 * catL.cur + ctx]!]!
      out := out.push lit.toUInt8
    st := { st with out := out }
    if out.size - start ≥ mlen then break
    -- the distance: implicit 0 (cells 0 and 1), or read with the distance context
    let mut dcode := 0
    let mut distance := st.d0
    if cell ≥ 2 then
      catD ← stepCat d catD
      let dctx := if copyLen > 4 then 3 else copyLen - 2
      let dc ← decodeSym d distTrees[cmapD[4 * catD.cur + dctx]!]!
      dcode := dc
      if dc < 16 then
        match shortDistance st dc with
        | .ok v => distance := v
        | .error e => throw e
      else if dc < 16 + ndirect then distance := dc - 15
      else
        let x := dc - ndirect - 16
        let ndistbits := 1 + x / 2 ^ (npostfix + 1)
        let hcode := x / 2 ^ npostfix
        let lcode := x % 2 ^ npostfix
        let offset := (2 + hcode % 2) * 2 ^ ndistbits - 4
        let dextra ← readBits d ndistbits
        distance := (offset + dextra) * 2 ^ npostfix + lcode + ndirect + 1
    let maxDist := min window out.size
    let produced := out.size - start
    if distance > maxDist then
      -- a static dictionary reference (section 8)
      if copyLen < 4 || copyLen > 24 then throw "Brotli dictionary reference has a length outside 4 to 24"
      let wordId := distance - maxDist - 1
      let nb := ndBits[copyLen]!
      let idx := wordId % 2 ^ nb
      let t := wordId / 2 ^ nb
      if t ≥ transformTable.size then throw "Brotli dictionary reference names no transform"
      let off := dOffset[copyLen]! + idx * copyLen
      let word := dictionary.get.extract off (off + copyLen)
      let w := transformWord word t
      if produced + w.size > mlen then throw "Brotli dictionary word runs past the meta-block length"
      st := { st with out := out ++ w }
    else
      if produced + copyLen > mlen then throw "Brotli copy runs past the meta-block length"
      let mut o := out
      for _ in [0:copyLen] do
        o := o.push (o.get! (o.size - distance))
      st := { st with out := o }
      if dcode != 0 then
        st := { st with d3 := st.d2, d2 := st.d1, d1 := st.d0, d0 := distance }
  if st.out.size - start != mlen then throw "Brotli meta-block makes no progress"
  return st

/-- WBITS (section 9.1): the window size is `2 ^ WBITS - 16`. -/
def readWindowBits (d : ByteArray) : M Nat := do
  if (← readBits d 1) == 0 then return 16
  let n ← readBits d 3
  if n != 0 then return 17 + n
  let m ← readBits d 3
  if m == 1 then throw "Brotli large-window stream (not RFC 7932) is not read"
  if m != 0 then return 8 + m
  return 17

/-- Decode a whole stream; output past `limit` bytes is refused. -/
def decode (d : ByteArray) (limit : Nat) : M ByteArray := do
  let wbits ← readWindowBits d
  let window := 2 ^ wbits - 16
  let mut st : St := ⟨ByteArray.empty, 4, 11, 15, 16⟩
  for _ in [0:d.size * 8 + 1] do
    let isLast := (← readBits d 1) == 1
    if isLast then
      if (← readBits d 1) == 1 then
        alignZero d
        return st.out
    let mn ← readBits d 2
    if mn == 3 then
      -- a metadata block: skipped
      if (← readBits d 1) != 0 then throw "Brotli reserved bit is set"
      let nb ← readBits d 2
      let mut len := 0
      for i in [0:nb] do
        let b ← readBits d 8
        if i + 1 == nb && nb > 1 && b == 0 then throw "Brotli metadata length has a zero last byte"
        len := len + b * 2 ^ (8 * i)
      if nb > 0 then len := len + 1
      alignZero d
      let p ← get
      if p + len * 8 > d.size * 8 then throw "Brotli stream is truncated"
      set (p + len * 8)
    else
      let nibbles := mn + 4
      let mut mlen := 0
      for i in [0:nibbles] do
        let b ← readBits d 4
        if i + 1 == nibbles && nibbles > 4 && b == 0 then throw "Brotli meta-block length has a zero last nibble"
        mlen := mlen + b * 2 ^ (4 * i)
      mlen := mlen + 1
      if st.out.size + mlen > limit then throw s!"Brotli output exceeds {limit} bytes"
      let unc ← if isLast then pure false else do pure ((← readBits d 1) == 1)
      if unc then
        alignZero d
        let p ← get
        if p + mlen * 8 > d.size * 8 then throw "Brotli stream is truncated"
        st := { st with out := st.out ++ d.extract (p / 8) (p / 8 + mlen) }
        set (p + mlen * 8)
      else
        st ← compressedBlock d window mlen st
    if isLast then
      alignZero d
      return st.out
  throw "Brotli stream has no last meta-block"

/-- The output of a Brotli stream (RFC 7932) that is the whole of `input`, at most `limit`
bytes. -/
def decompress (input : ByteArray) (limit : Nat) : Except String ByteArray := do
  let (out, pos) ← (decode input limit).run 0
  if pos != input.size * 8 then throw "Brotli stream is followed by other data"
  return out

end L4Factoidal.Codec.Brotli
