/-
L4Factoidal.Qlvr.Vocab — the QLever vocabulary, `on-disk-compressed`
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

Format record: docs/designissues/2026-10-11-qlever-index-format.md, section 2.

  * `<base>.vocabulary.codebooks`: `u64` count, then per block of 2^20 words
    two `fsst_decoder_t` (2,304 bytes each).
  * `<base>.vocabulary.words.external.offsets`: `u64 o[0..n]`, then the
    32-byte MmapVector trailer (`u64 size, u64 capacity, u64 bytesize,
    u32 magic 7601577, u32 version 0`).
  * `<base>.vocabulary.words.external`: the compressed words, concatenated.

Word `i` is bytes `[o[i], o[i+1])` of `.words.external`, decoded with the
second decoder of pair `i / 2^20`, then with the first.

`Vocab` holds the bytes of the offsets and external files; a word is decoded
only when asked for (`wordBytes`), from a slice of those bytes. Nothing is
decoded at load time.

The vocabulary is sorted first by the first byte of the stored word, then by
ICU collation (`index/vocabulary/StringSortComparator.h:307-333`). `findWord`
uses only the first-byte order (a binary search for the range of words that
share the target's first byte) and then scans that range linearly. A
byte-wise binary search inside the range is wrong under ICU collation.

## Loops

`findFirstByte` (binary search, fuel = log2 of the vocabulary size + 2) and
`scanRange` (fuel = the range length) are tail calls with a fuel `Nat` first;
`foldWords` likewise.
-/
import L4Factoidal.Codec.Zstd
import L4Factoidal.Qlvr.Fsst

namespace L4Factoidal.Qlvr

open L4Factoidal.Codec.Zstd (word64)

/-- Magic number of the MmapVector trailer (`util/MmapVector.h:29-47`). -/
def mmapMagic : UInt64 := 7601577

/-- Words per FSST decoder pair (`CompressedVocabulary.h:39-44`). -/
def wordsPerDecoder : Nat := 2 ^ 20

structure Vocab where
  decoders : Array (Fsst.Decoder × Fsst.Decoder)
  offsets : ByteArray
  external : ByteArray
  /-- number of words -/
  size : Nat
  deriving Inhabited

/-- Parse the 32-byte MmapVector trailer at the end of `d`:
    `(size, bytesize)`. -/
def parseMmapTrailer (d : ByteArray) (what : String) : Except String (Nat × Nat) :=
  if d.size < 32 then .error s!"{what}: {d.size} bytes, shorter than the 32-byte trailer"
  else
    let t := d.size - 32
    let size := (word64 d t).toNat
    let bytesize := (word64 d (t + 16)).toNat
    let mv := word64 d (t + 24)
    if mv &&& 0xFFFFFFFF != mmapMagic then .error s!"{what}: trailer magic {mv &&& 0xFFFFFFFF}, want {mmapMagic}"
    else if mv >>> 32 != 0 then .error s!"{what}: trailer version {mv >>> 32}, want 0"
    else if bytesize > t then .error s!"{what}: trailer bytesize {bytesize} exceeds the data"
    else .ok (size, bytesize)

/-- Load the vocabulary from the bytes of its three files. -/
def Vocab.load (codebooks offsets external : ByteArray) : Except String Vocab := do
  if codebooks.size < 8 then throw "codebooks: shorter than its count"
  let n := (word64 codebooks 0).toNat
  if 8 + n * 2 * Fsst.decoderBytes != codebooks.size then
    throw s!"codebooks: {n} decoder pairs need {8 + n * 2 * Fsst.decoderBytes} bytes, file has {codebooks.size}"
  let mut decs : Array (Fsst.Decoder × Fsst.Decoder) := #[]
  for k in [0:n] do
    let a ← Fsst.Decoder.parse codebooks (8 + 2 * k * Fsst.decoderBytes)
    let b ← Fsst.Decoder.parse codebooks (8 + (2 * k + 1) * Fsst.decoderBytes)
    decs := decs.push (a, b)
  let (cnt, bytesize) ← parseMmapTrailer offsets "words.external.offsets"
  if cnt == 0 || bytesize != 8 * cnt then
    throw s!"words.external.offsets: {cnt} entries but bytesize {bytesize}"
  let words := cnt - 1
  if (words + wordsPerDecoder - 1) / wordsPerDecoder > n then
    throw s!"codebooks: {n} decoder pairs for {words} words"
  if (word64 offsets (8 * words)).toNat != external.size then
    throw s!"words.external: size {external.size}, last offset {(word64 offsets (8 * words)).toNat}"
  pure { decoders := decs, offsets, external, size := words }

/-- The compressed byte range of word `i`. -/
def Vocab.range (v : Vocab) (i : Nat) : Except String (Nat × Nat) :=
  if i ≥ v.size then .error s!"vocabulary: index {i} out of range (size {v.size})"
  else
    let a := (word64 v.offsets (8 * i)).toNat
    let b := (word64 v.offsets (8 * i + 8)).toNat
    if a > b || b > v.external.size then .error s!"vocabulary: word {i} has bad offsets {a}..{b}"
    else .ok (a, b)

/-- The stored form of word `i`, as bytes (UTF-8). -/
def Vocab.wordBytes (v : Vocab) (i : Nat) : Except String ByteArray := do
  let (a, b) ← v.range i
  let (d1, d2) := v.decoders.getD (i / wordsPerDecoder) default
  let s1 ← Fsst.decodeRange d2 v.external a b
  Fsst.decode d1 s1

/-- The stored form of word `i`. -/
def vocabWord (v : Vocab) (i : Nat) : Except String String := do
  let b ← v.wordBytes i
  match String.fromUTF8? b with
  | some s => pure s
  | none => throw s!"vocabulary: word {i} is not UTF-8"

/-- The first byte of word `i` (0 for an empty word). -/
def Vocab.firstByte (v : Vocab) (i : Nat) : Except String UInt8 := do
  let b ← v.wordBytes i
  pure (b.get! 0)

/-- Binary search: the least index in `[lo, hi)` whose first byte is `≥ c`
    (first-byte order holds for the whole vocabulary). -/
def findFirstByte (v : Vocab) (c : UInt8) : Nat → Nat → Nat → Except String Nat
  | 0, lo, _ => .ok lo
  | k+1, lo, hi =>
    if lo ≥ hi then .ok lo
    else
      let mid := (lo + hi) / 2
      match v.firstByte mid with
      | .error e => .error e
      | .ok b =>
        if b < c then findFirstByte v c k (mid + 1) hi
        else findFirstByte v c k lo mid

/-- Linear scan of `[i, stop)` for the word whose bytes equal `target`.
    Returns the index and the number of words decoded. -/
def scanRange (v : Vocab) (target : ByteArray) (stop : Nat) :
    Nat → Nat → Except String (Option Nat)
  | 0, _ => .ok none
  | k+1, i =>
    if i ≥ stop then .ok none
    else match v.wordBytes i with
      | .error e => .error e
      | .ok w => if w.data == target.data then .ok (some i) else scanRange v target stop k (i + 1)

/-- The bounds `[lo, hi)` of the words whose first byte is the first byte of
    `target`. -/
def Vocab.firstByteRange (v : Vocab) (target : ByteArray) : Except String (Nat × Nat) := do
  let c := target.get! 0
  let fuel := Nat.log2 v.size + 2
  let lo ← findFirstByte v c fuel 0 v.size
  let hi ← if c == 255 then pure v.size else findFirstByte v (c + 1) fuel lo v.size
  pure (lo, hi)

/-- The `VocabIndex` of a stored word (an IRI in angle brackets, or a literal
    in the stored form), or `none`. Cost: a binary search on the first byte,
    then one decode per word of that first-byte range. -/
def Vocab.findWord (v : Vocab) (target : String) : Except String (Option Nat) := do
  let t := target.toUTF8
  if t.size == 0 then return none
  let (lo, hi) ← v.firstByteRange t
  scanRange v t hi (hi - lo + 1) lo

/-- Fold over words `[i, v.size)` in index order. -/
def foldWords {α : Type} (v : Vocab) (f : α → Nat → ByteArray → α) :
    Nat → Nat → α → Except String α
  | 0, _, acc => .ok acc
  | k+1, i, acc =>
    if i ≥ v.size then .ok acc
    else match v.wordBytes i with
      | .error e => .error e
      | .ok w => foldWords v f k (i + 1) (f acc i w)

end L4Factoidal.Qlvr
