/-
L4Factoidal.Qlvr.Side — the qlvr side index: string to `VocabIndex` by
binary search, without the ICU collation of the QLever vocabulary
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

The QLever vocabulary is sorted by first byte, then by ICU collation (format
record, section 2), so a byte-wise binary search over it is wrong. The side
index is a second copy of the words, sorted byte-wise, written by
`l4qlvr side-index INDEXDIR` into the directory `INDEXDIR.qlvr-side/` (next
to the QLever index directory, never inside it). It is our format, not
QLever's:

  * `side.header` (64 bytes): `QLVRSIDE`, then `u64` little-endian: format
    version 1, word count, byte size of `<base>.vocabulary.words.external`,
    XXH64 (seed 0) of the whole `<base>.vocabulary.words.external.offsets`
    file, byte size of `words.sorted`, entry size 24, 0.
  * `words.sorted`: the stored forms of all words (format record, section 2,
    "The stored form of a word"), concatenated in unsigned byte order.
  * `words.entries`: one 24-byte entry per word in the same order: `u64`
    offset into `words.sorted`, `u64` length, `u64` `VocabIndex`.

A reader checks the word count, the external size and the offsets hash
against the vocabulary it has loaded, and refuses a side index that does not
match (it was built for another index, or the vocabulary changed).

The build is an external merge sort: chunks of the vocabulary in index order
are decoded, sorted in memory (`mergeSortBy`) and written as run files of
records `u32 length, word bytes, u64 VocabIndex`; the runs are then merged
into `words.sorted` and `words.entries`. Memory is bounded by one chunk plus
one read buffer per run. The file I/O is in the harness
(`Harness/Qlvr.lean`); this module has the byte layouts and the search.

## Loops

`encodeRunLoop` is a tail call with a fuel `Nat` first and the output as an
accumulator. `sideLookupM` is a `for` loop of at most `log2 n + 2` probes.
-/
import L4Factoidal.Codec.Zstd
import L4Factoidal.Qlvr.Sort
-- `cmpBytes` below compiles to `cmpBytesFast` only in a module that imports the module of its
-- `@[csimp]` theorem (https://github.com/danbri/factoidal/issues/871, found by tools/lean-csimp-reach.py).
import L4Factoidal.Qlvr.CmpBytesFast

namespace L4Factoidal.Qlvr.Side

open L4Factoidal.Codec.Zstd (word64)

def magic : ByteArray := "QLVRSIDE".toUTF8
def version : UInt64 := 1
def entryBytes : Nat := 24
def headerBytes : Nat := 64

/-- Append a `u64` little-endian. -/
def put64 (b : ByteArray) (x : UInt64) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
   |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8 |>.push (x >>> 48).toUInt8
   |>.push (x >>> 56).toUInt8

/-- Append a `u32` little-endian. -/
def put32 (b : ByteArray) (x : UInt32) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

/-- The `u32` little-endian at `p` (the caller checked the bounds). -/
def get32 (d : ByteArray) (p : Nat) : Nat :=
  (d.get! p).toNat + (d.get! (p + 1)).toNat * 256 + (d.get! (p + 2)).toNat * 65536 +
    (d.get! (p + 3)).toNat * 16777216

structure Header where
  count : Nat
  externalSize : Nat
  offsetsHash : UInt64
  sortedSize : Nat
  deriving Repr, BEq

def Header.encode (h : Header) : ByteArray :=
  let b := magic
  let b := put64 b version
  let b := put64 b h.count.toUInt64
  let b := put64 b h.externalSize.toUInt64
  let b := put64 b h.offsetsHash
  let b := put64 b h.sortedSize.toUInt64
  let b := put64 b entryBytes.toUInt64
  put64 b 0

def Header.parse (d : ByteArray) : Except String Header :=
  if d.size != headerBytes then .error s!"side.header: {d.size} bytes, want {headerBytes}"
  else if (d.extract 0 8).data != magic.data then .error "side.header: magic is not QLVRSIDE"
  else if word64 d 8 != version then .error s!"side.header: version {word64 d 8}, want {version}"
  else if (word64 d 48).toNat != entryBytes then .error s!"side.header: entry size {word64 d 48}"
  else .ok { count := (word64 d 16).toNat, externalSize := (word64 d 24).toNat,
             offsetsHash := word64 d 32, sortedSize := (word64 d 40).toNat }

/-- One entry of `words.entries`. -/
def encodeEntry (b : ByteArray) (off len idx : Nat) : ByteArray :=
  put64 (put64 (put64 b off.toUInt64) len.toUInt64) idx.toUInt64

/-- Records `i..` of a sorted chunk as run-file bytes:
    `u32 length, word bytes, u64 VocabIndex` each. -/
def encodeRunLoop (ws : Array (ByteArray × Nat)) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | k+1, i, acc =>
    if h : i < ws.size then
      let (w, idx) := ws[i]
      encodeRunLoop ws k (i + 1) (put64 (put32 acc w.size.toUInt32 ++ w) idx.toUInt64)
    else acc

def encodeRun (ws : Array (ByteArray × Nat)) : ByteArray :=
  encodeRunLoop ws (ws.size + 1) 0 (ByteArray.emptyWithCapacity (ws.size * 48))

/-- Sort a chunk of `(word, VocabIndex)` pairs by unsigned byte order. -/
def sortChunk (ws : Array (ByteArray × Nat)) : Array (ByteArray × Nat) :=
  mergeSortBy ws (fun a b => cmpBytes a.1 b.1 != .gt)

/-- Binary search for `target` over a side index of `n` entries, through
    two fetch functions `(offset, length) ↦ bytes` (positioned reads of
    `words.entries` and `words.sorted`, or slices of bytes in memory).
    Returns the `VocabIndex` (or `none`) and the number of probes. -/
def sideLookupM {m : Type → Type} [Monad m] (fetchEnt fetchWord : Nat → Nat → m ByteArray)
    (n : Nat) (target : ByteArray) : ExceptT String m (Option Nat × Nat) := do
  let mut lo := 0
  let mut hi := n
  let mut probes := 0
  for _ in [0:Nat.log2 n + 2] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let e ← (fetchEnt (entryBytes * mid) entryBytes : m ByteArray)
    if e.size != entryBytes then throw s!"words.entries: short read at entry {mid}"
    let off := (word64 e 0).toNat
    let len := (word64 e 8).toNat
    let w ← (fetchWord off len : m ByteArray)
    if w.size != len then throw s!"words.sorted: short read at {off}"
    probes := probes + 1
    match cmpBytes w target with
    | .lt => lo := mid + 1
    | .gt => hi := mid
    | .eq => return (some (word64 e 16).toNat, probes)
  return (none, probes)

/-- The side index of a list of words, in memory: `(entries, sorted)`. -/
def buildInMemory (ws : Array (ByteArray × Nat)) : ByteArray × ByteArray := Id.run do
  let s := sortChunk ws
  let mut ent := ByteArray.empty
  let mut dat := ByteArray.empty
  for (w, idx) in s do
    ent := encodeEntry ent dat.size w.size idx
    dat := dat ++ w
  return (ent, dat)

private def testWords : Array (ByteArray × Nat) :=
  #[("<http://b>".toUTF8, 3), ("\"x\"@en".toUTF8, 0), ("<http://a>".toUTF8, 2), ("\"é\"".toUTF8, 1)]

private def testLookup (t : String) : Option Nat :=
  let (ent, dat) := buildInMemory testWords
  match (sideLookupM (m := _root_.Id) (fun o n => ent.extract o (o + n)) (fun o n => dat.extract o (o + n))
          testWords.size t.toUTF8).run with
  | .ok (r, _) => r
  | .error _ => none

#guard testLookup "<http://a>" == some 2
#guard testLookup "<http://b>" == some 3
#guard testLookup "\"x\"@en" == some 0
#guard testLookup "\"é\"" == some 1
#guard testLookup "<http://c>" == none
#guard testLookup "" == none
#guard (Header.parse ({ count := 5, externalSize := 9, offsetsHash := 7, sortedSize := 3 } : Header).encode).toOption ==
  some { count := 5, externalSize := 9, offsetsHash := 7, sortedSize := 3 }
#guard get32 (put32 ByteArray.empty 0xA1B2C3D4) 0 == 0xA1B2C3D4

end L4Factoidal.Qlvr.Side
