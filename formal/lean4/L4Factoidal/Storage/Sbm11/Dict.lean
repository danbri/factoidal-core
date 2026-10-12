/-
L4Factoidal.Storage.Sbm11.Dict — GDV1 and GDX1, the global term dictionary
of wire version 11 (`docs/designissues/2026-10-11-shardborough-vs-qlever.md`
section 6.2; https://github.com/danbri/factoidal/issues/788).

The dictionary is the list of the keys (`TermKey.termKey?`) of every
non-inline term of a generation, strictly increasing in unsigned byte
order. The rank of a key in that list is the payload of its term id
(`TermId`). Keys are cut into pages of `pageTerms` = 64.

## Bytes

All integers little-endian. A SMALL field is one byte `n` when `n < 255`,
else the byte 255 and `n` as u32.

GDV1 (`dict.gdv1`):

    "GDV1"  version u8 = 1  pageTerms u8 = 64
    page*   one per 64 keys, the last one may be shorter

    page  = SMALL count
            (count > 0)  SMALL len(k0)  k0
                         then for each next key k after prev:
                         SMALL shared  SMALL len(suffix)  suffix
            where shared is the longest common prefix of prev and k and
            suffix = k without its first `shared` bytes (front coding)

GDX1 (`dict.gdx1`):

    "GDX1"  version u8 = 1  termCount u64  pageCount u64
    entry*  one per page, 12 bytes: pageOffset u64 (in GDV1), pageLen u32

Entry `i` is at byte `21 + 12 i`. A string-to-id lookup binary-searches the
pages by their first keys; a page starts with its first key in full, so a
probe reads one entry and one page. The page of rank `r` is `r / 64`, so id
to key is one entry read and one page read.

The design record (section 6.2) put the first key of every page into GDX1
as well. On the olympics data that copy is about 645,000 bytes and takes
the dictionary from 9.4 MB to 10.02 MB, above the stage 2 target of 10 MB,
so the first keys are read from GDV1.

## Admission

`dictAdmitted`: keys strictly increasing (`strictlySorted`), fewer than
`2^60` keys (the id payload), every key and every page count below `2^32`,
every GDX1 field inside its width. The decoder checks the same predicate on
what it read, and also that the pages are exactly the 64-key cut of the key
list and that GDX1 is exactly the directory of those pages. The round trip
`DictTheorems.decodeDict_encodeDict?` has `encodeDict? keys = some (v, x)` as
its only hypothesis.

## Fetch-function interface

`lookupM` and `keyOfRankM` take two functions `(offset, length) ↦ bytes`,
one per file, in any monad: positioned reads (`pread`) from the native
harness, or slices of bytes in memory (`m = Id`). This is the design of
`Qlvr.Scan`. The spec decoders work over `List UInt8`. The runtime path
decodes one page with `decodePageAt`, which reads a `ByteArray` by
position and builds no list; `DictFastTheorems.decodePageAt_eq` proves it
returns the keys and the end position that `decodePage` returns.

## Loops

Every recursive function here is a tail call with an accumulator (or a
fuel `Nat` first); `lookupM` is a `for` loop of at most `log2 n + 2`
probes. No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKey
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.Sbm11.Dict

open L4Factoidal.Storage (readU32LE writeU32LE readU64LE writeU64LE)
open L4Factoidal (two32 two64)

def pageTerms : Nat := 64

/-! ## Small fields -/

def putSmall (n : Nat) : List UInt8 :=
  if n < 255 then [n.toUInt8] else 255 :: writeU32LE (UInt32.ofNat n)

def getSmall (bs : List UInt8) : Option (Nat × List UInt8) :=
  match bs with
  | [] => none
  | b :: rest =>
    if b.toNat < 255 then some (b.toNat, rest)
    else
      match readU32LE rest 0 with
      | none => none
      | some v => some (v.toNat, rest.drop 4)

/-! ## Front coding -/

def lcpGo : List UInt8 → List UInt8 → Nat → Nat
  | a :: as, b :: bs, n => if a == b then lcpGo as bs (n + 1) else n
  | _, _, n => n

/-- Length of the longest common prefix. -/
def lcp (a b : List UInt8) : Nat := lcpGo a b 0

/-- One front-coded entry: `k` after `prev`. -/
def piece (prev k : Key) : List UInt8 :=
  let s := lcp prev k
  putSmall s ++ putSmall (k.length - s) ++ k.drop s

def encodeEntriesGo : Key → List Key → List (List UInt8) → List (List UInt8)
  | _, [], acc => acc
  | prev, k :: ks, acc => encodeEntriesGo k ks (piece prev k :: acc)

def encodeEntries (prev : Key) (ks : List Key) : List UInt8 :=
  (encodeEntriesGo prev ks []).reverse.flatten

def encodePage (ks : List Key) : List UInt8 :=
  match ks with
  | [] => putSmall 0
  | k :: rest => putSmall ks.length ++ (putSmall k.length ++ k) ++ encodeEntries k rest

def decodeEntriesGo : Nat → Key → List Key → List UInt8 → Option (List Key × List UInt8)
  | 0, _, accRev, bs => some (accRev.reverse, bs)
  | n + 1, prev, accRev, bs =>
    match getSmall bs with
    | none => none
    | some (s, bs1) =>
      match getSmall bs1 with
      | none => none
      | some (len, bs2) =>
        if (bs2.take len).length == len then
          decodeEntriesGo n (prev.take s ++ bs2.take len) ((prev.take s ++ bs2.take len) :: accRev)
            (bs2.drop len)
        else none

/-- Decode one page and return the bytes after it. -/
def decodePage (bs : List UInt8) : Option (List Key × List UInt8) :=
  match getSmall bs with
  | none => none
  | some (c, bs1) =>
    if c == 0 then some ([], bs1)
    else
      match getSmall bs1 with
      | none => none
      | some (len, bs2) =>
        if (bs2.take len).length == len then
          decodeEntriesGo (c - 1) (bs2.take len) [bs2.take len] (bs2.drop len)
        else none

/-! ## Cutting into pages -/

def chunkGo {α : Type} (n : Nat) : Nat → List α → List (List α) → List (List α)
  | 0, _, acc => acc.reverse
  | f + 1, l, acc =>
    match l with
    | [] => acc.reverse
    | _ :: _ => chunkGo n f (l.drop n) (l.take n :: acc)

/-- `l` cut into lists of `n` (the last one may be shorter). -/
def chunk {α : Type} (n : Nat) (l : List α) : List (List α) := chunkGo n (l.length + 1) l []

/-! ## Order -/

/-- Unsigned byte order; a proper prefix sorts first. -/
def cmpKey : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if b < a then .gt else cmpKey as bs

def strictlySortedGo : Key → List Key → Bool
  | _, [] => true
  | prev, k :: ks => if cmpKey prev k == .lt then strictlySortedGo k ks else false

def strictlySorted : List Key → Bool
  | [] => true
  | k :: ks => strictlySortedGo k ks

/-! ## GDV1 -/

/-- `"GDV1"`, version 1, 64 keys per page. -/
def gdvHeader : List UInt8 := [71, 68, 86, 49, 1, 64]

def gdvBytes (pages : List (List Key)) : List UInt8 :=
  gdvHeader ++ (pages.map encodePage).flatten

def decodePagesGo : Nat → List UInt8 → List (List Key) → Option (List (List Key))
  | 0, _, _ => none
  | f + 1, bs, accRev =>
    match bs with
    | [] => some accRev.reverse
    | _ :: _ =>
      match decodePage bs with
      | none => none
      | some (p, rest) => decodePagesGo f rest (p :: accRev)

def decodeGdv (bs : List UInt8) : Option (List (List Key)) :=
  if bs.take 6 == gdvHeader then decodePagesGo (bs.length + 1) (bs.drop 6) [] else none

/-! ## GDX1 -/

structure DirEntry where
  pageOffset : Nat
  pageLen : Nat
  deriving DecidableEq, Repr, Inhabited

def firstKey (p : List Key) : Key := p.headD []

def dirEntriesGo : List (List Key) → Nat → List DirEntry → List DirEntry
  | [], _, acc => acc.reverse
  | p :: ps, off, acc =>
    dirEntriesGo ps (off + (encodePage p).length) (⟨off, (encodePage p).length⟩ :: acc)

/-- The directory of a page list: GDV1 offsets start after its header. -/
def dirEntries (pages : List (List Key)) : List DirEntry := dirEntriesGo pages gdvHeader.length []

def entryBytes (e : DirEntry) : List UInt8 :=
  writeU64LE (UInt64.ofNat e.pageOffset) ++ writeU32LE (UInt32.ofNat e.pageLen)

/-- `"GDX1"`, version 1. -/
def gdxMagic : List UInt8 := [71, 68, 88, 49, 1]

def gdxHeaderBytes : Nat := 21
def entrySize : Nat := 12

def gdxBytes (termCount : Nat) (es : List DirEntry) : List UInt8 :=
  gdxMagic ++ writeU64LE (UInt64.ofNat termCount) ++ writeU64LE (UInt64.ofNat es.length) ++
    (es.map entryBytes).flatten

def decodeEntry (bs : List UInt8) : Option (DirEntry × List UInt8) :=
  match readU64LE bs 0 with
  | none => none
  | some a =>
    match readU32LE (bs.drop 8) 0 with
    | none => none
    | some b => some (⟨a.toNat, b.toNat⟩, (bs.drop 8).drop 4)

def decodeEntriesN : Nat → List UInt8 → List DirEntry → Option (List DirEntry × List UInt8)
  | 0, bs, accRev => some (accRev.reverse, bs)
  | n + 1, bs, accRev =>
    match decodeEntry bs with
    | none => none
    | some (e, rest) => decodeEntriesN n rest (e :: accRev)

/-- `(termCount, directory)`. -/
def decodeGdx (bs : List UInt8) : Option (Nat × List DirEntry) :=
  if bs.take 5 == gdxMagic then
    match readU64LE (bs.drop 5) 0 with
    | none => none
    | some tc =>
      match readU64LE ((bs.drop 5).drop 8) 0 with
      | none => none
      | some pc =>
        match decodeEntriesN pc.toNat (((bs.drop 5).drop 8).drop 8) [] with
        | some (es, []) => some (tc.toNat, es)
        | _ => none
  else none

/-! ## The dictionary -/

def pageFits (p : List Key) : Bool :=
  decide (p.length < two32) && p.all (fun k => decide (k.length < two32))

def entryFits (e : DirEntry) : Bool :=
  decide (e.pageOffset < two64) && decide (e.pageLen < two32)

/-- `2 ^ 60`: the dictionary holds fewer keys than an id payload can name. -/
@[reducible, noinline] def maxTerms : Nat := 1152921504606846976

/-- Encoder admission, which is also the decoder's check. -/
def dictAdmitted (keys : List Key) (pages : List (List Key)) : Bool :=
  strictlySorted keys && decide (keys.length < maxTerms) && decide (pages.length < two64) &&
    pages.all pageFits && (dirEntries pages).all entryFits

/-- GDV1 and GDX1 bytes of a key list, or `none` when it is not admitted. -/
def encodeDict? (keys : List Key) : Option (List UInt8 × List UInt8) :=
  let pages := chunk pageTerms keys
  if dictAdmitted keys pages then
    some (gdvBytes pages, gdxBytes keys.length (dirEntries pages))
  else none

def decodeDict (gdv gdx : List UInt8) : Option (List Key) :=
  match decodeGdv gdv, decodeGdx gdx with
  | some pages, some (tc, es) =>
    if chunk pageTerms pages.flatten == pages && dictAdmitted pages.flatten pages &&
        tc == pages.flatten.length && es == dirEntries pages then
      some pages.flatten
    else none
  | _, _ => none

/-! ## The page decoder over a byte array -/

def bytesToList (b : ByteArray) : List UInt8 := b.data.toList

/-- `getSmall` at position `i` of `b`: the value and the next position. -/
def getSmallAt (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  if h : i < b.size then
    if b[i].toNat < 255 then some (b[i].toNat, i + 1)
    else if h4 : i + 4 < b.size then
      match readU32LE [b[i + 1], b[i + 2], b[i + 3], b[i + 4]] 0 with
      | some v => some (v.toNat, i + 5)
      | none => none
    else none
  else none

def decodeEntriesAt (b : ByteArray) :
    Nat → ByteArray → Array ByteArray → Nat → Option (Array ByteArray × Nat)
  | 0, _, acc, i => some (acc, i)
  | n + 1, prev, acc, i =>
    match getSmallAt b i with
    | none => none
    | some (s, i1) =>
      match getSmallAt b i1 with
      | none => none
      | some (len, i2) =>
        if i2 + len ≤ b.size then
          decodeEntriesAt b n (prev.extract 0 s ++ b.extract i2 (i2 + len))
            (acc.push (prev.extract 0 s ++ b.extract i2 (i2 + len))) (i2 + len)
        else none

/-- One page from position `i` of `b`: its keys and the position after it.
    Equal to `decodePage` on the list view (`DictFastTheorems.decodePageAt_eq`). -/
def decodePageAt (b : ByteArray) (i : Nat) : Option (Array ByteArray × Nat) :=
  match getSmallAt b i with
  | none => none
  | some (c, i1) =>
    if c == 0 then some (#[], i1)
    else
      match getSmallAt b i1 with
      | none => none
      | some (len, i2) =>
        if i2 + len ≤ b.size then
          decodeEntriesAt b (c - 1) (b.extract i2 (i2 + len)) #[b.extract i2 (i2 + len)] (i2 + len)
        else none

/-- The first key of a page, from its head only. -/
def firstKeyAt (b : ByteArray) : Option ByteArray :=
  match getSmallAt b 0 with
  | none => none
  | some (c, i1) =>
    if c == 0 then none
    else
      match getSmallAt b i1 with
      | none => none
      | some (len, i2) => if i2 + len ≤ b.size then some (b.extract i2 (i2 + len)) else none

/-! ## Executable access through fetch functions -/

def word64At (b : ByteArray) (p : Nat) : Nat :=
  (b.get! p).toNat + (b.get! (p + 1)).toNat * 256 + (b.get! (p + 2)).toNat * 65536 +
    (b.get! (p + 3)).toNat * 16777216 + (b.get! (p + 4)).toNat * 4294967296 +
    (b.get! (p + 5)).toNat * 1099511627776 + (b.get! (p + 6)).toNat * 281474976710656 +
    (b.get! (p + 7)).toNat * 72057594037927936

def word32At (b : ByteArray) (p : Nat) : Nat :=
  (b.get! p).toNat + (b.get! (p + 1)).toNat * 256 + (b.get! (p + 2)).toNat * 65536 +
    (b.get! (p + 3)).toNat * 16777216

/-- Unsigned byte order on byte arrays (a loop; a proper prefix sorts first). -/
def cmpBytesAt (a b : ByteArray) : Ordering := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    let x := a.get! i
    let y := b.get! i
    if x < y then return .lt
    if y < x then return .gt
  return compare a.size b.size

/-- The GDX1 header, read from its first 21 bytes. -/
structure GdxHeader where
  termCount : Nat
  pageCount : Nat
  deriving Repr, Inhabited

def parseGdxHeader (b : ByteArray) : Except String GdxHeader :=
  if b.size < gdxHeaderBytes then .error s!"GDX1: header of {b.size} bytes"
  else if bytesToList (b.extract 0 5) != gdxMagic then .error "GDX1: magic or version is not GDX1 version 1"
  else .ok { termCount := word64At b 5, pageCount := word64At b 13 }

def parseEntryBytes (b : ByteArray) : Except String DirEntry :=
  if b.size != entrySize then .error s!"GDX1: entry of {b.size} bytes"
  else .ok ⟨word64At b 0, word32At b 8⟩

/-- Directory entry `i`. -/
def entryM {m : Type → Type} [Monad m] (fetchGdx : Nat → Nat → m ByteArray) (i : Nat) :
    ExceptT String m DirEntry := do
  let b ← (fetchGdx (gdxHeaderBytes + entrySize * i) entrySize : m ByteArray)
  match parseEntryBytes b with
  | .ok e => pure e
  | .error e => throw e

/-- The bytes of page `i`. -/
def pageBytesM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray) (i : Nat) :
    ExceptT String m ByteArray := do
  let e ← entryM fetchGdx i
  let b ← (fetchGdv e.pageOffset e.pageLen : m ByteArray)
  if b.size != e.pageLen then throw s!"GDV1: short read of page {i}"
  pure b

/-- The keys of page `i`. -/
def pageM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray) (i : Nat) :
    ExceptT String m (Array ByteArray) := do
  let b ← pageBytesM fetchGdx fetchGdv i
  match decodePageAt b 0 with
  | some (ks, j) => if j == b.size then pure ks else throw s!"GDV1: page {i} has trailing bytes"
  | none => throw s!"GDV1: page {i} does not decode"

/-- The position of `k` in a page, by a loop over its keys. -/
def indexInPage (ks : Array ByteArray) (k : ByteArray) : Option Nat := Id.run do
  for i in [0:ks.size] do
    if ks[i]! == k then return some i
  return none

/-- String-to-id: the rank of key `k`, or `none` when it is not in the
    dictionary, and the number of page reads. Binary search over the first
    keys of the pages, then a scan of one page. A rank this returns is
    always right: it is the position of a key equal to `k` in a decoded
    page. That every key is FOUND rests on the pages being in key order,
    which `l4sbm11-dict-pack --check` verifies for every key of a
    dictionary. -/
def lookupM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (k : ByteArray) : ExceptT String m (Option Nat × Nat) := do
  -- the last page whose first key is ≤ k: firstKey(lo) ≤ k when lo > 0,
  -- and firstKey(hi) > k when hi < pageCount
  let mut lo := 0
  let mut hi := h.pageCount
  let mut probes := 0
  for _ in [0:Nat.log2 h.pageCount + 2] do
    if lo + 1 ≥ hi then break
    let mid := (lo + hi) / 2
    let b ← pageBytesM fetchGdx fetchGdv mid
    probes := probes + 1
    match firstKeyAt b with
    | none => throw s!"GDV1: page {mid} has no first key"
    | some fk =>
      match cmpBytesAt fk k with
      | .gt => hi := mid
      | _ => lo := mid
  if h.pageCount == 0 then return (none, probes)
  let ks ← pageM fetchGdx fetchGdv lo
  match indexInPage ks k with
  | some i => return (some (lo * pageTerms + i), probes + 1)
  | none => return (none, probes + 1)

/-- Id-to-key: the key of rank `r`, one entry read and one page read. -/
def keyOfRankM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (r : Nat) : ExceptT String m ByteArray := do
  if r ≥ h.termCount then throw s!"rank {r} is not below the term count {h.termCount}"
  let ks ← pageM fetchGdx fetchGdv (r / pageTerms)
  match ks[r % pageTerms]? with
  | some k => pure k
  | none => throw s!"GDV1: page {r / pageTerms} has no entry {r % pageTerms}"

/-! ## Unit tests -/

private def ks0 : List Key :=
  [[1, 98], [2, 104, 58, 97], [2, 104, 58, 97, 98], [2, 104, 58, 98], [3], [3, 0], [3, 120]]

#guard getSmall (putSmall 254 ++ [9]) == some (254, [9])
#guard getSmall (putSmall 255 ++ [9]) == some (255, [9])
#guard getSmall (putSmall 70000) == some (70000, [])
#guard lcp [1, 2, 3] [1, 2, 4] == 2
#guard lcp [] [1] == 0
#guard decodePage (encodePage ks0 ++ [7]) == some (ks0, [7])
#guard decodePage (encodePage [] ++ [7]) == some ([], [7])
#guard (decodePageAt ⟨(encodePage ks0 ++ [7]).toArray⟩ 0).map (fun r => (r.1.toList.map bytesToList, r.2)) ==
  some (ks0, (encodePage ks0).length)
#guard cmpBytesAt ⟨#[1]⟩ ⟨#[1, 0]⟩ == .lt
#guard cmpBytesAt ⟨#[2]⟩ ⟨#[1, 0]⟩ == .gt
#guard cmpBytesAt ⟨#[1, 0]⟩ ⟨#[1, 0]⟩ == .eq
#guard chunk 3 [1, 2, 3, 4, 5, 6, 7] == [[1, 2, 3], [4, 5, 6], [7]]
#guard chunk 3 ([] : List Nat) == []
#guard strictlySorted ks0
#guard !strictlySorted [[1], [1]]
#guard !strictlySorted [[2], [1, 5]]
#guard cmpKey [1] [1, 0] == .lt

private def bigKeys : List Key := (List.range 200).map fun i => [2, (i / 10).toUInt8, (i % 10).toUInt8]

#guard match encodeDict? bigKeys with
  | some (v, x) => decodeDict v x == some bigKeys
  | none => false
#guard match encodeDict? ks0 with
  | some (v, x) => decodeDict v x == some ks0
  | none => false
#guard encodeDict? [[1], [1]] == none
#guard match encodeDict? ([] : List Key) with
  | some (v, x) => decodeDict v x == some []
  | none => false

private def memLookup (keys : List Key) (k0 : Key) : Option Nat :=
  let k : ByteArray := ⟨k0.toArray⟩
  match encodeDict? keys with
  | none => none
  | some (v, x) =>
    let vb : ByteArray := ⟨v.toArray⟩
    let xb : ByteArray := ⟨x.toArray⟩
    match parseGdxHeader xb with
    | .error _ => none
    | .ok h =>
      match (lookupM (m := Id) (fun o n => xb.extract o (o + n)) (fun o n => vb.extract o (o + n)) h k).run with
      | .ok (r, _) => r
      | .error _ => none

private def memKey (keys : List Key) (r : Nat) : Option Key :=
  match encodeDict? keys with
  | none => none
  | some (v, x) =>
    let vb : ByteArray := ⟨v.toArray⟩
    let xb : ByteArray := ⟨x.toArray⟩
    match parseGdxHeader xb with
    | .error _ => none
    | .ok h =>
      match (keyOfRankM (m := Id) (fun o n => xb.extract o (o + n)) (fun o n => vb.extract o (o + n)) h r).run with
      | .ok k => some k.data.toList
      | .error _ => none

#guard (List.range 200).all fun i => memLookup bigKeys (bigKeys[i]!) == some i
#guard (List.range 200).all fun i => memKey bigKeys i == some (bigKeys[i]!)
#guard memLookup bigKeys [2, 30, 0] == none
#guard memLookup bigKeys [1] == none
#guard memLookup bigKeys [3] == none
#guard memLookup bigKeys [2, 5, 5, 0] == none
#guard memLookup ks0 [3, 0] == some 5
#guard memLookup [] [3, 0] == none
#guard memKey bigKeys 200 == none

end L4Factoidal.Storage.Sbm11.Dict
