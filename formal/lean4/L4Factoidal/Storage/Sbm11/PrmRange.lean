/-
L4Factoidal.Storage.Sbm11.PrmRange — the PRM1 entries of the blocks a key
prefix selects, found by binary search over the entries and read in one
positioned read (https://github.com/danbri/factoidal/issues/805).

Until issue 805 every query process read each PRM1 file it used whole and
decoded every entry, even under `--verify none`: 8,185,170 bytes for the SPO
permutation of the DBpedia slice, for a lookup of one subject. The query
engine now asks its store for the entries of one key range
(`IdQuery.Store.blocksForRange`), and the store answers with `rangeM`:

  1. `lo`: the first block whose last row is not below the key prefix (a
     binary search, `searchM`, that reads one entry per probe; the same
     search as `IdQuery.firstBlockGo`);
  2. `hi`: the first block from `lo` whose first row is above the key prefix
     (a second binary search);
  3. the entries of blocks `[lo, hi)`, in one read.

`rangeM` is generic over a `Reader`: the block count, one entry, and the
entries of a range. `arrayReader` reads them from an array (the in-memory
store of the tests and theorems); `bytesReader` from positioned reads of the
PRM1 file (the I/O store, `Harness/Sbm11Query.lean`: `pread` under
`--verify none`, the Merkle-verified chunk reader under `--verify merkle`).
The PRM1 layout (`Block.lean`): a 22-byte header, then one 92-byte entry per
block, entry `k` at byte `22 + 92 k`.

`PrmRangeTheorems.rangeM_array`: over an admitted PRM1 array the result is
`IdQuery.metasFor` (the entries of the blocks `blocksFor` returns).
`PrmRangeTheorems.rangeM_bytes`: over positioned reads of a PRM1 file that
`PrmAt.decodePrmAt` decodes, `openM` gives the entry count and the result is
`metasFor` of the decoded entries.

Loops: `searchM` is a fuel-bounded monadic tail call of depth at most
`log2 count + 2` (allow line in `tools/lean-tail-recursion-allow.txt`, as
`Dict.searchPagesM`); `entriesFromGo` is a tail call with fuel. No `sorry`,
no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PrmAt
import L4Factoidal.Storage.Sbm11.IdQuery

namespace L4Factoidal.Storage.Sbm11.PrmRange

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.IdQuery (prefixCmp blocksFor metasFor)

/-! ## The search -/

/-- Binary search with fuel over `[l, h)`: the least `i` there for which
    `probe i` answers `true`, or `h` when there is none, provided the answers
    are monotone (`false` then `true`; `PrmRangeTheorems.searchPure_spec`). -/
def searchM {m : Type → Type} [Monad m] (probe : Nat → ExceptT String m Bool) :
    Nat → Nat → Nat → ExceptT String m Nat
  | 0, l, _ => pure l
  | f + 1, l, h =>
    if l < h then do
      let mid := (l + h) / 2
      let b ← probe mid
      if b then searchM probe f l mid else searchM probe f (mid + 1) h
    else pure l

/-- What `rangeM` reads: the block count, the entry of one block, and the
    entries of the blocks `[lo, hi)` in order. -/
structure Reader (m : Type → Type) where
  count : Nat
  entry : Nat → ExceptT String m BlockMeta
  slice : Nat → Nat → ExceptT String m (Array BlockMeta)

/-- The PRM1 entries of the blocks that may hold a row with the key prefix:
    the first block whose last row is not below the prefix (as
    `IdQuery.firstBlockGo`), the first block from there whose first row is
    above it, and the entries between, in one read. -/
def rangeM {m : Type → Type} [Monad m] (r : Reader m) (key : Array UInt64) :
    ExceptT String m (Array BlockMeta) := do
  let fuel := Nat.log2 r.count + 2
  let lo ← searchM (fun i => do return prefixCmp (← r.entry i).last key != .lt) fuel 0 r.count
  let hi ← searchM (fun i => do return prefixCmp (← r.entry i).first key == .gt) fuel lo r.count
  if lo < hi then r.slice lo hi else pure #[]

/-! ## Readers -/

/-- The entries of an array (the in-memory store). -/
def arrayReader {m : Type → Type} [Monad m] (ms : Array BlockMeta) : Reader m where
  count := ms.size
  entry i := pure ms[i]!
  slice lo hi := pure (ms.extract lo hi)

/-- Entries `k .. n - 1` of a buffer that holds `n` consecutive 92-byte
    entries from its byte 0, appended to `acc` (a tail call with fuel). -/
def entriesFromGo (b : ByteArray) (n : Nat) : Nat → Nat → Array BlockMeta → Option (Array BlockMeta)
  | 0, _, acc => some acc
  | f + 1, k, acc =>
    if k ≥ n then some acc
    else match PrmAt.entryAt b (prmEntryBytes * k) with
      | some e => entriesFromGo b n f (k + 1) (acc.push e)
      | none => none

/-- The `n` entries of a buffer of `92 n` bytes. -/
def entriesFrom (b : ByteArray) (n : Nat) : Option (Array BlockMeta) :=
  entriesFromGo b n (n + 1) 0 (Array.mkEmpty n)

/-- The PRM1 header (22 bytes): the permutation code, the block count and the
    row count, after the magic and version. -/
def headerOf (b : ByteArray) : Option (Nat × Nat × Nat) := do
  if b.size < prmHeaderBytes then none
  if !(b.get! 0 == 80 && b.get! 1 == 82 && b.get! 2 == 77 && b.get! 3 == 49 && b.get! 4 == 1) then none
  let (count, _) ← get64At b 6
  let (total, _) ← get64At b 14
  some ((b.get! 5).toNat, count, total)

/-- Open a PRM1 file of `fileBytes` bytes through `read off len` (a positioned
    read): the header, its permutation code `perm`, and the file length
    `22 + 92 count`. Returns the block count. -/
def openM {m : Type → Type} [Monad m] (read : Nat → Nat → ExceptT String m ByteArray)
    (fileBytes perm : Nat) : ExceptT String m Nat := do
  let h ← read 0 prmHeaderBytes
  match headerOf h with
  | none => throw "PRM1: the header does not decode"
  | some (p, count, _) =>
    if p != perm then throw s!"PRM1: permutation code {p}, expected {perm}"
    else if fileBytes != prmHeaderBytes + prmEntryBytes * count then
      throw s!"PRM1: {fileBytes} bytes, the header says {count} entries"
    else pure count

/-- The entry of block `i`, by one positioned read of its 92 bytes. -/
def entryOfM {m : Type → Type} [Monad m] (read : Nat → Nat → ExceptT String m ByteArray) (i : Nat) :
    ExceptT String m BlockMeta := do
  let b ← read (prmHeaderBytes + prmEntryBytes * i) prmEntryBytes
  match PrmAt.entryAt b 0 with
  | some e => pure e
  | none => throw s!"PRM1: entry {i} does not decode"

/-- The entries of blocks `[lo, hi)`, by one positioned read. -/
def sliceOfM {m : Type → Type} [Monad m] (read : Nat → Nat → ExceptT String m ByteArray) (lo hi : Nat) :
    ExceptT String m (Array BlockMeta) := do
  let b ← read (prmHeaderBytes + prmEntryBytes * lo) (prmEntryBytes * (hi - lo))
  match entriesFrom b (hi - lo) with
  | some es => pure es
  | none => throw s!"PRM1: entries {lo} to {hi} do not decode"

/-- The entries of a PRM1 file of `count` blocks, read through `read`
    (the I/O store). -/
def bytesReader {m : Type → Type} [Monad m] (read : Nat → Nat → ExceptT String m ByteArray) (count : Nat) :
    Reader m where
  count
  entry := entryOfM read
  slice := sliceOfM read

/-! ## Tests on a sample PRM1 -/

private def mkB (f l : Row) (off : Nat) : BlockMeta :=
  { first := f, last := l, rows := 2, offset := off, len0 := 1, len1 := 1, len2 := 1, len3 := 1 }

private def sampleMs : Array BlockMeta :=
  #[mkB ⟨1, 1, 1, 0⟩ ⟨1, 2, 5, 0⟩ 6, mkB ⟨1, 3, 0, 0⟩ ⟨2, 1, 1, 0⟩ 10, mkB ⟨2, 1, 2, 0⟩ ⟨2, 1, 9, 0⟩ 14,
    mkB ⟨2, 2, 0, 0⟩ ⟨4, 0, 0, 0⟩ 18, mkB ⟨5, 0, 0, 0⟩ ⟨5, 0, 3, 0⟩ 22, mkB ⟨7, 7, 7, 0⟩ ⟨9, 0, 0, 0⟩ 26]

private def sampleBytes : ByteArray := ⟨(prmBytes 2 sampleMs.toList).toArray⟩

private def readS (off len : Nat) : ExceptT String Id ByteArray := pure (sampleBytes.extract off (off + len))

private def sampleKeys : List (Array UInt64) :=
  [#[], #[0], #[1], #[2], #[3], #[4], #[5], #[6], #[7], #[8], #[9], #[10], #[1, 2], #[1, 3], #[2, 1],
    #[2, 1, 5], #[2, 2], #[5, 0, 3], #[4, 0, 0], #[8, 0]]

#guard (PrmAt.decodePrmAt sampleBytes).map (·.2) == some sampleMs
#guard sampleKeys.all fun k =>
  (Id.run (rangeM (m := Id) (arrayReader sampleMs) k).run).toOption == some (metasFor sampleMs k)
#guard sampleKeys.all fun k =>
  (Id.run (do let n ← openM readS sampleBytes.size 2; rangeM (bytesReader readS n) k).run).toOption ==
    some (metasFor sampleMs k)
-- the keys select empty and non-empty ranges
#guard (sampleKeys.map fun k => (metasFor sampleMs k).size) == [6, 0, 2, 3, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 2, 1, 1, 1, 1, 1]
-- a wrong permutation code, a wrong length and a short file are refused
#guard (Id.run (openM readS sampleBytes.size 1).run).toOption.isNone
#guard (Id.run (openM readS (sampleBytes.size + 1) 2).run).toOption.isNone
#guard (Id.run (openM (m := Id) (fun off len => pure ((sampleBytes.extract 0 10).extract off (off + len))) 10 2).run).toOption.isNone

end L4Factoidal.Storage.Sbm11.PrmRange
