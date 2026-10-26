/-
L4Factoidal.Storage.Sbm11.DictFinger — string-to-id for a walk over keys in
byte order (stage 5, the replay of the delta log,
https://github.com/danbri/factoidal/issues/858).

`Dict.lookupM` finds one key. Its binary search reads a whole page (one GDX1
entry and one GDV1 page) at each probe: 13 probes for the 6,251 pages of a
dictionary of 400,000 terms, then one more read for the page that holds the
key. The replay of a delta log looks up every distinct term of the log. At
about 28 positioned reads for each term, each read being `open`, `fstat`,
`pread` and `close` of the file, 203,264 entries took 58 s.

A walk over keys in byte order does not need the binary search. The page that
holds a key is not before the page that held the key before it, so the walk
keeps a finger: the page of the last key and its keys. For a key `k`:

  1. `k` is not above the last key of the finger's page: the finger's page.
  2. The finger's page is the last page: the finger's page.
  3. Otherwise read the next page (kept in the finger as `ahead`, so that a run
     of keys in the gap after the finger's page reads it once):
       a. its first key is above `k`: the finger's page (k is in the gap);
       b. `k` is not above its last key: the next page;
       c. otherwise `searchPagesM` over the pages from the next page on.

A page is read once for the whole walk when the keys are dense (cases 1 to 3b),
and a key far from the finger costs what `lookupM` costs (case 3c, and the
first key of a walk).

`lookupNextM` gives the same answer as `lookupM` for a key that is not below
the key the finger was found for, over the bytes `encodeDict?` writes
(`DictFingerTheorems.lookupNextM_eq_lookupM`). `lookupWalkM` checks that order
itself, with one comparison of the key against the key before it, and looks a
key that is below it up from no finger: its answers are those of `lookupM`
for keys in any order (`DictFingerTheorems.walkM_encodeDict`), and a sequence
that is out of order costs more. The sort that puts the keys in order is
therefore a matter of speed, not of correctness. The `#guard`s compare the walk
with `lookupM` for the keys of a sample dictionary and for keys that it does not
hold, in byte order and not.

## Loops

`findPageM`, `pageNextM`, `lookupNextM` and `lookupWalkM` have no loop:
`searchPagesM` is a tail call with fuel, and its depth is at most
`Nat.log2 pageCount + 2`. The loop over the keys is the caller's
(`Harness/Sbm11Query.lean`, a `for` loop in `IO`; `DictFingerTheorems.walkM` is
the same loop as a recursion).
-/
import L4Factoidal.Storage.Sbm11.Dict

namespace L4Factoidal.Storage.Sbm11.Dict

/-- The page that the last key of a walk was found on, its keys, and the keys
    of the next page when they have been read. -/
structure Finger where
  page : Nat
  keys : Array ByteArray
  ahead : Option (Array ByteArray) := none

/-- The page that holds `k` among the pages `lo` and after (`lookupM` with
    `lo = 0`): the last page in `[lo, pageCount)` whose first key is not above
    `k`, which `searchPagesM` finds when page `lo` is page 0 or its first key
    is not above `k`. The dictionary has at least one page. -/
def findPageM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (lo : Nat) (k : ByteArray) : ExceptT String m Finger := do
  let (res, _) ← searchPagesM fetchGdx fetchGdv k (Nat.log2 (h.pageCount - lo) + 2) lo h.pageCount 0
  let ks ← pageM fetchGdx fetchGdv res
  pure { page := res, keys := ks }

/-- The keys of the page after the finger's: the ones read ahead, or read now. -/
def nextPageM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (f : Finger) : ExceptT String m (Array ByteArray) :=
  match f.ahead with
  | some a => pure a
  | none => pageM fetchGdx fetchGdv (f.page + 1)

/-- The page that holds `k` when `k` is above the last key of the finger's
    page and a page follows it (cases 3a to 3c above). -/
def stepPageM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (f : Finger) (k : ByteArray) : ExceptT String m Finger := do
  let ks1 ← nextPageM fetchGdx fetchGdv f
  match ks1[0]?, ks1.back? with
  | some first1, some last1 =>
    if cmpBytesAt first1 k == .gt then pure { f with ahead := some ks1 }
    else if cmpBytesAt k last1 != .gt then pure { page := f.page + 1, keys := ks1 }
    else findPageM fetchGdx fetchGdv h (f.page + 1) k
  | _, _ => findPageM fetchGdx fetchGdv h 0 k

/-- The page that holds `k`, when `k` is not below the key that `fg` was
    found for (`fg = none`: no key yet). -/
def pageNextM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (fg : Option Finger) (k : ByteArray) : ExceptT String m Finger := do
  match fg with
  | none => findPageM fetchGdx fetchGdv h 0 k
  | some f =>
    match f.keys.back? with
    | none => findPageM fetchGdx fetchGdv h 0 k
    | some last =>
      if cmpBytesAt k last != .gt then pure f
      else if f.page + 1 ≥ h.pageCount then pure f
      else stepPageM fetchGdx fetchGdv h f k

/-- String-to-id for the next key of a walk in byte order: the rank of `k`
    or `none`, and the finger for the key after it. `lookupM` gives the same
    rank (`DictFingerTheorems.lookupNextM_eq_lookupM`). -/
def lookupNextM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (fg : Option Finger) (k : ByteArray) : ExceptT String m (Option Nat × Option Finger) := do
  if h.pageCount == 0 then return (none, none)
  let f ← pageNextM fetchGdx fetchGdv h fg k
  match indexInPage f.keys k with
  | some i => return (some (f.page * pageTerms + i), some f)
  | none => return (none, some f)

/-- Where a walk stands: the key it answered last and the finger that key left. -/
abbrev Walk := Option (ByteArray × Finger)

/-- The finger a walk uses for `k`: the one it holds when the key before is not
    above `k` (`Dict.cmpBytesAt`), none otherwise. -/
def Walk.fingerFor (w : Walk) (k : ByteArray) : Option Finger :=
  match w with
  | some (p, f) => if cmpBytesAt p k != .gt then some f else none
  | none => none

/-- String-to-id for the next key of a walk over keys in any order: the finger
    is used when the key is not below the key before it, and a key that is below
    it is looked up from no finger, so a sequence that is out of order costs
    more and gives the same answers (`DictFingerTheorems.lookupWalkM_dictOk`: no
    hypothesis on the order). -/
def lookupWalkM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (w : Walk) (k : ByteArray) : ExceptT String m (Option Nat × Walk) := do
  let (r, fg') ← lookupNextM fetchGdx fetchGdv h (w.fingerFor k) k
  return (r, fg'.map fun f => (k, f))

/-! ## Tests against `lookupM` -/

private def sampleKeys : List (List UInt8) :=
  ((List.range 200).map fun i => [2, 104, 0x30 + (i / 100).toUInt8, 0x30 + (i / 10 % 10).toUInt8, 0x30 + (i % 10).toUInt8])
    ++ [[3, 97], [3, 97, 98], [3, 98], [4, 97, 0, 101, 110], [4, 97, 98, 0, 101, 110], [5, 120, 0, 49]]

/-- Keys the sample holds and keys it does not: before the first, in the gap
    between two pages, between two keys of a page, after the last. -/
private def probes : List (List UInt8) :=
  [[], [0], [1], [2], [2, 104], [2, 104, 0x30], [2, 104, 0x30, 0x30], [2, 104, 0x30, 0x30, 0x30], [2, 104, 0x30, 0x30, 0x30, 0],
   [2, 104, 0x30, 0x31, 0x30], [2, 104, 0x30, 0x31, 0x30, 0], [2, 104, 0x30, 0x31, 0x39],
   [2, 104, 0x31, 0x32, 0x33], [2, 104, 0x31, 0x32, 0x33, 0], [2, 104, 0x31, 0x39, 0x39], [2, 104, 0x31, 0x39, 0x39, 1],
   [2, 255], [3], [3, 97], [3, 97, 97], [3, 97, 98], [3, 97, 255], [3, 98], [3, 98, 0], [4], [4, 97, 0, 101, 110],
   [4, 97, 255], [5], [5, 120, 0, 49], [5, 120, 0, 49, 0], [6], [255]]

private def sorted3 (l : List (List UInt8)) : List (List UInt8) :=
  l.mergeSort fun a b => cmpKey a b != .gt

/-- The answers of `lookupM` and of a walk with `lookupWalkM` over `targets`
    in the order given (in byte order or not), as ranks. -/
private def walkAgrees (keys : List (List UInt8)) (targets : List (List UInt8)) : Bool :=
  match encodeDict? keys with
  | none => false
  | some (gdv, gdx) =>
    let gdvB : ByteArray := ⟨gdv.toArray⟩
    let gdxB : ByteArray := ⟨gdx.toArray⟩
    let fetch (b : ByteArray) (off len : Nat) : Id ByteArray := b.extract off (off + len)
    match parseGdxHeader gdxB with
    | .error _ => false
    | .ok h =>
      let rec go : List (List UInt8) → Walk → Bool
        | [], _ => true
        | t :: rest, w =>
          let tb : ByteArray := ⟨t.toArray⟩
          match (lookupM (fetch gdxB) (fetch gdvB) h tb).run, (lookupWalkM (fetch gdxB) (fetch gdvB) h w tb).run with
          | .ok (r, _), .ok (r', w') => r == r' && go rest w'
          | _, _ => false
      go targets none

#guard walkAgrees sampleKeys (sorted3 probes)
-- out of byte order: reversed, and interleaved
#guard walkAgrees sampleKeys (sorted3 probes).reverse
#guard walkAgrees sampleKeys (sorted3 (sampleKeys ++ probes)).reverse
#guard walkAgrees sampleKeys (probes ++ sampleKeys ++ probes.reverse)
#guard walkAgrees sampleKeys (sorted3 sampleKeys)
#guard walkAgrees sampleKeys (sorted3 (sampleKeys ++ probes))
-- every key alone (the first key of a walk)
#guard (sampleKeys ++ probes).all fun t => walkAgrees sampleKeys [t]
-- a key after a key that is far from it, and a key twice
#guard walkAgrees sampleKeys [[2, 104, 0x30, 0x30, 0x30], [5, 120, 0, 49], [255]]
#guard walkAgrees sampleKeys [[2, 104, 0x31, 0x32, 0x33], [2, 104, 0x31, 0x32, 0x33], [2, 104, 0x31, 0x32, 0x33, 0]]
-- the gap after a page, for several keys in a row
#guard walkAgrees sampleKeys [[2, 104, 0x30, 0x36, 0x33, 0], [2, 104, 0x30, 0x36, 0x33, 1], [2, 104, 0x30, 0x36, 0x34]]
-- an empty dictionary and a one-key dictionary
#guard walkAgrees [] [[1], [2]]
#guard walkAgrees [[3]] [[], [3], [3, 0], [4]]
-- exactly one page (64 keys) and one page and one key (65)
#guard walkAgrees ((List.range 64).map fun i => [2, i.toUInt8]) ((List.range 66).map fun i => [2, i.toUInt8])
#guard walkAgrees ((List.range 65).map fun i => [2, i.toUInt8]) ((List.range 67).map fun i => [2, i.toUInt8])
#guard walkAgrees ((List.range 65).map fun i => [2, 2 * i.toUInt8]) ((List.range 140).map fun i => [2, i.toUInt8])

end L4Factoidal.Storage.Sbm11.Dict
