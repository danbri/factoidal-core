/-
L4Factoidal.Storage.Sbm11.DictRange — the rank of the first dictionary key
that is not below a byte string (stage 4,
https://github.com/danbri/factoidal/issues/790).

The keys of GDV1 are strictly increasing in unsigned byte order
(`DictTheorems.decodeDict_sorted`), so the keys with a given prefix are one
rank range `[lowerBound P, lowerBound (P ++ [0xFF]))` when no key holds the
byte 0xFF (UTF-8 never does; a key is a class byte, UTF-8 and 0x00
separators). The id query path uses it for `STRSTARTS` (a prefix of the
lexical form is a prefix of the key of an `xsd:string` or `rdf:langString`
literal) and for the rank range of a key class.

`lowerBoundM` is a binary search over the pages by their first keys (as
`Dict.lookupM`), then a scan of one page. The `#guard`s compare it with the
definition (`lowerBoundList`: the number of keys below the target) on an
encoded sample dictionary for every target of a list.
-/
import L4Factoidal.Storage.Sbm11.Dict

namespace L4Factoidal.Storage.Sbm11.DictRange

open L4Factoidal.Storage.Sbm11.Dict

/-- The definition: the number of keys below `k` (the keys are sorted). -/
def lowerBoundList (keys : List ByteArray) (k : ByteArray) : Nat :=
  (keys.filter fun x => cmpBytesAt x k == .lt).length

/-- The first position of a page's keys whose key is not below `k`
    (`ks.size` when there is none). -/
def firstNotBelow (ks : Array ByteArray) (k : ByteArray) : Nat := Id.run do
  for i in [0:ks.size] do
    if cmpBytesAt ks[i]! k != .lt then return i
  return ks.size

/-- The rank of the first key that is not below `k`: the last page whose
    first key is not above `k` (binary search with fuel), then that page.
    When every key of that page is below `k`, the answer is the first rank of
    the next page (its first key is above `k`). -/
def lowerBoundM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray)
    (h : GdxHeader) (k : ByteArray) : ExceptT String m Nat := do
  if h.pageCount == 0 then return 0
  let (lo, _) ← searchPagesM fetchGdx fetchGdv k (Nat.log2 h.pageCount + 2) 0 h.pageCount 0
  let ks ← pageM fetchGdx fetchGdv lo
  -- page `lo`'s first key is not above `k` unless `lo` is page 0
  return min h.termCount (lo * pageTerms + firstNotBelow ks k)

/-! ## Tests against the definition -/

private def sampleKeys : List (List UInt8) :=
  ((List.range 200).map fun i => [2, 104, 0x30 + (i / 100).toUInt8, 0x30 + (i / 10 % 10).toUInt8, 0x30 + (i % 10).toUInt8])
    ++ [[3, 97], [3, 97, 98], [3, 98], [4, 97, 0, 101, 110], [4, 97, 98, 0, 101, 110], [5, 120, 0, 49]]

private def check (targets : List (List UInt8)) : Bool :=
  match encodeDict? sampleKeys with
  | none => false
  | some (gdv, gdx) =>
    let gdvB : ByteArray := ⟨gdv.toArray⟩
    let gdxB : ByteArray := ⟨gdx.toArray⟩
    let fetch (b : ByteArray) (off len : Nat) : Id ByteArray := b.extract off (off + len)
    match parseGdxHeader gdxB with
    | .error _ => false
    | .ok h =>
      let keys := sampleKeys.map fun k => (⟨k.toArray⟩ : ByteArray)
      targets.all fun t =>
        let tb : ByteArray := ⟨t.toArray⟩
        match (lowerBoundM (fetch gdxB) (fetch gdvB) h tb).run with
        | .ok r => r == lowerBoundList keys tb
        | .error _ => false

#guard check [[], [0], [1], [2], [2, 104], [2, 104, 0x30], [2, 104, 0x31, 0x32], [2, 104, 0x31, 0x32, 0x33, 0],
  [2, 104, 0x31, 0x39, 0x39], [2, 104, 0x31, 0x39, 0x39, 1], [2, 255], [3], [3, 97], [3, 97, 255], [3, 98, 0],
  [4], [4, 97], [4, 97, 255], [5], [5, 120, 0, 49], [6], [255]]

end L4Factoidal.Storage.Sbm11.DictRange
