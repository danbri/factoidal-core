/-
L4Factoidal.Storage.Sbm11.PrmAt — a PRM1 decoder over a `ByteArray` for the
query path (stage 4, https://github.com/danbri/factoidal/issues/790).

`Block.decodePrm` (the decoder of the round-trip theorem
`decodePrm_encodePrm?`) reads a `List UInt8`; converting a 635 KB PRM1 file
to a list and decoding it was most of the 77 ms open of stage 3 (stage 3
record, open item 3). `decodePrmAt` reads the same fields with `get64At` and
`get32At` into an `Array`, then applies the same admission (`prmAdmitted`,
the row total). `PrmAtTheorems.decodePrmAt_eq` proves it equal to
`decodePrm` on every input; the `#guard`s below and `l4sbm11 prm-check GEN`
(every PRM1 file of a generation) compare the two as well.
-/
import L4Factoidal.Storage.Sbm11.Block

namespace L4Factoidal.Storage.Sbm11.PrmAt

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column

/-- One 92-byte entry at `i`. -/
def entryAt (b : ByteArray) (i : Nat) : Option BlockMeta := do
  let (f0, i) ← get64At b i
  let (f1, i) ← get64At b i
  let (f2, i) ← get64At b i
  let (f3, i) ← get64At b i
  let (l0, i) ← get64At b i
  let (l1, i) ← get64At b i
  let (l2, i) ← get64At b i
  let (l3, i) ← get64At b i
  let (rows, i) ← get32At b i
  let (offset, i) ← get64At b i
  let (len0, i) ← get32At b i
  let (len1, i) ← get32At b i
  let (len2, i) ← get32At b i
  let (len3, _) ← get32At b i
  some { first := ⟨f0, f1, f2, f3⟩, last := ⟨l0, l1, l2, l3⟩, rows, offset, len0, len1, len2, len3 }

/-- Entries `k..count-1`, appended to `acc` (tail call with fuel). -/
def entriesGo (b : ByteArray) (count : Nat) : Nat → Nat → Array BlockMeta → Option (Array BlockMeta)
  | 0, _, acc => some acc
  | f + 1, k, acc =>
    if k ≥ count then some acc
    else match entryAt b (prmHeaderBytes + prmEntryBytes * k) with
      | some m => entriesGo b count f (k + 1) (acc.push m)
      | none => none

/-- A PRM1 file: its permutation code and its entries, with the admission of
    `decodePrm`. -/
def decodePrmAt (b : ByteArray) : Option (Nat × Array BlockMeta) := do
  if b.size < prmHeaderBytes then none
  if !(b.get! 0 == 80 && b.get! 1 == 82 && b.get! 2 == 77 && b.get! 3 == 49 && b.get! 4 == 1) then none
  let p := (b.get! 5).toNat
  let (count, _) ← get64At b 6
  let (total, _) ← get64At b 14
  if b.size != prmHeaderBytes + prmEntryBytes * count then none
  let ms ← entriesGo b count (count + 1) 0 (Array.mkEmpty count)
  let l := ms.toList
  if prmAdmitted p l && total == rowSum l then some (p, ms) else none

private def rs : List Row := [⟨1, 2, 3, 0⟩, ⟨1, 2, 4, 0⟩, ⟨1, 5, 4, 0⟩, ⟨7, 0, 0, 0⟩]

#guard match encodeBlock? 6 rs, encodeBlock? 0 [⟨8, 0, 0, 0⟩, ⟨9, 1, 1, 0⟩] with
  | some (m1, b1), some (m2, _) =>
    let m2 := { m2 with offset := 6 + b1.length }
    let bytes := prmBytes 2 [m1, m2]
    (decodePrmAt ⟨bytes.toArray⟩).map (fun (p, ms) => (p, ms.toList)) == decodePrm bytes &&
      (decodePrm bytes).isSome &&
      -- a changed row count, an unordered file and a truncated file are refused by both
      (decodePrmAt ⟨(prmBytes 2 [m2, m1]).toArray⟩).isNone && (decodePrm (prmBytes 2 [m2, m1])).isNone &&
      (decodePrmAt ⟨(bytes.take (bytes.length - 1)).toArray⟩).isNone
  | _, _ => false

end L4Factoidal.Storage.Sbm11.PrmAt
