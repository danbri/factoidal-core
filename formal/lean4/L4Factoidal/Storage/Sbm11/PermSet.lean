/-
L4Factoidal.Storage.Sbm11.PermSet — the exact check that the four
permutations of an SBM11 generation hold one quad set (lemma L3b of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776,
https://github.com/danbri/factoidal/issues/793 item 4).

Until 2026-10-12 activation compared the permutations only by an
order-independent digest (the sum and the xor of a 64-bit hash of each
quad). Equal digests do not give equal quad sets. Activation now also runs
this check, on the disk-resident path with bounded memory
(`Harness/Sbm11PermCheck.lean`):

  * every row of permutation `p` (POS, SPO, OSP) is re-keyed to the PSO row
    of its quad (`rekey`);
  * the PSO blocks are cut into groups of at most `M` rows; the first row of
    each group after the first is a bound; the bucket of a PSO row is the
    number of bounds not above it (`bucketOf`);
  * the re-keyed rows are written to one file per bucket; each bucket is read
    back, sorted (`sortRows`, `Array.mergeSort`) and compared row by row with
    the PSO rows of its group; a bucket with more rows than its group is
    refused without being read.

`sameQuads key nb a c` is that check as a function of lists: the bucket of
every row is below `nb`, and for every bucket `j` the sorted rows of `a` in
bucket `j` are the rows of `c` in bucket `j`. `sameQuads_perm` proves that it
gives `a ~ c` (equal as multisets) for any bucket function. `perms_same`
is L3b: when the check holds for the rows of permutation `p` against the
rows of PSO, the two permutations denote the same quads (`ofPermRow`).

The theorem is about the check as a function of the rows. The `IO` code
reads the rows by `decodeBlockAt` (whose properties are proved), writes and
reads the bucket files, and compares; that file handling is tested
(`tests/sbm11/run.sh` part (j)), not proved.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Overlay

namespace L4Factoidal.Storage.Sbm11.PermSet

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Overlay (toPermRow ofPermRow)

/-- A row of permutation `perm` as the PSO row of the same quad. -/
def rekey (perm : Nat) (r : Row) : Row := toPermRow 0 (ofPermRow perm r)

/-- The first index `i ≥ lo` with `r < bounds[i]` (binary search with fuel):
    with sorted bounds, the number of bounds not above `r`. -/
def bucketGo (bounds : Array Row) (r : Row) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if r.lt bounds[mid]! then bucketGo bounds r f lo mid else bucketGo bounds r f (mid + 1) hi
    else lo

/-- The bucket of a PSO row. -/
def bucketOf (bounds : Array Row) (r : Row) : Nat :=
  bucketGo bounds r (Nat.log2 bounds.size + 2) 0 bounds.size

/-- Rows in `Row.lt` order (`Array.mergeSort`, a permutation of its input:
    `Array.mergeSort_perm`). -/
def sortRows (xs : Array Row) : Array Row := xs.mergeSort fun a b => !b.lt a

/-- Bucket `j`: the sorted rows of `a` in it are the rows of `c` in it. -/
def bucketSame (key : Row → Nat) (a c : List Row) (j : Nat) : Bool :=
  (sortRows (a.filter (key · == j)).toArray).toList == c.filter (key · == j)

/-- The exact check over `nb` buckets. -/
def sameQuads (key : Row → Nat) (nb : Nat) (a c : List Row) : Bool :=
  a.all (key · < nb) && c.all (key · < nb) && (List.range nb).all (bucketSame key a c)

theorem bucketSame_perm (key : Row → Nat) (a c : List Row) (j : Nat) (h : bucketSame key a c j = true) :
    (a.filter (key · == j)).Perm (c.filter (key · == j)) := by
  unfold bucketSame at h
  have he : (sortRows (a.filter (key · == j)).toArray).toList = c.filter (key · == j) := by
    simpa using h
  have hp : (sortRows (a.filter (key · == j)).toArray).Perm (a.filter (key · == j)).toArray :=
    Array.mergeSort_perm
  rw [Array.perm_iff_toList_perm] at hp
  rw [he] at hp
  exact hp.symm.trans (by simp)

/-- The check gives equal multisets, for any bucket function. -/
theorem sameQuads_perm (key : Row → Nat) (nb : Nat) (a c : List Row) (h : sameQuads key nb a c = true) :
    a.Perm c := by
  unfold sameQuads at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ha, hc⟩, hb⟩ := h
  rw [List.perm_iff_count]
  intro x
  by_cases hx : key x < nb
  · have hj := List.Perm.count_eq (bucketSame_perm key a c (key x) (hb (key x) (List.mem_range.mpr hx))) x
    rwa [List.count_filter (by simp), List.count_filter (by simp)] at hj
  · have h1 : x ∉ a := fun hm => hx (ha x hm)
    have h2 : x ∉ c := fun hm => hx (hc x hm)
    rw [List.count_eq_zero_of_not_mem h1, List.count_eq_zero_of_not_mem h2]

theorem ofPermRow_toPermRow_zero (q : Row) : ofPermRow 0 (toPermRow 0 q) = q := by
  cases q; rfl

theorem ofPermRow_rekey (perm : Nat) (r : Row) : ofPermRow 0 (rekey perm r) = ofPermRow perm r :=
  ofPermRow_toPermRow_zero _

/-- **L3b.** When the exact check holds for the rows of permutation `perm`
    (re-keyed) against the rows of PSO, the two permutations denote the same
    quads, with the same multiplicity. -/
theorem perms_same (perm : Nat) (key : Row → Nat) (nb : Nat) (rowsP rows0 : List Row)
    (h : sameQuads key nb (rowsP.map (rekey perm)) rows0 = true) :
    (rowsP.map (ofPermRow perm)).Perm (rows0.map (ofPermRow 0)) := by
  have hp := (sameQuads_perm key nb _ _ h).map (ofPermRow 0)
  rw [List.map_map] at hp
  have he : (ofPermRow 0 ∘ rekey perm) = ofPermRow perm := funext (ofPermRow_rekey perm)
  rwa [he] at hp

/-- The quad sets are equal (membership). -/
theorem perms_same_mem (perm : Nat) (key : Row → Nat) (nb : Nat) (rowsP rows0 : List Row)
    (h : sameQuads key nb (rowsP.map (rekey perm)) rows0 = true) (q : Row) :
    q ∈ rowsP.map (ofPermRow perm) ↔ q ∈ rows0.map (ofPermRow 0) :=
  (perms_same perm key nb rowsP rows0 h).mem_iff

/-! ## Samples -/

private def rs0 : List Row := [⟨1, 1, 2, 0⟩, ⟨1, 3, 2, 0⟩, ⟨2, 1, 5, 0⟩, ⟨2, 4, 1, 7⟩]
/-- The same quads as SPO rows. -/
private def rs2 : List Row := rs0.map fun r => toPermRow 2 (ofPermRow 0 r)

#guard rs2.map (rekey 2) |>.all (rs0.contains ·)
#guard [#[], #[(⟨2, 0, 0, 0⟩ : Row)], #[⟨1, 3, 0, 0⟩, ⟨2, 4, 0, 0⟩]].all fun bounds =>
  sameQuads (bucketOf bounds) (bounds.size + 1) (rs2.map (rekey 2)) rs0
-- a permutation that holds another quad is refused, whatever the bounds
#guard [#[], #[(⟨2, 0, 0, 0⟩ : Row)]].all fun bounds =>
  !sameQuads (bucketOf bounds) (bounds.size + 1) ((⟨9, 9, 9, 0⟩ :: rs2.tail).map (rekey 2)) rs0
-- one quad twice in place of another
#guard !sameQuads (bucketOf #[]) 1 ((rs2.head! :: rs2.tail.dropLast).map (rekey 2) ++ [rekey 2 rs2.head!]) rs0
#guard bucketOf #[⟨1, 3, 0, 0⟩, ⟨2, 4, 0, 0⟩] ⟨1, 1, 2, 0⟩ == 0
#guard bucketOf #[⟨1, 3, 0, 0⟩, ⟨2, 4, 0, 0⟩] ⟨1, 3, 0, 0⟩ == 1
#guard bucketOf #[⟨1, 3, 0, 0⟩, ⟨2, 4, 0, 0⟩] ⟨2, 4, 1, 7⟩ == 2

#print axioms perms_same

end L4Factoidal.Storage.Sbm11.PermSet
