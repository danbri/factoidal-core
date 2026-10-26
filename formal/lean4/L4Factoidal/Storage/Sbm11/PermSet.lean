/-
L4Factoidal.Storage.Sbm11.PermSet — the exact check that the four
permutations of an SBM11 generation hold one quad set (lemma L3b of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776,
https://github.com/danbri/factoidal/issues/793 item 4).

Activation compares the permutations by an order-independent digest (the
sum and the xor of a 64-bit hash of each quad) and, because equal digests do
not give equal quad sets, also by this exact check
(`Harness/Sbm11PermCheck.lean`, disk-resident, memory bounded):

  * every row of permutation `p` (POS, SPO, OSP) is re-keyed to the PSO row
    of its quad (`rekey`), in the order of `p`;
  * the re-keyed rows are cut into consecutive segments. For POS a segment
    ends where the predicate changes (POS and PSO both start with the
    predicate); SPO and OSP are one segment each;
  * each segment is sorted (`sortRows`, `Array.mergeSort`; a segment larger
    than the memory limit is sorted as runs on disk that are merged), and
    the sorted segments, one after the other, must be the PSO rows, row by
    row, to the end of PSO.

`segmentsSame outs c` is the last step as a function of lists: the outputs
of the segments, concatenated, equal `c`. `segments_perm`: when each output
is a permutation of its segment (`PermPairs`), the check gives
`segs.flatten ~ c`. `perms_same` is L3b: when the segments are the re-keyed
rows of permutation `p` in order, and the check holds against the rows of
PSO, the two permutations denote the same quads (`ofPermRow`), with the same
multiplicity. `perms_same_sorted` is the instance that the in-memory path
runs (each output is `sortRowsL` of its segment).

The check compares whole lists, so it needs neither the row counts of the
manifest nor the strict order of the permutations (both are checked
elsewhere in activation); until 2026-10-22 the check bucketed the re-keyed
rows on disk by groups of PSO blocks (`sameQuads`, 32 bytes per row, about
5 times the generation on olympics;
https://github.com/danbri/factoidal/issues/810).

The theorem is about the check as a function of the rows. The `IO` code
reads the rows by `decodeBlockAt` (whose properties are proved), cuts the
segments, sorts in memory by `sortRows` (proved a permutation), writes and
merges sorted runs for a segment above the memory limit, and compares; the
run files and the merge are tested (`tests/sbm11/run.sh` part (j),
`tests/sbm11/perm_check_disk.sh`), not proved.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Overlay

namespace L4Factoidal.Storage.Sbm11.PermSet

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Overlay (toPermRow ofPermRow)

/-- A row of permutation `perm` as the PSO row of the same quad. -/
def rekey (perm : Nat) (r : Row) : Row := toPermRow 0 (ofPermRow perm r)

/-- `rekey` of the row `⟨a, b, c, g⟩`, with no intermediate row (the
    activation loop reads the four columns of a decoded block). -/
@[inline] def rekeyCols (perm a b c g : Nat) : Row :=
  match perm with
  | 0 => ⟨a, b, c, g⟩
  | 1 => ⟨a, c, b, g⟩
  | 2 => ⟨b, a, c, g⟩
  | _ => ⟨c, b, a, g⟩

theorem rekeyCols_eq (perm a b c g : Nat) : rekeyCols perm a b c g = rekey perm ⟨a, b, c, g⟩ := by
  match perm with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- Rows in `Row.lt` order (`Array.mergeSort`, a permutation of its input:
    `Array.mergeSort_perm`). -/
def sortRows (xs : Array Row) : Array Row := (xs.toList.mergeSort fun a b => !b.lt a).toArray

/-- `sortRows` on lists. -/
def sortRowsL (l : List Row) : List Row := (sortRows l.toArray).toList

theorem sortRowsL_perm (l : List Row) : (sortRowsL l).Perm l := by
  unfold sortRowsL sortRows
  simpa using List.mergeSort_perm l _

/-- `PermPairs outs segs`: the lists have the same length and each output is
    a permutation of the segment at the same place. -/
inductive PermPairs : List (List Row) → List (List Row) → Prop
  | nil : PermPairs [] []
  | cons {o s : List Row} {os ss : List (List Row)} : o.Perm s → PermPairs os ss → PermPairs (o :: os) (s :: ss)

/-- The exact check: the outputs of the segments, one after the other, are
    the rows of PSO. -/
def segmentsSame (outs : List (List Row)) (c : List Row) : Bool := outs.flatten == c

theorem flatten_perm_of_forall2 : ∀ {outs segs : List (List Row)},
    PermPairs outs segs → outs.flatten.Perm segs.flatten
  | [], [], .nil => List.Perm.refl _
  | _ :: _, _ :: _, .cons h t => by
    simp only [List.flatten_cons]
    exact List.Perm.append h (flatten_perm_of_forall2 t)

/-- The check gives equal multisets when each output is a permutation of its
    segment. -/
theorem segments_perm (outs segs : List (List Row)) (c : List Row)
    (hp : PermPairs outs segs) (h : segmentsSame outs c = true) :
    segs.flatten.Perm c := by
  unfold segmentsSame at h
  have he : outs.flatten = c := by simpa using h
  rw [← he]
  exact (flatten_perm_of_forall2 hp).symm

theorem ofPermRow_toPermRow_zero (q : Row) : ofPermRow 0 (toPermRow 0 q) = q := by
  cases q; rfl

theorem ofPermRow_rekey (perm : Nat) (r : Row) : ofPermRow 0 (rekey perm r) = ofPermRow perm r :=
  ofPermRow_toPermRow_zero _

/-- **L3b.** When the segments are the re-keyed rows of permutation `perm`
    in order, each output is a permutation of its segment, and the
    concatenated outputs are the rows of PSO, the two permutations denote the
    same quads, with the same multiplicity. -/
theorem perms_same (perm : Nat) (outs segs : List (List Row)) (rowsP rows0 : List Row)
    (hseg : segs.flatten = rowsP.map (rekey perm))
    (hp : PermPairs outs segs) (h : segmentsSame outs rows0 = true) :
    (rowsP.map (ofPermRow perm)).Perm (rows0.map (ofPermRow 0)) := by
  have hq := (segments_perm outs segs rows0 hp h).map (ofPermRow 0)
  rw [hseg, List.map_map] at hq
  have he : (ofPermRow 0 ∘ rekey perm) = ofPermRow perm := funext (ofPermRow_rekey perm)
  rwa [he] at hq

theorem forall2_perm_sorted : ∀ segs : List (List Row), PermPairs (segs.map sortRowsL) segs
  | [] => .nil
  | s :: t => .cons (sortRowsL_perm s) (forall2_perm_sorted t)

/-- L3b for the in-memory path: every segment sorted by `sortRowsL`. -/
theorem perms_same_sorted (perm : Nat) (segs : List (List Row)) (rowsP rows0 : List Row)
    (hseg : segs.flatten = rowsP.map (rekey perm))
    (h : segmentsSame (segs.map sortRowsL) rows0 = true) :
    (rowsP.map (ofPermRow perm)).Perm (rows0.map (ofPermRow 0)) :=
  perms_same perm (segs.map sortRowsL) segs rowsP rows0 hseg (forall2_perm_sorted segs) h

/-- The quad sets are equal (membership). -/
theorem perms_same_mem (perm : Nat) (outs segs : List (List Row)) (rowsP rows0 : List Row)
    (hseg : segs.flatten = rowsP.map (rekey perm))
    (hp : PermPairs outs segs) (h : segmentsSame outs rows0 = true) (q : Row) :
    q ∈ rowsP.map (ofPermRow perm) ↔ q ∈ rows0.map (ofPermRow 0) :=
  (perms_same perm outs segs rowsP rows0 hseg hp h).mem_iff

/-! ## Samples -/

private def rs0 : List Row := [⟨1, 1, 2, 0⟩, ⟨1, 3, 2, 0⟩, ⟨2, 1, 5, 0⟩, ⟨2, 4, 1, 7⟩]
/-- The same quads as POS and SPO rows, in the order of each permutation. -/
private def rs1 : List Row := sortRowsL (rs0.map fun r => toPermRow 1 (ofPermRow 0 r))
private def rs2 : List Row := sortRowsL (rs0.map fun r => toPermRow 2 (ofPermRow 0 r))

/-- Segments of POS: cut where the predicate (column 0) changes. -/
private def posSegs (l : List Row) : List (List Row) :=
  (l.splitBy fun a b => a.c0 == b.c0)

#guard rs2.map (rekey 2) |>.all (rs0.contains ·)
-- POS: one segment per predicate; SPO: one segment
#guard segmentsSame ((posSegs (rs1.map (rekey 1))).map sortRowsL) rs0
#guard segmentsSame ([rs2.map (rekey 2)].map sortRowsL) rs0
-- a permutation that holds another quad is refused
#guard !segmentsSame ([(⟨9, 9, 9, 0⟩ :: rs2.tail).map (rekey 2)].map sortRowsL) rs0
-- one quad twice in place of another
#guard !segmentsSame ([(rs2.head! :: rs2.tail.dropLast).map (rekey 2) ++ [rekey 2 rs2.head!]].map sortRowsL) rs0
-- a missing quad (PSO not consumed to its end)
#guard !segmentsSame ([rs2.tail.map (rekey 2)].map sortRowsL) rs0

#print axioms perms_same
#print axioms perms_same_sorted

end L4Factoidal.Storage.Sbm11.PermSet
