import Init

/-!
# Streaming complete join readback validation

The runtime walks the supplied packed words once. It checks each pair while
constructing the final decoded list in a tail-recursive accumulator. No packed
reference buffer or intermediate list of sorted pairs is allocated.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin.Readback

def segmentPairs (row start count : Nat) : List (Nat × Nat) :=
  (List.range count).map (fun d => (row,start+d))

def segmentWords (row start count : Nat) : List UInt32 :=
  (segmentPairs row start count).flatMap (fun p => [UInt32.ofNat p.1,UInt32.ofNat p.2])

def segmentDecoded (order : Array Nat) (row start count : Nat) : List (Nat × Nat) :=
  (segmentPairs row start count).map (fun p => (p.1,order[p.2]?.getD 0))

theorem segmentPairs_succ (row start count : Nat) :
    segmentPairs row start (count+1) = (row,start) :: segmentPairs row (start+1) count := by
  simp only [segmentPairs, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro d hd
  simp [Nat.add_comm, Nat.add_left_comm]

theorem segmentWords_succ (row start count : Nat) :
    segmentWords row start (count+1) =
      UInt32.ofNat row :: UInt32.ofNat start :: segmentWords row (start+1) count := by
  simp [segmentWords, segmentPairs_succ]

theorem segmentDecoded_succ (order : Array Nat) (row start count : Nat) :
    segmentDecoded order row start (count+1) =
      (row,order[start]?.getD 0) :: segmentDecoded order row (start+1) count := by
  simp [segmentDecoded, segmentPairs_succ]

/-- Consumes precisely one run, checking the actual packed words. -/
def segment (order : Array Nat) (row : Nat) :
    Nat → Nat → List UInt32 → List (Nat × Nat) → Option (List UInt32 × List (Nat × Nat))
  | 0, _, words, acc => some (words,acc)
  | n+1, start, a :: b :: words, acc =>
      if a == UInt32.ofNat row && b == UInt32.ofNat start then
        segment order row n (start+1) words ((row,order[start]?.getD 0)::acc)
      else none
  | _+1, _, _, _ => none

theorem segment_model (order : Array Nat) (row count start : Nat)
    (rest : List UInt32) (acc : List (Nat × Nat)) :
    segment order row count start (segmentWords row start count ++ rest) acc =
      some (rest,(segmentDecoded order row start count).reverse ++ acc) := by
  induction count generalizing start acc with
  | zero => simp [segment, segmentWords, segmentDecoded, segmentPairs]
  | succ n ih =>
    simp [segmentWords_succ, segmentDecoded_succ, segment, ih,
      List.reverse_cons, List.append_assoc]

theorem segment_sound (order : Array Nat) (row count start : Nat)
    (words rest : List UInt32) (acc result : List (Nat × Nat))
    (h : segment order row count start words acc = some (rest,result)) :
    words = segmentWords row start count ++ rest ∧
      result = (segmentDecoded order row start count).reverse ++ acc := by
  induction count generalizing start words acc with
  | zero =>
    simp only [segment, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp [segmentWords, segmentDecoded, segmentPairs]
  | succ n ih =>
    cases words with
    | nil => simp [segment] at h
    | cons a words =>
      cases words with
      | nil => simp [segment] at h
      | cons b words =>
        simp only [segment] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨rfl,rfl⟩
          rcases ih (start+1) words ((row,order[start]?.getD 0)::acc) h with ⟨hw,ha⟩
          simp [segmentWords_succ, segmentDecoded_succ, hw, ha,
            List.reverse_cons, List.append_assoc]
        · contradiction

def rowWords (upper : Array UInt32) (entry : UInt32 × Nat) : List UInt32 :=
  segmentWords entry.2 entry.1.toNat ((upper[entry.2]?.getD 0).toNat-entry.1.toNat)

def rowDecoded (order : Array Nat) (upper : Array UInt32) (entry : UInt32 × Nat) :
    List (Nat × Nat) :=
  segmentDecoded order entry.2 entry.1.toNat ((upper[entry.2]?.getD 0).toNat-entry.1.toNat)

/-- Tail-recursive validator and decoder for all rows. The only output-sized
    allocation is its decoded result accumulator. -/
def rows (order : Array Nat) (upper : Array UInt32) :
    List (UInt32 × Nat) → List UInt32 → List (Nat × Nat) → Option (List (Nat × Nat))
  | [], words, acc => if words.isEmpty then some acc.reverse else none
  | entry :: entries, words, acc =>
      match segment order entry.2 ((upper[entry.2]?.getD 0).toNat-entry.1.toNat)
          entry.1.toNat words acc with
      | none => none
      | some (rest,result) => rows order upper entries rest result

theorem rows_model (order : Array Nat) (upper : Array UInt32) (entries : List (UInt32 × Nat))
    (acc : List (Nat × Nat)) :
    rows order upper entries (entries.flatMap (rowWords upper)) acc =
      some (acc.reverse ++ entries.flatMap (rowDecoded order upper)) := by
  induction entries generalizing acc with
  | nil => simp [rows]
  | cons entry entries ih =>
    simp only [List.flatMap_cons, rowWords, rows, segment_model]
    rw [ih]
    simp [rowDecoded, List.reverse_append, List.append_assoc]

theorem rows_sound (order : Array Nat) (upper : Array UInt32) (entries : List (UInt32 × Nat))
    (words : List UInt32) (acc answer : List (Nat × Nat))
    (h : rows order upper entries words acc = some answer) :
    words = entries.flatMap (rowWords upper) ∧
      answer = acc.reverse ++ entries.flatMap (rowDecoded order upper) := by
  induction entries generalizing words acc with
  | nil =>
    cases words with
    | nil => simpa [rows] using h.symm
    | cons a words => simp [rows] at h
  | cons entry entries ih =>
    unfold rows at h
    cases hs : segment order entry.2 ((upper[entry.2]?.getD 0).toNat-entry.1.toNat)
        entry.1.toNat words acc with
    | none => simp [hs] at h
    | some result =>
      rcases result with ⟨rest,result⟩
      simp only [hs] at h
      rcases ih rest result h with ⟨hr,ha⟩
      rcases segment_sound order entry.2 _ entry.1.toNat words rest acc result hs with ⟨hw,hd⟩
      constructor
      · simpa [rowWords, List.flatMap_cons, hr] using hw
      · simpa [rowDecoded, List.flatMap_cons, hd, List.reverse_append,
          List.append_assoc] using ha

#print axioms segment_sound
#print axioms rows_sound
#print axioms rows_model

end L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin.Readback
