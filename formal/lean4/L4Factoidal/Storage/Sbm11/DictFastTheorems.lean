/-
L4Factoidal.Storage.Sbm11.DictFastTheorems — the byte-array page decoder
equals the list page decoder.

`Dict.decodePageAt` is what the lookups run: it reads a `ByteArray` by
position and builds one `ByteArray` per key, no list. `Dict.decodePage` is
the decoder the round trip `decodeDict_encodeDict?` is stated over. This
module proves them equal on every input:

* `getSmallAt_spec`: one SMALL field.
* `decodeEntriesAt_spec`: the front-coded entries.
* `decodePageAt_eq`: `(decodePageAt b i).map view = decodePage (drop i)`,
  where `view` turns the keys into lists and the end position into the
  rest of the list.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DictTheorems

namespace L4Factoidal.Storage.Sbm11.Dict

open L4Factoidal.Storage (readU32LE)

theorem bytesToList_length (b : ByteArray) : (bytesToList b).length = b.size := by
  simp only [bytesToList, Array.length_toList]; rfl

theorem drop_bytesToList_cons (b : ByteArray) (i : Nat) (h : i < b.size) :
    (bytesToList b).drop i = b[i] :: (bytesToList b).drop (i + 1) := by
  have hl : i < (bytesToList b).length := by rw [bytesToList_length]; exact h
  rw [List.drop_eq_getElem_cons hl]
  simp [bytesToList, ByteArray.getElem_eq_getElem_data]

theorem drop_bytesToList_of_le (b : ByteArray) (i : Nat) (h : b.size ≤ i) :
    (bytesToList b).drop i = [] := by
  apply List.drop_of_length_le
  rw [bytesToList_length]; exact h

theorem bytesToList_extract (b : ByteArray) (a c : Nat) :
    bytesToList (b.extract a c) = ((bytesToList b).drop a).take (c - a) := by
  simp [bytesToList, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem bytesToList_append (x y : ByteArray) :
    bytesToList (x ++ y) = bytesToList x ++ bytesToList y := by
  simp [bytesToList, ByteArray.data_append]

theorem readU32LE_short (l : List UInt8) (h : l.length < 4) : readU32LE l 0 = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

theorem getSmallAt_spec (b : ByteArray) (i : Nat) :
    (getSmallAt b i).map (fun r => (r.1, (bytesToList b).drop r.2)) =
      getSmall ((bytesToList b).drop i) := by
  unfold getSmallAt
  by_cases hi : i < b.size
  · rw [dif_pos hi, drop_bytesToList_cons b i hi]
    by_cases hx : b[i].toNat < 255
    · rw [if_pos hx]; simp [getSmall, hx]
    · rw [if_neg hx]
      by_cases h4 : i + 4 < b.size
      · rw [dif_pos h4]
        have e : (bytesToList b).drop (i + 1) =
            b[i + 1] :: b[i + 2] :: b[i + 3] :: b[i + 4] :: (bytesToList b).drop (i + 5) := by
          rw [drop_bytesToList_cons b (i + 1) (by omega), drop_bytesToList_cons b (i + 2) (by omega),
            drop_bytesToList_cons b (i + 3) (by omega), drop_bytesToList_cons b (i + 4) (by omega)]
        simp only [getSmall, hx, if_false, e]
        simp [readU32LE]
      · rw [dif_neg h4]
        simp only [getSmall, hx, if_false]
        rw [readU32LE_short _ (by simp [bytesToList_length]; omega)]
        rfl
  · rw [dif_neg hi, drop_bytesToList_of_le b i (by omega)]
    rfl

theorem getSmallAt_le (b : ByteArray) (i v j : Nat) (h : getSmallAt b i = some (v, j)) :
    j ≤ b.size := by
  unfold getSmallAt at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
        · cases h
      · cases h
  · cases h

private theorem take_length_beq (l : List UInt8) (len : Nat) :
    (((l.take len).length == len) = true) ↔ len ≤ l.length := by
  simp only [beq_iff_eq, List.length_take]
  omega

theorem decodeEntriesAt_spec (b : ByteArray) (n : Nat) :
    ∀ (prev : ByteArray) (acc : Array ByteArray) (i : Nat),
      (decodeEntriesAt b n prev acc i).map
          (fun r => (r.1.toList.map bytesToList, (bytesToList b).drop r.2)) =
        decodeEntriesGo n (bytesToList prev) (acc.toList.map bytesToList).reverse
          ((bytesToList b).drop i) := by
  induction n with
  | zero => intro prev acc i; simp [decodeEntriesAt, decodeEntriesGo]
  | succ n ih =>
    intro prev acc i
    have hs1 := getSmallAt_spec b i
    simp only [decodeEntriesAt, decodeEntriesGo]
    cases h1 : getSmallAt b i with
    | none =>
      rw [h1] at hs1
      rw [← hs1]
      rfl
    | some p1 =>
      obtain ⟨s, i1⟩ := p1
      rw [h1] at hs1
      rw [← hs1]
      dsimp only [Option.map_some]
      have hs2 := getSmallAt_spec b i1
      cases h2 : getSmallAt b i1 with
      | none =>
        rw [h2] at hs2
        rw [← hs2]
        rfl
      | some p2 =>
        obtain ⟨len, i2⟩ := p2
        rw [h2] at hs2
        rw [← hs2]
        dsimp only [Option.map_some]
        have hi2 := getSmallAt_le b i1 len i2 h2
        have hlen : ((bytesToList b).drop i2).length = b.size - i2 := by
          simp [bytesToList_length]
        by_cases hfit : i2 + len ≤ b.size
        · rw [if_pos hfit, if_pos ((take_length_beq _ _).mpr (by omega))]
          rw [ih]
          have hk : bytesToList (prev.extract 0 s ++ b.extract i2 (i2 + len)) =
              (bytesToList prev).take s ++ ((bytesToList b).drop i2).take len := by
            rw [bytesToList_append, bytesToList_extract, bytesToList_extract]
            simp
          rw [hk, List.drop_drop]
          simp [Array.toList_push, hk]
        · rw [if_neg hfit]
          have hno : ¬ (((((bytesToList b).drop i2).take len).length == len) = true) := by
            rw [take_length_beq]; omega
          rw [if_neg hno]
          rfl

/-- The byte-array page decoder equals the list page decoder. -/
theorem decodePageAt_eq (b : ByteArray) (i : Nat) :
    (decodePageAt b i).map (fun r => (r.1.toList.map bytesToList, (bytesToList b).drop r.2)) =
      decodePage ((bytesToList b).drop i) := by
  have hs1 := getSmallAt_spec b i
  unfold decodePageAt decodePage
  cases h1 : getSmallAt b i with
  | none =>
    rw [h1] at hs1
    rw [← hs1]
    rfl
  | some p1 =>
    obtain ⟨c, i1⟩ := p1
    rw [h1] at hs1
    rw [← hs1]
    dsimp only [Option.map_some]
    by_cases hc : (c == 0) = true
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc]
      have hs2 := getSmallAt_spec b i1
      cases h2 : getSmallAt b i1 with
      | none =>
        rw [h2] at hs2
        rw [← hs2]
        rfl
      | some p2 =>
        obtain ⟨len, i2⟩ := p2
        rw [h2] at hs2
        rw [← hs2]
        dsimp only [Option.map_some]
        have hi2 := getSmallAt_le b i1 len i2 h2
        have hlen : ((bytesToList b).drop i2).length = b.size - i2 := by
          simp [bytesToList_length]
        by_cases hfit : i2 + len ≤ b.size
        · rw [if_pos hfit, if_pos ((take_length_beq _ _).mpr (by omega))]
          rw [decodeEntriesAt_spec, List.drop_drop]
          simp [bytesToList_extract]
        · rw [if_neg hfit]
          have hno : ¬ (((((bytesToList b).drop i2).take len).length == len) = true) := by
            rw [take_length_beq]; omega
          rw [if_neg hno]
          rfl

/-- What `pageM` accepts: a page that decodes to its end. Then its keys are
    exactly the keys `decodePage` reads from the same bytes. -/
theorem decodePageAt_whole (b : ByteArray) (ks : Array ByteArray)
    (h : decodePageAt b 0 = some (ks, b.size)) :
    decodePage (bytesToList b) = some (ks.toList.map bytesToList, []) := by
  have e := decodePageAt_eq b 0
  rw [h] at e
  simp only [Option.map_some, List.drop_zero] at e
  rw [← e, drop_bytesToList_of_le b b.size (Nat.le_refl _)]

end L4Factoidal.Storage.Sbm11.Dict
