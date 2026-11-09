/-
L4Factoidal.WHATWG.Encoding.SingleByteTheorems — the single-byte encodings of the
Encoding Standard (section 9) round-trip where their index is a bijection.

Specification: Encoding Standard, WHATWG, commit be17ac5c (2026-10-19): section 9.1.1
"single-byte decoder", section 9.1.2 "single-byte encoder", section 5 "index pointer"
(the FIRST pointer of a code point, `Core.reverseIndex`).

Theorems:

  * `reverseIndex_getElem?`: the reverse index answers, for a code point, the first
    pointer whose entry is that code point (the fold of `reverseIndex` is the search of
    the pointers in increasing order).
  * `singleByte_roundTrip`: for a byte `b` ≥ 0x80 whose pointer `b − 0x80` has a code
    point `cp` above U+007F that no earlier pointer has, the single-byte decoder gives
    `cp` and the single-byte encoder (over the reverse of the same index) gives `b`
    back. Every used pointer of an index whose used entries are distinct and above
    U+007F meets the condition; the `#guard`s below check that each of the 28
    single-byte indexes of section 9 is such a bijection between its used pointers and
    their code points (some pointers are unused: the decoder's error bytes).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.Encoding

/-- The fold of inserts that `reverseIndex` makes, over any list of steps: the last step
that inserts `v` decides, and a map that no step changes answers as before. -/
theorem foldl_skip_getElem? (L : List Nat) (skip : Nat → Bool) (f : Nat → UInt32) (g : Nat → Nat)
    (m : Std.HashMap UInt32 Nat) (v : UInt32) :
    (L.foldl (fun m i => if skip i then m else m.insert (f i) (g i)) m)[v]? =
      ((L.reverse.find? (fun i => !skip i && f i == v)).map g).or m[v]? := by
  induction L generalizing m with
  | nil => simp
  | cons i L ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, List.find?_append]
    cases h : L.reverse.find? (fun i => !skip i && f i == v) with
    | some j => simp
    | none =>
      cases hs : skip i
      · by_cases hv : f i = v
        · simp [hs, hv, Std.HashMap.getElem?_insert]
        · have hv' : (f i == v) = false := by simpa using hv
          simp [hs, hv', Std.HashMap.getElem?_insert]
      · simp [hs]

/-- The search over the steps `n − 1, …, 0` meets step `n − 1 − p` first when no step
before it (a pointer below `p`) matches. -/
theorem find?_reverse_range (n p : Nat) (hp : p < n) (P : Nat → Bool)
    (hP : P (n - 1 - p) = true) (hbefore : ∀ j, j < p → P (n - 1 - j) = false) :
    (List.range n).reverse.find? P = some (n - 1 - p) := by
  have hl : p < (List.range n).reverse.length := by simp; omega
  have hget : (List.range n).reverse[p] = n - 1 - p := by
    rw [List.getElem_reverse]; simp
  rw [List.find?_eq_some_iff_append]
  refine ⟨hP, (List.range n).reverse.take p, (List.range n).reverse.drop (p + 1), ?_, ?_⟩
  · rw [← hget, ← List.drop_eq_getElem_cons hl, List.take_append_drop]
  · intro a ha
    rw [List.mem_iff_getElem] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    have hj' : j < p := by simp at hj; omega
    rw [List.getElem_take, List.getElem_reverse]
    simp only [List.getElem_range, List.length_range]
    rw [hbefore j hj']
    rfl

/-- A pointer `p` that no earlier pointer shares a code point with is the index pointer
of its code point. -/
theorem reverseIndex_getElem? (idx : Array UInt32) (keep : Nat → Bool) (p : Nat) (hp : p < idx.size)
    (hnull : idx[p]! ≠ nullCp) (hk : keep p = true)
    (hfirst : ∀ q, q < p → idx[q]! ≠ idx[p]!) :
    (reverseIndex idx keep)[idx[p]!]? = some p := by
  unfold reverseIndex
  simp only []
  rw [foldl_skip_getElem? (List.range idx.size) (fun i => idx[idx.size - 1 - i]! == nullCp || !keep (idx.size - 1 - i))
    (fun i => idx[idx.size - 1 - i]!) (fun i => idx.size - 1 - i)]
  have e : idx.size - 1 - (idx.size - 1 - p) = p := by omega
  rw [find?_reverse_range idx.size p hp]
  · simp [e]
  · simp [e, hnull, hk]
  · intro j hj
    have e2 : idx.size - 1 - (idx.size - 1 - j) = j := by omega
    simp [e2, hfirst j hj]

/-- The single-byte round trip for one byte. -/
theorem singleByte_roundTrip (idx : Array UInt32) (b : UInt8) (hb : 0x80 ≤ b.toNat)
    (hp : b.toNat - 0x80 < idx.size) (hnull : idx[b.toNat - 0x80]! ≠ nullCp)
    (hhi : 0x7F < (idx[b.toNat - 0x80]!).toNat)
    (hfirst : ∀ q, q < b.toNat - 0x80 → idx[q]! ≠ idx[b.toNat - 0x80]!) :
    ((Decoder.singleByte idx).handle (some b)).result = .items [idx[b.toNat - 0x80]!] ∧
    ((Encoder.singleByte (reverseIndex idx (fun _ => true))).handle (some idx[b.toNat - 0x80]!)).result =
      .bytes [b] := by
  have h7 : (0x7F : UInt8).toNat = 127 := rfl
  have hna : isAscii b = false := by
    unfold isAscii
    apply decide_eq_false
    intro h
    have := UInt8.le_iff_toNat_le.mp h
    omega
  have hrev := reverseIndex_getElem? idx (fun _ => true) (b.toNat - 0x80) hp hnull rfl hfirst
  generalize hq : b.toNat - 0x80 = p at hp hnull hhi hfirst hrev ⊢
  generalize hc : idx[p]! = cp at hnull hhi hrev ⊢
  have h1 : idx[p]? = some cp := by
    rw [← hc, Array.getElem?_eq_getElem hp, getElem!_pos idx p hp]
  have hcp : indexCodePoint idx p = some cp := by
    unfold indexCodePoint
    rw [h1]
    have hne : (cp == nullCp) = false := by simpa using hnull
    simp only [hne, Bool.false_eq_true, if_false]
  refine ⟨?_, ?_⟩
  · have hq' : b.toNat - 128 = p := hq
    simp only [Decoder.handle, hna, Bool.false_eq_true, if_false, hq', hcp]
  · have h7' : (0x7F : UInt32).toNat = 127 := rfl
    have hle : ¬ (cp ≤ 0x7F) := by
      intro h
      have := UInt32.le_iff_toNat_le.mp h
      omega
    have hb' : p + 0x80 = b.toNat := by omega
    simp only [Encoder.handle, hle, if_false, hrev, hb', Nat.toUInt8_eq, UInt8.ofNat_toNat]

/-! ## The indexes of section 9 are bijections on their used pointers -/

/-- Every used entry of the index is above U+007F and no two used entries are equal. -/
def isBijectionAbove7F (idx : Array UInt32) : Bool :=
  let used := idx.toList.filter (· != nullCp)
  used.all (fun c => c.toNat > 0x7F) && used.eraseDups.length == used.length

#guard Encoding.all.all fun e => !e.isSingleByte || isBijectionAbove7F (parseIndex (singleByteIndexText e))
#guard (Encoding.all.filter Encoding.isSingleByte).length == 28

end L4Factoidal.WHATWG.Encoding
