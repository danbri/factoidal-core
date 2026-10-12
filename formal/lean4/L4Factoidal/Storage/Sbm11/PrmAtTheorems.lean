/-
L4Factoidal.Storage.Sbm11.PrmAtTheorems — the query path's PRM1 decoder over
a `ByteArray` equals the decoder of the round-trip theorem (lemma L2 of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `get32At_spec`: the 4-byte field over a `ByteArray` and over its list.
* `decodePrmAt_eq`: `PrmAt.decodePrmAt b`, with its entries as a list, is
  `Block.decodePrm` of the bytes of `b`, on every input.

* `decodePrmAt_admitted`: so `decodePrm_admitted` (a decoded PRM1 is
  sorted, without overlap and contiguous) holds of what the query path
  reads, and `ScanTheorems.blocksFor_complete` applies to it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PrmAt
import L4Factoidal.Storage.Sbm11.BlockTheorems

namespace L4Factoidal.Storage.Sbm11.PrmAt

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length drop_bytesToList_cons
  drop_bytesToList_of_le)

private theorem get32_short (l : List UInt8) (h : l.length < 4) : get32 l = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

theorem get32At_spec (b : ByteArray) (i : Nat) :
    (get32At b i).map (fun r => (r.1, (bytesToList b).drop r.2)) = get32 ((bytesToList b).drop i) := by
  unfold get32At
  by_cases h : i + 4 ≤ b.size
  · rw [dif_pos h]
    rw [drop_bytesToList_cons b i (by omega), drop_bytesToList_cons b (i + 1) (by omega),
      drop_bytesToList_cons b (i + 2) (by omega), drop_bytesToList_cons b (i + 3) (by omega)]
    rfl
  · rw [dif_neg h, get32_short _ (by simp [bytesToList_length]; omega)]
    rfl

/-- In range, the 8-byte field reads the same value over both forms. -/
theorem get64At_in (b : ByteArray) (i : Nat) (h : i + 8 ≤ b.size) :
    ∃ v, get64At b i = some (v, i + 8) ∧
      get64 ((bytesToList b).drop i) = some (v, (bytesToList b).drop (i + 8)) := by
  have hs := get64At_spec b i
  unfold get64At at hs ⊢
  rw [dif_pos h] at hs ⊢
  exact ⟨_, rfl, hs.symm⟩

theorem get32At_in (b : ByteArray) (i : Nat) (h : i + 4 ≤ b.size) :
    ∃ v, get32At b i = some (v, i + 4) ∧
      get32 ((bytesToList b).drop i) = some (v, (bytesToList b).drop (i + 4)) := by
  have hs := get32At_spec b i
  unfold get32At at hs ⊢
  rw [dif_pos h] at hs ⊢
  exact ⟨_, rfl, hs.symm⟩

/-- An entry in range reads the same over both forms. -/
theorem entryAt_in (b : ByteArray) (i : Nat) (h : i + 92 ≤ b.size) :
    ∃ m, entryAt b i = some m ∧
      getEntry ((bytesToList b).drop i) = some (m, (bytesToList b).drop (i + 92)) := by
  obtain ⟨f0, a0, b0⟩ := get64At_in b i (by omega)
  obtain ⟨f1, a1, b1⟩ := get64At_in b (i + 8) (by omega)
  obtain ⟨f2, a2, b2⟩ := get64At_in b (i + 8 + 8) (by omega)
  obtain ⟨f3, a3, b3⟩ := get64At_in b (i + 8 + 8 + 8) (by omega)
  obtain ⟨l0, a4, b4⟩ := get64At_in b (i + 8 + 8 + 8 + 8) (by omega)
  obtain ⟨l1, a5, b5⟩ := get64At_in b (i + 8 + 8 + 8 + 8 + 8) (by omega)
  obtain ⟨l2, a6, b6⟩ := get64At_in b (i + 8 + 8 + 8 + 8 + 8 + 8) (by omega)
  obtain ⟨l3, a7, b7⟩ := get64At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8) (by omega)
  obtain ⟨rw, a8, b8⟩ := get32At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) (by omega)
  obtain ⟨off, a9, b9⟩ := get64At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4) (by omega)
  obtain ⟨n0, a10, b10⟩ := get32At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8) (by omega)
  obtain ⟨n1, a11, b11⟩ := get32At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4) (by omega)
  obtain ⟨n2, a12, b12⟩ := get32At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4 + 4) (by omega)
  obtain ⟨n3, a13, b13⟩ := get32At_in b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4 + 4 + 4) (by omega)
  refine ⟨{ first := ⟨f0, f1, f2, f3⟩, last := ⟨l0, l1, l2, l3⟩, rows := rw, offset := off,
            len0 := n0, len1 := n1, len2 := n2, len3 := n3 }, ?_, ?_⟩
  · simp only [entryAt, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, bind, Option.bind]
  · have e : i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4 + 4 + 4 + 4 = i + 92 := by omega
    rw [e] at b13
    simp only [getEntry, getRow, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, bind,
      Option.bind]

theorem entriesGo_eq (b : ByteArray) (count : Nat) (hsz : b.size = prmHeaderBytes + prmEntryBytes * count) :
    ∀ n k (acc : Array BlockMeta), k + n = count →
      (entriesGo b count (n + 1) k acc).map (fun a => (a.toList, ([] : List UInt8))) =
        getEntriesGo n ((bytesToList b).drop (prmHeaderBytes + prmEntryBytes * k)) acc.toList.reverse := by
  intro n
  induction n with
  | zero =>
    intro k acc hk
    simp only [Nat.add_zero] at hk
    subst hk
    simp only [entriesGo, Nat.le_refl, if_true, getEntriesGo, List.reverse_reverse, Option.map_some]
    rw [drop_bytesToList_of_le b _ (by omega)]
  | succ n ih =>
    intro k acc hk
    obtain ⟨m, ha, hg⟩ := entryAt_in b (prmHeaderBytes + prmEntryBytes * k)
      (by simp only [prmHeaderBytes, prmEntryBytes] at hsz ⊢; rw [hsz, ← hk]; rw [Nat.mul_add]; omega)
    rw [show entriesGo b count (n + 1 + 1) k acc =
        (if k ≥ count then some acc else
          match entryAt b (prmHeaderBytes + prmEntryBytes * k) with
          | some m => entriesGo b count (n + 1) (k + 1) (acc.push m)
          | none => none) from rfl]
    rw [if_neg (by omega), ha]
    simp only [getEntriesGo, hg]
    have e : prmHeaderBytes + prmEntryBytes * k + 92 = prmHeaderBytes + prmEntryBytes * (k + 1) := by
      simp only [prmHeaderBytes, prmEntryBytes]; omega
    rw [e, ih (k + 1) (acc.push m) (by omega)]
    simp

private theorem get64_rest_length (l r : List UInt8) (v : Nat) (h : get64 l = some (v, r)) :
    r.length + 8 = l.length := by
  match l, h with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest, h =>
    simp only [get64, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp

private theorem get32_rest_length (l r : List UInt8) (v : Nat) (h : get32 l = some (v, r)) :
    r.length + 4 = l.length := by
  match l, h with
  | _ :: _ :: _ :: _ :: rest, h =>
    simp only [get32, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp

theorem getRow_rest_length (l r : List UInt8) (x : Row) (h : getRow l = some (x, r)) :
    r.length + 32 = l.length := by
  simp only [getRow, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, r1⟩, h1, ⟨_, r2⟩, h2, ⟨_, r3⟩, h3, ⟨_, r4⟩, h4, hfin⟩ := h
  dsimp only at h2 h3 h4 hfin
  have := get64_rest_length _ _ _ h1
  have := get64_rest_length _ _ _ h2
  have := get64_rest_length _ _ _ h3
  have := get64_rest_length _ _ _ h4
  simp only [Option.some.injEq, Prod.mk.injEq] at hfin
  obtain ⟨_, rfl⟩ := hfin
  omega

theorem getEntry_rest_length (l r : List UInt8) (m : BlockMeta) (h : getEntry l = some (m, r)) :
    r.length + 92 = l.length := by
  simp only [getEntry, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨_, r1⟩, h1, ⟨_, r2⟩, h2, ⟨_, r3⟩, h3, ⟨_, r4⟩, h4, ⟨_, r5⟩, h5, ⟨_, r6⟩, h6,
    ⟨_, r7⟩, h7, ⟨_, r8⟩, h8, hfin⟩ := h
  dsimp only at h2 h3 h4 h5 h6 h7 h8 hfin
  have := getRow_rest_length _ _ _ h1
  have := getRow_rest_length _ _ _ h2
  have := get32_rest_length _ _ _ h3
  have := get64_rest_length _ _ _ h4
  have := get32_rest_length _ _ _ h5
  have := get32_rest_length _ _ _ h6
  have := get32_rest_length _ _ _ h7
  have := get32_rest_length _ _ _ h8
  simp only [Option.some.injEq, Prod.mk.injEq] at hfin
  obtain ⟨_, rfl⟩ := hfin
  omega

theorem getEntriesGo_length : ∀ (n : Nat) (l : List UInt8) (acc ms : List BlockMeta) (rest : List UInt8),
    getEntriesGo n l acc = some (ms, rest) → rest.length + 92 * n = l.length := by
  intro n
  induction n with
  | zero =>
    intro l acc ms rest h
    simp only [getEntriesGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp
  | succ n ih =>
    intro l acc ms rest h
    simp only [getEntriesGo] at h
    split at h
    · cases h
    · rename_i m r hm
      have h1 := getEntry_rest_length _ _ _ hm
      have h2 := ih _ _ _ _ h
      rw [Nat.mul_succ]
      omega

private theorem byte_get! (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

/-- The query path's PRM1 decoder equals `Block.decodePrm` on every input. -/
theorem decodePrmAt_eq (b : ByteArray) :
    (decodePrmAt b).map (fun r => (r.1, r.2.toList)) = decodePrm (bytesToList b) := by
  by_cases hs : b.size < prmHeaderBytes
  · -- too short: both refuse
    have hn : decodePrmAt b = none := by simp [decodePrmAt, hs]
    rw [hn]
    have hl : (bytesToList b).length < 22 := by
      rw [bytesToList_length]; simpa [prmHeaderBytes] using hs
    unfold decodePrm
    split
    · rename_i rest heq
      rw [heq] at hl
      cases h1 : get64 rest with
      | none => rfl
      | some p =>
        obtain ⟨c, r1⟩ := p
        have := get64_rest_length _ _ _ h1
        have h2 : get64 r1 = none := by
          match r1, this with
          | [], _ => rfl
          | [_], _ => rfl
          | [_, _], _ => rfl
          | [_, _, _], _ => rfl
          | [_, _, _, _], _ => rfl
          | [_, _, _, _, _], _ => rfl
          | [_, _, _, _, _, _], _ => rfl
          | [_, _, _, _, _, _, _], _ => rfl
          | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp at hl h; omega
        simp [h2]
    · rfl
  · have hs' : 22 ≤ b.size := by simpa [prmHeaderBytes] using hs
    have hL : bytesToList b = b[0] :: b[1] :: b[2] :: b[3] :: b[4] :: b[5] :: (bytesToList b).drop 6 := by
      have := drop_bytesToList_cons b 0 (by omega)
      rw [List.drop_zero] at this
      conv => lhs; rw [this]
      rw [drop_bytesToList_cons b 1 (by omega), drop_bytesToList_cons b 2 (by omega),
        drop_bytesToList_cons b 3 (by omega), drop_bytesToList_cons b 4 (by omega),
        drop_bytesToList_cons b 5 (by omega)]
    obtain ⟨count, hc1, hc2⟩ := get64At_in b 6 (by omega)
    obtain ⟨total, ht1, ht2⟩ := get64At_in b 14 (by omega)
    have g0 := byte_get! b 0 (by omega)
    have g1 := byte_get! b 1 (by omega)
    have g2 := byte_get! b 2 (by omega)
    have g3 := byte_get! b 3 (by omega)
    have g4 := byte_get! b 4 (by omega)
    have g5 := byte_get! b 5 (by omega)
    by_cases hmag : b[0] = 80 ∧ b[1] = 82 ∧ b[2] = 77 ∧ b[3] = 49 ∧ b[4] = 1
    · obtain ⟨m0, m1, m2, m3, m4⟩ := hmag
      rw [hL, m0, m1, m2, m3, m4]
      simp only [decodePrm]
      rw [hc2]
      simp only [show 6 + 8 = 14 from rfl]
      rw [ht2]
      simp only [show 14 + 8 = 22 from rfl]
      by_cases hsz : b.size = prmHeaderBytes + prmEntryBytes * count
      · have he := entriesGo_eq b count hsz count 0 (Array.mkEmpty count) (by omega)
        simp only [prmHeaderBytes, Nat.mul_zero, Nat.add_zero] at he
        have hme : (Array.mkEmpty count : Array BlockMeta).toList.reverse = [] := rfl
        rw [hme] at he
        have hmk : (Array.mkEmpty count : Array BlockMeta) = #[] := rfl
        rw [hmk] at he
        rw [← he]
        have hdec : decodePrmAt b = (entriesGo b count (count + 1) 0 #[]).bind (fun ms =>
            if prmAdmitted b[5].toNat ms.toList && total == rowSum ms.toList then some (b[5].toNat, ms)
            else none) := by
          have hs2 : ¬ (prmHeaderBytes + prmEntryBytes * count < prmHeaderBytes) := by omega
          simp [decodePrmAt, hs2, g0, g1, g2, g3, g4, g5, m0, m1, m2, m3, m4, hc1, ht1, hsz]
        rw [hdec]
        cases entriesGo b count (count + 1) 0 #[] with
        | none => rfl
        | some ms =>
          simp only [Option.bind_some, Option.map_some]
          by_cases hA : (prmAdmitted b[5].toNat ms.toList && total == rowSum ms.toList) = true
          · simp [hA]
          · simp only [Bool.not_eq_true] at hA
            simp [hA]
      · -- the size does not match the entry count: both refuse
        have hn : decodePrmAt b = none := by
          simp only [decodePrmAt, hs, if_false, g0, g1, g2, g3, g4, g5, m0, m1, m2, m3, m4, hc1, ht1]
          simp [hsz]
        rw [hn]
        cases hg : getEntriesGo count ((bytesToList b).drop 22) [] with
        | none => simp
        | some p =>
          obtain ⟨ms, rest⟩ := p
          cases rest with
          | cons _ _ => simp
          | nil =>
            exfalso
            apply hsz
            have hlen := getEntriesGo_length count ((bytesToList b).drop 22) [] ms [] hg
            simp only [List.length_drop, bytesToList_length, List.length_nil] at hlen
            show b.size = 22 + 92 * count
            omega
    · have hn : decodePrmAt b = none := by
        simp only [decodePrmAt, hs, if_false, g0, g1, g2, g3, g4, g5]
        have : (b[0] == 80 && b[1] == 82 && b[2] == 77 && b[3] == 49 && b[4] == 1) = false := by
          rw [Bool.eq_false_iff]
          intro hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          exact hmag ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
        simp [this]
      rw [hn, hL]
      unfold decodePrm
      split
      · rename_i heq
        simp only [List.cons.injEq] at heq
        exact absurd ⟨heq.1, heq.2.1, heq.2.2.1, heq.2.2.2.1, heq.2.2.2.2.1⟩ hmag
      · rfl

/-- What the query path reads from a PRM1 file is admitted. -/
theorem decodePrmAt_admitted (b : ByteArray) (p : Nat) (ms : Array BlockMeta)
    (h : decodePrmAt b = some (p, ms)) : prmAdmitted p ms.toList = true ∧ p < 4 := by
  have he := decodePrmAt_eq b
  rw [h] at he
  exact decodePrm_admitted _ _ _ he.symm

end L4Factoidal.Storage.Sbm11.PrmAt
