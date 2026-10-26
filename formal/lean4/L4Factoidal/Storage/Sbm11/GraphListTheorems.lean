/-
L4Factoidal.Storage.Sbm11.GraphListTheorems — the GNL1 codec
(`Storage/Sbm11/GraphList.lean`): the round trip, one byte form for each list,
and the byte-array decoder.

* `decode_encode?`: `encode? xs = some bs → decode bs = some xs`. The only
  hypothesis is the encoder's admission.
* `encode?_decode`: `decode bs = some xs → encode? xs = some bs`: the decoder
  returns only lists the encoder admits, and only from the bytes the encoder
  writes for them. With `decode_encode?`, encoder admission equals decoder
  admission (skill `shardborough-storage`, format rule 1), and a list has one
  byte form.
* `admitted_of_decode`: a list that decodes is admitted.
* `decodeAt_eq`: the runtime decoder over a `ByteArray` returns the list that
  `decode` returns, on every input.

No hypothesis states a conclusion. No `sorry`, no user `axiom`, no
`native_decide`, no `partial`. `#print axioms` at the end of the file.
-/
import L4Factoidal.Storage.Sbm11.GraphList
import L4Factoidal.Storage.Sbm11.ColumnTheorems

namespace L4Factoidal.Storage.Sbm11.GraphList

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Column (put64 get64 rawBytes getRawGo get64At get64_put64 getRawGo_rawBytes
  get64At_spec)
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length drop_bytesToList_cons
  drop_bytesToList_of_le)

/-! ## Facts about the parts -/

theorem idAdmitted_lt (x : Nat) (h : idAdmitted x = true) : x < two64 := by
  simp only [idAdmitted, Bool.or_eq_true, beq_iff_eq, tagBnode, tagIri] at h
  have h60 : two60 = 1152921504606846976 := rfl
  have h64 : two64 = 18446744073709551616 := rfl
  rcases h with h | h <;> (rw [h60] at h; rw [h64]; omega)

private theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8]

/-- A `get64` that succeeds read the bytes `put64` writes for its value. -/
theorem put64_get64 (bs r : List UInt8) (v : Nat) (h : get64 bs = some (v, r)) :
    bs = put64 v ++ r := by
  match bs, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, h =>
    simp only [get64, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l0 := b0.toNat_lt
    have l1 := b1.toNat_lt
    have l2 := b2.toNat_lt
    have l3 := b3.toNat_lt
    have l4 := b4.toNat_lt
    have l5 := b5.toNat_lt
    have l6 := b6.toNat_lt
    have l7 := b7.toNat_lt
    simp only [put64, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (apply UInt8.toNat_inj.mp; rw [toNat_toUInt8]; omega)

/-- `getRawGo` puts the ids it reads after the reversed accumulator. -/
theorem getRawGo_acc : ∀ (n : Nat) (bs : List UInt8) (acc : List Nat),
    getRawGo n bs acc = (getRawGo n bs []).map (fun r => (acc.reverse ++ r.1, r.2)) := by
  intro n
  induction n with
  | zero => intro bs acc; simp [getRawGo]
  | succ n ih =>
    intro bs acc
    simp only [getRawGo]
    cases get64 bs with
    | none => rfl
    | some p =>
      obtain ⟨v, rest⟩ := p
      dsimp only
      rw [ih rest (v :: acc), ih rest [v]]
      cases getRawGo n rest [] with
      | none => rfl
      | some q => simp

/-- What `getRawGo` read from the empty accumulator: `n` ids, written in front
    of what is left by `rawBytes`. -/
theorem getRawGo_canon : ∀ (n : Nat) (bs r : List UInt8) (xs : List Nat),
    getRawGo n bs [] = some (xs, r) → xs.length = n ∧ bs = rawBytes xs ++ r := by
  intro n
  induction n with
  | zero =>
    intro bs r xs h
    simp only [getRawGo, List.reverse_nil, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [rawBytes]
  | succ n ih =>
    intro bs r xs h
    simp only [getRawGo] at h
    cases hg : get64 bs with
    | none => rw [hg] at h; cases h
    | some p =>
      obtain ⟨v, rest⟩ := p
      rw [hg] at h
      dsimp only at h
      rw [getRawGo_acc] at h
      cases hr : getRawGo n rest [] with
      | none => rw [hr] at h; cases h
      | some q =>
        obtain ⟨ys, r'⟩ := q
        rw [hr] at h
        simp only [Option.map_some, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.singleton_append, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hx, hr'⟩ := h
        subst hx hr'
        obtain ⟨hl, hb⟩ := ih rest r' ys hr
        refine ⟨by simp [hl], ?_⟩
        rw [put64_get64 bs rest v hg, hb]
        simp [rawBytes, List.append_assoc]

theorem getRawGo_length : ∀ (n : Nat) (bs r : List UInt8) (xs : List Nat),
    getRawGo n bs [] = some (xs, r) → xs.length = n := by
  intro n
  induction n with
  | zero =>
    intro bs r xs h
    simp only [getRawGo, List.reverse_nil, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | succ n ih =>
    intro bs r xs h
    simp only [getRawGo] at h
    cases hg : get64 bs with
    | none => rw [hg] at h; cases h
    | some p =>
      obtain ⟨v, rest⟩ := p
      rw [hg] at h
      dsimp only at h
      rw [getRawGo_acc] at h
      cases hr : getRawGo n rest [] with
      | none => rw [hr] at h; cases h
      | some q =>
        obtain ⟨ys, r'⟩ := q
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        simp [ih rest r' ys hr]

/-! ## The round trip -/

theorem admitted_parts (xs : List Nat) (h : admitted xs = true) :
    xs ≠ [] ∧ xs.length < two64 ∧ (∀ x ∈ xs, idAdmitted x = true) ∧ increasing xs = true := by
  simp only [admitted, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- `decode` of a list of at least four bytes. -/
theorem decode_cons (m0 m1 m2 m3 : UInt8) (rest : List UInt8) :
    decode (m0 :: m1 :: m2 :: m3 :: rest) =
      if [m0, m1, m2, m3] = magic then
        match get64 rest with
        | none => none
        | some (n, r1) =>
          match getRawGo n r1 [] with
          | some (xs, []) => if admitted xs then some xs else none
          | _ => none
      else none := rfl

/-- The round trip. The only hypothesis is the encoder's admission. -/
theorem decode_encode? (xs : List Nat) (bs : List UInt8) (h : encode? xs = some bs) :
    decode bs = some xs := by
  unfold encode? at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, hlen, hids, _⟩ := admitted_parts xs hadm
    have hlt : ∀ x ∈ xs, x < two64 := fun x hx => idAdmitted_lt x (hids x hx)
    have hraw := getRawGo_rawBytes xs [] [] hlt
    simp only [List.reverse_nil, List.nil_append, List.append_nil] at hraw
    show decode (71 :: 78 :: 76 :: 49 :: (put64 xs.length ++ rawBytes xs)) = some xs
    rw [decode_cons, if_pos (show ([71, 78, 76, 49] : List UInt8) = magic from rfl),
      get64_put64 _ hlen]
    simp only [hraw, hadm, if_true]
  · cases h

/-- A list that decodes is admitted. -/
theorem admitted_of_decode (bs : List UInt8) (xs : List Nat) (h : decode bs = some xs) :
    admitted xs = true := by
  unfold decode at h
  repeat' split at h
  all_goals (cases h <;> first | assumption | rfl)

/-- One byte form for each list: the decoder returns only lists the encoder
    admits, from the bytes the encoder writes for them. -/
theorem encode?_decode (bs : List UInt8) (xs : List Nat) (h : decode bs = some xs) :
    encode? xs = some bs := by
  have hadm := admitted_of_decode bs xs h
  match bs, h with
  | m0 :: m1 :: m2 :: m3 :: rest, h =>
    rw [decode_cons] at h
    split at h
    · rename_i hm
      split at h
      · cases h
      · rename_i n r1 hg
        split at h
        · rename_i ys hr
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            obtain ⟨hl, hb⟩ := getRawGo_canon n r1 [] ys hr
            have hrest := put64_get64 rest r1 n hg
            simp only [List.append_nil] at hb
            unfold encode?
            rw [if_pos hadm, hrest, hb, hl]
            have hm' : magic = [m0, m1, m2, m3] := hm.symm
            simp [hm']
          · cases h
        · cases h
    · cases h

/-! ## The byte-array decoder -/

/-- The result of `idsAtGo`, as a function of what `getRawGo` reads. -/
def idsSpec (prev : Option Nat) (acc : Array Nat) : Option (List Nat × List UInt8) → Option (List Nat)
  | some (xs, []) => if xs.all idAdmitted && chainFrom prev xs then some (acc.toList ++ xs) else none
  | _ => none

theorem idsSpec_some_nil (prev : Option Nat) (acc : Array Nat) (xs : List Nat) :
    idsSpec prev acc (some (xs, [])) =
      if (xs.all idAdmitted && chainFrom prev xs) = true then some (acc.toList ++ xs) else none := rfl

theorem idsAtGo_spec (b : ByteArray) : ∀ (n i : Nat) (prev : Option Nat) (acc : Array Nat),
    (idsAtGo b n i prev acc).map Array.toList =
      idsSpec prev acc (getRawGo n ((bytesToList b).drop i) []) := by
  intro n
  induction n with
  | zero =>
    intro i prev acc
    simp only [idsAtGo, getRawGo, List.reverse_nil]
    by_cases h : b.size ≤ i
    · rw [if_pos h, drop_bytesToList_of_le b i h]
      simp [idsSpec, chainFrom]
    · rw [if_neg h]
      have hne : (bytesToList b).drop i ≠ [] := by
        intro he
        have := congrArg List.length he
        simp [bytesToList_length] at this
        omega
      cases hd : (bytesToList b).drop i with
      | nil => exact absurd hd hne
      | cons x xs => rfl
  | succ n ih =>
    intro i prev acc
    have hs := get64At_spec b i
    cases h1 : get64At b i with
    | none =>
      rw [h1] at hs
      have hg : get64 ((bytesToList b).drop i) = none := hs.symm
      simp only [idsAtGo, h1, getRawGo, hg]
      rfl
    | some p =>
      obtain ⟨v, j⟩ := p
      rw [h1] at hs
      simp only [Option.map_some] at hs
      have hrw : getRawGo (n + 1) ((bytesToList b).drop i) [] = getRawGo n ((bytesToList b).drop j) [v] := by
        simp only [getRawGo, ← hs]
      have hids : idsAtGo b (n + 1) i prev acc =
          if (idAdmitted v && after prev v) = true then idsAtGo b n j (some v) (acc.push v) else none := by
        simp only [idsAtGo, h1]
      rw [hrw, getRawGo_acc, hids]
      have hih := ih j (some v) (acc.push v)
      by_cases hc : (idAdmitted v && after prev v) = true
      · rw [if_pos hc, hih]
        cases getRawGo n ((bytesToList b).drop j) [] with
        | none => rfl
        | some q =>
          obtain ⟨xs, r⟩ := q
          cases r with
          | cons y ys => rfl
          | nil =>
            simp only [Option.map_some, List.reverse_cons, List.reverse_nil, List.nil_append,
              List.singleton_append, idsSpec, chainFrom, List.all_cons]
            simp only [Bool.and_eq_true] at hc
            simp [hc.1, hc.2, Array.toList_push]
      · rw [if_neg hc]
        cases getRawGo n ((bytesToList b).drop j) [] with
        | none => rfl
        | some q =>
          obtain ⟨xs, r⟩ := q
          cases r with
          | cons y ys => rfl
          | nil =>
            have hf : ((v :: xs).all idAdmitted && chainFrom prev (v :: xs)) = false := by
              simp only [List.all_cons, chainFrom]
              cases h2 : idAdmitted v <;> cases h3 : after prev v <;> simp_all
            show Option.map Array.toList none = idsSpec prev acc (some ([v].reverse ++ xs, []))
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
            rw [idsSpec_some_nil, hf]
            rfl

theorem get64At_lt' (b : ByteArray) (i v j : Nat) (h : get64At b i = some (v, j)) : v < two64 := by
  unfold get64At at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rename_i hb
    have := (b[i]'(by omega)).toNat_lt
    have := (b[i+1]'(by omega)).toNat_lt
    have := (b[i+2]'(by omega)).toNat_lt
    have := (b[i+3]'(by omega)).toNat_lt
    have := (b[i+4]'(by omega)).toNat_lt
    have := (b[i+5]'(by omega)).toNat_lt
    have := (b[i+6]'(by omega)).toNat_lt
    have := (b[i+7]'(by omega)).toNat_lt
    simp only [two64]
    omega
  · cases h

/-- The runtime decoder returns the list that `decode` returns, on every input. -/
theorem decodeAt_eq (b : ByteArray) : (decodeAt b).map Array.toList = decode (bytesToList b) := by
  by_cases hsz : 4 ≤ b.size
  · have hl : bytesToList b = b[0] :: b[1] :: b[2] :: b[3] :: (bytesToList b).drop 4 := by
      have h0 := drop_bytesToList_cons b 0 (by omega)
      have h1 := drop_bytesToList_cons b 1 (by omega)
      have h2 := drop_bytesToList_cons b 2 (by omega)
      have h3 := drop_bytesToList_cons b 3 (by omega)
      simp only [List.drop_zero, Nat.reduceAdd] at h0 h1 h2 h3
      conv => lhs; rw [h0, h1, h2, h3]
    have hg : ∀ k (hk : k < b.size), b.get! k = b[k] := by
      intro k hk
      simp [ByteArray.get!, hk]
      rfl
    have hmagic : magicAt b = decide ([b[0], b[1], b[2], b[3]] = magic) := by
      simp only [magicAt, hg 0 (by omega), hg 1 (by omega), hg 2 (by omega), hg 3 (by omega), magic,
        decide_eq_true hsz, Bool.true_and]
      by_cases a0 : b[0] = 71 <;> by_cases a1 : b[1] = 78 <;> by_cases a2 : b[2] = 76 <;>
        by_cases a3 : b[3] = 49 <;> simp [a0, a1, a2, a3]
    rw [hl, decode_cons]
    unfold decodeAt
    rw [hmagic]
    by_cases hm : [b[0], b[1], b[2], b[3]] = magic
    · rw [if_pos (decide_eq_true hm), if_pos hm]
      have hs := get64At_spec b 4
      cases h1 : get64At b 4 with
      | none =>
        rw [h1] at hs
        have hg4 : get64 ((bytesToList b).drop 4) = none := hs.symm
        rw [hg4]; rfl
      | some p =>
        obtain ⟨n, i⟩ := p
        rw [h1] at hs
        simp only [Option.map_some] at hs
        rw [← hs]
        dsimp only
        by_cases hn : n = 0
        · subst hn
          simp only [beq_self_eq_true, if_true, Option.map_none, getRawGo, List.reverse_nil]
          cases hd : (bytesToList b).drop i with
          | nil => simp [admitted]
          | cons y ys => rfl
        · have hn' : (n == 0) = false := by simpa using hn
          rw [if_neg (by simp [hn']), idsAtGo_spec]
          cases hr : getRawGo n ((bytesToList b).drop i) [] with
          | none => rfl
          | some q =>
            obtain ⟨xs, r⟩ := q
            cases r with
            | cons y ys => rfl
            | nil =>
              rw [idsSpec_some_nil]
              have hlen := getRawGo_length n _ [] xs hr
              have hnlt : n < two64 := get64At_lt' b 4 n i h1
              have hne : xs ≠ [] := by
                intro he; subst he; simp at hlen; omega
              have hadm : admitted xs = (xs.all idAdmitted && chainFrom none xs) := by
                simp only [admitted, increasing]
                have h1' : (!xs.isEmpty) = true := by simpa using hne
                have h2' : decide (xs.length < two64) = true := by simp [hlen, hnlt]
                rw [h1', h2']
                simp
              show _ = (if admitted xs = true then some xs else none)
              rw [hadm]
              split <;> simp
    · rw [if_neg (by simpa using hm), if_neg hm]
      rfl
  · have hmag : magicAt b = false := by simp [magicAt, hsz]
    unfold decodeAt
    rw [hmag]
    simp only [Bool.false_eq_true, if_false, Option.map_none]
    unfold decode
    split
    · rename_i m0 m1 m2 m3 rest heq
      have := congrArg List.length heq
      simp [bytesToList_length] at this
      omega
    · rfl

end L4Factoidal.Storage.Sbm11.GraphList

#print axioms L4Factoidal.Storage.Sbm11.GraphList.decode_encode?
#print axioms L4Factoidal.Storage.Sbm11.GraphList.encode?_decode
#print axioms L4Factoidal.Storage.Sbm11.GraphList.admitted_of_decode
#print axioms L4Factoidal.Storage.Sbm11.GraphList.decodeAt_eq
