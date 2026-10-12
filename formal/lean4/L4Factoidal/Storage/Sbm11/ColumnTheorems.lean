/-
L4Factoidal.Storage.Sbm11.ColumnTheorems — the column frame round trip and
the byte-array decoder.

* `get64_put64`, `get32_put32`: the fixed-width fields.
* `getVar_putVar`: the varint of `n`, most significant group first.
* `unzz_zz`: the zig-zag difference.
* `decodeColumn_encodeColumn?`: `encodeColumn? xs = some bs →
  decodeColumn xs.length (bs ++ rest) = some (xs, rest)`. The only
  hypothesis is the encoder's admission.
* `decodeColumnAt_eq`: the runtime decoder over a `ByteArray` returns the
  column and the end position that `decodeColumn` returns, on every input.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Column
import L4Factoidal.Storage.Sbm11.DictFastTheorems

namespace L4Factoidal.Storage.Sbm11.Column

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.Dict (bytesToList bytesToList_length drop_bytesToList_cons
  drop_bytesToList_of_le)

private theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8]

/-! ## Fixed-width fields -/

theorem get64_put64 (v : Nat) (h : v < two64) (rest : List UInt8) :
    get64 (put64 v ++ rest) = some (v, rest) := by
  have h' : v < 18446744073709551616 := h
  simp only [put64, get64, List.cons_append, List.nil_append, toNat_toUInt8, Option.some.injEq,
    Prod.mk.injEq, and_true]
  omega

theorem get32_put32 (v : Nat) (h : v < 4294967296) (rest : List UInt8) :
    get32 (put32 v ++ rest) = some (v, rest) := by
  simp only [put32, get32, List.cons_append, List.nil_append, toNat_toUInt8, Option.some.injEq,
    Prod.mk.injEq, and_true]
  omega

theorem put64_length (v : Nat) : (put64 v).length = 8 := rfl
theorem put32_length (v : Nat) : (put32 v).length = 4 := rfl

/-! ## Varints -/

theorem vbeGo_append (f : Nat) : ∀ (n : Nat) (L T : List UInt8),
    vbeGo f n (L ++ T) = vbeGo f n L ++ T := by
  induction f with
  | zero => intro n L T; rfl
  | succ f ih =>
    intro n L T
    simp only [vbeGo]
    split
    · rfl
    · rw [← List.cons_append, ih]

theorem putVar_append (n : Nat) (T : List UInt8) : putVar n [] ++ T = putVar n T := by
  unfold putVar
  rw [← vbeGo_append]
  rfl

/-- What the varint decoder does with a list that starts with `P`: from any
    accumulator it returns `acc * M + val` and the bytes after `P`. -/
private def Decodes (rest L : List UInt8) (M val : Nat) : Prop :=
  ∃ P : List UInt8, L = P ++ rest ∧ 0 < P.length ∧
    ∀ (acc F : Nat), P.length ≤ F → getVarGo F acc L = some (acc * M + val, rest)

private theorem toNat_cont (n : Nat) : ((n % 128 + 128).toUInt8).toNat = n % 128 + 128 := by
  rw [toNat_toUInt8]; omega

private theorem vbeGo_decodes (rest : List UInt8) (f : Nat) : ∀ (n : Nat) (L : List UInt8) (M val : Nat),
    n ≤ f → Decodes rest L M val → ∃ M', Decodes rest (vbeGo f n L) M' (n * M + val) := by
  induction f with
  | zero =>
    intro n L M val hn hd
    have : n = 0 := by omega
    subst this
    exact ⟨M, by simpa [vbeGo] using hd⟩
  | succ f ih =>
    intro n L M val hn hd
    by_cases h0 : n = 0
    · subst h0
      exact ⟨M, by simpa [vbeGo] using hd⟩
    · simp only [vbeGo, h0, if_false]
      obtain ⟨P, hL, hP, hdec⟩ := hd
      have hd' : Decodes rest ((n % 128 + 128).toUInt8 :: L) (128 * M) ((n % 128) * M + val) := by
        refine ⟨(n % 128 + 128).toUInt8 :: P, by rw [hL]; rfl, by simp, ?_⟩
        intro acc F hF
        cases F with
        | zero => simp at hF
        | succ F =>
          simp only [getVarGo, toNat_cont]
          have hnot : ¬ (n % 128 + 128 < 128) := by omega
          rw [if_neg hnot]
          have hF' : P.length ≤ F := by simp at hF; omega
          rw [hdec _ _ hF']
          have : n % 128 + 128 - 128 = n % 128 := by omega
          rw [this]
          simp only [Option.some.injEq, Prod.mk.injEq, and_true]
          rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
      obtain ⟨M', hM'⟩ := ih (n / 128) _ _ _ (by omega) hd'
      refine ⟨M', ?_⟩
      have hn : n / 128 * (128 * M) + (n % 128 * M + val) = n * M + val := by
        have hdm := Nat.div_add_mod n 128
        have e : n * M = (n / 128) * (128 * M) + (n % 128) * M := by
          calc n * M = (128 * (n / 128) + n % 128) * M := by rw [hdm]
            _ = (n / 128) * (128 * M) + (n % 128) * M := by
              rw [Nat.add_mul, Nat.mul_comm 128 (n / 128), Nat.mul_assoc]
        rw [e, Nat.add_assoc]
      rw [hn] at hM'
      exact hM'

theorem getVar_putVar (n : Nat) (rest : List UInt8) : getVar (putVar n rest) = some (n, rest) := by
  have h0 : Decodes rest ((n % 128).toUInt8 :: rest) 128 (n % 128) := by
    refine ⟨[(n % 128).toUInt8], rfl, by simp, ?_⟩
    intro acc F hF
    cases F with
    | zero => simp at hF
    | succ F =>
      simp only [getVarGo, toNat_toUInt8]
      have hlt : n % 128 % 256 < 128 := by omega
      rw [if_pos hlt]
      have : n % 128 % 256 = n % 128 := by omega
      rw [this]
  obtain ⟨M', P, hL, _, hdec⟩ := vbeGo_decodes rest n (n / 128) _ 128 (n % 128) (Nat.div_le_self n 128) h0
  unfold getVar putVar
  rw [hL] at hdec
  rw [hL, hdec 0 _ (by simp)]
  have : n / 128 * 128 + n % 128 = n := Nat.div_add_mod' n 128
  simp [this]

/-! ## Zig-zag -/

theorem unzz_zz (prev v : Nat) : unzz prev (zz prev v) = some v := by
  unfold zz unzz
  by_cases h : prev ≤ v
  · rw [if_pos h]
    have e : 2 * (v - prev) % 2 = 0 := by omega
    rw [if_pos e]
    congr 1; omega
  · rw [if_neg h]
    have e : ¬ ((2 * (prev - v) - 1) % 2 = 0) := by omega
    rw [if_neg e]
    have e2 : (2 * (prev - v) - 1 + 1) / 2 ≤ prev := by omega
    rw [if_pos e2]
    congr 1; omega

/-! ## Raw and delta -/

theorem getRawGo_rawBytes : ∀ (xs : List Nat) (acc : List Nat) (rest : List UInt8),
    (∀ x ∈ xs, x < two64) →
    getRawGo xs.length (rawBytes xs ++ rest) acc = some (acc.reverse ++ xs, rest) := by
  intro xs
  induction xs with
  | nil => intro acc rest _; simp [getRawGo, rawBytes]
  | cons x xs ih =>
    intro acc rest hx
    have hrb : rawBytes (x :: xs) ++ rest = put64 x ++ (rawBytes xs ++ rest) := by
      simp [rawBytes, List.append_assoc]
    rw [hrb, List.length_cons]
    simp only [getRawGo]
    rw [get64_put64 x (hx x (by simp))]
    dsimp only
    rw [ih (x :: acc) rest (fun y hy => hx y (by simp [hy]))]
    simp

private def piece (p x : Nat) : List UInt8 := putVar (zz p x) []

theorem getDeltaGo_deltaBytes : ∀ (xs : List Nat) (prev : Nat) (acc : List Nat) (rest : List UInt8),
    (∀ x ∈ xs, x < two64) →
    getDeltaGo xs.length prev ((List.zipWith (fun p x => putVar (zz p x) []) (prev :: xs) xs).flatten ++ rest) acc =
      some (acc.reverse ++ xs, rest) := by
  intro xs
  induction xs with
  | nil => intro prev acc rest _; simp [getDeltaGo]
  | cons x xs ih =>
    intro prev acc rest hx
    have hz : (List.zipWith (fun p x => putVar (zz p x) []) (prev :: x :: xs) (x :: xs)).flatten ++ rest =
        putVar (zz prev x) ((List.zipWith (fun p x => putVar (zz p x) []) (x :: xs) xs).flatten ++ rest) := by
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.append_assoc]
      rw [putVar_append]
    rw [hz, List.length_cons]
    simp only [getDeltaGo]
    rw [getVar_putVar]
    dsimp only
    rw [unzz_zz]
    dsimp only
    rw [if_pos (hx x (by simp)), ih x (x :: acc) rest (fun y hy => hx y (by simp [hy]))]
    simp

private theorem replicate_of_all (x : Nat) (r : List Nat) (h : (r.all (· == x)) = true) :
    List.replicate (r.length + 1) x = x :: r := by
  rw [List.replicate_succ]
  congr 1
  symm
  rw [List.eq_replicate_iff]
  refine ⟨rfl, ?_⟩
  intro b hb
  have := List.all_eq_true.mp h b hb
  simpa using this

/-- The column frame round trip. The only hypothesis is the encoder's
    admission. -/
theorem decodeColumn_encodeColumn? (xs : List Nat) (bs : List UInt8)
    (h : encodeColumn? xs = some bs) (rest : List UInt8) :
    decodeColumn xs.length (bs ++ rest) = some (xs, rest) := by
  unfold encodeColumn? at h
  split at h
  · rename_i hadm
    have hall : ∀ x ∈ xs, x < two64 := by
      intro x hx
      have := List.all_eq_true.mp hadm x hx
      simpa using this
    simp only [Option.some.injEq] at h
    subst h
    cases xs with
    | nil => simp [frameBytes, decodeColumn, tagRaw, tagConst, getRawGo]
    | cons x r =>
      simp only [frameBytes]
      split
      · rename_i hsame
        simp only [List.cons_append, decodeColumn, tagConst, beq_self_eq_true, if_true]
        rw [get64_put64 x (hall x (by simp))]
        dsimp only
        rw [List.length_cons, replicate_of_all x r hsame]
      · split
        · simp only [List.cons_append, decodeColumn]
          have h1 : (tagDelta == tagConst) = false := by decide
          have h2 : (tagDelta == tagRaw) = false := by decide
          have h3 : (tagDelta == tagDelta) = true := by decide
          rw [h1, h2, h3]
          simp only [Bool.false_eq_true, if_false, if_true]
          have := getDeltaGo_deltaBytes (x :: r) 0 [] rest hall
          simpa [deltaBytes] using this
        · simp only [List.cons_append, decodeColumn]
          have h1 : (tagRaw == tagConst) = false := by decide
          have h2 : (tagRaw == tagRaw) = true := by decide
          rw [h1, h2]
          simp only [Bool.false_eq_true, if_false, if_true]
          have := getRawGo_rawBytes (x :: r) [] rest hall
          simpa using this
  · cases h

/-! ## The byte-array decoder -/

private theorem get64_short (l : List UInt8) (h : l.length < 8) : get64 l = none := by
  match l, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl
  | [_, _, _, _], _ => rfl
  | [_, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _], _ => rfl
  | [_, _, _, _, _, _, _], _ => rfl

theorem get64At_spec (b : ByteArray) (i : Nat) :
    (get64At b i).map (fun r => (r.1, (bytesToList b).drop r.2)) = get64 ((bytesToList b).drop i) := by
  unfold get64At
  by_cases h : i + 8 ≤ b.size
  · rw [dif_pos h]
    rw [drop_bytesToList_cons b i (by omega), drop_bytesToList_cons b (i + 1) (by omega),
      drop_bytesToList_cons b (i + 2) (by omega), drop_bytesToList_cons b (i + 3) (by omega),
      drop_bytesToList_cons b (i + 4) (by omega), drop_bytesToList_cons b (i + 5) (by omega),
      drop_bytesToList_cons b (i + 6) (by omega), drop_bytesToList_cons b (i + 7) (by omega)]
    rfl
  · rw [dif_neg h, get64_short _ (by simp [bytesToList_length]; omega)]
    rfl

theorem getVarAtGo_spec (b : ByteArray) (f : Nat) : ∀ (acc i : Nat),
    (getVarAtGo b f acc i).map (fun r => (r.1, (bytesToList b).drop r.2)) =
      getVarGo f acc ((bytesToList b).drop i) := by
  induction f with
  | zero => intro acc i; rfl
  | succ f ih =>
    intro acc i
    unfold getVarAtGo
    by_cases h : i < b.size
    · rw [dif_pos h, drop_bytesToList_cons b i h]
      simp only [getVarGo]
      split
      · rfl
      · exact ih _ _
    · rw [dif_neg h, drop_bytesToList_of_le b i (by omega)]
      rfl

theorem getVarAt_spec (b : ByteArray) (i : Nat) :
    (getVarAt b i).map (fun r => (r.1, (bytesToList b).drop r.2)) = getVar ((bytesToList b).drop i) := by
  unfold getVarAt getVar
  rw [getVarAtGo_spec]
  simp [bytesToList_length]

theorem rawAtGo_spec (b : ByteArray) (n : Nat) : ∀ (i : Nat) (acc : Array Nat),
    (rawAtGo b n i acc).map (fun r => (r.1.toList, (bytesToList b).drop r.2)) =
      getRawGo n ((bytesToList b).drop i) acc.toList.reverse := by
  induction n with
  | zero => intro i acc; simp [rawAtGo, getRawGo]
  | succ n ih =>
    intro i acc
    have hs := get64At_spec b i
    simp only [rawAtGo, getRawGo]
    cases h1 : get64At b i with
    | none =>
      rw [h1] at hs
      rw [← hs]
      rfl
    | some p =>
      obtain ⟨v, j⟩ := p
      rw [h1] at hs
      rw [← hs]
      dsimp only [Option.map_some]
      rw [ih]
      simp

theorem deltaAtGo_spec (b : ByteArray) (n : Nat) : ∀ (prev i : Nat) (acc : Array Nat),
    (deltaAtGo b n prev i acc).map (fun r => (r.1.toList, (bytesToList b).drop r.2)) =
      getDeltaGo n prev ((bytesToList b).drop i) acc.toList.reverse := by
  induction n with
  | zero => intro prev i acc; simp [deltaAtGo, getDeltaGo]
  | succ n ih =>
    intro prev i acc
    have hs := getVarAt_spec b i
    simp only [deltaAtGo, getDeltaGo]
    cases h1 : getVarAt b i with
    | none =>
      rw [h1] at hs
      rw [← hs]
      rfl
    | some p =>
      obtain ⟨z, j⟩ := p
      rw [h1] at hs
      rw [← hs]
      dsimp only [Option.map_some]
      cases unzz prev z with
      | none => rfl
      | some v =>
        dsimp only
        split
        · rw [ih]; simp
        · rfl

/-- The runtime column decoder equals the specification decoder. -/
theorem decodeColumnAt_eq (b : ByteArray) (n i : Nat) :
    (decodeColumnAt b n i).map (fun r => (r.1.toList, (bytesToList b).drop r.2)) =
      decodeColumn n ((bytesToList b).drop i) := by
  unfold decodeColumnAt
  by_cases h : i < b.size
  · rw [dif_pos h, drop_bytesToList_cons b i h]
    simp only [decodeColumn]
    split
    · have hs := get64At_spec b (i + 1)
      cases h1 : get64At b (i + 1) with
      | none =>
        rw [h1] at hs
        rw [← hs]
        rfl
      | some p =>
        obtain ⟨v, j⟩ := p
        rw [h1] at hs
        rw [← hs]
        simp
    · split
      · rw [rawAtGo_spec]; simp
      · split
        · rw [deltaAtGo_spec]; simp
        · rfl
  · rw [dif_neg h, drop_bytesToList_of_le b i (by omega)]
    rfl

/-- What a reader accepts: a frame of `n` rows that ends at `j`. Then its
    column is the one `decodeColumn` reads from the same bytes. -/
theorem decodeColumnAt_some (b : ByteArray) (n i j : Nat) (col : Array Nat)
    (h : decodeColumnAt b n i = some (col, j)) :
    decodeColumn n ((bytesToList b).drop i) = some (col.toList, (bytesToList b).drop j) := by
  rw [← decodeColumnAt_eq, h]
  rfl

end L4Factoidal.Storage.Sbm11.Column
