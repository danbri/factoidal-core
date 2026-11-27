import EthereumWallet.Abi.Codec

/-!
# ABI codec: round trip, canonical form and refusals

What is proved here, for the definitions in `Codec.lean` as written (the
compiler and runtime are trusted):

* `decodeAt_enc`: the single-pass decoder returns `v` on any array that holds
  the encoding of a well-typed `v` at the position it is asked to read.
* `decodeArgsAt_sound`: the strict decoder accepts only the canonical
  encoding of the value it returns, filling the data exactly.
* `decodeArgsAt_complete`, `decodeArgs_encodeArgs`: decode ∘ encode = id.
* `encodeArgs_injective`: two well-typed argument lists with the same
  encoding are equal.
* refusals at the bounds: `readWord_out_of_bounds` (in `Bytes.lean`),
  `decodeAt_array_count_refused`, `decodeArgsAt_bad_type`,
  `runFields_bad_offset`.
-/

namespace EthereumWallet.Abi

/-! ## The sequence encoding, one field at a time -/

theorem headTotal_fold (fs : List (Bool × List UInt8)) (a : Nat) :
    fs.foldl (fun a f => a + (if f.1 then 32 else f.2.length)) a
      = a + fs.foldl (fun a f => a + (if f.1 then 32 else f.2.length)) 0 := by
  induction fs generalizing a with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldl_cons]
    rw [ih (a + _), ih (0 + _)]
    omega

theorem headTotal_cons (f : Bool × List UInt8) (fs : List (Bool × List UInt8)) :
    headTotal (f :: fs) = (if f.1 then 32 else f.2.length) + headTotal fs := by
  simp only [headTotal, List.foldl_cons]
  rw [headTotal_fold]
  omega

theorem headsLoop_acc (fs : List (Bool × List UInt8)) (cur : Nat) (acc : List (List UInt8)) :
    headsLoop fs cur acc = acc.reverse ++ headsLoop fs cur [] := by
  induction fs generalizing cur acc with
  | nil => simp [headsLoop]
  | cons f fs ih =>
    simp only [headsLoop]
    split
    · rw [ih, ih (acc := [_])]; simp
    · rw [ih, ih (acc := [_])]; simp

theorem heads_nil (cur : Nat) : heads [] cur = [] := by
  simp [heads, headsLoop]

theorem tails_nil : tails [] = [] := by
  simp [tails]

theorem heads_cons_dyn (e : List UInt8) (fs : List (Bool × List UInt8)) (cur : Nat) :
    heads ((true, e) :: fs) cur = word cur ++ heads fs (cur + e.length) := by
  simp only [heads, headsLoop, if_true]
  rw [headsLoop_acc]
  simp

theorem heads_cons_static (e : List UInt8) (fs : List (Bool × List UInt8)) (cur : Nat) :
    heads ((false, e) :: fs) cur = e ++ heads fs cur := by
  simp only [heads, headsLoop, Bool.false_eq_true, if_false]
  rw [headsLoop_acc]
  simp

theorem tails_cons_dyn (e : List UInt8) (fs : List (Bool × List UInt8)) :
    tails ((true, e) :: fs) = e ++ tails fs := by
  simp [tails]

theorem tails_cons_static (e : List UInt8) (fs : List (Bool × List UInt8)) :
    tails ((false, e) :: fs) = tails fs := by
  simp [tails]

theorem heads_length (fs : List (Bool × List UInt8)) (cur : Nat) :
    (heads fs cur).length = headTotal fs := by
  induction fs generalizing cur with
  | nil => simp [heads_nil, headTotal]
  | cons f fs ih =>
    obtain ⟨dyn, e⟩ := f
    cases dyn with
    | true => rw [heads_cons_dyn, headTotal_cons]; simp [ih, word_length]
    | false => rw [heads_cons_static, headTotal_cons]; simp [ih]

theorem encSeq_length (fs : List (Bool × List UInt8)) :
    (encSeq fs).length = headTotal fs + (tails fs).length := by
  simp [encSeq, heads_length]

/-! ## The field loop decodes what the sequence encoding wrote -/

/-- Each field decoder reads back its field's value from any window on that
    field's encoding. -/
def FieldsOk (d : ByteArray) : List FieldDec → List (Bool × List UInt8) → List AbiValue → Prop
  | [], [], [] => True
  | f :: fs, e :: es, v :: vs =>
    f.dyn = e.1
      ∧ (e.2.length < two256 → ∀ p, Window d p e.2 → f.run p = .ok (v, e.2.length))
      ∧ FieldsOk d fs es vs
  | _, _, _ => False

theorem runFields_ok (d : ByteArray) (base : Nat) :
    ∀ (fs : List FieldDec) (es : List (Bool × List UInt8)) (vs : List AbiValue)
      (hp cur : Nat) (acc : List AbiValue),
      FieldsOk d fs es vs →
      (heads es cur).length < two256 →
      cur + (tails es).length < two256 →
      Window d (base + hp) (heads es cur) →
      Window d (base + cur) (tails es) →
      runFields d base fs hp cur acc = .ok (acc.reverse ++ vs, cur + (tails es).length)
  | [], [], [], hp, cur, acc, _, _, _, _, _ => by
    simp [runFields, tails_nil]
  | f :: fs, (dyn, e) :: es, v :: vs, hp, cur, acc, hok, hH, hT, hwH, hwT => by
    obtain ⟨hdyn, hrun, hrest⟩ := hok
    simp only at hdyn hrun
    cases dyn with
    | true =>
      rw [heads_cons_dyn] at hH hwH
      rw [tails_cons_dyn] at hT hwT
      simp only [List.length_append, word_length] at hH hT
      have hw := readWord_of_window d (base + hp) cur (by omega) hwH.left
      have hr := hrun (by omega) (base + cur) hwT.left
      have hwH' : Window d (base + (hp + 32)) (heads es (cur + e.length)) := by
        have := hwH.right
        rw [word_length, Nat.add_assoc] at this
        exact this
      have hwT' : Window d (base + (cur + e.length)) (tails es) := by
        have := hwT.right
        rw [Nat.add_assoc] at this
        exact this
      have hih := runFields_ok d base fs es vs (hp + 32) (cur + e.length) (v :: acc) hrest
        (by omega) (by omega) hwH' hwT'
      simp only [runFields, hdyn, hw, hr, if_true]
      rw [hih]
      simp [Nat.add_assoc, tails_cons_dyn]
    | false =>
      rw [heads_cons_static] at hH hwH
      rw [tails_cons_static] at hT hwT
      simp only [List.length_append] at hH
      have hr := hrun (by omega) (base + hp) hwH.left
      have hwH' : Window d (base + (hp + e.length)) (heads es cur) := by
        have := hwH.right
        rw [Nat.add_assoc] at this
        exact this
      have hih := runFields_ok d base fs es vs (hp + e.length) cur (v :: acc) hrest
        (by omega) hT hwH' hwT
      simp only [runFields, hdyn, hr, Bool.false_eq_true, if_false]
      rw [hih]
      simp [tails_cons_static]
  | [], [], _ :: _, _, _, _, h, _, _, _, _ => by simp [FieldsOk] at h
  | [], _ :: _, _, _, _, _, h, _, _, _, _ => by simp [FieldsOk] at h
  | _ :: _, [], _, _, _, _, h, _, _, _, _ => by simp [FieldsOk] at h
  | _ :: _, _ :: _, [], _, _, _, h, _, _, _, _ => by simp [FieldsOk] at h

/-! ## Sizes -/

theorem headSize_dyn : ∀ (t : AbiType), t.isDynamic = true → t.headSize = 32
  | .uint _, _ => by simp [AbiType.headSize]
  | .int _, _ => by simp [AbiType.headSize]
  | .address, _ => by simp [AbiType.headSize]
  | .bool, _ => by simp [AbiType.headSize]
  | .fixedBytes _, _ => by simp [AbiType.headSize]
  | .bytes, _ => by simp [AbiType.headSize]
  | .string, _ => by simp [AbiType.headSize]
  | .array _, _ => by simp [AbiType.headSize]
  | .fixedArray t n, h => by
    simp only [AbiType.isDynamic] at h
    simp [AbiType.headSize, h]
  | .tuple ts, h => by
    simp only [AbiType.isDynamic] at h
    simp [AbiType.headSize, h]

mutual
/-- Kind: size bound. Says: a well-formed type has a head of at least 32 bytes.
    Does not say: anything about ill-formed types (empty tuples, `T[0]`). -/
theorem headSize_ge : ∀ (t : AbiType), t.wf = true → 32 ≤ t.headSize
  | .uint _, _ => by simp [AbiType.headSize]
  | .int _, _ => by simp [AbiType.headSize]
  | .address, _ => by simp [AbiType.headSize]
  | .bool, _ => by simp [AbiType.headSize]
  | .fixedBytes _, _ => by simp [AbiType.headSize]
  | .bytes, _ => by simp [AbiType.headSize]
  | .string, _ => by simp [AbiType.headSize]
  | .array _, _ => by simp [AbiType.headSize]
  | .fixedArray t n, h => by
    simp only [AbiType.wf, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [AbiType.headSize]
    split
    · omega
    · have h1 := headSize_ge t h.2
      have h2 : 1 * t.headSize ≤ n * t.headSize := Nat.mul_le_mul_right _ h.1
      omega
  | .tuple ts, h => by
    simp only [AbiType.wf, Bool.and_eq_true] at h
    simp only [AbiType.headSize]
    split
    · omega
    · exact headSizeL_ge ts h.2 (by simpa using h.1)
theorem headSizeL_ge : ∀ (ts : List AbiType), wfL ts = true → ts ≠ [] → 32 ≤ headSizeL ts
  | [], _, h => absurd rfl h
  | t :: ts, h, _ => by
    simp only [wfL, Bool.and_eq_true] at h
    simp only [headSizeL]
    have := headSize_ge t h.1
    omega
end

theorem tails_map_static (f : AbiValue → List UInt8) (vs : List AbiValue) :
    tails (vs.map fun x => (false, f x)) = [] := by
  induction vs with
  | nil => simp [tails]
  | cons v vs ih => rw [List.map_cons, tails_cons_static, ih]

theorem tails_encL_static : ∀ (ts : List AbiType) (vs : List AbiValue),
    anyDynamic ts = false → tails (encL ts vs) = []
  | [], _, _ => by simp [encL, tails_nil]
  | t :: ts, vs, h => by
    simp only [anyDynamic, Bool.or_eq_false_iff] at h
    cases vs with
    | nil => simp [encL, tails_nil]
    | cons v vs =>
      simp only [encL, h.1]
      rw [tails_cons_static]
      exact tails_encL_static ts vs h.2

theorem headTotal_map (t : AbiType)
    (ih : ∀ v, t.check v = true → t.isDynamic = false → (t.enc v).length = t.headSize) :
    ∀ (vs : List AbiValue), vs.all (fun x => t.check x) = true →
      headTotal (vs.map fun x => (t.isDynamic, t.enc x)) = vs.length * t.headSize
  | [], _ => by simp [headTotal]
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.map_cons, headTotal_cons, headTotal_map t ih vs h.2, List.length_cons, Nat.succ_mul]
    cases hd : t.isDynamic with
    | true => simp [headSize_dyn t hd]; omega
    | false => simp [ih v h.1 hd]; omega

theorem padLen_le (n : Nat) : padLen n < 32 := by
  simp only [padLen]; omega

mutual
/-- Kind: size. Says: a well-typed value of a static type encodes to exactly the type's head size.
    Does not say: anything about dynamic types. -/
theorem enc_length_static : ∀ (t : AbiType) (v : AbiValue),
    t.wf = true → t.check v = true → t.isDynamic = false → (t.enc v).length = t.headSize
  | .uint _, v, _, hc, _ => by
    cases v with
    | uint n => simp [AbiType.enc, AbiType.headSize, word_length]
    | _ => simp [AbiType.check] at hc
  | .int _, v, _, hc, _ => by
    cases v with
    | int n => simp [AbiType.enc, AbiType.headSize, word_length]
    | _ => simp [AbiType.check] at hc
  | .address, v, _, hc, _ => by
    cases v with
    | address n => simp [AbiType.enc, AbiType.headSize, word_length]
    | _ => simp [AbiType.check] at hc
  | .bool, v, _, hc, _ => by
    cases v with
    | bool n => simp [AbiType.enc, AbiType.headSize, word_length]
    | _ => simp [AbiType.check] at hc
  | .fixedBytes k, v, hwf, hc, _ => by
    cases v with
    | bytes b =>
      simp only [AbiType.check, decide_eq_true_eq] at hc
      simp only [AbiType.wf, decide_eq_true_eq] at hwf
      simp only [AbiType.enc, AbiType.headSize, List.length_append, List.length_replicate]
      omega
    | _ => simp [AbiType.check] at hc
  | .bytes, _, _, _, hd => by simp [AbiType.isDynamic] at hd
  | .string, _, _, _, hd => by simp [AbiType.isDynamic] at hd
  | .array _, _, _, _, hd => by simp [AbiType.isDynamic] at hd
  | .fixedArray t n, v, hwf, hc, hd => by
    cases v with
    | seq vs =>
      simp only [AbiType.check, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [AbiType.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      simp only [AbiType.isDynamic] at hd
      have hht := headTotal_map t (fun v hc hd => enc_length_static t v hwf.2 hc hd) vs hc.2
      rw [hd] at hht
      simp only [AbiType.enc, AbiType.headSize, hd, Bool.false_eq_true, if_false]
      rw [encSeq_length, hht, tails_map_static]
      simp [hc.1]
    | _ => simp [AbiType.check] at hc
  | .tuple ts, v, hwf, hc, hd => by
    cases v with
    | seq vs =>
      simp only [AbiType.check] at hc
      simp only [AbiType.wf, Bool.and_eq_true] at hwf
      simp only [AbiType.isDynamic] at hd
      simp only [AbiType.enc, AbiType.headSize, hd, Bool.false_eq_true, if_false]
      rw [encSeq_length, tails_encL_static ts vs hd, headTotal_encL ts vs hwf.2 hc]
      simp
    | _ => simp [AbiType.check] at hc
theorem headTotal_encL : ∀ (ts : List AbiType) (vs : List AbiValue),
    wfL ts = true → checkL ts vs = true → headTotal (encL ts vs) = headSizeL ts
  | [], _, _, _ => by simp [encL, headTotal, headSizeL]
  | t :: ts, vs, hwf, hc => by
    cases vs with
    | nil => simp [checkL] at hc
    | cons v vs =>
      simp only [checkL, Bool.and_eq_true] at hc
      simp only [wfL, Bool.and_eq_true] at hwf
      simp only [encL, headSizeL]
      rw [headTotal_cons, headTotal_encL ts vs hwf.2 hc.2]
      cases hd : t.isDynamic with
      | true => simp [headSize_dyn t hd]
      | false => simp [enc_length_static t v hwf.1 hc.1 hd]
end

/-! ## Leaves -/

theorem pow_le_two256 (bits : Nat) (h : bits ≤ 256) : 2 ^ bits ≤ two256 :=
  Nat.pow_le_pow_right (by decide) h

theorem wordToInt_intToWord (bits : Nat) (i : Int) (hb : 1 ≤ bits ∧ bits ≤ 256)
    (h : intInRange bits i = true) : wordToInt (intToWord i) = i ∧ intToWord i < two256 := by
  have hp : 2 ^ (bits - 1) ≤ two255 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 := two256_eq
  cases i with
  | ofNat n =>
    simp only [intInRange, decide_eq_true_eq] at h
    have hlt : n < two255 := by omega
    refine ⟨?_, ?_⟩
    · show wordToInt n = Int.ofNat n
      unfold wordToInt
      rw [if_pos hlt]
    · show n < two256
      omega
  | negSucc n =>
    simp only [intInRange, decide_eq_true_eq] at h
    have hlt : ¬ (two256 - (n + 1) < two255) := by omega
    have he : two256 - (two256 - (n + 1)) - 1 = n := by omega
    refine ⟨?_, ?_⟩
    · show wordToInt (two256 - (n + 1)) = Int.negSucc n
      unfold wordToInt
      rw [if_neg hlt, he]
    · show two256 - (n + 1) < two256
      omega

theorem decBytes_ok (d : ByteArray) (p : Nat) (b : List UInt8)
    (hl : (encBytes b).length < two256) (hw : Window d p (encBytes b)) :
    decBytes d p = .ok (.bytes b, (encBytes b).length) := by
  simp only [encBytes] at hl hw ⊢
  have hlen : (word b.length ++ b ++ List.replicate (padLen b.length) 0).length
      = 32 + b.length + padLen b.length := by
    simp only [List.length_append, word_length, List.length_replicate]
  rw [hlen] at hl ⊢
  have hsz := hw.size
  rw [hlen] at hsz
  have hn := readWord_of_window d p b.length (by omega) hw.left.left
  have hb : takeBytes d (p + 32) b.length = b := by
    have := hw.left.right
    rw [word_length] at this
    exact takeBytes_of_window d (p + 32) b this
  have hz : allZero d (p + 32 + b.length) (padLen b.length) = true := by
    have := hw.right
    simp only [List.length_append, word_length] at this
    rw [← Nat.add_assoc] at this
    exact allZero_of_window d _ _ this
  simp only [decBytes, hn]
  rw [if_pos (by omega), if_pos (by omega)]
  simp [hz, hb]

/-! ## Round trip of the single pass -/

theorem fieldsOk_replicate (d : ByteArray) (t : AbiType)
    (ih : ∀ v p, t.check v = true → (t.enc v).length < two256 → Window d p (t.enc v) →
      t.decodeAt d p = .ok (v, (t.enc v).length)) :
    ∀ (vs : List AbiValue), vs.all (fun x => t.check x) = true →
      FieldsOk d (List.replicate vs.length ⟨t.isDynamic, t.decodeAt d⟩)
        (vs.map fun x => (t.isDynamic, t.enc x)) vs
  | [], _ => by simp [FieldsOk]
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.length_cons, List.replicate_succ, List.map_cons, FieldsOk]
    exact ⟨trivial, fun hl p hw => ih v p h.1 hl hw, fieldsOk_replicate d t ih vs h.2⟩

/-- The array and fixed-array step, shared by both cases of `decodeAt_enc`. -/
theorem runFields_rep (d : ByteArray) (t : AbiType) (hwf : t.wf = true)
    (ih : ∀ v p, t.check v = true → (t.enc v).length < two256 → Window d p (t.enc v) →
      t.decodeAt d p = .ok (v, (t.enc v).length))
    (vs : List AbiValue) (hc : vs.all (fun x => t.check x) = true) (base : Nat)
    (hl : (encSeq (vs.map fun x => (t.isDynamic, t.enc x))).length < two256)
    (hw : Window d base (encSeq (vs.map fun x => (t.isDynamic, t.enc x)))) :
    vs.length * t.headSize ≤ d.size - base
      ∧ runFields d base (List.replicate vs.length ⟨t.isDynamic, t.decodeAt d⟩) 0
          (vs.length * t.headSize) []
        = .ok (vs, (encSeq (vs.map fun x => (t.isDynamic, t.enc x))).length) := by
  have hok := fieldsOk_replicate d t ih vs hc
  have hht := headTotal_map t (fun v hc hd => enc_length_static t v hwf hc hd) vs hc
  generalize (vs.map fun x => (t.isDynamic, t.enc x)) = es at hok hht hl hw
  rw [encSeq_length] at hl ⊢
  simp only [encSeq] at hw
  have hH := hw.left
  have hT := hw.right
  rw [heads_length] at hT
  have hsz := hH.size
  rw [heads_length] at hsz
  rw [← hht]
  refine ⟨by omega, ?_⟩
  have := runFields_ok d base (List.replicate vs.length ⟨t.isDynamic, t.decodeAt d⟩) es vs 0
    (headTotal es) [] hok (by rw [heads_length]; omega) (by omega) (by simpa using hH) hT
  simpa using this

mutual
/-- Kind: round trip (single pass). Says: on any array holding the encoding of a
    well-typed value of a well-formed type at `p`, with the encoding shorter than
    `2^256` bytes, `decodeAt` returns that value and the encoding's length.
    Does not say: that `decodeAt` rejects every other input; `decodeArgsAt_sound` covers that. -/
theorem decodeAt_enc : ∀ (t : AbiType) (d : ByteArray) (v : AbiValue) (p : Nat),
    t.wf = true → t.check v = true → (t.enc v).length < two256 → Window d p (t.enc v) →
    t.decodeAt d p = .ok (v, (t.enc v).length)
  | .uint bits, d, v, p, hwf, hc, _, hw => by
    cases v with
    | uint n =>
      simp only [AbiType.check, decide_eq_true_eq] at hc
      simp only [AbiType.wf, decide_eq_true_eq] at hwf
      simp only [AbiType.enc] at hw ⊢
      have hn : n < two256 := Nat.lt_of_lt_of_le hc (pow_le_two256 bits hwf.2.1)
      simp only [AbiType.decodeAt, readWord_of_window d p n hn hw, hc, if_true, word_length]
    | _ => simp [AbiType.check] at hc
  | .int bits, d, v, p, hwf, hc, _, hw => by
    cases v with
    | int i =>
      simp only [AbiType.check] at hc
      simp only [AbiType.wf, decide_eq_true_eq] at hwf
      simp only [AbiType.enc] at hw ⊢
      have hrt := wordToInt_intToWord bits i ⟨by omega, hwf.2.1⟩ hc
      simp only [AbiType.decodeAt, readWord_of_window d p _ hrt.2 hw, hrt.1, hc, if_true,
        word_length]
    | _ => simp [AbiType.check] at hc
  | .address, d, v, p, _, hc, _, hw => by
    cases v with
    | address a =>
      simp only [AbiType.check, decide_eq_true_eq] at hc
      simp only [AbiType.enc] at hw ⊢
      have hn : a < two256 := Nat.lt_of_lt_of_le hc (pow_le_two256 160 (by decide))
      simp only [AbiType.decodeAt, readWord_of_window d p a hn hw, hc, if_true, word_length]
    | _ => simp [AbiType.check] at hc
  | .bool, d, v, p, _, hc, _, hw => by
    cases v with
    | bool b =>
      simp only [AbiType.enc] at hw ⊢
      have h1 : (1 : Nat) < two256 := by decide
      cases b with
      | true =>
        simp only [if_true] at hw ⊢
        simp [AbiType.decodeAt, readWord_of_window d p 1 h1 hw, word_length]
      | false =>
        simp only [Bool.false_eq_true, if_false] at hw ⊢
        simp [AbiType.decodeAt, readWord_of_window d p 0 (by decide) hw, word_length]
    | _ => simp [AbiType.check] at hc
  | .fixedBytes k, d, v, p, hwf, hc, _, hw => by
    cases v with
    | bytes b =>
      simp only [AbiType.check, decide_eq_true_eq] at hc
      simp only [AbiType.wf, decide_eq_true_eq] at hwf
      simp only [AbiType.enc] at hw ⊢
      have hsz := hw.size
      simp only [List.length_append, List.length_replicate] at hsz ⊢
      have hb : takeBytes d p k = b := by
        have := takeBytes_of_window d p b hw.left
        rw [hc] at this
        exact this
      have hz : allZero d (p + k) (32 - k) = true := by
        have := hw.right
        rw [hc] at this
        exact allZero_of_window d _ _ this
      simp only [AbiType.decodeAt, hz, hb, if_true]
      rw [if_pos (by omega)]
      congr 2
      omega
    | _ => simp [AbiType.check] at hc
  | .bytes, d, v, p, _, hc, hl, hw => by
    cases v with
    | bytes b =>
      simp only [AbiType.enc] at hl hw ⊢
      simp only [AbiType.decodeAt]
      exact decBytes_ok d p b hl hw
    | _ => simp [AbiType.check] at hc
  | .string, d, v, p, _, hc, hl, hw => by
    cases v with
    | bytes b =>
      simp only [AbiType.enc] at hl hw ⊢
      simp only [AbiType.decodeAt]
      exact decBytes_ok d p b hl hw
    | _ => simp [AbiType.check] at hc
  | .array t, d, v, p, hwf, hc, hl, hw => by
    cases v with
    | seq vs =>
      simp only [AbiType.check] at hc
      simp only [AbiType.wf] at hwf
      simp only [AbiType.enc] at hl hw ⊢
      simp only [List.length_append, word_length] at hl ⊢
      have hw2 := hw.right
      rw [word_length] at hw2
      have hrep := runFields_rep d t hwf
        (fun v p hc hl hw => decodeAt_enc t d v p hwf hc hl hw) vs hc (p + 32) (by omega) hw2
      have hge := headSize_ge t hwf
      have hcount : vs.length < two256 := by
        have h1 : vs.length * 1 ≤ vs.length * t.headSize := Nat.mul_le_mul_left _ (by omega)
        have h2 := hrep.1
        have h3 := hw2.size
        have h4 := encSeq_length (vs.map fun x => (t.isDynamic, t.enc x))
        have h5 := headTotal_map t (fun v hc hd => enc_length_static t v hwf hc hd) vs hc
        omega
      have hn := readWord_of_window d p vs.length hcount hw.left
      have hok : countOk t.headSize vs.length (d.size - (p + 32)) = true := by
        simp only [countOk, decide_eq_true_eq]
        exact ⟨by omega, hrep.1⟩
      simp only [AbiType.decodeAt, hn, hok, hrep.2, if_true]
    | _ => simp [AbiType.check] at hc
  | .fixedArray t n, d, v, p, hwf, hc, hl, hw => by
    cases v with
    | seq vs =>
      simp only [AbiType.check, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [AbiType.wf, Bool.and_eq_true, decide_eq_true_eq] at hwf
      simp only [AbiType.enc] at hl hw ⊢
      have hrep := runFields_rep d t hwf.2
        (fun v p hc hl hw => decodeAt_enc t d v p hwf.2 hc hl hw) vs hc.2 p hl hw
      have hge := headSize_ge t hwf.2
      rw [hc.1] at hrep
      have hok : countOk t.headSize n (d.size - p) = true := by
        simp only [countOk, decide_eq_true_eq]
        exact ⟨by omega, hrep.1⟩
      simp only [AbiType.decodeAt, hok, hrep.2, if_true]
    | _ => simp [AbiType.check] at hc
  | .tuple ts, d, v, p, hwf, hc, hl, hw => by
    cases v with
    | seq vs =>
      simp only [AbiType.check] at hc
      simp only [AbiType.wf, Bool.and_eq_true] at hwf
      simp only [AbiType.enc] at hl hw ⊢
      have := runFields_tuple ts d vs p hwf.2 hc hl hw
      simp only [AbiType.decodeAt, this]
    | _ => simp [AbiType.check] at hc
theorem fieldsOk_tuple : ∀ (ts : List AbiType) (d : ByteArray) (vs : List AbiValue),
    wfL ts = true → checkL ts vs = true → FieldsOk d (fieldDecs ts d) (encL ts vs) vs
  | [], d, vs, _, hc => by
    cases vs with
    | nil => simp [fieldDecs, encL, FieldsOk]
    | cons v vs => simp [checkL] at hc
  | t :: ts, d, vs, hwf, hc => by
    cases vs with
    | nil => simp [checkL] at hc
    | cons v vs =>
      simp only [checkL, Bool.and_eq_true] at hc
      simp only [wfL, Bool.and_eq_true] at hwf
      simp only [fieldDecs, encL, FieldsOk]
      exact ⟨trivial, fun hl p hw => decodeAt_enc t d v p hwf.1 hc.1 hl hw,
        fieldsOk_tuple ts d vs hwf.2 hc.2⟩
/-- The tuple step: the field loop over a tuple's types reads back the tuple. -/
theorem runFields_tuple : ∀ (ts : List AbiType) (d : ByteArray) (vs : List AbiValue) (base : Nat),
    wfL ts = true → checkL ts vs = true →
    (encSeq (encL ts vs)).length < two256 → Window d base (encSeq (encL ts vs)) →
    runFields d base (fieldDecs ts d) 0 (headSizeL ts) []
      = .ok (vs, (encSeq (encL ts vs)).length)
  | ts, d, vs, base, hwf, hc, hl, hw => by
    have hok := fieldsOk_tuple ts d vs hwf hc
    have hht := headTotal_encL ts vs hwf hc
    generalize encL ts vs = es at hok hht hl hw
    rw [encSeq_length] at hl ⊢
    simp only [encSeq] at hw
    have hH := hw.left
    have hT := hw.right
    rw [heads_length] at hT
    rw [← hht]
    have := runFields_ok d base (fieldDecs ts d) es vs 0 (headTotal es) [] hok
      (by rw [heads_length]; omega) (by omega) (by simpa using hH) hT
    simpa using this
end

end EthereumWallet.Abi
