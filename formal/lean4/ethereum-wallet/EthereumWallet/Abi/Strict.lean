import EthereumWallet.Abi.Proofs

/-!
# The strict argument decoder: what it accepts, and where it refuses

`decodeArgsAt_sound` and `decodeArgsAt_complete` together say that, for
accepted types, `decodeArgsAt ts d base = .ok vs` holds exactly when `vs` is
well typed and the bytes of `d` from `base` to its end are the canonical
encoding of `vs`. The refusal theorems name the outcome at each bound.
-/

namespace EthereumWallet.Abi

/-- Kind: soundness (canonical form). Says: when the strict decoder accepts, the types were
    accepted, the value is well typed, and the data from `base` to the end is exactly the
    canonical encoding of the value: no trailing bytes, no gaps, no shared or reordered tails,
    no dirty padding. So the decoded value's encoding is no longer than the input.
    Does not say: that the encoding function itself matches Solidity's; vectors test that. -/
theorem decodeArgsAt_sound (ts : List AbiType) (d : ByteArray) (base : Nat) (vs : List AbiValue)
    (h : decodeArgsAt ts d base = .ok vs) :
    typesOk ts = true ∧ checkL ts vs = true ∧ Window d base (encodeArgs ts vs)
      ∧ base + (encodeArgs ts vs).length = d.size := by
  simp only [decodeArgsAt] at h
  split at h
  next hty =>
    split at h
    next => cases h
    next r hr =>
      split at h
      next hsz =>
        split at h
        next hck =>
          split at h
          next hcan =>
            cases h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcan
            exact ⟨hty, hck, (windowB_iff _ _ _).mp hcan.2, hcan.1⟩
          next => cases h
        next => cases h
      next => cases h
  next => cases h

/-- Kind: completeness. Says: the strict decoder accepts every canonical encoding of a
    well-typed value of accepted types that fills the data from `base`, when the encoding is
    shorter than `2^256` bytes.
    Does not say: anything about encodings of `2^256` bytes or more (none can exist in memory). -/
theorem decodeArgsAt_complete (ts : List AbiType) (d : ByteArray) (base : Nat) (vs : List AbiValue)
    (hty : typesOk ts = true) (hc : checkL ts vs = true)
    (hl : (encodeArgs ts vs).length < two256) (hw : Window d base (encodeArgs ts vs))
    (hsz : base + (encodeArgs ts vs).length = d.size) :
    decodeArgsAt ts d base = .ok vs := by
  have hwf : wfL ts = true := by
    simp only [typesOk, Bool.and_eq_true] at hty
    exact hty.1
  have hwb := (windowB_iff d base (encodeArgs ts vs)).mpr hw
  simp only [encodeArgs] at hl hw hsz hwb
  have hrun := runFields_tuple ts d vs base hwf hc hl hw
  simp [decodeArgsAt, encodeArgs, hty, hrun, hsz, hc, hwb]

/-- Kind: round trip. Says: decode ∘ encode = id on well-typed argument lists of accepted types.
    Does not say: anything about ill-typed values, whose encoding is the empty list. -/
theorem decodeArgs_encodeArgs (ts : List AbiType) (vs : List AbiValue)
    (hty : typesOk ts = true) (hc : checkL ts vs = true)
    (hl : (encodeArgs ts vs).length < two256) :
    decodeArgs ts (toBytes (encodeArgs ts vs)) = .ok vs :=
  decodeArgsAt_complete ts _ 0 vs hty hc hl (window_toBytes _)
    (by rw [toBytes_size]; omega)

/-- Kind: injectivity. Says: two well-typed argument lists with the same encoding are equal.
    Does not say: that different type lists give different encodings (they need not). -/
theorem encodeArgs_injective (ts : List AbiType) (vs vs' : List AbiValue)
    (hty : typesOk ts = true) (hc : checkL ts vs = true) (hc' : checkL ts vs' = true)
    (hl : (encodeArgs ts vs).length < two256) (h : encodeArgs ts vs = encodeArgs ts vs') :
    vs = vs' := by
  have h1 := decodeArgs_encodeArgs ts vs hty hc hl
  have h2 := decodeArgs_encodeArgs ts vs' hty hc' (h ▸ hl)
  rw [h, h2] at h1
  exact (Except.ok.inj h1).symm

/-! ## Refusals at the bounds -/

/-- Kind: refusal at the bound. Says: types that are ill formed or nested beyond
    `maxTypeDepth` are refused before any byte is read.
    Does not say: which of the two reasons applied. -/
theorem decodeArgsAt_bad_type (ts : List AbiType) (d : ByteArray) (base : Nat)
    (h : typesOk ts = false) : decodeArgsAt ts d base = .error .badType := by
  simp [decodeArgsAt, h]

/-- Kind: bound. Says: a count that passes `countOk` is at most the bytes that are left.
    Does not say: that the elements then decode. -/
theorem countOk_le (headSize n rem : Nat) (h : countOk headSize n rem = true) : n ≤ rem := by
  simp only [countOk, decide_eq_true_eq] at h
  have : n * 1 ≤ n * headSize := Nat.mul_le_mul_left _ h.1
  omega

/-- Kind: refusal at the bound. Says: an array whose count does not fit in the data that is
    left is refused, and the test comes before the element decoders are built.
    Does not say: what happens for counts that fit. -/
theorem decodeAt_array_count_refused (t : AbiType) (d : ByteArray) (p n : Nat)
    (hn : readWord d p = .ok n) (h : countOk t.headSize n (d.size - (p + 32)) = false) :
    (AbiType.array t).decodeAt d p = .error .lengthOutOfBounds := by
  simp [AbiType.decodeAt, hn, h]

/-- Kind: refusal at the bound. Says: the same for `T[k]` with `k` from the type. -/
theorem decodeAt_fixedArray_count_refused (t : AbiType) (d : ByteArray) (p n : Nat)
    (h : countOk t.headSize n (d.size - p) = false) :
    (AbiType.fixedArray t n).decodeAt d p = .error .lengthOutOfBounds := by
  simp [AbiType.decodeAt, h]

/-- Kind: refusal (strictness). Says: a dynamic field whose offset is not the end of the
    previous tail is refused, so tails cannot overlap, repeat or leave gaps.
    Does not say: anything about static fields, which have no offset. -/
theorem runFields_bad_offset (d : ByteArray) (base : Nat) (f : FieldDec) (fs : List FieldDec)
    (hp cur o : Nat) (acc : List AbiValue) (hd : f.dyn = true)
    (ho : readWord d (base + hp) = .ok o) (hne : o ≠ cur) :
    runFields d base (f :: fs) hp cur acc = .error .badOffset := by
  simp [runFields, hd, ho, hne]

/-- Kind: resource bound. Says: the field loop returns one value per field decoder.
    Does not say: how large each value is; `decodeArgsAt_sound` bounds the whole. -/
theorem runFields_length (d : ByteArray) (base : Nat) :
    ∀ (fs : List FieldDec) (hp cur : Nat) (acc : List AbiValue) (r : List AbiValue × Nat),
      runFields d base fs hp cur acc = .ok r → r.1.length = acc.length + fs.length
  | [], hp, cur, acc, r, h => by
    simp only [runFields] at h
    cases h
    simp
  | f :: fs, hp, cur, acc, r, h => by
    simp only [runFields] at h
    split at h
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h
          · have := runFields_length d base fs _ _ _ r h
            simp only [List.length_cons] at this ⊢
            omega
        · cases h
    · split at h
      · cases h
      · have := runFields_length d base fs _ _ _ r h
        simp only [List.length_cons] at this ⊢
        omega

/-- Kind: resource bound. Says: an array the single pass accepts has at most as many elements
    as the input has bytes, whatever count the input claimed.
    Does not say: the tighter bound (bytes / 32), which also holds for well-formed types. -/
theorem decodeAt_array_length_le (t : AbiType) (d : ByteArray) (p : Nat) (v : AbiValue) (c : Nat)
    (h : (AbiType.array t).decodeAt d p = .ok (v, c)) :
    ∃ vs, v = .seq vs ∧ vs.length ≤ d.size := by
  simp only [AbiType.decodeAt] at h
  split at h
  · cases h
  · rename_i n hn
    split at h
    · rename_i hok
      split at h
      · cases h
      · rename_i r hr
        cases h
        have hlen := runFields_length d (p + 32) _ _ _ _ r hr
        have hle := countOk_le _ _ _ hok
        simp only [List.length_nil, List.length_replicate, Nat.zero_add] at hlen
        exact ⟨r.1, rfl, by omega⟩
    · cases h

end EthereumWallet.Abi
