/-
L4Factoidal.EXPath.Binary.Theorems — properties of the EXPath Binary
4.0 octet functions (`EXPath.Binary.Octets`), bound to the existing
code they reuse or agree with.

* `packBE_eq_packBEAcc` (in `Octets`, with `@[csimp]`): the
  accumulator form that runs is the recursive form the other theorems
  are about.
* `beValue_packBE`: unpacking `n` packed octets gives the value modulo
  `256^n` (bin:unpack-unsigned-integer after bin:pack-integer).
* `packBE_beValue`: packing the value of `n` octets gives the octets
  back (bin:pack-integer after bin:unpack-unsigned-integer).
* `signedOf_twosComplement`: the signed reading of the two's
  complement of `v` in `n` octets is `v`, for `v` in the signed range
  (bin:unpack-integer after bin:pack-integer).
* `orderBytes_orderBytes`: least-significant-first order is undone
  by itself.
* `ofHex_hexOfBytes`: bin:hex reads the canonical `xs:hexBinary`
  lexical form of `XSD.hexOfBytes` back to the same octets.
* `fromBase64url_toBase64url`: bin:from-base64url inverts
  bin:to-base64url, through the proved codec
  `JOSE.Base64Url.decode_encode`.
* `octetNot_octetNot`, `xor_self`: bit operations.
-/
import L4Factoidal.EXPath.Binary.Lib
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.EXPath.Binary

/-! ## Packing and unpacking integers -/

/-- Induction from the right end of a list. -/
theorem snocInd {P : List Nat → Prop} (nil : P []) (snoc : ∀ l b, P l → P (l ++ [b])) :
    ∀ l, P l := by
  have : ∀ r : List Nat, P r.reverse := by
    intro r
    induction r with
    | nil => simpa using nil
    | cons b r ih => simpa using snoc _ b ih
  intro l
  simpa using this l.reverse

theorem beValue_append_one (l : List Nat) (b : Nat) :
    beValue (l ++ [b]) = beValue l * 256 + b := by
  simp [beValue, List.foldl_append]

theorem packBE_length (n v : Nat) : (packBE n v).length = n := by
  induction n generalizing v with
  | zero => simp [packBE]
  | succ n ih => simp [packBE, ih]

theorem beValue_packBE (n v : Nat) : beValue (packBE n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [packBE, beValue, Nat.mod_one]
  | succ n ih =>
    rw [packBE, beValue_append_one, ih, Nat.pow_succ', Nat.mod_mul]
    omega

theorem beValue_lt (bs : List Nat) (h : ∀ b ∈ bs, b < 256) : beValue bs < 256 ^ bs.length := by
  revert h
  refine snocInd (P := fun bs => (∀ b ∈ bs, b < 256) → beValue bs < 256 ^ bs.length) ?_ ?_ bs
  · intro _; simp [beValue]
  · intro l b ih h
    rw [beValue_append_one]
    have hl := ih (fun x hx => h x (List.mem_append_left _ hx))
    have hb := h b (by simp)
    rw [List.length_append, List.length_singleton, Nat.pow_succ]
    have : (beValue l + 1) * 256 ≤ 256 ^ l.length * 256 := Nat.mul_le_mul_right _ hl
    omega

theorem packBE_beValue (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    packBE bs.length (beValue bs) = bs := by
  revert h
  refine snocInd (P := fun bs => (∀ b ∈ bs, b < 256) → packBE bs.length (beValue bs) = bs) ?_ ?_ bs
  · intro _; simp [packBE]
  · intro l b ih h
    have hb := h b (by simp)
    have hl := ih (fun x hx => h x (List.mem_append_left _ hx))
    rw [List.length_append, List.length_singleton, packBE, beValue_append_one]
    have h1 : (beValue l * 256 + b) / 256 = beValue l := by omega
    have h2 : (beValue l * 256 + b) % 256 = b := by omega
    rw [h1, h2, hl]

/-- bin:unpack-unsigned-integer of bin:pack-integer (most significant
    first, offset 0, the same size). -/
theorem pow256_cast (n : Nat) : ((256 : Int) ^ n) = ((256 ^ n : Nat) : Int) := by
  simp

theorem pow256_pos (n : Nat) : 0 < 256 ^ n := Nat.pow_pos (by decide)

theorem twosComplement_lt (n : Nat) (v : Int) : twosComplement n v < 256 ^ n := by
  unfold twosComplement
  rw [pow256_cast]
  have hpos := pow256_pos n
  have h1 := Int.emod_lt_of_pos v (b := ((256 ^ n : Nat) : Int)) (by omega)
  have h2 := Int.emod_nonneg v (b := ((256 ^ n : Nat) : Int)) (by omega)
  omega

/-- bin:unpack-unsigned-integer of bin:pack-integer (most significant
    first, offset 0, the same size). -/
theorem unpack_pack_unsigned (n : Nat) (v : Int) :
    beValue (packBEAcc n (twosComplement n v) []) = twosComplement n v := by
  rw [packBE_eq_packBEAcc, List.append_nil, beValue_packBE]
  exact Nat.mod_eq_of_lt (twosComplement_lt n v)

theorem orderBytes_orderBytes (little : Bool) (bs : List Nat) :
    orderBytes little (orderBytes little bs) = bs := by
  cases little <;> simp [orderBytes]

/-- bin:unpack-integer of bin:pack-integer: the value comes back when
    it is in the signed range of `n` octets. -/
theorem signedOf_twosComplement (n : Nat) (v : Int) (hn : 0 < n)
    (lo : -(((256 ^ n / 2 : Nat)) : Int) ≤ v) (hi : v < ((256 ^ n / 2 : Nat) : Int)) :
    signedOf n (twosComplement n v) = v := by
  have hM := pow256_pos n
  have hev : 256 ^ n % 2 = 0 := by
    cases n with
    | zero => omega
    | succ k => rw [Nat.pow_succ]; omega
  have hval : (v % ((256 ^ n : Nat) : Int)) = (if 0 ≤ v then v else v + ((256 ^ n : Nat) : Int)) := by
    split
    · exact Int.emod_eq_of_lt (by assumption) (by omega)
    · rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
  unfold signedOf twosComplement
  rw [pow256_cast, hval]
  by_cases hv : 0 ≤ v
  · rw [if_pos hv]
    have hc : (decide (n > 0) && decide (v.toNat ≥ 256 ^ n / 2)) = false := by
      have : ¬ (v.toNat ≥ 256 ^ n / 2) := by omega
      simp [this]
    rw [if_neg (by rw [hc]; decide)]
    omega
  · rw [if_neg hv]
    have hge : (v + ((256 ^ n : Nat) : Int)).toNat ≥ 256 ^ n / 2 := by omega
    have hc : (decide (n > 0) && decide ((v + ((256 ^ n : Nat) : Int)).toNat ≥ 256 ^ n / 2)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hn, hge⟩
    rw [if_pos hc]
    omega

/-! ## Bit operations -/

theorem octetNot_octetNot (a : Nat) (h : a < 256) : octetNot (octetNot a) = a := by
  unfold octetNot; omega

theorem xor_self (bs : List Nat) : List.zipWith octetXor bs bs = bs.map (fun _ => 0) := by
  induction bs with
  | nil => rfl
  | cons b r ih => simp [List.zipWith, octetXor]

/-! ## bin:hex and the canonical xs:hexBinary form -/

theorem hexDigit_hexDigitChar (n : Nat) (h : n < 16) :
    hexDigit? (XSD.hexDigitChar n) = some n := by
  have : n ∈ List.range 16 := List.mem_range.mpr h
  revert n
  decide

theorem isStripped_hexDigitChar (n : Nat) (h : n < 16) :
    isStripped (XSD.hexDigitChar n) = false := by
  have : n ∈ List.range 16 := List.mem_range.mpr h
  revert n
  decide

theorem hexPairsAcc_flatMap (bs acc : List Nat) (h : ∀ b ∈ bs, b < 256) :
    hexPairsAcc (bs.flatMap (fun b => [b / 16, b % 16])) acc = acc.reverse ++ bs := by
  induction bs generalizing acc with
  | nil => simp [hexPairsAcc]
  | cons b r ih =>
    have hb := h b (by simp)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, hexPairsAcc]
    rw [ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    have : b / 16 * 16 + b % 16 = b := by omega
    simp [this]

theorem hexPairs_flatMap (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    hexPairs (bs.flatMap (fun b => [b / 16, b % 16])) = bs := by
  simp [hexPairs, hexPairsAcc_flatMap bs [] h]

/-- bin:hex of the canonical `xs:hexBinary` lexical form
    (`XSD.hexOfBytes`, used by `string(xs:hexBinary(...))`) gives the
    octets back. -/
theorem ofHex_hexOfBytes (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    ofHex (XSD.hexOfBytes bs) = some bs := by
  have hd : ∀ b ∈ bs, b / 16 < 16 ∧ b % 16 < 16 := fun b hb => by
    have := h b hb; constructor <;> omega
  have hchars : (XSD.hexOfBytes bs).toList =
      bs.flatMap (fun b => [XSD.hexDigitChar (b / 16), XSD.hexDigitChar (b % 16)]) := by
    simp [XSD.hexOfBytes]
  have hfilter : ((XSD.hexOfBytes bs).toList.filter (! isStripped ·)) = (XSD.hexOfBytes bs).toList := by
    rw [List.filter_eq_self, hchars]
    intro c hc
    simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨b, hb, hc⟩ := hc
    rcases hc with rfl | rfl
    · simp [isStripped_hexDigitChar _ (hd b hb).1]
    · simp [isStripped_hexDigitChar _ (hd b hb).2]
  have hmap : ∀ (l : List Nat), (∀ b ∈ l, b < 256) →
      (l.flatMap (fun b => [XSD.hexDigitChar (b / 16), XSD.hexDigitChar (b % 16)])).mapM hexDigit?
        = some (l.flatMap (fun b => [b / 16, b % 16])) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b r ih =>
      have hb := hl b (by simp)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.mapM_cons,
        hexDigit_hexDigitChar _ (by omega : b / 16 < 16), hexDigit_hexDigitChar _ (by omega : b % 16 < 16),
        ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))]
      rfl
  have hlen : ∀ (l : List Nat), (l.flatMap (fun b => [b / 16, b % 16])).length = 2 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons b r ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega
  unfold ofHex
  rw [hfilter, hchars, hmap bs h]
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some, hlen bs, Nat.mul_mod_right]
  simp [hexPairs_flatMap bs h]

/-! ## bin:to-base64url and bin:from-base64url -/

/-- No base64url digit is whitespace or `=`. -/
theorem encodeDigit_plain (d : Nat) (h : d < 64) :
    (JOSE.Base64Url.encodeDigit d == ' ' || JOSE.Base64Url.encodeDigit d == '\t' ||
     JOSE.Base64Url.encodeDigit d == '\n' || JOSE.Base64Url.encodeDigit d == '\r' ||
     JOSE.Base64Url.encodeDigit d == '=') = false := by
  have : d ∈ List.range 64 := List.mem_range.mpr h
  revert d
  decide

theorem dropWhile_none {l : List Char} (p : Char → Bool) (h : ∀ c ∈ l, p c = false) :
    l.dropWhile p = l := by
  cases l with
  | nil => rfl
  | cons c r => simp [List.dropWhile, h c (by simp)]

/-- bin:from-base64url inverts bin:to-base64url: the round trip through
    `JOSE.Base64Url.decode_encode`. -/
theorem fromBase64url_toBase64url (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    fromBase64url? (String.ofList (JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat))) = some bs := by
  have hplain : ∀ c ∈ JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat),
      (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '=') = false := by
    intro c hc
    simp only [JOSE.Base64Url.encodeChars, List.mem_map] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    exact encodeDigit_plain d (JOSE.Base64Url.digitLt64 _ d hd)
  have hfilter : (JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat)).filter
      (fun c => !(c == ' ' || c == '\t' || c == '\n' || c == '\r')) =
      JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat) := by
    rw [List.filter_eq_self]
    intro c hc
    have := hplain c hc
    simp only [Bool.or_eq_false_iff] at this
    simp [this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2]
  have hdrop : ((JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat)).reverse.dropWhile (· == '=')).reverse =
      JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat) := by
    rw [dropWhile_none]
    · simp
    · intro c hc
      have := hplain c (List.mem_reverse.mp hc)
      simp only [Bool.or_eq_false_iff] at this
      exact this.2
  unfold fromBase64url?
  simp only [String.toList_ofList]
  rw [hfilter, hdrop, JOSE.Base64Url.decode_encode]
  simp only [Option.map_some, List.map_map]
  congr 1
  conv => rhs; rw [← List.map_id bs]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp, UInt8.toNat_ofNat', id]
  have := h b hb
  omega

end L4Factoidal.EXPath.Binary
