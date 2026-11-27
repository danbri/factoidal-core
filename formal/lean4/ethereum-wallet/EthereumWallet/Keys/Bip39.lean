import L4Factoidal.Crypto.SHA2
import EthereumWallet.Keys.Bip39English
import EthereumWallet.Keys.Risk

/-!
# BIP-39 mnemonics (English): entropy to words and back

Entropy of 16, 20, 24, 28 or 32 bytes, a checksum of the first `ENT/32` bits of its
SHA-256, 11-bit groups, one word per group (BIP-39, "Generating the mnemonic").

The entropy is an input. Nothing here makes random numbers: the host supplies
operating-system random bytes and this module refuses any other length.

Layout, so that the theorems are about the code that runs:

* numbers: `toDigits` / `fromDigits` (big-endian digits in a base), with both round trips proved;
* words: a word is the list of its characters; the wordlist is 2048 numbers
  (`Bip39English.lean`, generated from the published file), and a word's number is its
  letters read as base-27 digits. `wordIndex?` looks a word up by number and accepts it
  only if the number spells exactly that word;
* sentences: words joined by one space (U+0020). `parse` is strict: one space between
  words, lower case, nothing before or after.

What is proved here (see `Bip39Theorems.lean` for the list with axioms): `parse` after
`generate` returns the entropy, for every valid length; wrong lengths, wrong word counts,
unknown words and checksum mismatches are refused; whatever `parse` accepts is exactly
what `generate` produces for the entropy it returns.

Not proved: that `sha256` is SHA-256 (tested against published vectors), and nothing about
timing. The entry points `generate`, `parse` and `isValid` take the risk token of
`Keys/Risk.lean`; the functions they are built from are internal and take none. Not constant-time: the entropy passes through `Nat` arithmetic (GMP, variable-time)
and list operations whose timing depends on the data. The entropy, the indices and the
words are ordinary immutable heap values; they are freed by reference counting when the
caller drops them and are not zeroised.
-/

namespace EthereumWallet.Keys.Bip39

open L4Factoidal.Crypto (sha256)

inductive Error where
  /-- Entropy must be 16, 20, 24, 28 or 32 bytes. -/
  | entropyLength (bytes : Nat)
  /-- A mnemonic has 12, 15, 18, 21 or 24 words. -/
  | wordCount (words : Nat)
  /-- The sentence is longer than any valid mnemonic can be. -/
  | sentenceTooLong
  /-- Some word is not in the wordlist. -/
  | unknownWord
  /-- A word index of 2048 or more (cannot come from a word). -/
  | indexRange
  /-- The checksum bits do not match the entropy. -/
  | checksum
  /-- A passphrase or mnemonic with non-ASCII bytes needs Unicode NFKD first. -/
  | notAscii
  deriving DecidableEq, Repr

/-! ## Digits in a base -/

/-- The `k` low digits of `v` in base `b`, most significant first, in front of `acc`.
Structural and tail recursive on `k`. -/
def toDigits (b : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | k + 1, v, acc => toDigits b k (v / b) (v % b :: acc)

/-- The number spelled by digits, most significant first. -/
def fromDigits (b : Nat) (l : List Nat) : Nat := l.foldl (fun a d => a * b + d) 0

/-- Little-endian value, used only in proofs (no code is generated for it). -/
noncomputable def valLE (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: t => d + b * valLE b t

theorem toDigits_length (b : Nat) : ∀ (k v : Nat) (acc : List Nat),
    (toDigits b k v acc).length = k + acc.length := by
  intro k
  induction k with
  | zero => intro v acc; simp [toDigits]
  | succ k ih => intro v acc; simp only [toDigits, ih, List.length_cons]; omega

theorem toDigits_lt (b : Nat) (hb : 0 < b) : ∀ (k v : Nat) (acc : List Nat),
    (∀ d ∈ acc, d < b) → ∀ d ∈ toDigits b k v acc, d < b := by
  intro k
  induction k with
  | zero => intro v acc h; simpa [toDigits] using h
  | succ k ih =>
    intro v acc h
    simp only [toDigits]
    apply ih
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact Nat.mod_lt _ hb
    · exact h d hd

theorem fromDigits_toDigits_aux (b : Nat) : ∀ (k v : Nat) (acc : List Nat), v < b ^ k →
    (toDigits b k v acc).foldl (fun a d => a * b + d) 0 = acc.foldl (fun a d => a * b + d) v := by
  intro k
  induction k with
  | zero =>
    intro v acc h
    have hv : v = 0 := by simpa using h
    subst hv
    rfl
  | succ k ih =>
    intro v acc h
    have hdiv : v / b < b ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm] at h
      exact Nat.div_lt_of_lt_mul h
    have hsplit : v / b * b + v % b = v := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod v b
    simp only [toDigits]
    rw [ih (v / b) (v % b :: acc) hdiv]
    simp only [List.foldl_cons, hsplit]

/-- Kind: round trip.
    Says: reading back the `k` digits of a number below `b ^ k` gives the number.
    Does not say: anything for larger numbers (their high digits are dropped). -/
theorem fromDigits_toDigits (b k v : Nat) (h : v < b ^ k) :
    fromDigits b (toDigits b k v []) = v := by
  unfold fromDigits
  rw [fromDigits_toDigits_aux b k v [] h]
  rfl

theorem toDigits_valLE (b : Nat) (hb : 0 < b) : ∀ (r : List Nat) (acc : List Nat),
    (∀ d ∈ r, d < b) → toDigits b r.length (valLE b r) acc = r.reverse ++ acc := by
  intro r
  induction r with
  | nil => intro acc _; simp [toDigits, valLE]
  | cons d t ih =>
    intro acc h
    have hd : d < b := h d (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x < b := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have h1 : (d + b * valLE b t) / b = valLE b t := by
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hd, Nat.zero_add]
    have h2 : (d + b * valLE b t) % b = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    simp only [List.length_cons, toDigits, valLE, h1, h2]
    rw [ih (d :: acc) ht]
    simp

theorem valLE_snoc (b : Nat) : ∀ (r : List Nat) (d : Nat),
    valLE b (r ++ [d]) = valLE b r + b ^ r.length * d := by
  intro r
  induction r with
  | nil => intro d; simp [valLE]
  | cons x t ih =>
    intro d
    simp only [List.cons_append, valLE, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, ← Nat.mul_assoc, Nat.mul_comm b (b ^ t.length)]

theorem foldl_eq_valLE (b : Nat) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun a d => a * b + d) a = a * b ^ l.length + valLE b l.reverse := by
  intro l
  induction l with
  | nil => intro a; simp [valLE]
  | cons d t ih =>
    intro a
    simp only [List.foldl_cons, ih, List.reverse_cons, valLE_snoc, List.length_cons,
      List.length_reverse, Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm b (b ^ t.length), Nat.mul_comm d (b ^ t.length)]
    omega

/-- Kind: round trip.
    Says: the digits of the number spelled by `l` (all digits below the base) are `l`.
    Does not say: anything when some digit is out of range. -/
theorem toDigits_fromDigits (b : Nat) (hb : 0 < b) (l : List Nat) (h : ∀ d ∈ l, d < b) :
    toDigits b l.length (fromDigits b l) [] = l := by
  have key := toDigits_valLE b hb l.reverse [] (by simpa using h)
  unfold fromDigits
  rw [foldl_eq_valLE]
  simpa using key

theorem valLE_lt (b : Nat) : ∀ (r : List Nat), (∀ d ∈ r, d < b) → valLE b r < b ^ r.length := by
  intro r
  induction r with
  | nil => intro _; simp [valLE]
  | cons d t ih =>
    intro h
    have hd : d < b := h d (List.mem_cons_self ..)
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hm : b * (valLE b t + 1) ≤ b * b ^ t.length := Nat.mul_le_mul_left b ht
    rw [Nat.mul_succ] at hm
    simp only [valLE, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (b ^ t.length) b]
    omega

theorem fromDigits_lt (b : Nat) (l : List Nat) (h : ∀ d ∈ l, d < b) :
    fromDigits b l < b ^ l.length := by
  have key := valLE_lt b l.reverse (by simpa using h)
  unfold fromDigits
  rw [foldl_eq_valLE]
  simpa using key

theorem lt_pack {E c A B : Nat} (hE : E < A) (hc : c < B) : E * B + c < A * B := by
  have h1 : (E + 1) * B ≤ A * B := Nat.mul_le_mul_right B hE
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-! ## Words as numbers -/

/-- Digit to character: 1 to 26 are `a` to `z`; 0 is the character before `a`,
which no word contains (it keeps the map total and injective). -/
def digitChar (d : Nat) : Char := Char.ofNat (96 + d)

def charDigit (c : Char) : Nat := c.toNat - 96

/-- The characters of a word number, most significant letter first. `fuel` is the
largest word length (8 in the English list). Structural and tail recursive. -/
def codeChars : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, c, acc => if c = 0 then acc else codeChars fuel (c / 27) (digitChar (c % 27) :: acc)

/-- The number a character list spells in base 27. -/
def charsCode (w : List Char) : Nat := w.foldl (fun a ch => a * 27 + charDigit ch) 0

theorem charDigit_digitChar : ∀ d, d < 27 → charDigit (digitChar d) = d := by decide

theorem digitChar_ne_space : ∀ d, d < 27 → digitChar d ≠ ' ' := by decide

theorem charsCode_codeChars_aux : ∀ (fuel c : Nat) (acc : List Char), c < 27 ^ fuel →
    (codeChars fuel c acc).foldl (fun a ch => a * 27 + charDigit ch) 0
      = acc.foldl (fun a ch => a * 27 + charDigit ch) c := by
  intro fuel
  induction fuel with
  | zero =>
    intro c acc h
    have hc : c = 0 := by simpa using h
    subst hc
    rfl
  | succ fuel ih =>
    intro c acc h
    by_cases hc : c = 0
    · subst hc; simp [codeChars]
    · have hdiv : c / 27 < 27 ^ fuel := by
        rw [Nat.pow_succ, Nat.mul_comm] at h
        exact Nat.div_lt_of_lt_mul h
      have hsplit : c / 27 * 27 + c % 27 = c := by omega
      simp only [codeChars, if_neg hc]
      rw [ih (c / 27) _ hdiv]
      simp only [List.foldl_cons, charDigit_digitChar _ (Nat.mod_lt _ (by decide)), hsplit]

/-- Kind: round trip.
    Says: a number below `27 ^ fuel` is recovered from the characters it spells.
    Does not say: that every character list is the spelling of its number. -/
theorem charsCode_codeChars (fuel c : Nat) (h : c < 27 ^ fuel) :
    charsCode (codeChars fuel c []) = c := by
  unfold charsCode
  rw [charsCode_codeChars_aux fuel c [] h]
  rfl

theorem codeChars_no_space : ∀ (fuel c : Nat) (acc : List Char),
    (∀ ch ∈ acc, ch ≠ ' ') → ∀ ch ∈ codeChars fuel c acc, ch ≠ ' ' := by
  intro fuel
  induction fuel with
  | zero => intro c acc h; simpa [codeChars] using h
  | succ fuel ih =>
    intro c acc h
    by_cases hc : c = 0
    · simpa [codeChars, hc] using h
    · simp only [codeChars, if_neg hc]
      apply ih
      intro ch hch
      rcases List.mem_cons.mp hch with rfl | hch
      · exact digitChar_ne_space _ (Nat.mod_lt _ (by decide))
      · exact h ch hch

theorem codeChars_length : ∀ (fuel c : Nat) (acc : List Char),
    (codeChars fuel c acc).length ≤ fuel + acc.length := by
  intro fuel
  induction fuel with
  | zero => intro c acc; simp [codeChars]
  | succ fuel ih =>
    intro c acc
    by_cases hc : c = 0
    · simp only [codeChars, hc, if_true]; omega
    · simp only [codeChars, if_neg hc]
      have := ih (c / 27) (digitChar (c % 27) :: acc)
      simp only [List.length_cons] at this
      omega

/-! ## Lookup in a list of numbers -/

/-- Element `i`, or 0 past the end. -/
def nth : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => nth xs i

/-- Position of the first element equal to `c`, counting from `k`. Tail recursive. -/
def findIdx (c : Nat) : List Nat → Nat → Option Nat
  | [], _ => none
  | x :: xs, k => if x = c then some k else findIdx c xs (k + 1)

/-- `prev < key x₀ < key x₁ < ...` -/
def incKeys (key : Nat → Nat) (prev : Nat) : List Nat → Bool
  | [] => true
  | x :: t => decide (prev < key x) && incKeys key (key x) t

/-- The keys of the list are strictly increasing. -/
def sortedBy (key : Nat → Nat) : List Nat → Bool
  | [] => true
  | x :: t => incKeys key (key x) t

/-- Every element is below `b`. -/
def allLt (b : Nat) : List Nat → Bool
  | [] => true
  | x :: t => decide (x < b) && allLt b t

theorem incKeys_nth (key : Nat → Nat) : ∀ (l : List Nat) (prev j : Nat),
    incKeys key prev l = true → j < l.length → prev < key (nth l j) := by
  intro l
  induction l with
  | nil => intro prev j _ hj; simp at hj
  | cons x t ih =>
    intro prev j h hj
    simp only [incKeys, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := ih (key x) j h.2 (by simpa using hj)
      simp only [nth]
      omega

theorem findIdx_nth (key : Nat → Nat) : ∀ (l : List Nat) (k i : Nat),
    sortedBy key l = true → i < l.length → findIdx (nth l i) l k = some (k + i) := by
  intro l
  induction l with
  | nil => intro k i _ hi; simp at hi
  | cons x t ih =>
    intro k i hs hi
    cases i with
    | zero => simp [nth, findIdx]
    | succ i =>
      have hi' : i < t.length := by simpa using hi
      have hlt : key x < key (nth t i) := incKeys_nth key t (key x) i hs hi'
      have hne : x ≠ nth t i := by intro heq; rw [← heq] at hlt; omega
      have hst : sortedBy key t = true := by
        cases t with
        | nil => rfl
        | cons y t' =>
          simp only [sortedBy, incKeys, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
          exact hs.2
      have hnth : nth (x :: t) (i + 1) = nth t i := rfl
      have hf : findIdx (nth t i) (x :: t) k = findIdx (nth t i) t (k + 1) := by
        simp [findIdx, hne]
      rw [hnth, hf, ih (k + 1) i hst hi']
      congr 1
      omega

theorem allLt_nth (b : Nat) : ∀ (l : List Nat) (j : Nat),
    allLt b l = true → j < l.length → nth l j < b := by
  intro l
  induction l with
  | nil => intro j _ hj; simp at hj
  | cons x t ih =>
    intro j h hj
    simp only [allLt, Bool.and_eq_true, decide_eq_true_eq] at h
    cases j with
    | zero => exact h.1
    | succ j => exact ih j h.2 (by simpa using hj)

/-! ## The English wordlist -/

/-- Left-align a word number to eight base-27 digits: then the order of numbers is the
alphabetical order of words. Used only to check the list is sorted. -/
def leftAlign : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c => if c < 27 ^ 7 then leftAlign fuel (c * 27) else c

theorem codes_length : English.codes.length = 2048 := by decide +kernel

/-- Kind: data check (kernel evaluation over the 2048 numbers).
    Says: the wordlist is strictly sorted (alphabetically), so no word occurs twice.
    Does not say: that the numbers are the published words (the test executable
    re-spells the list and compares its SHA-256 with the published file's). -/
theorem codes_sorted : sortedBy (leftAlign 8) English.codes = true := by decide +kernel

/-- Kind: data check. Says: every word number is below `27 ^ 8` (at most eight letters). -/
theorem codes_lt : allLt (27 ^ 8) English.codes = true := by decide +kernel

/-- The characters of word `i` (0 to 2047). -/
def wordChars (i : Nat) : List Char := codeChars 8 (nth English.codes i) []

/-- The index of a word, if it is exactly a word of the list. -/
def wordIndex? (w : List Char) : Option Nat :=
  if codeChars 8 (charsCode w) [] = w then findIdx (charsCode w) English.codes 0 else none

/-- Kind: round trip.
    Says: every word of the list is found at its own index.
    Does not say: what `wordIndex?` does on other strings (see `wordIndex?_sound`). -/
theorem wordIndex_wordChars (i : Nat) (h : i < 2048) : wordIndex? (wordChars i) = some i := by
  have hlen : i < English.codes.length := by rw [codes_length]; exact h
  have hc : charsCode (wordChars i) = nth English.codes i :=
    charsCode_codeChars 8 _ (allLt_nth _ _ i codes_lt hlen)
  unfold wordIndex?
  rw [hc]
  have hw : codeChars 8 (nth English.codes i) [] = wordChars i := rfl
  rw [if_pos hw, findIdx_nth (leftAlign 8) _ 0 i codes_sorted hlen]
  simp

theorem findIdx_sound (c : Nat) : ∀ (l : List Nat) (k i : Nat),
    findIdx c l k = some i → k ≤ i ∧ i - k < l.length ∧ nth l (i - k) = c := by
  intro l
  induction l with
  | nil => intro k i h; simp [findIdx] at h
  | cons x t ih =>
    intro k i h
    by_cases hx : x = c
    · simp only [findIdx, if_pos hx, Option.some.injEq] at h
      subst h
      simp [nth, hx]
    · simp only [findIdx, if_neg hx] at h
      have ⟨h1, h2, h3⟩ := ih (k + 1) i h
      have hik : i - k = (i - (k + 1)) + 1 := by omega
      refine ⟨by omega, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [hik]; simpa [nth] using h3

/-- Kind: soundness.
    Says: an accepted word is, character for character, the list's word at the returned
    index, and the index is below 2048.
    Does not say: anything about case folding or Unicode look-alikes (they are refused). -/
theorem wordIndex?_sound (w : List Char) (i : Nat) (h : wordIndex? w = some i) :
    i < 2048 ∧ wordChars i = w := by
  unfold wordIndex? at h
  by_cases hw : codeChars 8 (charsCode w) [] = w
  · rw [if_pos hw] at h
    have ⟨_, h2, h3⟩ := findIdx_sound _ _ 0 i h
    simp only [Nat.sub_zero] at h2 h3
    refine ⟨by rw [← codes_length]; exact h2, ?_⟩
    unfold wordChars
    rw [h3]
    exact hw
  · rw [if_neg hw] at h
    cases h

/-! ## Entropy to indices and back -/

/-- The first `cs` bits of SHA-256 of the entropy, as a number. -/
def checksumOf (bytes : List UInt8) (cs : Nat) : Nat :=
  ((sha256 ⟨⟨bytes⟩⟩).get! 0).toNat / 2 ^ (8 - cs)

/-- The word indices for entropy bytes: entropy bits, then `length / 4` checksum bits,
cut into 11-bit groups. -/
def encodeIndices (bytes : List UInt8) : List Nat :=
  toDigits 2048 (3 * (bytes.length / 4))
    (fromDigits 256 (bytes.map UInt8.toNat) * 2 ^ (bytes.length / 4)
      + checksumOf bytes (bytes.length / 4)) []

/-- The entropy bytes spelled by word indices (checksum bits dropped). -/
def bytesOfIndices (idx : List Nat) : List UInt8 :=
  (toDigits 256 (4 * (idx.length / 3)) (fromDigits 2048 idx / 2 ^ (idx.length / 3)) []).map
    UInt8.ofNat

/-- The checksum bits carried by word indices. -/
def checksumBits (idx : List Nat) : Nat := fromDigits 2048 idx % 2 ^ (idx.length / 3)

/-- Word indices to entropy, checking the count, the index range and the checksum. -/
def decodeIndices (idx : List Nat) : Except Error (List UInt8) :=
  if idx.length % 3 = 0 ∧ 12 ≤ idx.length ∧ idx.length ≤ 24 then
    if ∀ i ∈ idx, i < 2048 then
      if checksumBits idx = checksumOf (bytesOfIndices idx) (idx.length / 3) then
        .ok (bytesOfIndices idx)
      else .error .checksum
    else .error .indexRange
  else .error (.wordCount idx.length)

theorem encodeIndices_length (bytes : List UInt8) :
    (encodeIndices bytes).length = 3 * (bytes.length / 4) := by
  simp [encodeIndices, toDigits_length]

theorem encodeIndices_lt (bytes : List UInt8) : ∀ i ∈ encodeIndices bytes, i < 2048 := by
  unfold encodeIndices
  exact toDigits_lt 2048 (by decide) _ _ _ (by simp)

theorem bytes_digits_lt (bytes : List UInt8) : ∀ d ∈ bytes.map UInt8.toNat, d < 256 := by
  intro d hd
  rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
  exact x.toNat_lt

theorem checksumOf_lt (bytes : List UInt8) (t : Nat) (ht : t ≤ 8) : checksumOf bytes t < 2 ^ t := by
  unfold checksumOf
  apply Nat.div_lt_of_lt_mul
  have hb : ((sha256 ⟨⟨bytes⟩⟩).get! 0).toNat < 256 := UInt8.toNat_lt _
  have hp : 2 ^ (8 - t) * 2 ^ t = 256 := by
    rw [← Nat.pow_add]
    have : 8 - t + t = 8 := by omega
    rw [this]
  omega

theorem pow_pack (t : Nat) : 256 ^ (4 * t) * 2 ^ t = 2048 ^ (3 * t) := by
  have h1 : (256 : Nat) = 2 ^ 8 := by decide
  have h2 : (2048 : Nat) = 2 ^ 11 := by decide
  rw [h1, h2, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

/-- Kind: round trip (numbers).
    Says: for entropy of 16, 20, 24, 28 or 32 bytes, decoding the indices that encoding
    produced gives the entropy back.
    Does not say: that `sha256` is SHA-256; the proof uses only that both sides call
    the same function. -/
theorem decode_encode (bytes : List UInt8)
    (hs : bytes.length % 4 = 0 ∧ 16 ≤ bytes.length ∧ bytes.length ≤ 32) :
    decodeIndices (encodeIndices bytes) = .ok bytes := by
  have hlen := encodeIndices_length bytes
  have hq : (encodeIndices bytes).length / 3 = bytes.length / 4 := by rw [hlen]; omega
  have h4 : 4 * (bytes.length / 4) = bytes.length := by omega
  have hE : fromDigits 256 (bytes.map UInt8.toNat) < 256 ^ (4 * (bytes.length / 4)) := by
    have := fromDigits_lt 256 _ (bytes_digits_lt bytes)
    rw [List.length_map] at this
    rw [h4]; exact this
  have hc := checksumOf_lt bytes (bytes.length / 4) (by omega)
  have hm : fromDigits 256 (bytes.map UInt8.toNat) * 2 ^ (bytes.length / 4)
      + checksumOf bytes (bytes.length / 4) < 2048 ^ (3 * (bytes.length / 4)) := by
    rw [← pow_pack]; exact lt_pack hE hc
  have hfrom : fromDigits 2048 (encodeIndices bytes)
      = fromDigits 256 (bytes.map UInt8.toNat) * 2 ^ (bytes.length / 4)
        + checksumOf bytes (bytes.length / 4) := by
    unfold encodeIndices
    exact fromDigits_toDigits 2048 _ _ hm
  have hpos : 0 < 2 ^ (bytes.length / 4) := Nat.pow_pos (by decide)
  have hbytes : bytesOfIndices (encodeIndices bytes) = bytes := by
    unfold bytesOfIndices
    rw [hq, hfrom, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hc, Nat.zero_add,
      h4]
    have key := toDigits_fromDigits 256 (by decide) _ (bytes_digits_lt bytes)
    rw [List.length_map] at key
    rw [key, List.map_map]
    have hid : (UInt8.ofNat ∘ UInt8.toNat) = id := by funext x; simp
    rw [hid, List.map_id]
  have hbits : checksumBits (encodeIndices bytes) = checksumOf bytes (bytes.length / 4) := by
    unfold checksumBits
    rw [hq, hfrom, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  unfold decodeIndices
  rw [if_pos (by rw [hlen]; omega), if_pos (encodeIndices_lt bytes), hbytes, hbits, hq,
    if_pos rfl]

/-- Kind: refusal.
    Says: indices whose checksum bits differ from the checksum of the entropy they spell
    are never accepted.
    Does not say: how likely a random error is to pass (1 in 16 to 1 in 256 by length). -/
theorem decodeIndices_checksum (idx : List Nat) (bytes : List UInt8)
    (h : checksumBits idx ≠ checksumOf (bytesOfIndices idx) (idx.length / 3)) :
    decodeIndices idx ≠ .ok bytes := by
  unfold decodeIndices
  rw [if_neg h]
  intro hok
  split at hok
  · split at hok <;> cases hok
  · cases hok

/-- Kind: refusal.
    Says: a word count other than 12, 15, 18, 21 or 24 is refused with `wordCount`. -/
theorem decodeIndices_count (idx : List Nat)
    (h : ¬ (idx.length % 3 = 0 ∧ 12 ≤ idx.length ∧ idx.length ≤ 24)) :
    decodeIndices idx = .error (.wordCount idx.length) := by
  unfold decodeIndices
  rw [if_neg h]

/-- Kind: soundness (numbers).
    Says: accepted indices are exactly the encoding of the entropy returned, and that
    entropy has a valid length. So `decodeIndices` accepts nothing `encodeIndices` does not produce.
    Does not say: anything about SHA-256 itself. -/
theorem encode_decode (idx : List Nat) (bytes : List UInt8) (h : decodeIndices idx = .ok bytes) :
    encodeIndices bytes = idx ∧ bytes.length % 4 = 0 ∧ 16 ≤ bytes.length ∧ bytes.length ≤ 32 := by
  unfold decodeIndices at h
  by_cases hcount : idx.length % 3 = 0 ∧ 12 ≤ idx.length ∧ idx.length ≤ 24
  · rw [if_pos hcount] at h
    by_cases hrange : ∀ i ∈ idx, i < 2048
    · rw [if_pos hrange] at h
      by_cases hsum : checksumBits idx = checksumOf (bytesOfIndices idx) (idx.length / 3)
      · rw [if_pos hsum] at h
        have hb : bytesOfIndices idx = bytes := by injection h
        have hblen : bytes.length = 4 * (idx.length / 3) := by
          rw [← hb]; simp [bytesOfIndices, toDigits_length]
        have hq : bytes.length / 4 = idx.length / 3 := by omega
        have hw : 3 * (idx.length / 3) = idx.length := by omega
        have hpos : 0 < 2 ^ (idx.length / 3) := Nat.pow_pos (by decide)
        have hM : fromDigits 2048 idx < 2048 ^ (3 * (idx.length / 3)) := by
          rw [hw]; exact fromDigits_lt 2048 idx hrange
        have hdiv : fromDigits 2048 idx / 2 ^ (idx.length / 3) < 256 ^ (4 * (idx.length / 3)) := by
          apply Nat.div_lt_of_lt_mul
          rw [Nat.mul_comm, pow_pack]; exact hM
        have hval : fromDigits 256 (bytes.map UInt8.toNat)
            = fromDigits 2048 idx / 2 ^ (idx.length / 3) := by
          rw [← hb]
          unfold bytesOfIndices
          rw [List.map_map]
          have hdl : ∀ d ∈ toDigits 256 (4 * (idx.length / 3))
              (fromDigits 2048 idx / 2 ^ (idx.length / 3)) [], d < 256 :=
            toDigits_lt 256 (by decide) _ _ _ (by simp)
          have hmap : List.map (UInt8.toNat ∘ UInt8.ofNat)
              (toDigits 256 (4 * (idx.length / 3)) (fromDigits 2048 idx / 2 ^ (idx.length / 3)) [])
              = toDigits 256 (4 * (idx.length / 3))
                (fromDigits 2048 idx / 2 ^ (idx.length / 3)) [] := by
            conv => rhs; rw [← List.map_id (toDigits 256 (4 * (idx.length / 3))
              (fromDigits 2048 idx / 2 ^ (idx.length / 3)) [])]
            apply List.map_congr_left
            intro d hd
            have := hdl d hd
            simp only [Function.comp, id]
            rw [UInt8.toNat_ofNat']
            omega
          rw [hmap]
          exact fromDigits_toDigits 256 _ _ hdiv
        refine ⟨?_, by omega, by omega, by omega⟩
        unfold encodeIndices
        rw [hq, hval]
        have hck : checksumOf bytes (idx.length / 3) = fromDigits 2048 idx % 2 ^ (idx.length / 3) := by
          rw [← hb]; exact hsum.symm
        have hsplit : fromDigits 2048 idx / 2 ^ (idx.length / 3) * 2 ^ (idx.length / 3)
            + fromDigits 2048 idx % 2 ^ (idx.length / 3) = fromDigits 2048 idx := by
          rw [Nat.mul_comm]; exact Nat.div_add_mod _ _
        rw [hck, hsplit, hw]
        exact toDigits_fromDigits 2048 (by decide) idx hrange
      · rw [if_neg hsum] at h; cases h
    · rw [if_neg hrange] at h; cases h
  · rw [if_neg hcount] at h; cases h

/-! ## Words -/

/-- Look every word up. This is the plain definition the theorems are about; the compiler
emits the loop `lookupAllFast` in its place (`lookupAll_eq_fast`). -/
def lookupAll : List (List Char) → Option (List Nat)
  | [] => some []
  | w :: t =>
    match wordIndex? w, lookupAll t with
    | some i, some r => some (i :: r)
    | _, _ => none

/-- `lookupAll` as a loop; `acc` holds the indices so far, reversed. -/
def lookupGo : List (List Char) → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | w :: t, acc =>
    match wordIndex? w with
    | some i => lookupGo t (i :: acc)
    | none => none

theorem lookupGo_eq : ∀ (ws : List (List Char)) (acc : List Nat),
    lookupGo ws acc = (lookupAll ws).map (acc.reverse ++ ·) := by
  intro ws
  induction ws with
  | nil => intro acc; simp [lookupGo, lookupAll]
  | cons w t ih =>
    intro acc
    cases hw : wordIndex? w with
    | none => cases ht : lookupAll t <;> simp [lookupGo, lookupAll, hw, ht]
    | some i => cases ht : lookupAll t <;> simp [lookupGo, lookupAll, hw, ih, ht]

def lookupAllFast (ws : List (List Char)) : Option (List Nat) := lookupGo ws []

/-- Kind: compiled form (`csimp`).
    Says: the loop the compiler emits for `lookupAll` returns the same value, for every input.
    Does not say: anything about the compiler itself, which is trusted. -/
@[csimp] theorem lookupAll_eq_fast : @lookupAll = @lookupAllFast := by
  funext ws
  rw [lookupAllFast, lookupGo_eq]
  cases lookupAll ws <;> simp

theorem lookupAll_map : ∀ (l : List Nat), (∀ i ∈ l, i < 2048) →
    lookupAll (l.map wordChars) = some l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.map_cons, lookupAll,
      wordIndex_wordChars a (h a (List.mem_cons_self ..)),
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem lookupAll_sound : ∀ (ws : List (List Char)) (idx : List Nat),
    lookupAll ws = some idx → idx.map wordChars = ws := by
  intro ws
  induction ws with
  | nil => intro idx h; simp only [lookupAll, Option.some.injEq] at h; subst h; rfl
  | cons w t ih =>
    intro idx h
    simp only [lookupAll] at h
    cases hw : wordIndex? w with
    | none => rw [hw] at h; cases h
    | some i =>
      cases ht : lookupAll t with
      | none => rw [hw, ht] at h; cases h
      | some r =>
        rw [hw, ht] at h
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.map_cons, (wordIndex?_sound w i hw).2, ih r ht]

/-- The words of a mnemonic for the given entropy. -/
def generateWords (entropy : ByteArray) : Except Error (List (List Char)) :=
  if entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32 then
    .ok ((encodeIndices entropy.data.toList).map wordChars)
  else .error (.entropyLength entropy.size)

/-- Words to entropy. More than 24 words are refused before any lookup. -/
def parseWords (ws : List (List Char)) : Except Error ByteArray :=
  if 24 < ws.length then .error (.wordCount ws.length)
  else
    match lookupAll ws with
    | none => .error .unknownWord
    | some idx =>
      match decodeIndices idx with
      | .ok bytes => .ok ⟨⟨bytes⟩⟩
      | .error e => .error e

theorem parseWords_of_lookup (ws : List (List Char)) (idx : List Nat) (hlen : ws.length ≤ 24)
    (hl : lookupAll ws = some idx) :
    parseWords ws = (match decodeIndices idx with
      | .ok bytes => .ok ⟨⟨bytes⟩⟩
      | .error e => .error e) := by
  unfold parseWords
  rw [if_neg (by omega), hl]

theorem size_eq_length (b : ByteArray) : b.data.toList.length = b.size := by
  cases b; rfl

theorem generateWords_ok (entropy : ByteArray)
    (h : entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32) :
    generateWords entropy = .ok ((encodeIndices entropy.data.toList).map wordChars) := by
  unfold generateWords
  rw [if_pos h]

theorem parseWords_generateWords (entropy : ByteArray) (ws : List (List Char))
    (h : generateWords entropy = .ok ws) : parseWords ws = .ok entropy := by
  unfold generateWords at h
  by_cases hv : entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32
  · rw [if_pos hv] at h
    injection h with h
    subst h
    have hl := size_eq_length entropy
    have hlen := encodeIndices_length entropy.data.toList
    rw [parseWords_of_lookup _ _ (by rw [List.length_map, hlen, hl]; omega)
      (lookupAll_map _ (encodeIndices_lt _)), decode_encode _ (by rw [hl]; exact hv)]
  · rw [if_neg hv] at h
    cases h

/-! ## Sentences -/

/-- Words joined by single spaces. Plain definition; compiled as the loop `joinWordsFast`. -/
def joinWords : List (List Char) → List Char
  | [] => []
  | [w] => w
  | w :: w2 :: t => w ++ ' ' :: joinWords (w2 :: t)

/-- Split at every space. Plain definition; compiled as the loop `splitWordsFast`
(`splitWords_eq_fast`). `parse` also bounds the length first. -/
def splitWords : List Char → List (List Char)
  | [] => [[]]
  | c :: t =>
    if c = ' ' then [] :: splitWords t
    else
      match splitWords t with
      | [] => [[c]]
      | w :: ws => (c :: w) :: ws

theorem splitWords_ne_nil : ∀ (cs : List Char), splitWords cs ≠ []
  | [] => by simp [splitWords]
  | c :: t => by
    by_cases hc : c = ' '
    · simp [splitWords, hc]
    · cases hs : splitWords t with
      | nil => exact absurd hs (splitWords_ne_nil t)
      | cons w ws => simp [splitWords, hc, hs]

/-- `joinWords` as a loop; `acc` holds the characters so far, reversed. -/
def joinGo : List (List Char) → List Char → List Char
  | [], acc => acc.reverse
  | [w], acc => acc.reverse ++ w
  | w :: w2 :: t, acc => joinGo (w2 :: t) (' ' :: (w.reverse ++ acc))

theorem joinGo_eq : ∀ (ws : List (List Char)) (acc : List Char),
    joinGo ws acc = acc.reverse ++ joinWords ws
  | [], acc => by simp [joinGo, joinWords]
  | [w], acc => by simp [joinGo, joinWords]
  | w :: w2 :: t, acc => by simp [joinGo, joinGo_eq (w2 :: t), joinWords]

def joinWordsFast (ws : List (List Char)) : List Char := joinGo ws []

/-- Kind: compiled form (`csimp`). Says: the loop emitted for `joinWords` returns the same value. -/
@[csimp] theorem joinWords_eq_fast : @joinWords = @joinWordsFast := by
  funext ws
  simp [joinWordsFast, joinGo_eq]

/-- `splitWords` as a loop; `cur` is the current word and `acc` the finished words, reversed. -/
def splitGo : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: t, cur, acc =>
    if c = ' ' then splitGo t [] (cur.reverse :: acc) else splitGo t (c :: cur) acc

/-- Put `pre` in front of the first word. -/
def consHead (pre : List Char) : List (List Char) → List (List Char)
  | [] => [pre]
  | w :: ws => (pre ++ w) :: ws

theorem splitGo_eq : ∀ (cs cur : List Char) (acc : List (List Char)),
    splitGo cs cur acc = acc.reverse ++ consHead cur.reverse (splitWords cs) := by
  intro cs
  induction cs with
  | nil => intro cur acc; simp [splitGo, splitWords, consHead]
  | cons c t ih =>
    intro cur acc
    cases hs : splitWords t with
    | nil => exact absurd hs (splitWords_ne_nil t)
    | cons w ws =>
      by_cases hc : c = ' '
      · simp [splitGo, splitWords, hc, ih, hs, consHead]
      · simp [splitGo, splitWords, hc, ih, hs, consHead]

def splitWordsFast (cs : List Char) : List (List Char) := splitGo cs [] []

/-- Kind: compiled form (`csimp`).
    Says: the loop emitted for `splitWords` returns the same value, so splitting uses
    constant stack whatever the sentence length. -/
@[csimp] theorem splitWords_eq_fast : @splitWords = @splitWordsFast := by
  funext cs
  rw [splitWordsFast, splitGo_eq]
  cases hs : splitWords cs with
  | nil => exact absurd hs (splitWords_ne_nil cs)
  | cons w ws => simp [consHead]

theorem splitWords_word : ∀ (w : List Char), (∀ ch ∈ w, ch ≠ ' ') → splitWords w = [w] := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons c t ih =>
    intro h
    have hc : c ≠ ' ' := h c (List.mem_cons_self ..)
    simp only [splitWords, if_neg hc, ih (fun ch hch => h ch (List.mem_cons_of_mem _ hch))]

theorem splitWords_word_space : ∀ (w rest : List Char), (∀ ch ∈ w, ch ≠ ' ') →
    splitWords (w ++ ' ' :: rest) = w :: splitWords rest := by
  intro w
  induction w with
  | nil => intro rest _; simp [splitWords]
  | cons c t ih =>
    intro rest h
    have hc : c ≠ ' ' := h c (List.mem_cons_self ..)
    simp only [List.cons_append, splitWords, if_neg hc,
      ih rest (fun ch hch => h ch (List.mem_cons_of_mem _ hch))]

theorem split_join : ∀ (ws : List (List Char)), ws ≠ [] → (∀ w ∈ ws, ∀ ch ∈ w, ch ≠ ' ') →
    splitWords (joinWords ws) = ws
  | [], h, _ => absurd rfl h
  | [w], _, h => by
    simp only [joinWords]
    exact splitWords_word w (h w (List.mem_cons_self ..))
  | w :: w2 :: t, _, h => by
    have ih := split_join (w2 :: t) (by simp) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [joinWords]
    rw [splitWords_word_space w _ (h w (List.mem_cons_self ..)), ih]

theorem joinWords_length : ∀ (ws : List (List Char)), (∀ w ∈ ws, w.length ≤ 8) →
    (joinWords ws).length ≤ 9 * ws.length
  | [], _ => by simp [joinWords]
  | [w], h => by
    have := h w (List.mem_cons_self ..)
    simp only [joinWords, List.length_cons, List.length_nil]
    omega
  | w :: w2 :: t, h => by
    have ih := joinWords_length (w2 :: t) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h w (List.mem_cons_self ..)
    simp only [joinWords, List.length_append, List.length_cons] at ih ⊢
    omega

/-- No valid mnemonic is longer: 24 words of at most 8 letters and 23 spaces is 215. -/
def maxSentenceChars : Nat := 512

/-- The mnemonic sentence for the given entropy (16, 20, 24, 28 or 32 bytes). -/
def generate (_ : SecretRisk) (entropy : ByteArray) : Except Error String :=
  match generateWords entropy with
  | .ok ws => .ok (String.ofList (joinWords ws))
  | .error e => .error e

/-- A mnemonic sentence to its entropy. Strict: lower-case words of the English list,
one space between words, nothing else. -/
def parse (_ : SecretRisk) (sentence : String) : Except Error ByteArray :=
  if maxSentenceChars < sentence.toList.length then .error .sentenceTooLong
  else parseWords (splitWords sentence.toList)

/-- True when `sentence` is a valid English mnemonic. -/
def isValid (risk : SecretRisk) (sentence : String) : Bool :=
  match parse risk sentence with
  | .ok _ => true
  | .error _ => false

end EthereumWallet.Keys.Bip39
