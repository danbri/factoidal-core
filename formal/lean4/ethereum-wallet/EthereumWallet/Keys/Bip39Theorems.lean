import EthereumWallet.Keys.Bip39

/-!
# BIP-39: the sentence-level theorems

`parse_generate` and `parse_sound` together say that `parse` accepts exactly the
sentences `generate` produces, and returns the entropy they were generated from.
The axioms each theorem rests on are printed at the end of this file.
-/

namespace EthereumWallet.Keys.Bip39

theorem wordChars_no_space (i : Nat) : ∀ ch ∈ wordChars i, ch ≠ ' ' :=
  codeChars_no_space 8 _ [] (by simp)

theorem wordChars_length (i : Nat) : (wordChars i).length ≤ 8 := by
  have := codeChars_length 8 (nth English.codes i) []
  simp only [List.length_nil, Nat.add_zero] at this
  exact this

/-- Kind: round trip.
    Says: for entropy of 16, 20, 24, 28 or 32 bytes (the only lengths `generate` accepts),
    parsing the generated sentence returns exactly that entropy.
    Does not say: that `sha256` is SHA-256, or anything about timing or memory hygiene. -/
theorem parse_generate (entropy : ByteArray) (sentence : String)
    (h : generate entropy = .ok sentence) : parse sentence = .ok entropy := by
  unfold generate at h
  by_cases hv : entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32
  · have hg := generateWords_ok entropy hv
    rw [hg] at h
    injection h with h
    subst h
    have hl := size_eq_length entropy
    have hlen : ((encodeIndices entropy.data.toList).map wordChars).length
        = 3 * (entropy.size / 4) := by
      rw [List.length_map, encodeIndices_length, hl]
    have hne : (encodeIndices entropy.data.toList).map wordChars ≠ [] := by
      intro hnil
      rw [hnil] at hlen
      simp only [List.length_nil] at hlen
      omega
    have hsp : ∀ w ∈ (encodeIndices entropy.data.toList).map wordChars, ∀ ch ∈ w, ch ≠ ' ' := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
      exact wordChars_no_space i
    have h8 : ∀ w ∈ (encodeIndices entropy.data.toList).map wordChars, w.length ≤ 8 := by
      intro w hw
      rcases List.mem_map.mp hw with ⟨i, _, rfl⟩
      exact wordChars_length i
    have hjl := joinWords_length _ h8
    unfold parse
    rw [String.toList_ofList, if_neg (by unfold maxSentenceChars; omega), split_join _ hne hsp]
    exact parseWords_generateWords entropy _ hg
  · unfold generateWords at h
    rw [if_neg hv] at h
    cases h

/-- Kind: refusal.
    Says: entropy that is not 16, 20, 24, 28 or 32 bytes is refused with its length.
    Does not say: that the entropy is random; that is the host's duty. -/
theorem generate_refuses_length (entropy : ByteArray)
    (h : ¬ (entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32)) :
    generate entropy = .error (.entropyLength entropy.size) := by
  unfold generate generateWords
  rw [if_neg h]

/-- Kind: totality on valid input.
    Says: every entropy of a valid length has a mnemonic. -/
theorem generate_accepts (entropy : ByteArray)
    (h : entropy.size % 4 = 0 ∧ 16 ≤ entropy.size ∧ entropy.size ≤ 32) :
    ∃ sentence, generate entropy = .ok sentence := by
  unfold generate
  rw [generateWords_ok entropy h]
  exact ⟨_, rfl⟩

/-- Kind: refusal (resource bound).
    Says: a sentence of more than 512 characters is refused before it is split.
    Does not say: that building the character list is free (it is linear in the input). -/
theorem parse_too_long (sentence : String) (h : maxSentenceChars < sentence.toList.length) :
    parse sentence = .error .sentenceTooLong := by
  unfold parse
  rw [if_pos h]

/-- Kind: refusal.
    Says: more than 24 words are refused before any word is looked up. -/
theorem parseWords_too_many (ws : List (List Char)) (h : 24 < ws.length) :
    parseWords ws = .error (.wordCount ws.length) := by
  unfold parseWords
  rw [if_pos h]

/-- Kind: refusal.
    Says: if any word is not in the list, nothing is accepted.
    Does not say: which word (the caller can ask `wordIndex?` per word). -/
theorem parseWords_unknown (ws : List (List Char)) (h : lookupAll ws = none)
    (hlen : ws.length ≤ 24) : parseWords ws = .error .unknownWord := by
  unfold parseWords
  rw [if_neg (by omega), h]

theorem parseWords_sound (ws : List (List Char)) (entropy : ByteArray)
    (h : parseWords ws = .ok entropy) : generateWords entropy = .ok ws := by
  by_cases hl : 24 < ws.length
  · rw [parseWords_too_many ws hl] at h; cases h
  · cases hlk : lookupAll ws with
    | none => rw [parseWords_unknown ws hlk (by omega)] at h; cases h
    | some idx =>
      rw [parseWords_of_lookup ws idx (by omega) hlk] at h
      cases hd : decodeIndices idx with
      | error e => rw [hd] at h; cases h
      | ok bytes =>
        rw [hd] at h
        have he : entropy = ⟨⟨bytes⟩⟩ := by injection h with h; exact h.symm
        subst he
        have ⟨henc, hv⟩ := encode_decode idx bytes hd
        have hws := lookupAll_sound ws idx hlk
        have hsz : (ByteArray.mk (Array.mk bytes)).size = bytes.length := rfl
        unfold generateWords
        rw [if_pos (by rw [hsz]; exact hv)]
        show Except.ok ((encodeIndices bytes).map wordChars) = Except.ok ws
        rw [henc, hws]

theorem join_split : ∀ (cs : List Char), joinWords (splitWords cs) = cs
  | [] => rfl
  | c :: t => by
    have ih := join_split t
    cases hs : splitWords t with
    | nil => exact absurd hs (splitWords_ne_nil t)
    | cons w ws =>
      rw [hs] at ih
      by_cases hc : c = ' '
      · simp [splitWords, hc, hs, joinWords, ih]
      · cases ws with
        | nil =>
          simp only [joinWords] at ih
          simp [splitWords, hc, hs, joinWords, ih]
        | cons w2 ws' =>
          simp only [joinWords] at ih
          simp [splitWords, hc, hs, joinWords, ih]

/-- Kind: soundness.
    Says: whatever `parse` accepts is exactly the sentence `generate` produces for the
    entropy returned: right words, right checksum, single spaces, lower case, nothing extra.
    With `parse_generate`: `parse s = .ok e` if and only if `generate e = .ok s`.
    Does not say: that sentences with other spacing or case, which other tools may accept,
    are wrong; they are refused here and the caller may normalise first. -/
theorem parse_sound (sentence : String) (entropy : ByteArray)
    (h : parse sentence = .ok entropy) : generate entropy = .ok sentence := by
  unfold parse at h
  by_cases hl : maxSentenceChars < sentence.toList.length
  · rw [if_pos hl] at h; cases h
  · rw [if_neg hl] at h
    unfold generate
    rw [parseWords_sound _ _ h]
    show Except.ok (String.ofList (joinWords (splitWords sentence.toList))) = Except.ok sentence
    rw [join_split, String.ofList_toList]

/-- Kind: refusal.
    Says: a sentence whose words are all known but whose checksum bits do not match is
    refused (stated on the word indices `lookupAll` returns). -/
theorem parseWords_checksum (ws : List (List Char)) (idx : List Nat) (entropy : ByteArray)
    (hlk : lookupAll ws = some idx)
    (hsum : checksumBits idx ≠ checksumOf (bytesOfIndices idx) (idx.length / 3)) :
    parseWords ws ≠ .ok entropy := by
  intro h
  by_cases hl : 24 < ws.length
  · rw [parseWords_too_many ws hl] at h; cases h
  · rw [parseWords_of_lookup ws idx (by omega) hlk] at h
    cases hd : decodeIndices idx with
    | error e => rw [hd] at h; cases h
    | ok bytes => exact decodeIndices_checksum idx bytes hsum hd

end EthereumWallet.Keys.Bip39

open EthereumWallet.Keys.Bip39 in
#print axioms parse_generate
open EthereumWallet.Keys.Bip39 in
#print axioms parse_sound
open EthereumWallet.Keys.Bip39 in
#print axioms generate_refuses_length
open EthereumWallet.Keys.Bip39 in
#print axioms generate_accepts
open EthereumWallet.Keys.Bip39 in
#print axioms parse_too_long
open EthereumWallet.Keys.Bip39 in
#print axioms parseWords_too_many
open EthereumWallet.Keys.Bip39 in
#print axioms parseWords_unknown
open EthereumWallet.Keys.Bip39 in
#print axioms parseWords_checksum
open EthereumWallet.Keys.Bip39 in
#print axioms decodeIndices_checksum
open EthereumWallet.Keys.Bip39 in
#print axioms decodeIndices_count
open EthereumWallet.Keys.Bip39 in
#print axioms decode_encode
open EthereumWallet.Keys.Bip39 in
#print axioms encode_decode
open EthereumWallet.Keys.Bip39 in
#print axioms wordIndex_wordChars
open EthereumWallet.Keys.Bip39 in
#print axioms wordIndex?_sound
open EthereumWallet.Keys.Bip39 in
#print axioms codes_sorted
open EthereumWallet.Keys.Bip39 in
#print axioms lookupAll_eq_fast
open EthereumWallet.Keys.Bip39 in
#print axioms joinWords_eq_fast
open EthereumWallet.Keys.Bip39 in
#print axioms splitWords_eq_fast
