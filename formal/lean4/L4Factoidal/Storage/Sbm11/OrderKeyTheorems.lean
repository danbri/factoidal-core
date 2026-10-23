/-
L4Factoidal.Storage.Sbm11.OrderKeyTheorems — ORDER BY on dictionary keys is
the reference ORDER BY for blank nodes, IRIs, `xsd:string` literals and
language-tagged literals whose lexical form holds no `0x00` (stage 1l of
docs/designissues/2026-10-12-parallel-block-scans.md;
https://github.com/danbri/factoidal/issues/961).

* `encN_cmp`, `char_cmp`: the unsigned byte order of the UTF-8 encodings of
  two characters (`String.utf8EncodeChar`) is the order of their code points;
  equal characters give equal encodings. Sixteen lemmas `cmpIJ`, one per pair
  of encoding lengths, each by `omega` on the code points.
* `flat_cmp`, `bytes_str`: the byte order of the UTF-8 bytes of two strings
  (`bytesOfString`, `String.toUTF8`) is `strCompare`, the code point order.
* `flat_sep_cmp`, `bytes_sep`: with no `0x00` byte in either string, the byte
  order of `string, 0x00, rest` is `strCompare` of the strings, then the
  order of the rests (the class-4 key: lexical form, `0x00`, language tag).
* `classify`: what `keyGroup? k = some g` says about the term of key `k`.
* `orderValue_keyOrder`: for two terms with keys `k₁`, `k₂` in groups `g₁`,
  `g₂`, `sparqlOrderValue` of their ORDER BY values is the order of `g₁` and
  `g₂`, and for one group `bytesCmp k₁ k₂`. Premises: the keys
  (`termKey?`) and the groups (`keyGroup?`); none states an order.
* `orderValue_error_term`, `orderValue_term_error`: an unbound variable (an
  error) comes before every term of the four groups.
* `keyGroupSlice?_eq`: the in-place check is `keyGroup?` of the key's bytes.

The id path (`IdQuery.orderKeysByKeysM?`) compares ids, and the ids of one
dictionary tag are ranks of the byte-sorted dictionary
(`DictTheorems.decodeDict_sorted`), so within a group the id order is
`bytesCmp` of the keys.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`. `decide
+kernel` evaluates the datatype IRI tests of two constants in the kernel.
-/
import L4Factoidal.Storage.Sbm11.OrderKey
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.TermCodecTheorems

namespace L4Factoidal.Storage.Sbm11.OrderKey

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage (bytesOfString)

/-! ## UTF-8 byte order is code point order -/

theorem u8lt (a b : Nat) : (UInt8.ofNat a < UInt8.ofNat b) ↔ a % 256 < b % 256 := by
  rw [UInt8.lt_iff_toNat_lt]; simp

theorem char_lt (c : Char) : c.val.toNat < 1114112 := by
  have := c.valid
  have e : c.toNat = c.val.toNat := rfl
  simp [UInt32.isValidChar, Nat.isValidChar] at this
  omega

/-- `String.utf8EncodeChar` of a code point given as a number. -/
def encN (v : Nat) : List UInt8 :=
  if v ≤ 127 then [UInt8.ofNat v]
  else if v ≤ 2047 then [UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)]
  else if v ≤ 65535 then
    [UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)]
  else
    [UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128), UInt8.ofNat (v / 64 % 64 + 128),
      UInt8.ofNat (v % 64 + 128)]

theorem encN_eq (c : Char) : String.utf8EncodeChar c = encN c.val.toNat := rfl

/-! The sixteen pairs of encoding lengths; in each, the bytes are compared
one at a time and `omega` decides every branch from the code points. -/

theorem cmp11 (v w : Nat) (s t : List UInt8) (hv : v ≤ 127) (hw : w ≤ 127) :
    bytesCmp ([UInt8.ofNat v] ++ s) ([UInt8.ofNat w] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp12 (v w : Nat) (s t : List UInt8) (hv : v ≤ 127) (hw : 127 < w ∧ w ≤ 2047) :
    bytesCmp ([UInt8.ofNat v] ++ s) ([UInt8.ofNat (w / 64 % 32 + 192), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp13 (v w : Nat) (s t : List UInt8) (hv : v ≤ 127) (hw : 2047 < w ∧ w ≤ 65535) :
    bytesCmp ([UInt8.ofNat v] ++ s) ([UInt8.ofNat (w / 4096 % 16 + 224), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp14 (v w : Nat) (s t : List UInt8) (hv : v ≤ 127) (hw : 65535 < w ∧ w < 1114112) :
    bytesCmp ([UInt8.ofNat v] ++ s) ([UInt8.ofNat (w / 262144 % 8 + 240), UInt8.ofNat (w / 4096 % 64 + 128), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp21 (v w : Nat) (s t : List UInt8) (hv : 127 < v ∧ v ≤ 2047) (hw : w ≤ 127) :
    bytesCmp ([UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat w] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp22 (v w : Nat) (s t : List UInt8) (hv : 127 < v ∧ v ≤ 2047) (hw : 127 < w ∧ w ≤ 2047) :
    bytesCmp ([UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 64 % 32 + 192), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp23 (v w : Nat) (s t : List UInt8) (hv : 127 < v ∧ v ≤ 2047) (hw : 2047 < w ∧ w ≤ 65535) :
    bytesCmp ([UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 4096 % 16 + 224), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp24 (v w : Nat) (s t : List UInt8) (hv : 127 < v ∧ v ≤ 2047) (hw : 65535 < w ∧ w < 1114112) :
    bytesCmp ([UInt8.ofNat (v / 64 % 32 + 192), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 262144 % 8 + 240), UInt8.ofNat (w / 4096 % 64 + 128), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp31 (v w : Nat) (s t : List UInt8) (hv : 2047 < v ∧ v ≤ 65535) (hw : w ≤ 127) :
    bytesCmp ([UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat w] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp32 (v w : Nat) (s t : List UInt8) (hv : 2047 < v ∧ v ≤ 65535) (hw : 127 < w ∧ w ≤ 2047) :
    bytesCmp ([UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 64 % 32 + 192), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp33 (v w : Nat) (s t : List UInt8) (hv : 2047 < v ∧ v ≤ 65535) (hw : 2047 < w ∧ w ≤ 65535) :
    bytesCmp ([UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 4096 % 16 + 224), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp34 (v w : Nat) (s t : List UInt8) (hv : 2047 < v ∧ v ≤ 65535) (hw : 65535 < w ∧ w < 1114112) :
    bytesCmp ([UInt8.ofNat (v / 4096 % 16 + 224), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 262144 % 8 + 240), UInt8.ofNat (w / 4096 % 64 + 128), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp41 (v w : Nat) (s t : List UInt8) (hv : 65535 < v ∧ v < 1114112) (hw : w ≤ 127) :
    bytesCmp ([UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat w] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp42 (v w : Nat) (s t : List UInt8) (hv : 65535 < v ∧ v < 1114112) (hw : 127 < w ∧ w ≤ 2047) :
    bytesCmp ([UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 64 % 32 + 192), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp43 (v w : Nat) (s t : List UInt8) (hv : 65535 < v ∧ v < 1114112) (hw : 2047 < w ∧ w ≤ 65535) :
    bytesCmp ([UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 4096 % 16 + 224), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem cmp44 (v w : Nat) (s t : List UInt8) (hv : 65535 < v ∧ v < 1114112) (hw : 65535 < w ∧ w < 1114112) :
    bytesCmp ([UInt8.ofNat (v / 262144 % 8 + 240), UInt8.ofNat (v / 4096 % 64 + 128), UInt8.ofNat (v / 64 % 64 + 128), UInt8.ofNat (v % 64 + 128)] ++ s) ([UInt8.ofNat (w / 262144 % 8 + 240), UInt8.ofNat (w / 4096 % 64 + 128), UInt8.ofNat (w / 64 % 64 + 128), UInt8.ofNat (w % 64 + 128)] ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  simp only [List.cons_append, List.nil_append, bytesCmp, u8lt]
  repeat' split
  all_goals first | rfl | omega

theorem encN_cmp (v w : Nat) (s t : List UInt8) (hv : v < 1114112) (hw : w < 1114112) :
    bytesCmp (encN v ++ s) (encN w ++ t) =
      (if v < w then -1 else if v = w then bytesCmp s t else 1) := by
  have rv : v ≤ 127 ∨ (127 < v ∧ v ≤ 2047) ∨ (2047 < v ∧ v ≤ 65535) ∨ (65535 < v ∧ v < 1114112) := by omega
  have rw' : w ≤ 127 ∨ (127 < w ∧ w ≤ 2047) ∨ (2047 < w ∧ w ≤ 65535) ∨ (65535 < w ∧ w < 1114112) := by omega
  unfold encN
  rcases rv with a | a | a | a <;> rcases rw' with b | b | b | b
  · rw [if_pos a, if_pos b]; exact cmp11 v w s t a b
  · rw [if_pos a, if_neg (by omega), if_pos (by omega)]; exact cmp12 v w s t a b
  · rw [if_pos a, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; exact cmp13 v w s t a b
  · rw [if_pos a, if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact cmp14 v w s t a b
  · rw [if_neg (by omega), if_pos (by omega), if_pos b]; exact cmp21 v w s t a b
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]; exact cmp22 v w s t a b
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact cmp23 v w s t a b
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact cmp24 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos b]; exact cmp31 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    exact cmp32 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    exact cmp33 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    exact cmp34 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos b]; exact cmp41 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    exact cmp42 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    exact cmp43 v w s t a b
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    exact cmp44 v w s t a b

/-- The UTF-8 bytes of a list of characters. -/
def flat (cs : List Char) : List UInt8 := cs.flatMap String.utf8EncodeChar

theorem char_cmp (a b : Char) (s t : List UInt8) :
    bytesCmp (String.utf8EncodeChar a ++ s) (String.utf8EncodeChar b ++ t) =
      (let c := intCompare (a.toNat : Int) (b.toNat : Int); if c == 0 then bytesCmp s t else c) := by
  rw [encN_eq, encN_eq, encN_cmp _ _ _ _ (char_lt a) (char_lt b)]
  have ea : a.toNat = a.val.toNat := rfl
  have eb : b.toNat = b.val.toNat := rfl
  rw [← ea, ← eb]
  generalize a.toNat = x
  generalize b.toNat = y
  unfold intCompare
  dsimp only
  repeat' split
  all_goals first | rfl | omega | simp_all

theorem bytesCmp_nil_enc (b : Char) (s : List UInt8) :
    bytesCmp [] (String.utf8EncodeChar b ++ s) = -1 := by
  cases h : String.utf8EncodeChar b with
  | nil => exact absurd h String.utf8EncodeChar_ne_nil
  | cons x xs => rfl

theorem bytesCmp_enc_nil (a : Char) (s : List UInt8) :
    bytesCmp (String.utf8EncodeChar a ++ s) [] = 1 := by
  cases h : String.utf8EncodeChar a with
  | nil => exact absurd h String.utf8EncodeChar_ne_nil
  | cons x xs => rfl

/-- Byte order of UTF-8 is `listCharCompare`, the code point order. -/
theorem flat_cmp : ∀ (as bs : List Char), bytesCmp (flat as) (flat bs) = listCharCompare as bs
  | [], [] => rfl
  | [], b :: bs => by
    simp only [flat, List.flatMap_cons, List.flatMap_nil]
    rw [bytesCmp_nil_enc]; rfl
  | a :: as, [] => by
    simp only [flat, List.flatMap_cons, List.flatMap_nil]
    rw [bytesCmp_enc_nil]; rfl
  | a :: as, b :: bs => by
    simp only [flat, List.flatMap_cons]
    rw [char_cmp]
    have ih := flat_cmp as bs
    simp only [flat] at ih
    rw [ih]; rfl

theorem enc_head_pos (b : Char) (s : List UInt8)
    (h : noZero (String.utf8EncodeChar b ++ s) = true) :
    bytesCmp (0 :: [] ++ []) [] = 1 ∧ ∃ x xs, String.utf8EncodeChar b = x :: xs ∧ (0 : UInt8) < x := by
  refine ⟨rfl, ?_⟩
  cases he : String.utf8EncodeChar b with
  | nil => exact absurd he String.utf8EncodeChar_ne_nil
  | cons x xs =>
    refine ⟨x, xs, rfl, ?_⟩
    rw [he] at h
    simp only [noZero, List.cons_append, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    have := h.1
    rw [UInt8.lt_iff_toNat_lt]
    have : x.toNat ≠ 0 := fun h0 => this (UInt8.toNat_inj.1 (by simpa using h0))
    simp; omega

theorem noZero_cons_append {x : List UInt8} {y : List UInt8} (h : noZero (x ++ y) = true) :
    noZero y = true := by
  simp only [noZero, List.all_append, Bool.and_eq_true] at h ⊢
  exact h.2

/-- With a `0x00` after each list and no `0x00` in either list, the byte order
    is the code point order of the lists, then the order of what follows the
    separators. -/
theorem flat_sep_cmp : ∀ (as bs : List Char) (X Y : List UInt8),
    noZero (flat as) = true → noZero (flat bs) = true →
    bytesCmp (flat as ++ 0 :: X) (flat bs ++ 0 :: Y) =
      (let r := listCharCompare as bs; if r == 0 then bytesCmp X Y else r)
  | [], [], X, Y, _, _ => by
    simp [flat, bytesCmp, listCharCompare]
  | [], b :: bs, X, Y, _, hb => by
    simp only [flat, List.flatMap_cons] at hb ⊢
    obtain ⟨_, x, xs, he, hx⟩ := enc_head_pos b _ hb
    rw [he]
    simp [bytesCmp, hx, listCharCompare]
  | a :: as, [], X, Y, ha, _ => by
    simp only [flat, List.flatMap_cons] at ha ⊢
    obtain ⟨_, x, xs, he, hx⟩ := enc_head_pos a _ ha
    rw [he]
    have : ¬ x < 0 := by
      rw [UInt8.lt_iff_toNat_lt]; simp
    simp [bytesCmp, hx, this, listCharCompare]
  | a :: as, b :: bs, X, Y, ha, hb => by
    simp only [flat, List.flatMap_cons] at ha hb ⊢
    rw [List.append_assoc, List.append_assoc, char_cmp]
    have ih := flat_sep_cmp as bs X Y (by simpa [flat] using noZero_cons_append ha)
      (by simpa [flat] using noZero_cons_append hb)
    simp only [flat] at ih
    rw [ih]
    simp only [listCharCompare]
    by_cases hc : (intCompare (a.toNat : Int) (b.toNat : Int) == 0) = true <;> simp [hc]

theorem bytesOfString_flat (s : String) : L4Factoidal.Storage.bytesOfString s = flat s.toList := by
  unfold L4Factoidal.Storage.bytesOfString
  conv => lhs; rw [← String.ofList_toList (s := s)]
  rw [L4Factoidal.Storage.byteArray_toList_eq, String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  unfold List.utf8Encode
  simp [flat]

/-- The terms whose ORDER BY reading is the term itself. -/
def plainOrd : Term → Prop
  | .bnode _ => True
  | .iri _ => True
  | .literal l => l.val.datatype = xsdString ∨ l.val.datatype = rdfLangString
  | .tripleTerm _ _ _ => False

theorem plainOrd_view (t : Term) (h : plainOrd t) :
    (EvalResult.term t).isNumericOperand = false ∧ orderView (.term t) = .term t := by
  cases t with
  | bnode b => exact ⟨rfl, rfl⟩
  | iri i => exact ⟨rfl, rfl⟩
  | tripleTerm s p o => exact absurd h id
  | literal l =>
    simp only [plainOrd] at h
    rcases h with h | h <;>
    · refine ⟨?_, ?_⟩
      · simp only [EvalResult.isNumericOperand, h]; decide +kernel
      · simp only [orderView, integerDerivedValue?, h, EvalResult.promoteLiteral, literalPromote]
        have e1 : integerDerivedBuiltinOfIri? xsdString.val = none := by decide
        have e2 : integerDerivedBuiltinOfIri? rdfLangString.val = none := by decide
        simp only [e1, e2]
        simp (config := { decide := true })

theorem sparqlOrder_plain (t1 t2 : Term) (h1 : plainOrd t1) (h2 : plainOrd t2) :
    sparqlOrderValue (.term t1) (.term t2) = sparqlOrderValues (.term t1) (.term t2) := by
  obtain ⟨n1, v1⟩ := plainOrd_view t1 h1
  obtain ⟨n2, v2⟩ := plainOrd_view t2 h2
  show sparqlOrder _ _ = _
  rw [sparqlOrder_eq_viewed, n1, n2, v1, v2]
  rfl


theorem zeros_eq_zero (bs : List UInt8) : (zeros bs = 0) ↔ noZero bs = true := by
  simp [zeros, noZero, List.countP_eq_zero]

theorem zeros_append (a b : List UInt8) : zeros (a ++ b) = zeros a + zeros b := by
  simp [zeros, List.countP_append]

theorem zeros_cons0 (b : List UInt8) : zeros (0 :: b) = zeros b + 1 := by
  simp [zeros]

theorem classify (t : Term) (k : Key) (g : Nat) (h : termKey? t = some k) (hg : keyGroup? k = some g) :
    (g = 1 ∧ ∃ b, t = .bnode b ∧ k = classBnode :: bytesOfString b) ∨
    (g = 2 ∧ ∃ i, t = .iri i ∧ k = classIri :: bytesOfString i.val) ∨
    (g = 3 ∧ ∃ l tag, t = .literal l ∧ l.val.datatype = rdfLangString ∧ l.val.langTag = some tag ∧
      noZero (bytesOfString l.val.lexicalForm) = true ∧
      k = classLang :: (bytesOfString l.val.lexicalForm ++ 0 :: bytesOfString tag)) ∨
    (g = 4 ∧ ∃ l, t = .literal l ∧ l.val.datatype = xsdString ∧ l.val.langTag = none ∧
      k = classString :: bytesOfString l.val.lexicalForm) := by
  cases t with
  | bnode b =>
    simp only [termKey?, atomKey?, Option.some.injEq] at h
    subst h
    simp [keyGroup?] at hg
    exact Or.inl ⟨hg.symm, b, rfl, rfl⟩
  | iri i =>
    simp only [termKey?, atomKey?, Option.some.injEq] at h
    subst h
    simp [keyGroup?, classIri, classBnode] at hg
    exact Or.inr (Or.inl ⟨hg.symm, i, rfl, rfl⟩)
  | tripleTerm s p o =>
    simp only [termKey?] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [keyGroup?, classTriple, classBnode, classIri, classLang, classString] at hg
    · exact absurd h (by simp)
  | literal l =>
    obtain ⟨lv, hw⟩ := l
    simp only [termKey?, atomKey?, literalKey?] at h
    split at h
    · rename_i hl hd
      split at h
      · rename_i hs
        simp only [Option.some.injEq] at h
        subst h
        simp [keyGroup?, classString, classBnode, classIri, classLang] at hg
        refine Or.inr (Or.inr (Or.inr ⟨hg.symm, ⟨lv, hw⟩, rfl, Subtype.ext (by simpa using hs), hl, rfl⟩))
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp [keyGroup?, classTyped, classString, classBnode, classIri, classLang] at hg
        · exact absurd h (by simp)
    · rename_i tag hl hd
      split at h
      · rename_i ht
        simp only [Option.some.injEq] at h
        subst h
        have hdt : lv.datatype = rdfLangString := Subtype.ext (by simpa [literalWf, hl, hd] using hw)
        have htz : noZero (bytesOfString tag) = true := by
          simp only [tagAdmitted, Bool.and_eq_true] at ht; exact ht.1
        simp only [keyGroup?, classLang, classBnode, classIri] at hg
        simp only [zeros_append, zeros_cons0, (zeros_eq_zero _).2 htz] at hg
        have hz : zeros (bytesOfString lv.lexicalForm) = 0 := by
          revert hg; split <;> simp_all
        have hg3 : g = 3 := by revert hg; split <;> simp_all
        exact Or.inr (Or.inr (Or.inl ⟨hg3, ⟨lv, hw⟩, tag, rfl, hdt, hl, (zeros_eq_zero _).1 hz, rfl⟩))
      · exact absurd h (by simp)
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [keyGroup?, classDirLang, classString, classBnode, classIri, classLang] at hg
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- UTF-8 byte order of two strings is `strCompare`. -/
theorem bytes_str (a b : String) : bytesCmp (bytesOfString a) (bytesOfString b) = strCompare a b := by
  rw [bytesOfString_flat, bytesOfString_flat, flat_cmp]; rfl

/-- Two strings without `0x00` bytes, each followed by `0x00`: `strCompare`,
    then the bytes after the separators. -/
theorem bytes_sep (a b : String) (X Y : List UInt8) (ha : noZero (bytesOfString a) = true)
    (hb : noZero (bytesOfString b) = true) :
    bytesCmp (bytesOfString a ++ 0 :: X) (bytesOfString b ++ 0 :: Y) =
      (let r := strCompare a b; if r == 0 then bytesCmp X Y else r) := by
  rw [bytesOfString_flat] at ha hb ⊢
  rw [bytesOfString_flat]
  exact flat_sep_cmp _ _ X Y ha hb

theorem strCompare_self (a : String) : strCompare a a = 0 := by
  simp [strCompare_eq_fast, strCompareFast]

theorem bytesCmp_cons_same (c : UInt8) (A B : List UInt8) : bytesCmp (c :: A) (c :: B) = bytesCmp A B := by
  simp [bytesCmp]

theorem langStr : strCompare rdfLangString.val xsdString.val = -1 := by decide
theorem strLang : strCompare xsdString.val rdfLangString.val = 1 := by decide

theorem orderValue_keyOrder (t1 t2 : Term) (k1 k2 : Key) (g1 g2 : Nat)
    (h1 : termKey? t1 = some k1) (h2 : termKey? t2 = some k2)
    (hg1 : keyGroup? k1 = some g1) (hg2 : keyGroup? k2 = some g2) :
    sparqlOrderValue (IdQuery.orderValue t1) (IdQuery.orderValue t2) =
      (if g1 < g2 then -1 else if g2 < g1 then 1 else bytesCmp k1 k2) := by
  have c1 := classify t1 k1 g1 h1 hg1
  have c2 := classify t2 k2 g2 h2 hg2
  show sparqlOrderValue (.term t1) (.term t2) = _
  rcases c1 with ⟨rfl, b, rfl, rfl⟩ | ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, l, tag, rfl, hdt, hl, hz, rfl⟩ |
      ⟨rfl, l, rfl, hdt, hl, rfl⟩ <;>
  rcases c2 with ⟨rfl, b', rfl, rfl⟩ | ⟨rfl, i', rfl, rfl⟩ | ⟨rfl, l', tag', rfl, hdt', hl', hz', rfl⟩ |
      ⟨rfl, l', rfl, hdt', hl', rfl⟩ <;>
  rw [sparqlOrder_plain _ _ (by simp [plainOrd, *]) (by simp [plainOrd, *])] <;>
  simp only [sparqlOrderValues, erRank, literalOrder, bytesCmp_cons_same, strCompare_self,
    langStr, strLang, bytes_str, *] <;>
  (try rw [bytes_sep _ _ _ _ hz hz', bytes_str]) <;>
  simp (config := { decide := true }) only [termOrder, termRank, bytesCmp, classBnode, classIri, classLang,
    classString] <;>
  (try split) <;> simp_all


/-- An unbound variable (an error) comes first. -/
theorem orderValue_error_term (t : Term) (h : plainOrd t) :
    sparqlOrderValue .error (IdQuery.orderValue t) = -1 := by
  obtain ⟨n, v⟩ := plainOrd_view t h
  show sparqlOrder _ (.term t) = _
  rw [sparqlOrder_eq_viewed, n, v]
  cases t <;> simp_all [sparqlOrderViewed, sparqlOrderValues, erRank, EvalResult.isNumericOperand, orderView]

theorem orderValue_term_error (t : Term) (h : plainOrd t) :
    sparqlOrderValue (IdQuery.orderValue t) .error = 1 := by
  obtain ⟨n, v⟩ := plainOrd_view t h
  show sparqlOrder (.term t) _ = _
  rw [sparqlOrder_eq_viewed, n, v]
  cases t <;> simp_all [sparqlOrderViewed, sparqlOrderValues, erRank, EvalResult.isNumericOperand, orderView]

/-- A term of every group is `plainOrd`. -/
theorem plainOrd_of_group (t : Term) (k : Key) (g : Nat) (h : termKey? t = some k)
    (hg : keyGroup? k = some g) : plainOrd t := by
  rcases classify t k g h hg with ⟨_, b, rfl, _⟩ | ⟨_, i, rfl, _⟩ | ⟨_, l, tag, rfl, hdt, _⟩ |
    ⟨_, l, rfl, hdt, _⟩
  · trivial
  · trivial
  · exact Or.inr hdt
  · exact Or.inl hdt

theorem sliceList_empty (buf : ByteArray) (i e : Nat) (h : e ≤ i) : sliceList buf i e = [] := by
  simp [sliceList, ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop,
    Nat.sub_eq_zero_of_le h]

theorem zerosGo_spec (buf : ByteArray) (e : Nat) (he : e ≤ buf.size) :
    ∀ f i acc, e - i ≤ f → zerosGo buf e f i acc = acc + zeros (sliceList buf i e) := by
  intro f
  induction f with
  | zero =>
    intro i acc hf
    simp [zerosGo, sliceList_empty buf i e (by omega), zeros]
  | succ f ih =>
    intro i acc hf
    simp only [zerosGo]
    split
    · rename_i hle
      simp [sliceList_empty buf i e hle, zeros]
    · rename_i hlt
      have hok : sliceOk buf i e = true := by
        simp only [sliceOk, Bool.and_eq_true, decide_eq_true_eq]; omega
      rw [ih (i + 1) _ (by omega), sliceList_cons buf i e hok]
      simp only [zeros, List.countP_cons]
      split <;> simp_all <;> omega

theorem keyGroupSlice?_eq (buf : ByteArray) (a e : Nat) :
    keyGroupSlice? buf a e = keyGroup? (sliceList buf a e) := by
  unfold keyGroupSlice?
  split
  · rename_i hok
    rw [sliceList_cons buf a e hok]
    have he : e ≤ buf.size := by
      simp only [sliceOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
    rw [zerosGo_spec buf e he _ _ _ (Nat.le_refl _), Nat.zero_add]
    simp only [keyGroup?]
  · rfl

end L4Factoidal.Storage.Sbm11.OrderKey
