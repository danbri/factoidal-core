/-
L4Factoidal.XPath4.SerializeTheorems — what binds `XPath4.Serialize`
(Serialization 4.0) to the project's XML and JSON serializers.

Proved (no `sorry`, no new axioms):

* `hash_md5_shared`, `hash_sha1_shared`, `hash_sha256_shared`,
  `hash_blake3_shared`, `hash_crc32_shared` — `fn:hash` is the project's
  digest for each algorithm.
* `normalize_low` — `fn:normalize-unicode` returns text below U+00A0
  unchanged in all four forms.
* `sliceList_pos` — `fn:slice` with positive arguments is the filter that
  F&O 4.0 states.
* `escTextChar_eq_xml` — for a text character that needs no character
  reference, the XML output method escapes it as `XML.escapeText`
  (`L4Factoidal.XML.Theorems`, the serializer of the XML tree) does, when
  no character map applies, normalization is off and the encoding is
  UTF-8.
* `jsonEscChar_eq_json` — the JSON output method writes a string
  character of code point U+0020 or above as `JSON.escapeChar`
  (`L4Factoidal.JSON.Serialize`, the RFC 8259 serializer) does, in the
  canonical form (RFC 8785) for every such character, and in the default
  form for every such character outside U+007F..U+009F when
  `escape-solidus` is false.

Tested (`#guard`): the canonical JSON escape of the 32 C0 controls is
`JSON.escapeChar` (lowercase `\u00xx`, and the five short escapes).

Open: the round trip `parse-xml(serialize($doc))` deep-equal to `$doc` for
a well-formed document (it needs a proof that `Doc.ofNodes` builds its
table in preorder: https://github.com/danbri/factoidal/issues/1143).
-/
import L4Factoidal.XPath4.Serialize
import L4Factoidal.XML.Theorems
import L4Factoidal.JSON.Serialize
import L4Factoidal.XPath4.Fn4
import L4Factoidal.XPath4.DeepEqual

namespace L4Factoidal.XPath4

/-- A character the XML output method writes as itself or as one of the
    three entity references, with no character reference. -/
def xmlPlainChar (c : Char) : Bool :=
  c != '\r' && (c.toNat ≥ 0x20 || c == '\t' || c == '\n') &&
  !(0x7F ≤ c.toNat && c.toNat ≤ 0x9F) && c.toNat != 0x2028

theorem utf8_encodable (p : SerParams) (h : p.encoding = "UTF-8") (c : Char) :
    p.encodable c = true := by
  simp [SerParams.encodable, h]

theorem beq_false_of_toNat {c d : Char} (h : c.toNat ≠ d.toNat) : (c == d) = false :=
  beq_eq_false_iff_ne.mpr (fun e => h (e ▸ rfl))

theorem escTextChar_eq_xml (p : SerParams) (hm : p.charMap = []) (he : p.encoding = "UTF-8")
    (hc : p.canonical = false) (c : Char) (hp : xmlPlainChar c = true) :
    p.escTextChar c =
      (if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
       else if XML.needsCharRef c then XML.charRef c else String.singleton c) := by
  have henc := utf8_encodable p he c
  have hp' := hp
  simp only [xmlPlainChar, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hp'
  obtain ⟨⟨⟨hr, hlow⟩, hc1⟩, h28⟩ := hp'
  have hc1' : ¬ (0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) := by
    intro ⟨a, b⟩; simp [a, b] at hc1
  have hn : c.toNat ≥ 0x20 ∨ c.toNat = 9 ∨ c.toNat = 10 := by
    rcases hlow with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by rw [h]; rfl))
    · exact Or.inr (Or.inr (by rw [h]; rfl))
  have hcr : (c == '\r') = false := beq_false_of_toNat (by
    have : ('\r' : Char).toNat = 13 := rfl
    omega)
  have hnr : XML.needsCharRef c = false := by
    have e85 : (c == '\u0085') = false := beq_false_of_toNat (by
      have : ('\u0085' : Char).toNat = 0x85 := rfl
      omega)
    have e28 : (c == '\u2028') = false := beq_false_of_toNat (by
      have : ('\u2028' : Char).toNat = 0x2028 := rfl
      omega)
    have er : XML.isRestrictedCharCode c.toNat = false := by
      unfold XML.isRestrictedCharCode
      rcases hn with h | h | h
      · have h1 : ¬ (127 ≤ c.toNat ∧ c.toNat ≤ 132) := fun ⟨a, b⟩ => hc1' ⟨a, by omega⟩
        have h2 : ¬ (134 ≤ c.toNat ∧ c.toNat ≤ 159) := fun ⟨a, b⟩ => hc1' ⟨by omega, b⟩
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
        omega
      · rw [h]; decide
      · rw [h]; decide
    simp [XML.needsCharRef, hcr, e85, e28, er]
  have hctl : ((0x7F ≤ c.toNat && c.toNat ≤ 0x9F) || c.toNat == 0x2028 ||
      (c.toNat < 0x20 && c.toNat != 9 && c.toNat != 10)) = false := by
    rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff]
    refine ⟨⟨hc1, by simpa using h28⟩, ?_⟩
    rcases hn with h | h | h
    · have : ¬ c.toNat < 0x20 := by omega
      simp [this]
    · simp [h]
    · simp [h]
  simp only [SerParams.escTextChar, SerParams.mapped, hm, List.lookup, hnr, hc, henc, hcr, hctl,
    Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false, if_true, ite_true]

theorem json_short_none (c : Char) (h1 : (c == '"') = false) (h2 : (c == '\\') = false)
    (hlow : c.toNat ≥ 0x20) :
    (if c == '"' then some "\\\"" else if c == '\\' then some "\\\\"
     else if c == '\x08' then some "\\b" else if c == '\x0C' then some "\\f"
     else if c == '\n' then some "\\n" else if c == '\r' then some "\\r"
     else if c == '\t' then some "\\t" else (none : Option String)) = none := by
  have e8 : (c == '\x08') = false := beq_false_of_toNat (by have : ('\x08' : Char).toNat = 8 := rfl; omega)
  have e12 : (c == '\x0C') = false := beq_false_of_toNat (by have : ('\x0C' : Char).toNat = 12 := rfl; omega)
  have e10 : (c == '\n') = false := beq_false_of_toNat (by have : ('\n' : Char).toNat = 10 := rfl; omega)
  have e13 : (c == '\r') = false := beq_false_of_toNat (by have : ('\r' : Char).toNat = 13 := rfl; omega)
  have e9 : (c == '\t') = false := beq_false_of_toNat (by have : ('\t' : Char).toNat = 9 := rfl; omega)
  simp [h1, h2, e8, e12, e10, e13, e9]

theorem json_escapeChar_plain (c : Char) (h1 : ¬ c = '"') (h2 : ¬ c = '\\') (hlow : c.toNat ≥ 0x20) :
    JSON.escapeChar c = String.singleton c := by
  simp only [JSON.escapeChar, h1, h2, if_false]
  have : ¬ c.toNat = 0x0A := by omega
  have : ¬ c.toNat = 0x0D := by omega
  have : ¬ c.toNat = 0x09 := by omega
  have : ¬ c.toNat = 0x08 := by omega
  have : ¬ c.toNat = 0x0C := by omega
  have : ¬ c.toNat < 0x20 := by omega
  simp [*]

/-- The canonical JSON form escapes a character of U+0020 or above as the
    RFC 8259 serializer does. -/
theorem jsonEscChar_canonical_eq_json (p : SerParams) (hc : p.canonical = true) (c : Char)
    (hlow : c.toNat ≥ 0x20) : p.jsonEscChar c = JSON.escapeChar c := by
  by_cases h1 : c = '"'
  · subst h1; simp [SerParams.jsonEscChar, hc, JSON.escapeChar]
  by_cases h2 : c = '\\'
  · subst h2; simp [SerParams.jsonEscChar, hc, JSON.escapeChar]
  have hs := json_short_none c (beq_eq_false_iff_ne.mpr h1) (beq_eq_false_iff_ne.mpr h2) hlow
  rw [json_escapeChar_plain c h1 h2 hlow]
  have : ¬ c.toNat < 0x20 := by omega
  simp only [SerParams.jsonEscChar, hc, if_true, hs]
  simp [this]

/-- The default JSON form, with `escape-solidus` false, no character map
    and UTF-8, escapes a character of U+0020 or above and outside
    U+007F..U+009F as the RFC 8259 serializer does. -/
theorem jsonEscChar_eq_json (p : SerParams) (hc : p.canonical = false) (hm : p.charMap = [])
    (hs : p.escapeSolidus = false) (he : p.encoding = "UTF-8") (c : Char)
    (hlow : c.toNat ≥ 0x20) (hc1 : ¬ (0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F)) :
    p.jsonEscChar c = JSON.escapeChar c := by
  have henc := utf8_encodable p he c
  by_cases h1 : c = '"'
  · subst h1; simp [SerParams.jsonEscChar, hc, hm, SerParams.mapped, JSON.escapeChar]
  by_cases h2 : c = '\\'
  · subst h2; simp [SerParams.jsonEscChar, hc, hm, SerParams.mapped, JSON.escapeChar]
  have hsn := json_short_none c (beq_eq_false_iff_ne.mpr h1) (beq_eq_false_iff_ne.mpr h2) hlow
  rw [json_escapeChar_plain c h1 h2 hlow]
  have hr : ((c.toNat < 0x20) || (0x7F ≤ c.toNat && c.toNat ≤ 0x9F)) = false := by
    simp only [Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    omega
  simp only [SerParams.jsonEscChar, hc, Bool.false_eq_true, if_false, SerParams.mapped, hm,
    List.lookup, hsn, hr, henc, if_true]
  by_cases h3 : c = '/'
  · subst h3; simp [hs]
  · simp [h3]

/-! ## `fn:hash` is the project's digests

`fn:hash` with each algorithm of F&O 4.0 §5.3.18 is the digest of
`L4Factoidal.Crypto` (or `Codec.crc32`) that other parts of the project
use, so the FIPS 180-4 and RFC 1321 vectors and the SHA-2 theorems of
`Crypto.SHA2Theorems` hold for it. -/

theorem hash_md5_shared (b : ByteArray) : hashBytes "MD5" b = some (Crypto.md5 b) := rfl
theorem hash_sha1_shared (b : ByteArray) : hashBytes "SHA-1" b = some (Crypto.sha1 b) := rfl
theorem hash_sha256_shared (b : ByteArray) : hashBytes "SHA-256" b = some (Crypto.sha256 b) := rfl
theorem hash_blake3_shared (b : ByteArray) : hashBytes "BLAKE3" b = some (Crypto.Blake3.hash b) := rfl
theorem hash_crc32_shared (b : ByteArray) : hashBytes "CRC-32" b = some (be32 (Codec.crc32 b)) := rfl

/-! ## `fn:normalize-unicode` -/

/-- Text below U+00A0 is in every normalization form (no character there
    has a decomposition or a non-zero combining class), so it is returned
    unchanged. -/
theorem normalize_low (f s : String) (hf : f ∈ ["NFC", "NFD", "NFKC", "NFKD"])
    (hs : s.toList.all (fun c => c.toNat < 0xA0) = true) : Unicode.normalize f s = some s := by
  simp only [Unicode.normalize]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  simp [hs]
  rcases hf with h | h | h | h <;> simp [h]

/-! ## `fn:slice` -/

/-- With a positive step and positive bounds, `fn:slice` keeps the items
    at the positions `start, start + step, ...` up to `end`: the filter of
    F&O 4.0 §14.1.x, `$input[position() ge $S and position() le $E and
    (position() - $S) mod $STEP eq 0]`. -/
theorem sliceList_pos {α} (xs : List α) (s e st : Int) (fuel : Nat)
    (hs : 0 < s) (he : 0 < e) (hst : 0 < st) :
    sliceList (fuel + 1) xs s e st =
      (xs.zipIdx 1).filterMap (fun (x, p) =>
        let p : Int := p
        if p ≥ s && p ≤ e && (p - s) % st == 0 then some x else none) := by
  have h1 : (s == 0) = false := by simp; omega
  have h2 : (e == 0) = false := by simp; omega
  have h3 : ¬ s < 0 := by omega
  have h4 : ¬ e < 0 := by omega
  have h5 : (st == 0) = false := by simp; omega
  have h6 : ¬ st < 0 := by omega
  simp [sliceList, h1, h2, h3, h4, h5, h6]

/-! ## Checks -/

#guard (List.range 32).all (fun n =>
  ({ canonical := true } : SerParams).jsonEscChar (Char.ofNat n) == JSON.escapeChar (Char.ofNat n))
#guard ({} : SerParams).escText "a<b & c>d" == XML.escapeText "a<b & c>d"
#guard civilFromDays 0 == (1970, 1, 1)
#guard civilFromDays 19782 == (2024, 2, 29)
#guard civilFromDays (-1) == (1969, 12, 31)
#guard civilFromDays (-719528) == (0, 1, 1)

end L4Factoidal.XPath4
