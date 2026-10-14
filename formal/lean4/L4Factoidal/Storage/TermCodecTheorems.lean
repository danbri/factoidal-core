/-
L4Factoidal.Storage.TermCodecTheorems — round-trip proofs for the durable
term codec of `L4Factoidal.Storage.DeltaLog`.

The delta log and the `BLK0` block wire format both encode an RDF term
with `serializeTerm?` and decode it with `parseTerm`. This module proves
that the decoder inverts the encoder on the subset the encoder admits,
with arbitrary trailing bytes present:

    serializeTerm? t = some bs → parseTerm (bs ++ rest) = some (t, rest)

The trailing-bytes form is what a framed reader needs. A record decoder
calls `parseTerm` on the remainder of a buffer, not on a byte sequence
that stops at the end of the term.

The proofs are layered. `stringOfBytes?_bytesOfString` is the UTF-8
round trip for one string. `parseLString_serializeLString?` lifts it to
the u32 length-prefixed field, over the little-endian field lemmas of
`L4Factoidal.Storage.Bytes`. `parseTerm_serializeTerm?` then follows the
tag dispatch of `parseTerm` case by case.

`serializeTerm?` refuses triple terms and literals with a base
direction, because the v1 decoder cannot reconstruct them.
`serializeTerm?_supported` proves that successful checked encoding
implies `L4Factoidal.Storage.BlockWireV0.termSupported`, and
`parseTerm_serializeTerm?_checked` gives the round trip without a
separate support hypothesis.

`termFitsU32` is the second admission condition: every length-prefixed
string in the term has a byte length below the u32 field limit.
Together the two conditions make the total encoder `serializeTerm` agree
with `serializeTerm?`, which gives the round trip in the form the block
codecs use.

`termFitsU32b_iff` relates `termFitsU32` to the decision procedure
`L4Factoidal.Storage.termFitsU32b` of `DeltaLog`. The block encoders gate
on that `Bool`, so both admission conditions are consequences of an
encoder's own guard and neither is a hypothesis of a codec round trip.

The term codec of DLOG version 2 (`serializeDeltaTerm?`, `parseDeltaTerm`,
https://github.com/danbri/factoidal/issues/792 item 1) has its own round trip,
for every term, triple terms at any depth and directional literals included:
`parseDeltaTerm_serializeDeltaTerm?`, whose one hypothesis is that the encoder
admits the term. `serializeDeltaTerm?_isSome_iff`: the encoder admits exactly
the terms of `termFitsU32`. `serializeDeltaTerm?_of_supported`: on the terms
the version 1 codec admits, version 2 writes the same bytes.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.BlockWireV0

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-! ## `ByteArray.toList`

`ByteArray.toList` is defined by an index loop rather than by
`data.toList`, and core carries no lemma relating the two. The UTF-8
round trip below needs that relation, because `bytesOfString` goes
through `ByteArray.toList` and `stringOfBytes?` rebuilds a `ByteArray`
from the list. -/

private theorem byteArray_toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  have key : ∀ n i r, bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
        intro i r h
        rw [ByteArray.toList.loop]
        have hi : ¬ (i < bs.size) := by omega
        simp only [hi, if_false]
        have hle : bs.data.toList.length ≤ i := by
          rw [Array.length_toList]; exact Nat.le_of_not_lt hi
        rw [List.drop_eq_nil_of_le hle]
        simp
    | succ n ih =>
        intro i r h
        rw [ByteArray.toList.loop]
        have hi : i < bs.size := by omega
        simp only [hi, if_true]
        rw [ih (i + 1) (bs.get! i :: r) (by omega)]
        have hlen : i < bs.data.toList.length := by
          rw [Array.length_toList]; exact hi
        rw [List.drop_eq_getElem_cons hlen]
        have hg : bs.get! i = bs.data.toList[i] := by
          rw [Array.getElem_toList]
          show bs.data[i]! = bs.data[i]
          rw [getElem!_pos]
        rw [hg]
        simp
  exact key (bs.size - i) i r rfl

/-- The index loop of `ByteArray.toList` yields the underlying array's
element list. -/
theorem byteArray_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  rw [ByteArray.toList, byteArray_toList_loop]; simp

/-! ## Length-prefixed strings -/

/-- The UTF-8 byte list of a string decodes back to that string. -/
theorem stringOfBytes?_bytesOfString (s : String) :
    stringOfBytes? (bytesOfString s) = some s := by
  rw [stringOfBytes?, bytesOfString, byteArray_toList_eq, Array.toArray_toList]
  simp [String.fromUTF8?, s.isValidUTF8, String.fromUTF8]

/-- A four-byte little-endian field is exactly what a reader steps over. -/
private theorem drop4_writeU32LE (n : UInt32) (t : List UInt8) :
    (writeU32LE n ++ t).drop 4 = t := by simp [writeU32LE]

/-- The length-prefixed string decoder inverts the admission-preserving
encoder and returns the trailing bytes unchanged. -/
theorem parseLString_serializeLString? (s : String) (bs rest : List UInt8)
    (h : serializeLString? s = some bs) :
    parseLString (bs ++ rest) = some (s, rest) := by
  by_cases hge : (bytesOfString s).length ≥ UInt32.size
  · rw [serializeLString?] at h; simp [hge] at h
  · rw [serializeLString?] at h
    simp only [hge, if_false, Option.some.injEq] at h
    subst h
    have hlt : (bytesOfString s).length < UInt32.size := Nat.lt_of_not_le hge
    rw [List.append_assoc, parseLString, readU32LE_writeU32LE_append]
    simp only [u32_toNat_ofNat_of_lt hlt, drop4_writeU32LE, List.take_left,
      List.drop_left, bne_self_eq_false, Bool.false_eq_true, if_false,
      stringOfBytes?_bytesOfString, Option.map_some]

/-- The single-byte decoder consumes exactly the head byte. -/
theorem parseU8_cons (b : UInt8) (rest : List UInt8) :
    parseU8 (b :: rest) = some (b, rest) := rfl

/-! ## Subjects -/

/-- The subject decoder inverts the admission-preserving subject encoder
and returns the trailing bytes unchanged. -/
theorem parseSubject_serializeSubject? (s : Subject) (bs rest : List UInt8)
    (h : serializeSubject? s = some bs) :
    parseSubject (bs ++ rest) = some (s, rest) := by
  cases s with
  | iri i =>
      rw [serializeSubject?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseSubject]
      simp [parseU8, subjTagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      rw [serializeSubject?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseSubject]
      simp [parseU8, subjTagIri, subjTagBnode, parseLString_serializeLString? _ _ _ hsb]

/-! ## Terms

`DeltaLog.mkLiteral?` — the literal reconstruction step of `parseTerm` —
is `private`, so it cannot be named here. `mkLiteralLocal` is a
definitionally equal copy; `show` bridges the two where `parseTerm`
unfolds. -/

private def mkLiteralLocal (lex dt : String) (tag : Option String) : Option Term :=
  if h : isIri dt then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, h⟩,
                         langTag := tag, direction := none }
    if hw : literalWf l then some (.literal ⟨l, hw⟩) else none
  else none

/-- Reconstruction from lexical form, datatype IRI and language tag
returns the original literal when its base direction is absent. -/
private theorem mkLiteralLocal_self (l : WfLiteral) (hd : l.val.direction = none) :
    mkLiteralLocal l.val.lexicalForm l.val.datatype.val l.val.langTag
      = some (.literal l) := by
  rw [mkLiteralLocal, dif_pos l.val.datatype.property]
  have hrec : ({ lexicalForm := l.val.lexicalForm,
                 datatype := ⟨l.val.datatype.val, l.val.datatype.property⟩,
                 langTag := l.val.langTag, direction := none } : Literal) = l.val := by
    rw [← hd]
  simp only [hrec]
  rw [dif_pos l.property]

/-- The literal case of the term round trip, kept separate because it
splits on the language tag. -/
private theorem parseTerm_serializeTerm?_literal (l : WfLiteral) (bs rest : List UInt8)
    (hd : l.val.direction = none) (h : serializeTerm? (.literal l) = some bs) :
    parseTerm (bs ++ rest) = some (.literal l, rest) := by
  rw [serializeTerm?] at h
  simp only [hd, Option.isSome_none, Bool.false_eq_true, if_false] at h
  cases hlex : serializeLString? l.val.lexicalForm with
  | none => rw [hlex] at h; simp [bind, Option.bind] at h
  | some lexb =>
  cases hdt : serializeLString? l.val.datatype.val with
  | none => rw [hlex, hdt] at h; simp [bind, Option.bind] at h
  | some dtb =>
  rw [hlex, hdt] at h
  simp only [bind, Option.bind] at h
  cases hlt : l.val.langTag with
  | none =>
      rw [hlt] at h
      simp only [Option.some.injEq] at h
      subst h
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (0 : UInt8) :: rest) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((0 : UInt8) :: rest) hdt
      have happ : lexb ++ dtb ++ [(0 : UInt8)] ++ rest
          = lexb ++ (dtb ++ (0 : UInt8) :: rest) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseTerm]
      simp only [bind, Option.bind, parseU8, h1, h2, termTagIri, termTagBnode,
        termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide),
        if_pos (by decide)]
      have hmk := mkLiteralLocal_self l hd
      rw [hlt] at hmk
      show Option.map (fun t => (t, rest))
        (mkLiteralLocal l.val.lexicalForm l.val.datatype.val none)
          = some (Term.literal l, rest)
      rw [hmk]
      rfl
  | some tag =>
      rw [hlt] at h
      dsimp only at h
      cases hlang : serializeLString? tag with
      | none => rw [hlang] at h; simp at h
      | some langb =>
      rw [hlang] at h
      simp only [Option.some.injEq] at h
      subst h
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (1 : UInt8) :: (langb ++ rest)) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((1 : UInt8) :: (langb ++ rest)) hdt
      have h3 := parseLString_serializeLString? tag langb rest hlang
      have happ : lexb ++ dtb ++ (1 : UInt8) :: langb ++ rest
          = lexb ++ (dtb ++ (1 : UInt8) :: (langb ++ rest)) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseTerm]
      simp only [bind, Option.bind, parseU8, h1, h2, h3, termTagIri, termTagBnode,
        termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide),
        if_neg (by decide), if_pos (by decide)]
      have hmk := mkLiteralLocal_self l hd
      rw [hlt] at hmk
      show Option.map (fun t => (t, rest))
        (mkLiteralLocal l.val.lexicalForm l.val.datatype.val (some tag))
          = some (Term.literal l, rest)
      rw [hmk]
      rfl

/-- The term decoder inverts the admission-preserving term encoder on
the subset `BlockWireV0.termSupported` admits, and returns the trailing
bytes unchanged.

The support hypothesis is needed only for the literal case, where the
v1 decoder reconstructs no base direction. -/
theorem parseTerm_serializeTerm? (t : Term) (bs rest : List UInt8)
    (hsup : BlockWireV0.termSupported t = true)
    (h : serializeTerm? t = some bs) :
    parseTerm (bs ++ rest) = some (t, rest) := by
  cases t with
  | iri i =>
      rw [serializeTerm?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseTerm]
      simp [parseU8, termTagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      rw [serializeTerm?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseTerm]
      simp [parseU8, termTagIri, termTagBnode,
        parseLString_serializeLString? _ _ _ hsb]
  | literal l =>
      rw [BlockWireV0.termSupported, Option.isNone_iff_eq_none] at hsup
      exact parseTerm_serializeTerm?_literal l bs rest hsup h
  | tripleTerm s p o =>
      rw [serializeTerm?] at h
      exact absurd h (by simp)

/-- Successful checked term encoding implies the v1 decoder's supported
subset. -/
theorem serializeTerm?_supported (t : Term) (bs : List UInt8)
    (h : serializeTerm? t = some bs) :
    BlockWireV0.termSupported t = true := by
  cases t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal literal =>
      cases hd : literal.val.direction with
      | none => simp [BlockWireV0.termSupported, hd]
      | some direction => simp [serializeTerm?, hd] at h
  | tripleTerm subject predicate object =>
      simp [serializeTerm?] at h

/-- Every admitted checked term encoding decodes with its trailing bytes
unchanged, without a separate support hypothesis. -/
theorem parseTerm_serializeTerm?_checked (t : Term) (bs rest : List UInt8)
    (h : serializeTerm? t = some bs) :
    parseTerm (bs ++ rest) = some (t, rest) :=
  parseTerm_serializeTerm? t bs rest (serializeTerm?_supported t bs h) h

/-! ## The total encoder

`serializeTerm` is the total encoder the block codecs call.
`serializeTerm?` is the same bytes plus an admission check, so the two
agree exactly when the term is supported and every length-prefixed
string in it fits the u32 field. -/

/-- A string whose UTF-8 byte length fits the u32 length prefix. -/
def stringFitsU32 (s : String) : Prop := (bytesOfString s).length < UInt32.size

/-- The string of a subject fits its u32 length prefix. -/
def subjectFitsU32 : Subject → Prop
  | .iri i => stringFitsU32 i.val
  | .bnode b => stringFitsU32 b

/-- Every length-prefixed string in the term fits its u32 length prefix, in
every part of a triple term too. -/
def termFitsU32 : Term → Prop
  | .iri i => stringFitsU32 i.val
  | .bnode b => stringFitsU32 b
  | .literal l =>
      stringFitsU32 l.val.lexicalForm ∧ stringFitsU32 l.val.datatype.val ∧
        ∀ tag, l.val.langTag = some tag → stringFitsU32 tag
  | .tripleTerm s p o => subjectFitsU32 s ∧ stringFitsU32 p.val ∧ termFitsU32 o

/-- The decision procedure `stringFitsU32b` of `L4Factoidal.Storage.DeltaLog`
decides `stringFitsU32`. -/
theorem stringFitsU32b_iff (s : String) : stringFitsU32b s = true ↔ stringFitsU32 s := by
  simp [stringFitsU32b, stringFitsU32]

/-- The decision procedure `termFitsU32b` of `L4Factoidal.Storage.DeltaLog`
decides `termFitsU32`. This is what lets a block encoder gate on the u32
length-prefix condition with a `Bool` guard and a proof read the `Prop` out
of that guard. -/
theorem subjectFitsU32b_iff (s : Subject) : subjectFitsU32b s = true ↔ subjectFitsU32 s := by
  cases s with
  | iri i => exact stringFitsU32b_iff i.val
  | bnode b => exact stringFitsU32b_iff b

theorem termFitsU32b_iff (t : Term) : termFitsU32b t = true ↔ termFitsU32 t := by
  induction t with
  | iri i => exact stringFitsU32b_iff i.val
  | bnode b => exact stringFitsU32b_iff b
  | literal l =>
      rw [termFitsU32b, termFitsU32, Bool.and_eq_true, Bool.and_eq_true,
        stringFitsU32b_iff, stringFitsU32b_iff]
      constructor
      · rintro ⟨⟨hlex, hdt⟩, htag⟩
        refine ⟨hlex, hdt, ?_⟩
        intro tag htageq
        simp only [htageq] at htag
        exact (stringFitsU32b_iff tag).mp htag
      · rintro ⟨hlex, hdt, htag⟩
        refine ⟨⟨hlex, hdt⟩, ?_⟩
        cases hlt : l.val.langTag with
        | none => rfl
        | some tag => exact (stringFitsU32b_iff tag).mpr (htag tag hlt)
  | tripleTerm s p o ih =>
      rw [termFitsU32b, termFitsU32, ← subjectFitsU32b_iff, ← stringFitsU32b_iff, ← ih]
      cases subjectFitsU32b s <;> cases stringFitsU32b p.val <;> simp

/-- The admission-preserving string encoder emits the total encoder's
bytes whenever the byte length fits. -/
theorem serializeLString?_eq_some (s : String) (h : stringFitsU32 s) :
    serializeLString? s = some (serializeLString s) := by
  rw [serializeLString?, serializeLString]
  exact if_neg (Nat.not_le.2 h)

/-- On the supported, fitting subset the admission-preserving term
encoder emits exactly the total encoder's bytes. -/
theorem serializeTerm?_eq_some_of_supported_of_fits (t : Term)
    (hsup : BlockWireV0.termSupported t = true) (hfit : termFitsU32 t) :
    serializeTerm? t = some (serializeTerm t) := by
  cases t with
  | iri i =>
      rw [serializeTerm?, serializeTerm, serializeLString?_eq_some _ hfit]
      rfl
  | bnode b =>
      rw [serializeTerm?, serializeTerm, serializeLString?_eq_some _ hfit]
      rfl
  | literal l =>
      obtain ⟨hlex, hdt, htag⟩ := hfit
      rw [BlockWireV0.termSupported, Option.isNone_iff_eq_none] at hsup
      rw [serializeTerm?]
      simp only [hsup, Option.isSome_none, Bool.false_eq_true, if_false]
      rw [serializeTerm, serializeLString?_eq_some _ hlex,
        serializeLString?_eq_some _ hdt]
      simp only [bind, Option.bind]
      cases hlt : l.val.langTag with
      | none => rfl
      | some tag =>
          dsimp only
          rw [serializeLString?_eq_some _ (htag tag hlt)]
  | tripleTerm s p o => simp [BlockWireV0.termSupported] at hsup

/-- The round trip in the form the block codecs use: the total encoder's
bytes, followed by arbitrary trailing bytes, decode back to the term. -/
theorem parseTerm_serializeTerm (t : Term) (rest : List UInt8)
    (hsup : BlockWireV0.termSupported t = true) (hfit : termFitsU32 t) :
    parseTerm (serializeTerm t ++ rest) = some (t, rest) :=
  parseTerm_serializeTerm? t (serializeTerm t) rest hsup
    (serializeTerm?_eq_some_of_supported_of_fits t hsup hfit)

/-! ## The term codec of DLOG version 2

`serializeDeltaTerm?` and `parseDeltaTerm` of `DeltaLog`: the version 1 codec
with a payload for tag 3 (the three component terms, so a triple term in the
object position nests) and the literal flag 2 (the language tag, then a
direction byte). The decoder is a loop with a stack of the subjects and
predicates read so far (`parseDeltaTermGo`); the round trip is proved for
every fuel above the number of bytes, which `parseDeltaTerm` supplies. -/

theorem serializeLString?_isSome_iff (s : String) :
    (serializeLString? s).isSome = true ↔ stringFitsU32 s := by
  rw [serializeLString?, stringFitsU32]
  by_cases h : (bytesOfString s).length ≥ two32
  · rw [if_pos h]; rw [two32_eq_uint32Size] at h; simp; omega
  · rw [if_neg h]; rw [two32_eq_uint32Size] at h; simp; omega

theorem mkDeltaLiteral?_self (l : WfLiteral) :
    mkDeltaLiteral? l.val.lexicalForm l.val.datatype.val l.val.langTag l.val.direction
      = some (.literal l) := by
  rw [mkDeltaLiteral?, dif_pos l.val.datatype.property]
  have hrec : ({ lexicalForm := l.val.lexicalForm,
                 datatype := ⟨l.val.datatype.val, l.val.datatype.property⟩,
                 langTag := l.val.langTag, direction := l.val.direction } : Literal) = l.val := rfl
  simp only [hrec]
  rw [dif_pos l.property]

theorem dirOfByte_dirByte (d : TextDirection) : dirOfByte (dirByte d) = some d := by
  cases d <;> rfl

theorem parseDeltaLeaf_literal (l : WfLiteral) (bs rest : List UInt8)
    (h : serializeDeltaLiteral? l = some bs) :
    parseDeltaLeaf (bs ++ rest) = some (.literal l, rest) := by
  rw [serializeDeltaLiteral?] at h
  cases hlex : serializeLString? l.val.lexicalForm with
  | none => rw [hlex] at h; simp [bind, Option.bind] at h
  | some lexb =>
  cases hdt : serializeLString? l.val.datatype.val with
  | none => rw [hlex, hdt] at h; simp [bind, Option.bind] at h
  | some dtb =>
  rw [hlex, hdt] at h
  simp only [bind, Option.bind] at h
  have hmk := mkDeltaLiteral?_self l
  cases htag : l.val.langTag with
  | none =>
    cases hdir : l.val.direction with
    | some d => rw [htag, hdir] at h; cases h
    | none =>
      rw [htag, hdir] at h
      simp only [Option.some.injEq] at h
      subst h
      rw [htag, hdir] at hmk
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (0 : UInt8) :: rest) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb ((0 : UInt8) :: rest) hdt
      have happ : lexb ++ dtb ++ [(0 : UInt8)] ++ rest = lexb ++ (dtb ++ (0 : UInt8) :: rest) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseDeltaLeaf]
      simp only [bind, Option.bind, parseU8, h1, h2, termTagIri, termTagBnode, termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), if_pos (by decide), hmk]
      rfl
  | some tag =>
    cases hlang : serializeLString? tag with
    | none =>
      cases hdir : l.val.direction <;> (rw [htag, hdir] at h; simp [hlang] at h)
    | some langb =>
    cases hdir : l.val.direction with
    | none =>
      rw [htag, hdir] at h
      simp only [hlang, Option.some.injEq] at h
      subst h
      rw [htag, hdir] at hmk
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (1 : UInt8) :: (langb ++ rest)) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((1 : UInt8) :: (langb ++ rest)) hdt
      have h3 := parseLString_serializeLString? tag langb rest hlang
      have happ : lexb ++ dtb ++ (1 : UInt8) :: langb ++ rest
          = lexb ++ (dtb ++ (1 : UInt8) :: (langb ++ rest)) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseDeltaLeaf]
      simp only [bind, Option.bind, parseU8, h1, h2, h3, termTagIri, termTagBnode, termTagLiteral]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide),
        if_pos (by decide), hmk]
      rfl
    | some d =>
      rw [htag, hdir] at h
      simp only [hlang, Option.some.injEq] at h
      subst h
      rw [htag, hdir] at hmk
      have h1 := parseLString_serializeLString? l.val.lexicalForm lexb
        (dtb ++ (2 : UInt8) :: (langb ++ dirByte d :: rest)) hlex
      have h2 := parseLString_serializeLString? l.val.datatype.val dtb
        ((2 : UInt8) :: (langb ++ dirByte d :: rest)) hdt
      have h3 := parseLString_serializeLString? tag langb (dirByte d :: rest) hlang
      have happ : lexb ++ dtb ++ (2 : UInt8) :: (langb ++ [dirByte d]) ++ rest
          = lexb ++ (dtb ++ (2 : UInt8) :: (langb ++ dirByte d :: rest)) := by
        simp [List.append_assoc]
      rw [List.cons_append, happ, parseDeltaLeaf]
      simp only [bind, Option.bind, parseU8, h1, h2, h3, termTagIri, termTagBnode, termTagLiteral,
        dirOfByte_dirByte]
      rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide),
        if_neg (by decide), if_pos (by decide), hmk]
      rfl

theorem parseDeltaLeaf_serializeDeltaLeaf? (t : Term) (bs rest : List UInt8)
    (h : serializeDeltaLeaf? t = some bs) :
    parseDeltaLeaf (bs ++ rest) = some (t, rest) := by
  cases t with
  | iri i =>
      rw [serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseDeltaLeaf]
      simp [parseU8, termTagIri, parseLString_serializeLString? _ _ _ hsb, i.property]
  | bnode b =>
      rw [serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨sb, hsb, rfl⟩ := h
      rw [List.cons_append, parseDeltaLeaf]
      simp [parseU8, termTagIri, termTagBnode, parseLString_serializeLString? _ _ _ hsb]
  | literal l => exact parseDeltaLeaf_literal l bs rest h
  | tripleTerm _ _ _ => simp [serializeDeltaLeaf?] at h

theorem serializeDeltaLiteral?_head (l : WfLiteral) (bs : List UInt8)
    (h : serializeDeltaLiteral? l = some bs) : ∃ rest, bs = termTagLiteral :: rest := by
  rw [serializeDeltaLiteral?] at h
  cases hlex : serializeLString? l.val.lexicalForm with
  | none => rw [hlex] at h; simp [bind, Option.bind] at h
  | some lexb =>
  cases hdt : serializeLString? l.val.datatype.val with
  | none => rw [hlex, hdt] at h; simp [bind, Option.bind] at h
  | some dtb =>
  rw [hlex, hdt] at h
  simp only [bind, Option.bind] at h
  cases htag : l.val.langTag with
  | none =>
    cases hdir : l.val.direction with
    | some d => rw [htag, hdir] at h; cases h
    | none =>
      rw [htag, hdir] at h
      simp only [Option.some.injEq] at h
      exact ⟨_, h.symm⟩
  | some tag =>
    cases hlang : serializeLString? tag with
    | none =>
      cases hdir : l.val.direction <;> (rw [htag, hdir] at h; simp [hlang] at h)
    | some langb =>
    cases hdir : l.val.direction with
    | none =>
      rw [htag, hdir] at h
      simp only [hlang, Option.some.injEq] at h
      exact ⟨_, h.symm⟩
    | some d =>
      rw [htag, hdir] at h
      simp only [hlang, Option.some.injEq] at h
      exact ⟨_, h.symm⟩

/-- A term that is not a triple term starts with a byte other than tag 3. -/
theorem serializeDeltaLeaf?_head (t : Term) (bs : List UInt8)
    (h : serializeDeltaLeaf? t = some bs) :
    ∃ b rest, bs = b :: rest ∧ (b == termTagTripleTerm) = false := by
  cases t with
  | iri i =>
      rw [serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨sb, -, rfl⟩ := h
      exact ⟨_, _, rfl, by decide⟩
  | bnode b =>
      rw [serializeDeltaLeaf?, Option.map_eq_some_iff] at h
      obtain ⟨sb, -, rfl⟩ := h
      exact ⟨_, _, rfl, by decide⟩
  | literal l =>
      obtain ⟨rest, hr⟩ := serializeDeltaLiteral?_head l bs h
      exact ⟨_, _, hr, by decide⟩
  | tripleTerm _ _ _ => simp [serializeDeltaLeaf?] at h

/-- The prefix of a triple term: tag 3, the subject term, the predicate term. -/
theorem serializeTriplePrefix?_parse (s : Subject) (p : WfIri) (pre rest : List UInt8)
    (h : serializeTriplePrefix? s p = some pre) :
    ∃ tail, pre ++ rest = termTagTripleTerm :: tail ∧
      ∃ afterS, parseSubject tail = some (s, afterS) ∧
        parsePredicateTerm afterS = some (p, rest) := by
  rw [serializeTriplePrefix?] at h
  cases hs : serializeSubject? s with
  | none => simp [hs, bind, Option.bind] at h
  | some sb =>
  cases hp : serializeLString? p.val with
  | none => simp [hs, hp, bind, Option.bind] at h
  | some pb =>
  simp only [hs, hp, bind, Option.bind, Option.some.injEq] at h
  subst h
  refine ⟨sb ++ (termTagIri :: (pb ++ rest)), by simp [List.append_assoc], _,
    parseSubject_serializeSubject? s sb _ hs, ?_⟩
  rw [parsePredicateTerm]
  simp [parseU8, parseLString_serializeLString? _ _ _ hp, p.property]

/-- The prefix is at least one byte. -/
theorem serializeTriplePrefix?_ne_nil (s : Subject) (p : WfIri) (pre : List UInt8)
    (h : serializeTriplePrefix? s p = some pre) : 1 ≤ pre.length := by
  rw [serializeTriplePrefix?] at h
  cases hs : serializeSubject? s with
  | none => simp [hs, bind, Option.bind] at h
  | some sb =>
  cases hp : serializeLString? p.val with
  | none => simp [hs, hp, bind, Option.bind] at h
  | some pb =>
  simp only [hs, hp, bind, Option.bind, Option.some.injEq] at h
  subst h
  simp

/-- The loop reads back every term the encoder writes, at any nesting depth,
    when its fuel is above the number of bytes: the triple terms read before
    it (`stack`) are put around it. -/
theorem parseDeltaTermGo_serializeDeltaTerm? : ∀ (t : Term) (bs rest : List UInt8)
    (stack : List (Subject × WfIri)) (fuel : Nat),
    serializeDeltaTerm? t = some bs → bs.length + rest.length < fuel →
    parseDeltaTermGo fuel (bs ++ rest) stack = some (wrapTriples stack t, rest)
  | .tripleTerm s p o, bs, rest, stack, fuel, h, hf => by
      rw [serializeDeltaTerm?] at h
      cases hpre : serializeTriplePrefix? s p with
      | none => simp [hpre, bind, Option.bind] at h
      | some pre =>
      cases ho : serializeDeltaTerm? o with
      | none => simp [hpre, ho, bind, Option.bind] at h
      | some ob =>
      simp only [hpre, ho, bind, Option.bind, Option.some.injEq] at h
      subst h
      have h1 := serializeTriplePrefix?_ne_nil s p pre hpre
      obtain ⟨tail, htail, afterS, hS, hP⟩ := serializeTriplePrefix?_parse s p pre (ob ++ rest) hpre
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      rw [List.append_assoc, htail, parseDeltaTermGo]
      simp only [beq_self_eq_true, if_true, hS, hP]
      have hlen : ob.length + rest.length < f := by
        simp only [List.length_append] at hf; omega
      rw [parseDeltaTermGo_serializeDeltaTerm? o ob rest ((s, p) :: stack) f ho hlen]
      rfl
  | .iri i, bs, rest, stack, fuel, h, hf => by
      obtain ⟨b, r, rfl, hb⟩ := serializeDeltaLeaf?_head (.iri i) bs h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      rw [List.cons_append, parseDeltaTermGo, ← List.cons_append]
      simp only [hb, Bool.false_eq_true, if_false]
      rw [parseDeltaLeaf_serializeDeltaLeaf? (.iri i) (b :: r) rest h]
      rfl
  | .bnode x, bs, rest, stack, fuel, h, hf => by
      obtain ⟨b, r, rfl, hb⟩ := serializeDeltaLeaf?_head (.bnode x) bs h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      rw [List.cons_append, parseDeltaTermGo, ← List.cons_append]
      simp only [hb, Bool.false_eq_true, if_false]
      rw [parseDeltaLeaf_serializeDeltaLeaf? (.bnode x) (b :: r) rest h]
      rfl
  | .literal l, bs, rest, stack, fuel, h, hf => by
      obtain ⟨b, r, rfl, hb⟩ := serializeDeltaLeaf?_head (.literal l) bs h
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
      rw [List.cons_append, parseDeltaTermGo, ← List.cons_append]
      simp only [hb, Bool.false_eq_true, if_false]
      rw [parseDeltaLeaf_serializeDeltaLeaf? (.literal l) (b :: r) rest h]
      rfl

/-- The round trip of the DLOG version 2 term codec, for every term: triple
    terms at any depth and directional literals included. The only hypothesis
    is that the encoder admits the term. -/
theorem parseDeltaTerm_serializeDeltaTerm? (t : Term) (bs rest : List UInt8)
    (h : serializeDeltaTerm? t = some bs) :
    parseDeltaTerm (bs ++ rest) = some (t, rest) := by
  rw [parseDeltaTerm]
  have := parseDeltaTermGo_serializeDeltaTerm? t bs rest [] ((bs ++ rest).length + 1) h
    (by simp)
  rw [this]
  rfl



/-- A well-formed literal with no language tag has no base direction. -/
theorem WfLiteral.direction_none_of_langTag_none (l : WfLiteral) (h : l.val.langTag = none) :
    l.val.direction = none := by
  have hw := l.property
  cases hd : l.val.direction with
  | none => rfl
  | some d => simp [literalWf, h, hd] at hw

theorem serializeDeltaLiteral?_isSome_iff (l : WfLiteral) :
    (serializeDeltaLiteral? l).isSome = true ↔
      stringFitsU32 l.val.lexicalForm ∧ stringFitsU32 l.val.datatype.val ∧
        ∀ tag, l.val.langTag = some tag → stringFitsU32 tag := by
  rw [serializeDeltaLiteral?]
  rw [← serializeLString?_isSome_iff l.val.lexicalForm, ← serializeLString?_isSome_iff l.val.datatype.val]
  cases hlex : serializeLString? l.val.lexicalForm with
  | none => simp [bind, Option.bind]
  | some lexb =>
  cases hdt : serializeLString? l.val.datatype.val with
  | none => simp [bind, Option.bind]
  | some dtb =>
  simp only [bind, Option.bind, Option.isSome_some, true_and]
  cases htag : l.val.langTag with
  | none =>
      have hd := WfLiteral.direction_none_of_langTag_none l htag
      rw [hd]
      simp
  | some tag =>
      have hiff := serializeLString?_isSome_iff tag
      cases hdir : l.val.direction with
      | none =>
          cases hl : serializeLString? tag with
          | none =>
              simp only [hl, Option.isSome_none, Bool.false_eq_true, false_iff] at hiff
              simp [hl, hiff]
          | some lb =>
              simp only [hl, Option.isSome_some, true_iff] at hiff
              simp [hl, hiff]
      | some d =>
          cases hl : serializeLString? tag with
          | none =>
              simp only [hl, Option.isSome_none, Bool.false_eq_true, false_iff] at hiff
              simp [hl, hiff]
          | some lb =>
              simp only [hl, Option.isSome_some, true_iff] at hiff
              simp [hl, hiff]

theorem serializeSubject?_isSome_iff (s : Subject) :
    (serializeSubject? s).isSome = true ↔ subjectFitsU32 s := by
  cases s with
  | iri i =>
      rw [serializeSubject?, subjectFitsU32, ← serializeLString?_isSome_iff]
      cases serializeLString? i.val <;> simp
  | bnode b =>
      rw [serializeSubject?, subjectFitsU32, ← serializeLString?_isSome_iff]
      cases serializeLString? b <;> simp

theorem serializeTriplePrefix?_isSome_iff (s : Subject) (p : WfIri) :
    (serializeTriplePrefix? s p).isSome = true ↔ subjectFitsU32 s ∧ stringFitsU32 p.val := by
  rw [serializeTriplePrefix?, ← serializeSubject?_isSome_iff, ← serializeLString?_isSome_iff]
  cases serializeSubject? s <;> cases serializeLString? p.val <;> simp [bind, Option.bind]

/-- The version 2 term encoder admits exactly the terms whose length-prefixed
    strings fit their u32 prefixes: every term, triple terms at any depth and
    directional literals included, up to the u32 limit. -/
theorem serializeDeltaTerm?_isSome_iff : ∀ t : Term,
    (serializeDeltaTerm? t).isSome = true ↔ termFitsU32 t
  | .iri i => by
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, termFitsU32, Option.isSome_map,
        serializeLString?_isSome_iff]
  | .bnode b => by
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, termFitsU32, Option.isSome_map,
        serializeLString?_isSome_iff]
  | .literal l => by
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, termFitsU32]
      exact serializeDeltaLiteral?_isSome_iff l
  | .tripleTerm s p o => by
      rw [serializeDeltaTerm?, termFitsU32, ← and_assoc, ← serializeTriplePrefix?_isSome_iff,
        ← serializeDeltaTerm?_isSome_iff o]
      cases serializeTriplePrefix? s p <;> cases serializeDeltaTerm? o <;> simp [bind, Option.bind]

/-- On the terms the version 1 codec admits, the version 2 encoder writes the
    same bytes: a version 1 frame is a version 2 frame. -/
theorem serializeDeltaTerm?_of_supported (t : Term)
    (hsup : BlockWireV0.termSupported t = true) :
    serializeDeltaTerm? t = serializeTerm? t := by
  cases t with
  | iri i => rfl
  | bnode b => rfl
  | literal l =>
      rw [BlockWireV0.termSupported, Option.isNone_iff_eq_none] at hsup
      simp only [serializeDeltaTerm?, serializeDeltaLeaf?, serializeDeltaLiteral?, serializeTerm?,
        hsup, Option.isSome_none, Bool.false_eq_true, if_false]
      cases l.val.langTag <;> rfl
  | tripleTerm _ _ _ => simp [BlockWireV0.termSupported] at hsup


#print axioms stringOfBytes?_bytesOfString
#print axioms parseLString_serializeLString?
#print axioms parseU8_cons
#print axioms parseSubject_serializeSubject?
#print axioms parseTerm_serializeTerm?
#print axioms serializeTerm?_supported
#print axioms parseTerm_serializeTerm?_checked
#print axioms termFitsU32b_iff
#print axioms serializeTerm?_eq_some_of_supported_of_fits
#print axioms parseTerm_serializeTerm
#print axioms parseDeltaLeaf_serializeDeltaLeaf?
#print axioms parseDeltaTermGo_serializeDeltaTerm?
#print axioms parseDeltaTerm_serializeDeltaTerm?
#print axioms serializeDeltaTerm?_isSome_iff
#print axioms serializeDeltaTerm?_of_supported
#print axioms subjectFitsU32b_iff

end L4Factoidal.Storage
