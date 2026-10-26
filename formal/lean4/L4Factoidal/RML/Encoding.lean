/-
L4Factoidal.RML.Encoding — the character encodings an RML source or
target names with `rml:encoding`.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Encoding formats":
`rml:UTF-8` (the default) and `rml:UTF-16`.

A file is BYTES until it is decoded, and the decoding is the part of
"read the source" that RML-IO specifies. Keeping it here, as a total
function of the bytes, leaves the host with the only thing that needs
I/O: fetching the bytes by path.

UTF-16 with a byte order mark is decoded in the order the mark gives. UTF-16
with none is big-endian, as RFC 2781 section 4.3 says when the encoding is
the unmarked form `UTF-16`. Lone surrogates are an error; so is invalid UTF-8.
-/
import L4Factoidal.RML.Error

namespace L4Factoidal.RML

inductive Encoding where
  | utf8 | utf16
deriving Repr, DecidableEq, Inhabited

def utf8Iri : String := "http://w3id.org/rml/UTF-8"
def utf16Iri : String := "http://w3id.org/rml/UTF-16"

/-- The encoding an `rml:encoding` IRI names; the empty string is the
    default, UTF-8. `none` for any IRI RML-IO does not define. -/
def Encoding.ofIri? (iri : String) : Option Encoding :=
  if iri.isEmpty || iri == utf8Iri then some .utf8
  else if iri == utf16Iri then some .utf16
  else none

/-- Pair the bytes into 16-bit code units in the given byte order. A
    trailing odd byte is dropped by the caller's length check. -/
private def units (le : Bool) : List UInt8 → List Nat
  | a :: b :: rest =>
      (if le then a.toNat + 256 * b.toNat else 256 * a.toNat + b.toNat) :: units le rest
  | _ => []

/-- `units` onto a reverse accumulator: a tail call per code unit. The
input is a whole UTF-16 source file; `units` conses after its recursive
call, one frame per code unit (https://github.com/danbri/factoidal/issues/746). -/
private def unitsTR (le : Bool) (bs : List UInt8) : List Nat := go bs []
where
  go : List UInt8 → List Nat → List Nat
    | a :: b :: rest, acc =>
        go rest ((if le then a.toNat + 256 * b.toNat else 256 * a.toNat + b.toNat) :: acc)
    | _, acc => acc.reverse

private theorem unitsTR_go_eq (le : Bool) :
    ∀ (bs : List UInt8) (acc : List Nat), unitsTR.go le bs acc = acc.reverse ++ units le bs
  | a :: b :: rest, acc => by simp [unitsTR.go, units, unitsTR_go_eq le rest]
  | [_], acc => by simp [unitsTR.go, units]
  | [], acc => by simp [unitsTR.go, units]

@[csimp] private theorem units_eq_unitsTR : @units = @unitsTR := by
  funext le bs; simp [unitsTR, unitsTR_go_eq]

/-- Decode UTF-16 code units to characters, joining surrogate pairs. -/
private def charsOfUnits : List Nat → Option (List Char)
  | [] => some []
  | u :: rest =>
      if u < 0xD800 || u > 0xDFFF then
        (Char.ofNat u :: ·) <$> charsOfUnits rest
      else if u ≤ 0xDBFF then
        match rest with
        | v :: rest' =>
            if 0xDC00 ≤ v && v ≤ 0xDFFF then
              (Char.ofNat (0x10000 + ((u - 0xD800) * 0x400) + (v - 0xDC00)) :: ·)
                <$> charsOfUnits rest'
            else none
        | [] => none
      else none
termination_by us => us.length

/-- `charsOfUnits` onto a reverse accumulator: a tail call per character
of the decoded file (https://github.com/danbri/factoidal/issues/746). -/
private def charsOfUnitsTR (us : List Nat) : Option (List Char) := go us []
where
  go : List Nat → List Char → Option (List Char)
    | [], acc => some acc.reverse
    | u :: rest, acc =>
        if u < 0xD800 || u > 0xDFFF then go rest (Char.ofNat u :: acc)
        else if u ≤ 0xDBFF then
          match rest with
          | v :: rest' =>
              if 0xDC00 ≤ v && v ≤ 0xDFFF then
                go rest' (Char.ofNat (0x10000 + ((u - 0xD800) * 0x400) + (v - 0xDC00)) :: acc)
              else none
          | [] => none
        else none
  termination_by us => us.length

private theorem charsOfUnitsTR_go_eq :
    ∀ (us : List Nat) (acc : List Char),
      charsOfUnitsTR.go us acc = (charsOfUnits us).map (acc.reverse ++ ·)
  | [], acc => by simp [charsOfUnitsTR.go, charsOfUnits]
  | u :: rest, acc => by
      unfold charsOfUnitsTR.go charsOfUnits
      by_cases h1 : (u < 0xD800 || u > 0xDFFF) = true
      · simp only [h1, if_true]
        rw [charsOfUnitsTR_go_eq rest]
        cases charsOfUnits rest <;> simp
      · simp only [h1]
        by_cases h2 : u ≤ 0xDBFF
        · simp only [h2, if_true]
          match rest with
          | v :: rest' =>
              simp only
              by_cases h3 : (0xDC00 ≤ v && v ≤ 0xDFFF) = true
              · simp only [h3, if_true]
                rw [charsOfUnitsTR_go_eq rest']
                cases charsOfUnits rest' <;> simp
              · simp [h3]
          | [] => simp
        · simp [h2]
termination_by us => us.length

@[csimp] private theorem charsOfUnits_eq_charsOfUnitsTR : @charsOfUnits = @charsOfUnitsTR := by
  funext us; simp [charsOfUnitsTR, charsOfUnitsTR_go_eq]

/-- Decode UTF-16 bytes, honouring a byte order mark. -/
def decodeUtf16? (b : ByteArray) : Option String :=
  let bs := b.toList
  if bs.length % 2 != 0 then none
  else
    let (le, body) :=
      match bs with
      | 0xFF :: 0xFE :: rest => (true, rest)
      | 0xFE :: 0xFF :: rest => (false, rest)
      | _ => (false, bs)
    (String.ofList <$> charsOfUnits (units le body))

/-- Encode a string as UTF-16, little-endian, with a byte order mark. -/
def encodeUtf16Le (s : String) : ByteArray :=
  let unitsOf (c : Char) : List Nat :=
    let n := c.toNat
    if n < 0x10000 then [n]
    else
      let m := n - 0x10000
      [0xD800 + m / 0x400, 0xDC00 + m % 0x400]
  let us := s.toList.flatMap unitsOf
  ByteArray.mk (#[0xFF, 0xFE] ++ (us.flatMap (fun u =>
    [UInt8.ofNat (u % 256), UInt8.ofNat (u / 256)])).toArray)

/-- Decode a file's bytes in the named encoding. UTF-8 drops a leading
    byte order mark. -/
def decodeBytes (enc : Encoding) (b : ByteArray) : Option String :=
  match enc with
  | .utf16 => decodeUtf16? b
  | .utf8 =>
      let b' := if b.size ≥ 3 && b.get! 0 == 0xEF && b.get! 1 == 0xBB && b.get! 2 == 0xBF
                then b.extract 3 b.size else b
      String.fromUTF8? b'

/-- Encode text in the named encoding. -/
def encodeText (enc : Encoding) (s : String) : ByteArray :=
  match enc with
  | .utf8  => s.toUTF8
  | .utf16 => encodeUtf16Le s

/-! ## Build-time checks -/

-- UTF-8 decodes, rejects invalid bytes, drops a byte order mark.
#guard decodeBytes .utf8 "Zoë".toUTF8 == some "Zoë"
#guard decodeBytes .utf8 (ByteArray.mk #[0xC3, 0x28]) == none
#guard decodeBytes .utf8 (ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x41]) == some "A"
-- UTF-16: both byte orders, with and without a mark; a pair outside the BMP.
#guard decodeBytes .utf16 (ByteArray.mk #[0xFF, 0xFE, 0x41, 0x00, 0xEB, 0x00]) == some "Aë"
#guard decodeBytes .utf16 (ByteArray.mk #[0xFE, 0xFF, 0x00, 0x41, 0x00, 0xEB]) == some "Aë"
#guard decodeBytes .utf16 (ByteArray.mk #[0x00, 0x41]) == some "A"
#guard decodeBytes .utf16 (ByteArray.mk #[0xFF, 0xFE, 0x3D, 0xD8, 0x00, 0xDE]) == some "😀"
-- A lone surrogate and an odd length are errors.
#guard decodeBytes .utf16 (ByteArray.mk #[0xFF, 0xFE, 0x3D, 0xD8]) == none
#guard decodeBytes .utf16 (ByteArray.mk #[0xFF, 0xFE, 0x41]) == none
-- The encoder and decoder agree, and the encoding differs from UTF-8.
#guard decodeBytes .utf16 (encodeText .utf16 "Zoë 😀 x") == some "Zoë 😀 x"
#guard (encodeText .utf16 "ab").size == 6
#guard (encodeText .utf8 "ab").size == 2
-- The IRIs.
#guard Encoding.ofIri? "" == some .utf8
#guard Encoding.ofIri? utf16Iri == some .utf16
#guard Encoding.ofIri? "http://w3id.org/rml/UTF-32" == none

end L4Factoidal.RML
