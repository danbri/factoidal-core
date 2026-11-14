/-
L4Factoidal.WebCodecs.Image: what `ImageDecoder` (WebCodecs §10) decides before and after the
pixels: whether a type is an image MIME type and one this engine decodes, and the orientation a
JPEG's Exif data gives its image. Record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 4.

  * `typeVerdict`: a type that is not a MIME type `type/subtype` (tokens, RFC 9110 §5.6.2) is
    invalid (a TypeError); `image/png`, `image/jpeg` and `image/gif` are supported (the engine
    decodes them in Lean); any other type is unsupported (NotSupportedError where the decoder is
    used), truthfully.
  * `exifOrientation`: the Orientation tag (0x0112) of IFD0 of the Exif segment (APP1) of a JPEG,
    in either byte order; 1 (as stored) when there is none (`exifOrientation_range`).
  * `orientationOf`: the eight Exif orientations as the frame's clockwise rotation and horizontal
    flip (the `VideoFrame` init), all distinct (`orientationOf_injective`).
-/
namespace L4Factoidal.WebCodecs.Image

/-- RFC 9110 `tchar`. -/
def tchar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-.^_`|~".toList.contains c

def token (s : String) : Bool := !s.isEmpty && s.toList.all tchar

inductive Verdict where
  | invalid | unsupported | supported
  deriving DecidableEq, Repr

def Verdict.name : Verdict → String
  | .invalid => "invalid" | .unsupported => "unsupported" | .supported => "supported"

/-- The types this engine decodes (lower case; MIME types are matched without case). -/
def decoded : List String := ["image/png", "image/jpeg", "image/gif"]

def typeVerdict (t : String) : Verdict :=
  let essence := (t.splitOn ";").headD ""
  match essence.splitOn "/" with
  | [a, b] =>
    if !(token a && token b) then .invalid
    else if decoded.contains (a.toLower ++ "/" ++ b.toLower) then .supported
    else .unsupported
  | _ => .invalid

/-- Policy. Says: a type is answered as supported only when its essence, without case, is one
of the three of `decoded`. -/
theorem typeVerdict_supported (t : String) (h : typeVerdict t = .supported) :
    ∃ a b, ((t.splitOn ";").headD "").splitOn "/" = [a, b] ∧
      decoded.contains (a.toLower ++ "/" ++ b.toLower) = true := by
  dsimp only [typeVerdict] at h
  split at h
  · rename_i a b hab
    refine ⟨a, b, hab, ?_⟩
    by_cases ht : (token a && token b) = true
    · by_cases hd : decoded.contains (a.toLower ++ "/" ++ b.toLower) = true
      · exact hd
      · simp [ht] at h
        exact absurd (by simpa using h) hd
    · simp [ht] at h
  · cases h

/-! ## Exif orientation -/

def u16 (b : ByteArray) (o : Nat) (le : Bool) : Nat :=
  if le then (b.get! o).toNat + (b.get! (o + 1)).toNat * 256 else (b.get! o).toNat * 256 + (b.get! (o + 1)).toNat

def u32 (b : ByteArray) (o : Nat) (le : Bool) : Nat :=
  if le then u16 b o true + u16 b (o + 2) true * 65536 else u16 b o false * 65536 + u16 b (o + 2) false

/-- The Orientation of the TIFF structure at `t` (Exif's), if IFD0 has one. -/
def tiffOrientation (b : ByteArray) (t : Nat) : Option Nat :=
  if t + 8 > b.size then none else
  let order := (b.get! t, b.get! (t + 1))
  let le? : Option Bool := if order == (0x49, 0x49) then some true else if order == (0x4D, 0x4D) then some false else none
  match le? with
  | none => none
  | some le =>
    let ifd := t + u32 b (t + 4) le
    if ifd + 2 > b.size then none else
    let n := u16 b ifd le
    ((List.range n).find? fun i =>
        let e := ifd + 2 + 12 * i
        e + 12 ≤ b.size && u16 b e le == 0x0112).map fun i => u16 b (ifd + 2 + 12 * i + 8) le

/-- The JPEG segments from `pos` (at most `fuel`): the orientation of the first Exif APP1. -/
def scan (b : ByteArray) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, pos =>
    if pos + 4 > b.size || b.get! pos != 0xFF then none else
    let marker := b.get! (pos + 1)
    if marker == 0xDA || marker == 0xD9 then none else
    let len := u16 b (pos + 2) false
    let exif := marker == 0xE1 && pos + 10 ≤ b.size &&
      [b.get! (pos + 4), b.get! (pos + 5), b.get! (pos + 6), b.get! (pos + 7), b.get! (pos + 8), b.get! (pos + 9)] ==
        [0x45, 0x78, 0x69, 0x66, 0, 0]
    if exif then tiffOrientation b (pos + 10) else scan b fuel (pos + 2 + len)

/-- The Exif orientation of a JPEG (1 to 8); 1 for any other image, or a value out of range. -/
def exifOrientation (b : ByteArray) : Nat :=
  if b.size < 4 || b.get! 0 != 0xFF || b.get! 1 != 0xD8 then 1 else
  match scan b b.size 2 with
  | some o => if 1 ≤ o && o ≤ 8 then o else 1
  | none => 1

/-- Bounds. Says: the orientation is one of the eight of Exif, whatever the bytes. -/
theorem exifOrientation_range (b : ByteArray) : 1 ≤ exifOrientation b ∧ exifOrientation b ≤ 8 := by
  unfold exifOrientation
  split
  · decide
  · split
    · rename_i o _
      split <;> simp_all
    · decide

/-- Exif orientation as rotation (degrees clockwise) then horizontal flip (WebCodecs' order). -/
def orientationOf : Nat → Nat × Bool
  | 2 => (0, true) | 3 => (180, false) | 4 => (180, true) | 5 => (90, true)
  | 6 => (90, false) | 7 => (270, true) | 8 => (270, false) | _ => (0, false)

/-- The eight orientations are eight different transforms. -/
theorem orientationOf_injective :
    ∀ a b : Fin 8, orientationOf (a.val + 1) = orientationOf (b.val + 1) → a = b := by decide

/-! ## Tests -/

#guard typeVerdict "image/png" == .supported
#guard typeVerdict "IMAGE/JPEG" == .supported
#guard typeVerdict "image/png; charset=x" == .supported
#guard typeVerdict "image/avif" == .unsupported
#guard typeVerdict "junk/type" == .unsupported
#guard typeVerdict "junk" == .invalid
#guard typeVerdict "" == .invalid
#guard typeVerdict "image/" == .invalid
-- A JPEG start, an APP1 Exif segment, little-endian TIFF with one IFD0 entry: Orientation 6.
private def jpeg (o : UInt8) : ByteArray := ⟨#[0xFF, 0xD8, 0xFF, 0xE1, 0, 30, 0x45, 0x78, 0x69, 0x66, 0, 0,
  0x49, 0x49, 42, 0, 8, 0, 0, 0, 1, 0, 0x12, 0x01, 3, 0, 1, 0, 0, 0, o, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xD9]⟩
#guard exifOrientation (jpeg 6) == 6
#guard exifOrientation (jpeg 9) == 1
#guard exifOrientation ⟨#[137, 80, 78, 71]⟩ == 1
#guard orientationOf 5 == (90, true)

end L4Factoidal.WebCodecs.Image
