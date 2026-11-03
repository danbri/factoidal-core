import L4Factoidal.Rendering.SfntNormalize
import L4Factoidal.Rendering.SfntGpos
import L4Factoidal.Unicode.Segmentation

/-!
# The Lean shaper pipeline

One left-to-right run through every stage of the Lean shaper
(https://github.com/danbri/factoidal/issues/1233): font-aware normalization,
nominal glyphs, cluster merging at HarfBuzz's monotone-grapheme level, GSUB,
GPOS. Clusters are given as UTF-8 byte offsets into the input text, as in the
`factoidal-font-data-v1` record.

Refused, with a message: a strong right-to-left character (the RTL shaper is
not implemented); a mark in a font with no GPOS table, where HarfBuzz uses its
own fallback mark positioning (a heuristic from glyph extents and combining
classes, not part of OpenType; not implemented); and everything the stages
refuse.
-/
namespace L4Factoidal.Rendering.SfntShape
open FontPolicy SfntMetrics SfntGpos

def isExtendedPictographic (c : Nat) : Bool :=
  Unicode.Segmentation.extPictTable.get c.toUInt32 != 0

def isRegionalIndicator (c : Nat) : Bool := 0x1F1E6 ≤ c && c ≤ 0x1F1FF

/-- HarfBuzz `hb_set_unicode_props` continuation flags (15.0.0): a mark
(General_Category M); an emoji modifier; a regional indicator after one that
is not itself a continuation; ZWJ and an Extended_Pictographic after it;
U+FF9E, U+FF9F and tags U+E0020 to U+E007F. ZWNJ is not a continuation. -/
def continuations (cps : Array Nat) : Array Bool := Id.run do
  let mut out : Array Bool := Array.replicate cps.size false
  let mut i := 0
  for _ in [0:cps.size] do
    if i ≥ cps.size then break
    let c := cps[i]!
    if isUnicodeMark c then out := out.set! i true
    else if c ≥ 0x80 then
      if 0x1F3FB ≤ c && c ≤ 0x1F3FF then out := out.set! i true
      else if i > 0 && isRegionalIndicator c then
        if isRegionalIndicator cps[i-1]! && !out[i-1]! then out := out.set! i true
      else if c == 0x200D then
        out := out.set! i true
        if i + 1 < cps.size && isExtendedPictographic cps[i+1]! then
          out := out.set! (i + 1) true
          i := i + 1
      else if (0xFF9E ≤ c && c ≤ 0xFF9F) || (0xE0020 ≤ c && c ≤ 0xE007F) then
        out := out.set! i true
    i := i + 1
  return out

/-- A strong right-to-left code point (Hebrew, Arabic, Syriac, Thaana, NKo,
Samaritan, Mandaic and their presentation forms). -/
def isStrongRtl (c : Nat) : Bool :=
  (0x0590 ≤ c && c ≤ 0x08FF) || (0xFB1D ≤ c && c ≤ 0xFDFF) || (0xFE70 ≤ c && c ≤ 0xFEFF) ||
  (0x10800 ≤ c && c ≤ 0x10FFF) || (0x1E800 ≤ c && c ≤ 0x1EFFF)

/-- HarfBuzz `is_default_ignorable` (hb-unicode.hh, 15.0.0). -/
def isDefaultIgnorable (c : Nat) : Bool :=
  c == 0x00AD || c == 0x034F || c == 0x061C || (0x17B4 ≤ c && c ≤ 0x17B5) ||
  (0x180B ≤ c && c ≤ 0x180F) || (0x200B ≤ c && c ≤ 0x200F) || (0x202A ≤ c && c ≤ 0x202E) ||
  (0x2060 ≤ c && c ≤ 0x206F) || (0xFE00 ≤ c && c ≤ 0xFE0F) || c == 0xFEFF ||
  (0xFFF0 ≤ c && c ≤ 0xFFF8) || (0x1D173 ≤ c && c ≤ 0x1D17A) || (0xE0000 ≤ c && c ≤ 0xE0FFF)

/-- HarfBuzz `space_fallback_type` (hb-unicode.hh, 15.0.0): 1 to 16 is a
divisor of the em; 17 is 4/18 em; 18 the space itself; 19 figure; 20
punctuation; 21 narrow; 0 not a space with a fallback. -/
def spaceFallbackType : Nat → Nat
  | 0x0020 | 0x00A0 => 18
  | 0x2000 | 0x2002 => 2
  | 0x2001 | 0x2003 | 0x3000 => 1
  | 0x2004 => 3 | 0x2005 => 4 | 0x2006 => 6 | 0x2007 => 19 | 0x2008 => 20
  | 0x2009 => 5 | 0x200A => 16 | 0x202F => 21 | 0x205F => 17
  | _ => 0

structure Shaped where
  script : String
  glyphs : Array Glyph
  /-- UTF-8 byte offset of each glyph's cluster. -/
  clusterBytes : Array Nat

def shape (b : ByteArray) (dir : Array TableRecord) (face : Face) (text : String)
    (limits : Limits := {}) : Except String Shaped := do
  if let some c := text.toList.find? (isStrongRtl ·.toNat) then
    throw s!"font.layout.unsupported: right-to-left text (U+{(String.ofList (Nat.toDigits 16 c.toNat)).toUpper}) needs the RTL shaper (https://github.com/danbri/factoidal/issues/1233)"
  let cps ← SfntNormalize.forFontIndexed face b text
  let mut nominal ← face.nominalOf b cps
  -- HarfBuzz normalizer fallbacks for characters the font lacks: Unicode
  -- spaces become the U+0020 glyph (width set after positioning) and U+2011
  -- becomes U+2010.
  let spaceGlyph ← face.glyph b ' '
  for k in [0:nominal.size] do
    let g := nominal[k]!
    if g.id == 0 then
      let st := spaceFallbackType g.codepoint
      if st != 0 && spaceGlyph != 0 then
        nominal := nominal.set! k { g with id := spaceGlyph, advance := face.advances[spaceGlyph]!, spaceFallback := st }
      else if g.codepoint == 0x2011 then
        let h ← face.glyph b (Char.ofNat 0x2010)
        if h != 0 then nominal := nominal.set! k { g with id := h, advance := face.advances[h]! }
  -- Monotone graphemes: a continuation joins the previous cluster.
  let cont := continuations (nominal.map (·.codepoint))
  for k in [1:nominal.size] do
    if cont[k]! then
      let g := nominal[k]!
      nominal := nominal.set! k { g with cluster := nominal[k - 1]!.cluster }
  let run ← SfntSubst.substitute face b dir text nominal limits
  if !dir.any (·.tag == "GPOS") then
    if let some g := run.find? (isUnicodeMark ·.codepoint) then
      throw s!"font.layout.unsupported: mark U+{(String.ofList (Nat.toDigits 16 g.codepoint)).toUpper} in a font with no GPOS table needs fallback mark positioning (https://github.com/danbri/factoidal/issues/1233)"
  let mut glyphs ← position b dir text run limits
  -- Space fallback widths (HarfBuzz `_hb_ot_shape_fallback_spaces`).
  let upem := face.unitsPerEm
  let advanceOf (c : Char) : Except String (Option Nat) := do
    let g ← face.glyph b c
    return if g == 0 then none else some face.advances[g]!
  let mut figure : Option Nat := none
  for d in "0123456789".toList do
    if figure.isNone then figure ← advanceOf d
  let punct := (← advanceOf '.').orElse fun _ => none
  let punct ← if punct.isSome then pure punct else advanceOf ','
  for k in [0:glyphs.size] do
    let g := glyphs[k]!
    if g.spaceFallback != 0 && !g.ligated then
      let st := g.spaceFallback
      let adv : Int :=
        if st ≤ 16 then ((upem + st / 2) / st : Nat)
        else if st == 17 then (upem * 4 / 18 : Nat)
        else if st == 19 then (figure.map (·: Nat → Int)).getD g.advance
        else if st == 20 then (punct.map (·: Nat → Int)).getD g.advance
        else if st == 21 then g.advance.tdiv 2
        else g.advance
      glyphs := glyphs.set! k { g with advance := adv }
  -- Default ignorables (HarfBuzz `hb_ot_zero_width_default_ignorables` and
  -- `hb_ot_hide_default_ignorables`): zero advance and x offset, then the
  -- space glyph, or deleted when the font has no space glyph.
  let ignorable (g : Glyph) : Bool := isDefaultIgnorable g.codepoint && !g.substituted
  if spaceGlyph != 0 then
    glyphs := glyphs.map fun g => if ignorable g then { g with id := spaceGlyph, advance := 0, xOffset := 0 } else g
  else
    glyphs := glyphs.filter (!ignorable ·)
  -- Source character index to UTF-8 byte offset.
  let mut offsets : Array Nat := #[]
  let mut acc := 0
  for c in text.toList do
    offsets := offsets.push acc
    acc := acc + c.utf8Size
  let script := match SfntKern.scriptTag text with
    | "latn" => "Latn" | "grek" => "Grek" | "cyrl" => "Cyrl" | _ => "Zyyy"
  return { script, glyphs, clusterBytes := glyphs.map fun g => offsets[g.cluster]?.getD acc }

end L4Factoidal.Rendering.SfntShape
