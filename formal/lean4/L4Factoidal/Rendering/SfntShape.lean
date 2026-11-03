import L4Factoidal.Rendering.SfntNormalize
import L4Factoidal.Rendering.SfntGpos

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

/-- A character that HarfBuzz joins to the previous cluster at the
monotone-grapheme level: a mark, ZWNJ, ZWJ, a variation selector, or an
emoji modifier. -/
def isContinuation (c : Nat) : Bool :=
  isUnicodeMark c || c == 0x200C || c == 0x200D || (0xFE00 ≤ c && c ≤ 0xFE0F) ||
  (0xE0100 ≤ c && c ≤ 0xE01EF) || (0x1F3FB ≤ c && c ≤ 0x1F3FF)

/-- A strong right-to-left code point (Hebrew, Arabic, Syriac, Thaana, NKo,
Samaritan, Mandaic and their presentation forms). -/
def isStrongRtl (c : Nat) : Bool :=
  (0x0590 ≤ c && c ≤ 0x08FF) || (0xFB1D ≤ c && c ≤ 0xFDFF) || (0xFE70 ≤ c && c ≤ 0xFEFF) ||
  (0x10800 ≤ c && c ≤ 0x10FFF) || (0x1E800 ≤ c && c ≤ 0x1EFFF)

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
  -- Monotone graphemes: a continuation joins the previous cluster.
  for k in [1:nominal.size] do
    if isContinuation nominal[k]!.codepoint then
      let g := nominal[k]!
      nominal := nominal.set! k { g with cluster := nominal[k - 1]!.cluster }
  let run ← SfntSubst.substitute face b dir text nominal limits
  if !dir.any (·.tag == "GPOS") then
    if let some g := run.find? (isUnicodeMark ·.codepoint) then
      throw s!"font.layout.unsupported: mark U+{(String.ofList (Nat.toDigits 16 g.codepoint)).toUpper} in a font with no GPOS table needs fallback mark positioning (https://github.com/danbri/factoidal/issues/1233)"
  let glyphs ← position b dir text run limits
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
