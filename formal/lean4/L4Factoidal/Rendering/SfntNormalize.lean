import L4Factoidal.Unicode.Normalization
import L4Factoidal.Rendering.SfntMetrics

/-!
# Font-aware normalization before glyph mapping

Stage of the Lean shaper (https://github.com/danbri/factoidal/issues/1233)
that HarfBuzz runs before GSUB in its default "composed" mode. It uses the
UAX #15 tables of `Unicode.Normalization`; the font decides what is kept:

1. Decompose: a character that the font has is kept. A character that the font
   does not have is replaced by its full canonical decomposition, if the font
   has every character of it; otherwise it is kept (and maps to `.notdef`).
2. Reorder: each run of characters with a non-zero Canonical_Combining_Class
   is sorted stably by that class (UAX #15 section 3).
3. Compose: a character with a non-zero combining class that is not blocked
   from the last starter (UAX #15 section 4) is composed with it, if the
   primary composite exists and the font has it.

Known difference from HarfBuzz, measured cases only: HarfBuzz composes only
marks of General_Category Mn, Mc or Me and has script-specific reordering
(for example Arabic modifier combining marks). Neither is here yet.
-/
namespace L4Factoidal.Rendering.SfntNormalize
open SfntMetrics Unicode.Normalization

/-- Code points of `text`, normalized for the font. -/
def forFont (f : Face) (b : ByteArray) (text : String) : Except String (Array Nat) := do
  let has (c : Nat) : Except String Bool := do
    if c > 0x10FFFF || (0xD800 ≤ c && c ≤ 0xDFFF) then return false
    return (← f.glyph b (Char.ofNat c)) != 0
  -- 1. decompose what the font lacks
  let mut dec : Array Nat := #[]
  for ch in text.toList do
    let c := ch.toNat
    if ← has c then
      dec := dec.push c
    else
      let parts := decomposeCps false #[c]
      let mut all : Bool := parts.size > 1
      for p in parts do
        unless ← has p do all := false
      dec := if all then dec ++ parts else dec.push c
  -- 2. canonical order of combining marks
  let ordered := reorder dec
  -- 3. compose where the font has the composite
  let mut out : Array Nat := Array.mkEmpty ordered.size
  let mut starter : Option Nat := none
  let mut lastCcc : Nat := 0
  for c in ordered do
    let cc := ccc c
    let mut done := false
    if let some si := starter then
      let adjacent := out.size == si + 1
      let blocked := !adjacent && (lastCcc == 0 || lastCcc ≥ cc)
      if cc != 0 && !blocked then
        if let some comp := composePair out[si]! c then
          if ← has comp then
            out := out.set! si comp
            done := true
    if !done then
      if cc == 0 then starter := some out.size
      out := out.push c
      lastCcc := cc
  return out

/-- `nominalRun` after font-aware normalization. Clusters are positions in the
normalized code point sequence. -/
def nominalRun (f : Face) (b : ByteArray) (text : String) : Except String (Array NominalGlyph) := do
  let cps ← forFont f b text
  f.nominalRun b (String.ofList (cps.toList.map Char.ofNat))

end L4Factoidal.Rendering.SfntNormalize
