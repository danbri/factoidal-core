import L4Factoidal.Rendering.SfntGpos
import L4Factoidal.Rendering.SfntCff
import L4Factoidal.Unicode.Normalization

/-!
# HarfBuzz fallback mark positioning, in Lean

For a font with no GPOS table, HarfBuzz places combining marks from glyph
extents and combining classes (`hb-ot-shape-fallback.cc`, HarfBuzz 15.0.0).
This is a heuristic, not part of OpenType; it is ported so that the Lean
shaper gives the same positions as the HarfBuzz oracle
(https://github.com/danbri/factoidal/issues/1233).

Ported: the modified combining class (`hb-unicode.hh`, `_hb_modified_combining_class`),
`recategorize_combining_class`, `position_mark`, `position_around_base`,
`position_cluster`, glyph extents of `glyf` fonts (`GlyphHeader::get_extents_without_var_scaled`:
the x bearing is the `hmtx` left side bearing). Left-to-right only.

CFF fonts get extents from `SfntCff` (Type 2 charstrings interpreted in
Lean). A font with neither `glyf` nor CFF has no extents: HarfBuzz then leaves
the marks zeroed. Refused: CFF2, and a mark after a ligature glyph (HarfBuzz
places it by ligature component; components are not tracked here).
-/
namespace L4Factoidal.Rendering.SfntFallback
open FontPolicy SfntMetrics SfntGpos

private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 32768 then (v : Int) - 65536 else v

/-- HarfBuzz `modified_combining_class` (hb-unicode.hh and hb-unicode.cc, 15.0.0). -/
def modifiedCcc (u : Nat) : Nat :=
  if u == 0x1A60 || u == 0x0FC6 then 254 else if u == 0x0F39 then 127 else
  match Unicode.Normalization.ccc u with
  | 10 => 22 | 11 => 15 | 12 => 16 | 13 => 17 | 14 => 23 | 15 => 18 | 16 => 19
  | 17 => 20 | 18 => 21 | 19 => 14 | 20 => 24 | 21 => 12 | 22 => 25 | 23 => 13
  | 24 => 10 | 25 => 11 | 26 => 26
  | 27 => 28 | 28 => 29 | 29 => 30 | 30 => 31 | 31 => 32 | 32 => 33 | 33 => 27
  | 34 => 34 | 35 => 35 | 36 => 36
  | 84 => 4 | 91 => 5 | 103 => 3 | 107 => 107 | 118 => 118 | 122 => 122
  | 129 => 129 | 130 => 132 | 132 => 131
  | c => c

/-- HarfBuzz `recategorize_combining_class`. Classes: 200 attached below
left, 202 attached below, 214 attached above, 216 attached above right, 218
below left, 220 below, 222 below right, 228 above left, 230 above, 232 above
right, 233 double below, 234 double above. -/
def recategorize (u klass : Nat) : Nat := Id.run do
  if klass ≥ 200 then return klass
  let mut k := klass
  if u / 256 == 0x0E then
    if k == 0 then
      if [0x0E31, 0x0E34, 0x0E35, 0x0E36, 0x0E37, 0x0E47, 0x0E4C, 0x0E4D, 0x0E4E].contains u then k := 232
      else if [0x0EB1, 0x0EB4, 0x0EB5, 0x0EB6, 0x0EB7, 0x0EBB, 0x0ECC, 0x0ECD].contains u then k := 230
      else if u == 0x0EBC then k := 220
    else if u == 0x0E3A then k := 222
  return match k with
    | 22 | 15 | 16 | 17 | 23 | 18 | 19 | 20 | 21 | 24 | 25 => 220
    | 13 => 214
    | 10 => 232
    | 11 | 14 => 228
    | 26 => 230
    | 28 | 29 | 31 | 32 | 27 | 34 | 35 | 36 => 230
    | 30 | 33 => 220
    | 3 => 222
    | 107 => 232
    | 118 => 220
    | 122 => 230
    | 129 => 220
    | 132 => 230
    | 131 => 220
    | c => c

structure Extents where
  xBearing : Int
  yBearing : Int
  width : Int
  height : Int
  deriving Repr, Inhabited

/-- Glyph extents as HarfBuzz computes them for a font with no variations:
`glyf` with the `hmtx` left side bearing, or CFF charstring bounds (`cff`, the
parsed CFF table); none when HarfBuzz gets none. -/
def extents (b : ByteArray) (dir : Array TableRecord) (cff : Option SfntCff.Font) (g : Nat) :
    Except String (Option Extents) := do
  let some glyf := dir.find? (·.tag == "glyf") | do
    match cff with
    | some f =>
      match ← SfntCff.extents b f g with
      | some (xb, yb, w, h) => return some ⟨xb, yb, w, h⟩
      | none => return none
    | none =>
      if dir.any (·.tag == "CFF2") then
        throw "font.layout.unsupported: fallback mark positioning in a CFF2 font (https://github.com/danbri/factoidal/issues/1233)"
      return none
  let some loca := dir.find? (·.tag == "loca") | throw "font.file.malformed: glyf without loca"
  let some head := dir.find? (·.tag == "head") | throw "font.file.malformed: no head table"
  let some hhea := dir.find? (·.tag == "hhea") | throw "font.file.malformed: no hhea table"
  let some hmtx := dir.find? (·.tag == "hmtx") | throw "font.file.malformed: no hmtx table"
  let long := i16 b (head.offset + 50) == 1
  let (o0, o1) := if long then (u32 b (loca.offset + 4 * g), u32 b (loca.offset + 4 * g + 4))
                  else (2 * u16 b (loca.offset + 2 * g), 2 * u16 b (loca.offset + 2 * g + 2))
  if (if long then 4 else 2) * (g + 2) > loca.length then throw "font.file.malformed: loca too short"
  if o1 ≤ o0 then return some ⟨0, 0, 0, 0⟩
  if o0 + 10 > glyf.length then throw "font.file.malformed: glyf header out of bounds"
  let h := glyf.offset + o0
  let (xMin, yMin, xMax, yMax) := (i16 b (h + 2), i16 b (h + 4), i16 b (h + 6), i16 b (h + 8))
  let numLong := u16 b (hhea.offset + 34)
  let lsbAt := if g < numLong then hmtx.offset + 4 * g + 2 else hmtx.offset + 4 * numLong + 2 * (g - numLong)
  let lsb := if lsbAt + 2 ≤ hmtx.offset + hmtx.length then i16 b lsbAt else min xMin xMax
  return some ⟨lsb, max yMin yMax, max xMin xMax - min xMin xMax, min yMin yMax - max yMin yMax⟩

/-- HarfBuzz `is_default_ignorable` (hb-unicode.hh, 15.0.0). -/
def isDefaultIgnorable (c : Nat) : Bool :=
  c == 0x00AD || c == 0x034F || c == 0x061C || (0x17B4 ≤ c && c ≤ 0x17B5) ||
  (0x180B ≤ c && c ≤ 0x180F) || (0x200B ≤ c && c ≤ 0x200F) || (0x202A ≤ c && c ≤ 0x202E) ||
  (0x2060 ≤ c && c ≤ 0x206F) || (0xFE00 ≤ c && c ≤ 0xFE0F) || c == 0xFEFF ||
  (0xFFF0 ≤ c && c ≤ 0xFFF8) || (0x1D173 ≤ c && c ≤ 0x1D17A) || (0xE0000 ≤ c && c ≤ 0xE0FFF)

/-- Characters HarfBuzz marks hidden: Mongolian free variation selectors,
tags, combining grapheme joiner. -/
def isHidden (c : Nat) : Bool :=
  (0x180B ≤ c && c ≤ 0x180D) || c == 0x180F || (0xE0020 ≤ c && c ≤ 0xE007F) || c == 0x034F

/-- HarfBuzz `position_mark`, for a left-to-right run. -/
def positionMark (base : Extents) (mark : Extents) (cc : Nat) (yGap : Int) : Extents × Int × Int := Id.run do
  let mut base := base
  let mut x : Int := 0
  let mut y : Int := 0
  if cc == 233 || cc == 234 then
    x := base.xBearing + base.width - mark.width.tdiv 2 - mark.xBearing
  else if cc == 200 || cc == 218 || cc == 228 then
    x := base.xBearing - mark.xBearing
  else if cc == 216 || cc == 222 || cc == 232 then
    x := base.xBearing + base.width - mark.width - mark.xBearing
  else
    x := base.xBearing + (base.width - mark.width).tdiv 2 - mark.xBearing
  let below := cc == 233 || cc == 218 || cc == 220 || cc == 222
  let attachedBelow := cc == 200 || cc == 202
  let above := cc == 234 || cc == 228 || cc == 230 || cc == 232
  let attachedAbove := cc == 214 || cc == 216
  if below || attachedBelow then
    if below then base := { base with height := base.height - yGap }
    y := base.yBearing + base.height - mark.yBearing
    if (yGap > 0) == (y > 0) then
      base := { base with height := base.height - y }
      y := 0
    base := { base with height := base.height + mark.height }
  else if above || attachedAbove then
    if above then base := { base with yBearing := base.yBearing + yGap, height := base.height - yGap }
    y := base.yBearing - mark.yBearing - mark.height
    if (yGap > 0) != (y > 0) then
      let correction := -(y.tdiv 2)
      base := { base with yBearing := base.yBearing + correction, height := base.height - correction }
      y := y + correction
    base := { base with yBearing := base.yBearing - mark.height, height := base.height + mark.height }
  return (base, x, y)

/-- HarfBuzz `_hb_ot_shape_fallback_mark_position` over a positioned run of
a font with no GPOS table. `advances` are the `hmtx` advances by glyph id. -/
def position (b : ByteArray) (dir : Array TableRecord) (upem : Nat) (advances : Array Nat)
    (isMark : Glyph → Bool) (run : Array Glyph) : Except String (Array Glyph) := do
  let mut out := run
  let n := out.size
  let ignorable (g : Glyph) : Bool := isHidden g.codepoint ||
    (isDefaultIgnorable g.codepoint && !g.substituted)
  let yGap : Int := (upem / 16 : Nat)
  let cff ← match dir.find? (·.tag == "CFF ") with
    | some t => pure (some (← SfntCff.readFont b t.offset t.length))
    | none => pure none
  -- Cluster starts: a glyph that is not a mark, not hidden and not ignorable.
  let mut starts : Array Nat := #[0]
  for i in [1:n] do
    let g := out[i]!
    if !isMark g && !ignorable g then starts := starts.push i
  starts := starts.push n
  for k in [0:starts.size - 1] do
    let s := starts[k]!
    let e := starts[k + 1]!
    if e - s < 2 then continue
    -- position_cluster_impl: bases and their following marks.
    let mut i := s
    for _ in [0:e - s] do
      if i ≥ e then break
      if isMark out[i]! then
        i := i + 1
        continue
      let mut j := i + 1
      for _ in [0:e - i] do
        if j ≥ e then break
        let gj := out[j]!
        if ignorable gj then
          j := j + 1
          continue
        if !isMark gj then break
        j := j + 1
      -- position_around_base (base i, marks up to j).
      let base := out[i]!
      if j > i + 1 then
        if base.ligated then
          throw s!"font.layout.unsupported: fallback mark positioning on a ligature glyph (https://github.com/danbri/factoidal/issues/1233)"
        -- No base extents: HarfBuzz zeroes the marks (already zero) and stops.
        let some be ← extents b dir cff base.id | do
          i := j
          continue
        let baseWidth : Nat := advances[base.id]?.getD 0
        let baseExt : Extents := { be with yBearing := be.yBearing + base.yOffset, xBearing := 0, width := baseWidth }
        let mut xOff : Int := -base.advance
        let mut cluster := baseExt
        let mut lastCc := 255
        for m in [i + 1:j] do
          let g := out[m]!
          let cc := if isMark g then recategorize g.codepoint (modifiedCcc g.codepoint) else 0
          if cc != 0 then
            if lastCc != cc then
              lastCc := cc
              cluster := baseExt
            match ← extents b dir cff g.id with
            | some me =>
              let (c2, x, y) := positionMark cluster me cc yGap
              cluster := c2
              out := out.set! m { g with advance := 0, xOffset := x + xOff, yOffset := y }
            | none =>
              -- No mark extents: HarfBuzz keeps the offsets and adds the run offset.
              out := out.set! m { g with advance := 0, xOffset := g.xOffset + xOff }
          else
            xOff := xOff - g.advance
      i := j
  return out

end L4Factoidal.Rendering.SfntFallback
