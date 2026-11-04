import L4Factoidal.Rendering.FontPolicy

/-!
# sfnt metrics and character map, read in Lean

First stage of the Lean shaper (owner decision 2 of 2026-11-03,
https://github.com/danbri/factoidal/issues/1233). This module reads, with
bounds checks, the tables needed to map text to glyphs without layout lookups:
`head` (units per em), `hhea` (ascender, descender, line gap, number of
long metrics), `maxp` (number of glyphs), `hmtx` (advance widths) and `cmap`
(subtable format 4 for the Basic Multilingual Plane, format 12 for all
Unicode scalar values, format 13 for many-to-one ranges). The OpenType specification is the reference;
HarfBuzz is the differential oracle.

It does not apply GSUB or GPOS. A run that needs them (ligatures, kerning,
joining) gives different glyphs or advances from HarfBuzz; `nominalRun` is the
nominal mapping only. Every loop is over input-proportional data and runs in
one frame.
-/
namespace L4Factoidal.Rendering.SfntMetrics
open FontPolicy

private def need (b : ByteArray) (i n : Nat) (what : String) : Except String Unit :=
  if i + n ≤ b.size then pure () else throw s!"font.file.malformed: {what} out of bounds"
private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 32768 then (v : Int) - 65536 else v

inductive CharMap where
  /-- Format 4 at this absolute offset, with its segment count. -/
  | format4 (offset segCount : Nat)
  /-- Format 12 at this absolute offset, with its group count. -/
  | format12 (offset groups : Nat)
  /-- Format 13 (many-to-one ranges) at this absolute offset, with its group count. -/
  | format13 (offset groups : Nat)
  /-- Format 0 (byte array of 256 glyph ids) at this absolute offset. -/
  | format0 (offset : Nat)
  /-- Format 6 (trimmed table) at this absolute offset. -/
  | format6 (offset firstCode count : Nat)
  deriving Repr, BEq

structure Face where
  unitsPerEm : Nat
  ascender : Int
  descender : Int
  lineGap : Int
  numGlyphs : Nat
  /-- One advance for each glyph id below `numGlyphs`. -/
  advances : Array Nat
  cmap : CharMap
  /-- The chosen subtable is (3,0) Symbol: a code point up to U+00FF the
  subtable lacks is looked up again at U+F000 plus it (HarfBuzz
  `_hb_symbol_pua_map`). -/
  cmapSymbol : Bool := false
  deriving Repr

private def table (dir : Array TableRecord) (tag : String) : Except String TableRecord :=
  match dir.find? (·.tag == tag) with
  | some t => pure t
  | none => throw s!"font.file.malformed: no {tag.quote} table"

/-- Choose the cmap subtable as HarfBuzz `find_best_subtable`: the first of
(3,0) Symbol, (3,10), (0,6), (0,4), (3,1), (0,3), (0,2), (0,1), (0,0) that
the font has. Formats 0, 4, 6, 12 and 13 are read; a Mac subtable only, or
another format, is refused. -/
private def chooseCmap (b : ByteArray) (t : TableRecord) : Except String (CharMap × Bool) := do
  need b t.offset 4 "cmap header"
  let n := u16 b (t.offset + 2)
  need b (t.offset + 4) (8 * n) "cmap encoding records"
  let order : List (Nat × Nat) := [(3, 0), (3, 10), (0, 6), (0, 4), (3, 1), (0, 3), (0, 2), (0, 1), (0, 0)]
  let find (pe : Nat × Nat) : Option Nat := (List.range n).findSome? fun k =>
    let r := t.offset + 4 + 8 * k
    if u16 b r == pe.1 && u16 b (r + 2) == pe.2 then some (t.offset + u32 b (r + 4)) else none
  let some (pe, sub) := order.findSome? (fun pe => (find pe).map (pe, ·))
    | throw "font.file.unsupported-cmap: no Unicode or Symbol cmap subtable"
  need b sub 2 "cmap subtable"
  let format := u16 b sub
  let cm ← if format == 12 || format == 13 then do
      need b sub 16 "cmap format 12 header"
      let groups := u32 b (sub + 12)
      need b (sub + 16) (12 * groups) "cmap format 12 groups"
      pure (if format == 12 then CharMap.format12 sub groups else CharMap.format13 sub groups)
    else if format == 4 then do
      need b sub 14 "cmap format 4 header"
      let segCount := u16 b (sub + 6) / 2
      need b (sub + 14) (8 * segCount + 2) "cmap format 4 arrays"
      pure (CharMap.format4 sub segCount)
    else if format == 0 then do
      need b sub (6 + 256) "cmap format 0"
      pure (CharMap.format0 sub)
    else if format == 6 then do
      need b sub 10 "cmap format 6 header"
      let count := u16 b (sub + 8)
      need b (sub + 10) (2 * count) "cmap format 6 glyph ids"
      pure (CharMap.format6 sub (u16 b (sub + 6)) count)
    else throw s!"font.file.unsupported-cmap: cmap subtable ({pe.1},{pe.2}) has format {format}"
  return (cm, pe == (3, 0))

/-- Read the face from the bytes and its checked table directory. -/
def Face.read (b : ByteArray) (dir : Array TableRecord) : Except String Face := do
  let head ← table dir "head"
  need b head.offset 54 "head"
  let upem := u16 b (head.offset + 18)
  unless 16 ≤ upem && upem ≤ 16384 do throw s!"font.file.malformed: unitsPerEm {upem}"
  let maxp ← table dir "maxp"
  need b maxp.offset 6 "maxp"
  let numGlyphs := u16 b (maxp.offset + 4)
  if numGlyphs == 0 then throw "font.file.malformed: no glyphs"
  let hhea ← table dir "hhea"
  need b hhea.offset 36 "hhea"
  let numLong := u16 b (hhea.offset + 34)
  unless 1 ≤ numLong && numLong ≤ numGlyphs do throw s!"font.file.malformed: numberOfHMetrics {numLong}"
  let hmtx ← table dir "hmtx"
  need b hmtx.offset (4 * numLong) "hmtx"
  let mut advances : Array Nat := Array.mkEmpty numGlyphs
  for g in [0:numGlyphs] do
    advances := advances.push (u16 b (hmtx.offset + 4 * (min g (numLong - 1))))
  let (cmap, cmapSymbol) ← chooseCmap b (← table dir "cmap")
  return { unitsPerEm := upem, ascender := i16 b (hhea.offset + 4), descender := i16 b (hhea.offset + 6),
           lineGap := i16 b (hhea.offset + 8), numGlyphs, advances, cmap, cmapSymbol }

/-- The glyph of code point `cp` in the chosen subtable; 0 when it has none. -/
def Face.glyphCp (f : Face) (b : ByteArray) (cp : Nat) : Except String Nat := do
  let g ← match f.cmap with
    | .format0 sub => pure (if cp < 256 then (b.get! (sub + 6 + cp)).toNat else 0)
    | .format6 sub first count =>
      pure (if first ≤ cp && cp < first + count then u16 b (sub + 10 + 2 * (cp - first)) else 0)
    | .format12 sub groups => do
      let mut found := 0
      for k in [0:groups] do
        let r := sub + 16 + 12 * k
        let lo := u32 b r
        let hi := u32 b (r + 4)
        if lo ≤ cp && cp ≤ hi then
          found := u32 b (r + 8) + (cp - lo)
          break
      pure found
    | .format13 sub groups => do
      let mut found := 0
      for k in [0:groups] do
        let r := sub + 16 + 12 * k
        if u32 b r ≤ cp && cp ≤ u32 b (r + 4) then
          found := u32 b (r + 8)
          break
      pure found
    | .format4 sub segCount => do
      if cp > 0xFFFF then pure 0 else
      let ends := sub + 14
      let starts := ends + 2 * segCount + 2
      let deltas := starts + 2 * segCount
      let ranges := deltas + 2 * segCount
      let mut found := 0
      for k in [0:segCount] do
        if u16 b (ends + 2 * k) ≥ cp then
          let start := u16 b (starts + 2 * k)
          if start ≤ cp then
            let delta := u16 b (deltas + 2 * k)
            let ro := u16 b (ranges + 2 * k)
            if ro == 0 then found := (cp + delta) % 65536
            else
              let addr := ranges + 2 * k + ro + 2 * (cp - start)
              need b addr 2 "cmap format 4 glyph index array"
              let raw := u16 b addr
              found := if raw == 0 then 0 else (raw + delta) % 65536
          break
      pure found
  -- A glyph id at or above numGlyphs is malformed data; map it to .notdef.
  return if g < f.numGlyphs then g else 0

/-- The nominal glyph of a character; 0 (`.notdef`) when the font has none. -/
def Face.glyph (f : Face) (b : ByteArray) (c : Char) : Except String Nat := do
  let g ← f.glyphCp b c.toNat
  if g == 0 && f.cmapSymbol && c.toNat ≤ 0xFF then f.glyphCp b (0xF000 + c.toNat) else pure g

structure NominalGlyph where
  id : Nat
  advance : Nat
  /-- Cluster: index of the source character (Unicode scalar offset). -/
  cluster : Nat
  /-- The code point this glyph was mapped from (kept through substitution). -/
  codepoint : Nat := 0
  /-- GSUB replaced this glyph (HarfBuzz `_hb_glyph_info_substituted`). -/
  substituted : Bool := false
  /-- GSUB formed a ligature at this glyph (HarfBuzz `_hb_glyph_info_ligated`). -/
  ligated : Bool := false
  /-- HarfBuzz space fallback type of a space mapped to the U+0020 glyph
  (`hb_unicode_funcs_t::space_t`; 0 = none). -/
  spaceFallback : Nat := 0
  deriving Repr, BEq, Inhabited

/-- One glyph for each character, by `cmap` and `hmtx` only (no GSUB/GPOS). -/
def Face.nominalRun (f : Face) (b : ByteArray) (text : String) : Except String (Array NominalGlyph) := do
  let mut out : Array NominalGlyph := #[]
  let mut i := 0
  for c in text.toList do
    let g ← f.glyph b c
    out := out.push { id := g, advance := f.advances[g]!, cluster := i, codepoint := c.toNat }
    i := i + 1
  return out

/-- One glyph for each (code point, source character index) pair. -/
def Face.nominalOf (f : Face) (b : ByteArray) (cps : Array (Nat × Nat)) : Except String (Array NominalGlyph) := do
  let mut out : Array NominalGlyph := Array.mkEmpty cps.size
  for (cp, src) in cps do
    let g ← if cp > 0x10FFFF || (0xD800 ≤ cp && cp ≤ 0xDFFF) then pure 0 else f.glyph b (Char.ofNat cp)
    out := out.push { id := g, advance := f.advances[g]!, cluster := src, codepoint := cp }
  return out

end L4Factoidal.Rendering.SfntMetrics
