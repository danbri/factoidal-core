import L4Factoidal.Rendering.FontPolicy

/-!
# sfnt metrics and character map, read in Lean

First stage of the Lean shaper (owner decision 2 of 2026-11-03,
https://github.com/danbri/factoidal/issues/1233). This module reads, with
bounds checks, the tables needed to map text to glyphs without layout lookups:
`head` (units per em), `hhea` (ascender, descender, line gap, number of
long metrics), `maxp` (number of glyphs), `hmtx` (advance widths) and `cmap`
(subtable format 4 for the Basic Multilingual Plane and format 12 for all
Unicode scalar values). The OpenType specification is the reference;
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
  deriving Repr

private def table (dir : Array TableRecord) (tag : String) : Except String TableRecord :=
  match dir.find? (·.tag == tag) with
  | some t => pure t
  | none => throw s!"font.file.malformed: no {tag.quote} table"

/-- Choose the cmap subtable: (3,10) or (0,4) format 12 first, then (3,1) or
(0,3) format 4, in the order of the OpenType `cmap` recommendations. -/
private def chooseCmap (b : ByteArray) (t : TableRecord) : Except String CharMap := do
  need b t.offset 4 "cmap header"
  let n := u16 b (t.offset + 2)
  need b (t.offset + 4) (8 * n) "cmap encoding records"
  let mut best : Option (Nat × CharMap) := none
  for k in [0:n] do
    let r := t.offset + 4 + 8 * k
    let platform := u16 b r
    let encoding := u16 b (r + 2)
    let sub := t.offset + u32 b (r + 4)
    let rank? : Option Nat :=
      if (platform == 3 && encoding == 10) || (platform == 0 && encoding == 4) then some 0
      else if (platform == 3 && encoding == 1) || (platform == 0 && encoding == 3) then some 1
      else none
    let some rank := rank? | continue
    need b sub 2 "cmap subtable"
    let format := u16 b sub
    let cand? ← if format == 12 then do
        need b sub 16 "cmap format 12 header"
        let groups := u32 b (sub + 12)
        need b (sub + 16) (12 * groups) "cmap format 12 groups"
        pure (some (CharMap.format12 sub groups))
      else if format == 4 then do
        need b sub 14 "cmap format 4 header"
        let segCount := u16 b (sub + 6) / 2
        need b (sub + 14) (8 * segCount + 2) "cmap format 4 arrays"
        pure (some (CharMap.format4 sub segCount))
      else pure none
    match cand?, best with
    | some c, none => best := some (rank, c)
    | some c, some (r0, _) => if rank < r0 then best := some (rank, c)
    | none, _ => pure ()
  match best with
  | some (_, c) => pure c
  | none => throw "font.file.unsupported-cmap: no Unicode cmap subtable of format 4 or 12"

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
  let cmap ← chooseCmap b (← table dir "cmap")
  return { unitsPerEm := upem, ascender := i16 b (hhea.offset + 4), descender := i16 b (hhea.offset + 6),
           lineGap := i16 b (hhea.offset + 8), numGlyphs, advances, cmap }

/-- The nominal glyph of a code point; 0 (`.notdef`) when the font has none. -/
def Face.glyph (f : Face) (b : ByteArray) (c : Char) : Except String Nat := do
  let cp := c.toNat
  let g ← match f.cmap with
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

structure NominalGlyph where
  id : Nat
  advance : Nat
  /-- Cluster: index of the source character (Unicode scalar offset). -/
  cluster : Nat
  /-- The code point this glyph was mapped from (kept through substitution). -/
  codepoint : Nat := 0
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
