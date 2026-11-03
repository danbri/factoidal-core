import L4Factoidal.Rendering.SfntSubst
import L4Factoidal.WHATWG.URL.IdnaData

/-!
# GPOS positioning in Lean

Stage of the Lean shaper (https://github.com/danbri/factoidal/issues/1233)
that replaces the `kern`-only pass of `SfntKern.kern` for a full run. It
follows HarfBuzz's default shaper for a left-to-right run:

1. advances from `hmtx`;
2. the lookups of the default GPOS features (`abvm`, `blwm`, `dist`, `kern`,
   `mark`, `mkmk`) once each, in lookup list order: type 1 (single
   adjustment), type 2 (pair adjustment), type 4 (mark-to-base) and type 6
   (mark-to-mark), with extension type 9;
3. glyphs of GDEF class 3 (mark) get zero advance; when the font has no GPOS
   their x offset is also reduced by the advance they had
   (HarfBuzz `adjust_mark_positioning_when_zeroing`). A font with no GDEF glyph
   class definition gets classes from the source character, as HarfBuzz's
   `hb_synthesize_glyph_classes` does: General_Category Mn, Mc or Me is a mark,
   anything else a base (`WHATWG.URL.IdnaData.markText`, Unicode 18.0.0);
4. each attached mark gets the offsets of the glyph it is attached to, less
   the advances from that glyph up to the mark.

Refused, with a message naming the lookup: type 3 (cursive), type 5
(mark-to-ligature), types 7 and 8, mark filtering sets. Device tables in value
records and anchors are not applied (unhinted, no variations). The OpenType
GPOS chapter is the reference; HarfBuzz is the differential oracle.
-/
namespace L4Factoidal.Rendering.SfntGpos
open FontPolicy SfntMetrics SfntKern SfntSubst

private def need (b : ByteArray) (i n : Nat) (what : String) : Except String Unit :=
  if i + n ≤ b.size then pure () else throw s!"font.file.malformed: GPOS {what} out of bounds"
private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 32768 then (v : Int) - 65536 else v

structure Glyph where
  id : Nat
  advance : Int
  xOffset : Int
  yOffset : Int
  cluster : Nat
  /-- Position of the glyph this mark is attached to. -/
  attachedTo : Option Nat := none
  deriving Repr, BEq, Inhabited

def defaultFeatures : List String := ["abvm", "blwm", "dist", "kern", "mark", "mkmk"]

/-- (x placement, y placement, x advance) of a value record. -/
def valueXYA (b : ByteArray) (fmt off : Nat) : Int × Int × Int :=
  let has (bit : Nat) := fmt / 2 ^ bit % 2 == 1
  let at_ (bit : Nat) : Nat := off + 2 * ((List.range bit).filter has).length
  ((if has 0 then i16 b (at_ 0) else 0), (if has 1 then i16 b (at_ 1) else 0), (if has 2 then i16 b (at_ 2) else 0))

/-- Anchor point (formats 1 to 3; the contour point and device tables of
formats 2 and 3 are not used). -/
def anchor (b : ByteArray) (off : Nat) : Except String (Int × Int) := do
  need b off 6 "anchor"
  let fmt := u16 b off
  unless 1 ≤ fmt && fmt ≤ 3 do throw s!"font.file.malformed: anchor format {fmt}"
  return (i16 b (off + 2), i16 b (off + 4))

/-- Mark class and anchor of the mark at coverage index `ci` of a MarkArray. -/
def markRecord (b : ByteArray) (arr ci : Nat) : Except String (Nat × Int × Int) := do
  need b arr 2 "mark array"
  if ci ≥ u16 b arr then throw "font.file.malformed: mark coverage index beyond mark array"
  let r := arr + 2 + 4 * ci
  need b r 4 "mark record"
  let a ← anchor b (arr + u16 b (r + 2))
  return (u16 b r, a)

/-- Anchor of class `cls` for the base at index `bi` of a BaseArray or
Mark2Array with `classes` classes; none for a null offset. -/
def baseAnchor (b : ByteArray) (arr bi classes cls : Nat) : Except String (Option (Int × Int)) := do
  need b arr 2 "base array"
  if bi ≥ u16 b arr then throw "font.file.malformed: base coverage index beyond base array"
  let r := arr + 2 + 2 * classes * bi
  need b r (2 * classes) "base record"
  if cls ≥ classes then throw "font.file.malformed: mark class beyond class count"
  let o := u16 b (r + 2 * cls)
  if o == 0 then return none
  return some (← anchor b (arr + o))

/-- Ranges of General_Category Mn, Mc and Me, from `IdnaData.markText`. -/
def unicodeMarkRanges : Array (Nat × Nat) :=
  let hex (t : String) : Nat :=
    t.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toUpper.toNat - 55)) 0
  ((WHATWG.URL.IdnaData.markText.splitOn ";").filter (· != "")).toArray.map fun r =>
    match r.splitOn "-" with
    | [a, z] => (hex a, hex z)
    | _ => (hex r, hex r)

def isUnicodeMark (c : Nat) : Bool := unicodeMarkRanges.any fun (a, z) => a ≤ c && c ≤ z

/-- Apply the default GPOS features to a substituted run. A synthesized
glyph class uses the glyph's source code point (`NominalGlyph.codepoint`). -/
def position (b : ByteArray) (dir : Array TableRecord) (text : String)
    (run : Array NominalGlyph) (limits : Limits := {}) : Except String (Array Glyph) := do
  let mut out : Array Glyph := run.map fun g => { id := g.id, advance := g.advance, xOffset := 0, yOffset := 0, cluster := g.cluster }
  let gdef? := (dir.find? (·.tag == "GDEF")).map (·.offset)
  let hasGlyphClasses : Bool := match gdef? with
    | some gd => gd + 6 ≤ b.size && u16 b (gd + 4) != 0
    | none => false
  let classes ← run.mapM fun g => do
    if hasGlyphClasses then gdefClasses b gdef? g.id
    else
      let (_, mc) ← gdefClasses b gdef? g.id
      pure (if isUnicodeMark g.codepoint then 3 else 1, mc)
  let isMark (k : Nat) : Bool := classes[k]!.1 == 3
  if let some gposRec := dir.find? (·.tag == "GPOS") then
    let gpos := gposRec.offset
    let lookups ← featureLookups b gpos (scriptTag text) defaultFeatures
    let lookupList := gpos + u16 b (gpos + 8)
    need b lookupList 2 "lookup list"
    let nl := u16 b lookupList
    let mut ops := 0
    for (_, l) in lookups do
      if l ≥ nl then throw "font.file.malformed: GPOS lookup index"
      need b (lookupList + 2 + 2 * l) 2 "lookup offset"
      let lk := lookupList + u16 b (lookupList + 2 + 2 * l)
      need b lk 6 "lookup"
      let ltype := u16 b lk
      let flag := u16 b (lk + 2)
      if flag &&& 0x10 != 0 then
        throw s!"font.layout.unsupported: GPOS lookup {l} uses a mark filtering set (https://github.com/danbri/factoidal/issues/1233)"
      let nsub := u16 b (lk + 4)
      need b (lk + 6) (2 * nsub) "subtable offsets"
      let mut subs : Array (Nat × Nat) := #[]
      for k in [0:nsub] do
        let s := lk + u16 b (lk + 6 + 2 * k)
        if ltype == 9 then
          need b s 8 "extension"
          subs := subs.push (u16 b (s + 2), s + u32 b (s + 4))
        else subs := subs.push (ltype, s)
      for (t, _) in subs do
        unless t == 1 || t == 2 || t == 4 || t == 6 do
          throw s!"font.layout.unsupported: GPOS lookup {l} has type {t} (https://github.com/danbri/factoidal/issues/1233)"
      let keep : Array Bool := (Array.range out.size).map fun k => !(skips flag classes[k]!)
      let mut i := 0
      for _ in [0:out.size] do
        if i ≥ out.size then break
        ops := ops + 1
        if ops > limits.lookupOperationsPerRun then
          throw s!"font.layout.limit: more than {limits.lookupOperationsPerRun} lookup operations in one run"
        if !keep[i]! then
          i := i + 1
          continue
        let mut advanceTo := i + 1
        for (t, s) in subs do
          let g := out[i]!
          need b s 6 "subtable header"
          if t == 1 then
            let some ci ← coverage b (s + u16 b (s + 2)) g.id | continue
            let fmt := u16 b s
            let vf := u16 b (s + 4)
            let rec_ ← if fmt == 1 then pure (s + 6)
              else if fmt == 2 then do
                if ci ≥ u16 b (s + 6) then throw "font.file.malformed: single adjustment index"
                pure (s + 8 + valueSize vf * ci)
              else throw s!"font.file.malformed: single adjustment format {fmt}"
            need b rec_ (valueSize vf) "single adjustment value"
            let (xp, yp, xa) := valueXYA b vf rec_
            out := out.set! i { g with xOffset := g.xOffset + xp, yOffset := g.yOffset + yp, advance := g.advance + xa }
            break
          else if t == 2 then
            let some j := nextOf keep i | continue
            let some r ← pairPos b s g.id out[j]!.id | continue
            let c := out[j]!
            out := out.set! i { g with xOffset := g.xOffset + r.first.1, advance := g.advance + r.first.2 }
            out := out.set! j { c with xOffset := c.xOffset + r.second.1, advance := c.advance + r.second.2 }
            advanceTo := if r.skipSecond then j + 1 else j
            break
          else
            -- Mark attachment: t == 4 (to base) or t == 6 (to mark).
            need b s 12 "mark attachment header"
            let some mci ← coverage b (s + u16 b (s + 2)) g.id | continue
            let nClasses := u16 b (s + 6)
            let (cls, ma) ← markRecord b (s + u16 b (s + 8)) mci
            -- The glyph to attach to: for type 4 the previous glyph that is
            -- not a mark; for type 6 the previous unskipped glyph, which must be a mark.
            let parent? : Option Nat :=
              if t == 4 then ((List.range i).reverse).find? (fun k => !isMark k)
              else match prevOf keep i with
                | some k => if isMark k then some k else none
                | none => none
            let some p := parent? | continue
            let some bci ← coverage b (s + u16 b (s + 4)) out[p]!.id | continue
            let some ba ← baseAnchor b (s + u16 b (s + 10)) bci nClasses cls | continue
            out := out.set! i { g with xOffset := ba.1 - ma.1, yOffset := ba.2 - ma.2, attachedTo := some p }
            break
        i := advanceTo
  -- Zero the width of marks; move them only when the font has no GPOS.
  let hasGpos := dir.any (·.tag == "GPOS")
  for k in [0:out.size] do
    if isMark k then
      let g := out[k]!
      out := out.set! k { g with xOffset := if hasGpos then g.xOffset else g.xOffset - g.advance, advance := 0 }
  -- Propagate attachment offsets, parents first (a parent precedes its mark).
  for k in [0:out.size] do
    let g := out[k]!
    if let some p := g.attachedTo then
      let parent := out[p]!
      let between := ((List.range (k - p)).map (p + ·)).foldl (fun acc q => acc + out[q]!.advance) (0 : Int)
      out := out.set! k { g with xOffset := g.xOffset + parent.xOffset - between, yOffset := g.yOffset + parent.yOffset }
  return out

end L4Factoidal.Rendering.SfntGpos
