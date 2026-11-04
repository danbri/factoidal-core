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

Cursive attachment (type 3) follows HarfBuzz for left-to-right text; context
positioning (types 7 and 8) matches as GSUB types 5 and 6. Mark to ligature
(type 5) uses the component of the mark (HarfBuzz lig_id, lig_comp). Mark filtering sets apply as in HarfBuzz. Device tables in value
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
  /-- Cursive attachment: the parent is at this position plus `cursiveChain`;
  0 when the glyph has no cursive parent (HarfBuzz `attach_chain`). -/
  cursiveChain : Int := 0
  codepoint : Nat := 0
  substituted : Bool := false
  ligated : Bool := false
  spaceFallback : Nat := 0
  /-- HarfBuzz ligature properties (`lig_props`): the ligature id (1 to 7;
  0 = none), the component of a mark or of a multiple-substitution output
  (0 = the ligature glyph itself), and the number of components of a
  ligature glyph. -/
  ligId : Nat := 0
  ligComp : Nat := 0
  ligNum : Nat := 0
  /-- Output of a multiple substitution (HarfBuzz `_hb_glyph_info_multiplied`). -/
  multiplied : Bool := false
  deriving Repr, BEq, Inhabited

/-- HarfBuzz default GPOS features for horizontal text. -/
def defaultFeatures : List String := ["abvm", "blwm", "curs", "dist", "kern", "mark", "mkmk"]

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

/-- Entry and exit anchors of the glyph at coverage index `ci` of a
CursivePosFormat1 subtable at `s`. -/
def entryExit (b : ByteArray) (s ci : Nat) : Except String (Option (Int × Int) × Option (Int × Int)) := do
  need b s 6 "cursive header"
  if u16 b s != 1 then throw s!"font.file.malformed: cursive format {u16 b s}"
  if ci ≥ u16 b (s + 4) then throw "font.file.malformed: cursive coverage index beyond records"
  let r := s + 6 + 4 * ci
  need b r 4 "entry exit record"
  let en := u16 b r
  let ex := u16 b (r + 2)
  let entry ← if en == 0 then pure none else some <$> anchor b (s + en)
  let exit ← if ex == 0 then pure none else some <$> anchor b (s + ex)
  return (entry, exit)

/-- HarfBuzz `reverse_cursive_minor_offset`, as a loop: the old cursive chain
from `child` is reversed so that it hangs from `child`, up to `newParent`. -/
def reverseCursive (out : Array Glyph) (child newParent : Nat) : Array Glyph := Id.run do
  -- The nodes of the chain, and whether the last edge reaches the new parent.
  let mut nodes : Array Nat := #[child]
  let mut k := child
  for _ in [0:out.size] do
    let c := out[k]!.cursiveChain
    if c == 0 then break
    let j : Int := (k : Int) + c
    if j < 0 || j ≥ out.size then break
    if j.toNat == newParent then break
    nodes := nodes.push j.toNat
    k := j.toNat
  let old := out
  let mut res := out
  res := res.set! child { res[child]! with cursiveChain := 0 }
  if nodes.size ≥ 2 then
    for m in [0:nodes.size - 1] do
      let a := nodes[m]!
      let z := nodes[m + 1]!
      res := res.set! z { res[z]! with yOffset := -old[a]!.yOffset, cursiveChain := -old[a]!.cursiveChain }
  return res

/-- Ranges of General_Category Mn, Mc and Me, from `IdnaData.markText`. -/
def unicodeMarkRanges : Array (Nat × Nat) :=
  let hex (t : String) : Nat :=
    t.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48 else c.toUpper.toNat - 55)) 0
  ((WHATWG.URL.IdnaData.markText.splitOn ";").filter (· != "")).toArray.map fun r =>
    match r.splitOn "-" with
    | [a, z] => (hex a, hex z)
    | _ => (hex r, hex r)

def isUnicodeMark (c : Nat) : Bool := unicodeMarkRanges.any fun (a, z) => a ≤ c && c ≤ z

/-- What GPOS lookups need from the font and the run. Glyph ids and classes
do not change during GPOS. -/
structure PCtx where
  b : ByteArray
  lookupList : Nat
  count : Nat
  gdef? : Option Nat
  classes : Array (Nat × Nat)

/-- Flag, mark filtering set and subtables (type, offset; extensions
resolved) of GPOS lookup `l`. -/
def gposLookup (c : PCtx) (l : Nat) : Except String (Nat × Option Nat × Array (Nat × Nat)) := do
  let b := c.b
  if l ≥ c.count then throw "font.file.malformed: GPOS lookup index"
  need b (c.lookupList + 2 + 2 * l) 2 "lookup offset"
  let lk := c.lookupList + u16 b (c.lookupList + 2 + 2 * l)
  need b lk 6 "lookup"
  let ltype := u16 b lk
  let flag := u16 b (lk + 2)
  let nsub := u16 b (lk + 4)
  need b (lk + 6) (2 * nsub) "subtable offsets"
  let set? ← lookupMarkSet b lk nsub flag
  let mut subs : Array (Nat × Nat) := #[]
  for k in [0:nsub] do
    let s := lk + u16 b (lk + 6 + 2 * k)
    if ltype == 9 then
      need b s 8 "extension"
      subs := subs.push (u16 b (s + 2), s + u32 b (s + 4))
    else subs := subs.push (ltype, s)
  for (t, _) in subs do
    unless t == 1 || t == 2 || t == 3 || t == 4 || t == 5 || t == 6 || t == 7 || t == 8 do
      throw s!"font.layout.unsupported: GPOS lookup {l} has type {t} (https://github.com/danbri/factoidal/issues/1233)"
  return (flag, set?, subs)

/-- Positions that the lookup flag and mark filtering set do not skip. -/
def gposKeep (c : PCtx) (flag : Nat) (set? : Option Nat) (out : Array Glyph) : Except String (Array Bool) :=
  (Array.range out.size).mapM fun k => do
    pure !(← skipsWithSet c.b c.gdef? flag set? c.classes[k]! out[k]!.id)

/-- One subtable of type 1 to 6 at position i: the new run and the
position to continue from, or none when the subtable does not apply. -/
def applyPosSubtable (c : PCtx) (flag : Nat) (keep : Array Bool) (t s : Nat) (out0 : Array Glyph) (i : Nat) :
    Except String (Option (Array Glyph × Nat)) := do
  let b := c.b
  let isMark (k : Nat) : Bool := c.classes[k]!.1 == 3
  let mut out := out0
  let g := out[i]!
  need b s 6 "subtable header"
    if t == 1 then
      let some ci ← coverage b (s + u16 b (s + 2)) g.id | return none
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
      return some (out, i + 1)
    else if t == 2 then
      let some j := nextOf keep i | return none
      let some r ← pairPos b s g.id out[j]!.id | return none
      let c := out[j]!
      out := out.set! i { g with xOffset := g.xOffset + r.first.1, yOffset := g.yOffset + r.firstY,
                                 advance := g.advance + r.first.2 }
      out := out.set! j { c with xOffset := c.xOffset + r.second.1, yOffset := c.yOffset + r.secondY,
                                 advance := c.advance + r.second.2 }
      return some (out, if r.skipSecond then j + 1 else j)
    else if t == 3 then
      -- Cursive attachment (HarfBuzz CursivePosFormat1::apply, left to right).
      let some ci ← coverage b (s + u16 b (s + 2)) g.id | return none
      let (some entry, _) ← entryExit b s ci | return none
      let some pi := prevOf keep i | return none
      let some pci ← coverage b (s + u16 b (s + 2)) out[pi]!.id | return none
      let (_, some exit) ← entryExit b s pci | return none
      let gp := out[pi]!
      out := out.set! pi { gp with advance := exit.1 + gp.xOffset }
      let d := entry.1 + g.xOffset
      out := out.set! i { g with advance := g.advance - d, xOffset := g.xOffset - d }
      -- Without the RightToLeft flag the later glyph is the child.
      let rtlFlag := flag &&& 1 != 0
      let (child, parent) := if rtlFlag then (pi, i) else (i, pi)
      let yOff : Int := if rtlFlag then entry.2 - exit.2 else exit.2 - entry.2
      out := reverseCursive out child parent
      let chain : Int := (parent : Int) - (child : Int)
      out := out.set! child { out[child]! with cursiveChain := chain, attachedTo := none, yOffset := yOff }
      if out[parent]!.cursiveChain == -chain then
        out := out.set! parent { out[parent]! with cursiveChain := 0, yOffset := 0 }
      return some (out, i + 1)
    else if t == 5 then
      -- Mark to ligature (HarfBuzz MarkLigPosFormat1::apply). The ligature is
      -- the previous glyph that is not a mark.
      need b s 12 "mark-to-ligature header"
      let some mci ← coverage b (s + u16 b (s + 2)) g.id | return none
      let nClasses := u16 b (s + 6)
      let (cls, ma) ← markRecord b (s + u16 b (s + 8)) mci
      let some p := ((List.range i).reverse).find? (fun k => !isMark k) | return none
      let some lci ← coverage b (s + u16 b (s + 4)) out[p]!.id | return none
      let la := s + u16 b (s + 10)
      need b la 2 "ligature array"
      if lci ≥ u16 b la then throw "font.file.malformed: ligature coverage index beyond ligature array"
      need b (la + 2 + 2 * lci) 2 "ligature attach offset"
      let attach := la + u16 b (la + 2 + 2 * lci)
      need b attach 2 "ligature attach"
      let comps := u16 b attach
      if comps == 0 then return none
      -- The mark's component when it belongs to this ligature (HarfBuzz lig_id/lig_comp).
      let lg := out[p]!
      let comp := if lg.ligId != 0 && lg.ligId == g.ligId && g.ligComp > 0 then min comps g.ligComp - 1 else comps - 1
      let some ba ← baseAnchor b attach comp nClasses cls | return none
      out := out.set! i { g with xOffset := ba.1 - ma.1, yOffset := ba.2 - ma.2, attachedTo := some p, cursiveChain := 0 }
      return some (out, i + 1)
    else
      -- Mark attachment: t == 4 (to base) or t == 6 (to mark).
      need b s 12 "mark attachment header"
      let some mci ← coverage b (s + u16 b (s + 2)) g.id | return none
      let nClasses := u16 b (s + 6)
      let (cls, ma) ← markRecord b (s + u16 b (s + 8)) mci
      -- The glyph to attach to: for type 4 the previous glyph that is
      -- not a mark; for type 6 the previous unskipped glyph, which must be a mark.
      -- Type 4: the previous glyph that is not a mark, but only the first glyph
      -- of a multiple-substitution sequence (HarfBuzz MarkBasePos `accept`).
      let acceptBase (k : Nat) : Bool :=
        let gk := out[k]!
        !gk.multiplied || gk.ligComp == 0 || k == 0 || isMark (k - 1) || !out[k - 1]!.multiplied ||
          gk.ligId != out[k - 1]!.ligId || gk.ligComp != out[k - 1]!.ligComp + 1
      -- Type 6: the previous unskipped glyph, a mark on the same base or the
      -- same ligature component (HarfBuzz MarkMarkPosFormat1::apply).
      let sameBase (k : Nat) : Bool :=
        let id1 := g.ligId
        let id2 := out[k]!.ligId
        let c1 := g.ligComp
        let c2 := out[k]!.ligComp
        if id1 == id2 then id1 == 0 || c1 == c2
        else (id1 > 0 && c1 == 0) || (id2 > 0 && c2 == 0)
      let parent? : Option Nat :=
        if t == 4 then ((List.range i).reverse).find? (fun k => !isMark k && acceptBase k)
        else match prevOf keep i with
          | some k => if isMark k && sameBase k then some k else none
          | none => none
      let some p := parent? | return none
      let some bci ← coverage b (s + u16 b (s + 4)) out[p]!.id | return none
      let some ba ← baseAnchor b (s + u16 b (s + 10)) bci nClasses cls | return none
      out := out.set! i { g with xOffset := ba.1 - ma.1, yOffset := ba.2 - ma.2, attachedTo := some p, cursiveChain := 0 }
      return some (out, i + 1)

/-- Apply GPOS lookup `l` at position i once (HarfBuzz `apply_forward` step).
Context subtables (types 7 and 8) match as GSUB types 5 and 6 and apply their
nested lookups at the matched positions; the nesting depth starts at 8. -/
def posAt (c : PCtx) : Nat → Nat → Array Glyph → Nat → Option (Array Bool) →
    Except String (Option (Array Glyph × Nat))
  | 0, _, _, _, _ => throw "font.layout.limit: nested GPOS context lookups deeper than 8"
  | depth + 1, l, out, i, keep? => do
    let (flag, set?, subs) ← gposLookup c l
    let keep ← match keep? with
      | some k => pure k
      | none => gposKeep c flag set? out
    if i ≥ out.size || !keep[i]! then return none
    let ids := out.map (·.id)
    for (t, s) in subs do
      if t == 7 || t == 8 then
        let some (inputs, recs) ← SfntSubst.matchContext c.b (t - 2) s ids keep i | continue
        let mut cur := out
        for (seq, nested) in recs do
          let some p := inputs[seq]? | continue
          match ← posAt c depth nested cur p none with
          | none => pure ()
          | some (next, _) => cur := next
        return some (cur, inputs.foldl max i + 1)
      else
        match ← applyPosSubtable c flag keep t s out i with
        | some r => return some r
        | none => pure ()
    return none

/-- Apply the default GPOS features to a substituted run. A synthesized
glyph class uses the glyph's source code point (`NominalGlyph.codepoint`). -/
def position (b : ByteArray) (dir : Array TableRecord) (text : String)
    (run : Array NominalGlyph) (limits : Limits := {}) (features : List String := defaultFeatures)
    (tags : List String := scriptTags text) : Except String (Array Glyph) := do
  let mut out : Array Glyph := run.map fun g =>
    { id := g.id, advance := g.advance, xOffset := 0, yOffset := 0, cluster := g.cluster,
      codepoint := g.codepoint, substituted := g.substituted, ligated := g.ligated, spaceFallback := g.spaceFallback,
      ligId := g.ligId, ligComp := g.ligComp, ligNum := g.ligNum, multiplied := g.multiplied }
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
    let lookups ← featureLookups b gpos tags [features]
    let lookupList := gpos + u16 b (gpos + 8)
    need b lookupList 2 "lookup list"
    let c : PCtx := { b, lookupList, count := u16 b lookupList, gdef?, classes }
    let mut ops := 0
    for (_, l) in lookups do
      let (flag, set?, _) ← gposLookup c l
      let keep ← gposKeep c flag set? out
      let mut i := 0
      for _ in [0:out.size] do
        if i ≥ out.size then break
        ops := ops + 1
        if ops > limits.lookupOperationsPerRun then
          throw s!"font.layout.limit: more than {limits.lookupOperationsPerRun} lookup operations in one run"
        if !keep[i]! then
          i := i + 1
          continue
        match ← posAt c 8 l out i (some keep) with
        | some (next, n) =>
          out := next
          i := max n (i + 1)
        | none => i := i + 1
  -- Zero the width of marks; move them only when the font has no GPOS.
  let hasGpos := dir.any (·.tag == "GPOS")
  for k in [0:out.size] do
    if isMark k then
      let g := out[k]!
      out := out.set! k { g with xOffset := if hasGpos then g.xOffset else g.xOffset - g.advance, advance := 0 }
  -- Propagate cursive offsets: a glyph's y offset adds its parent's final
  -- one; at most 64 links, as HarfBuzz's nesting limit.
  let before := out
  for k in [0:out.size] do
    if before[k]!.cursiveChain != 0 then
      let mut sum : Int := 0
      let mut n := k
      for _ in [0:64] do
        let c := before[n]!.cursiveChain
        if c == 0 then break
        let j : Int := (n : Int) + c
        if j < 0 || j ≥ out.size then break
        n := j.toNat
        sum := sum + before[n]!.yOffset
      out := out.set! k { out[k]! with yOffset := out[k]!.yOffset + sum }
  -- Propagate attachment offsets, parents first (a parent precedes its mark).
  for k in [0:out.size] do
    let g := out[k]!
    if let some p := g.attachedTo then
      let parent := out[p]!
      let between := ((List.range (k - p)).map (p + ·)).foldl (fun acc q => acc + out[q]!.advance) (0 : Int)
      out := out.set! k { g with xOffset := g.xOffset + parent.xOffset - between, yOffset := g.yOffset + parent.yOffset }
  return out

end L4Factoidal.Rendering.SfntGpos
