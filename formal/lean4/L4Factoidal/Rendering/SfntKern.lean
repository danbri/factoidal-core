import L4Factoidal.Rendering.SfntMetrics
import L4Factoidal.Unicode.ScriptData

/-!
# GPOS pair kerning in Lean

Second stage of the Lean shaper (https://github.com/danbri/factoidal/issues/1233):
the `kern` feature of GPOS, lookup type 2 (pair adjustment, formats 1 and 2)
and type 9 (extension) wrapping type 2. The OpenType GPOS chapter is the
reference; HarfBuzz is the differential oracle.

Profile limits, each a refusal or a stated difference, not a silent one:
* one script for the run, chosen from the first letter, as HarfBuzz's
  `guess_segment_properties` does for a buffer: `latn`, `grek`, `cyrl`, else
  `DFLT`; the default language system of that script;
* lookup flags IgnoreBaseGlyphs, IgnoreLigatures, IgnoreMarks and the mark
  attachment type use the GDEF glyph and mark attachment class definitions;
  a mark filtering set (GDEF 1.2 MarkGlyphSetsDef) keeps only the marks it
  covers, as in HarfBuzz;
* lookups other than type 2 in the `kern` feature are refused.
Every loop is bounded by a count read from the font and checked against the
table bounds, and by `Limits.lookupOperationsPerRun`.
-/
namespace L4Factoidal.Rendering.SfntKern
open FontPolicy SfntMetrics

private def need (b : ByteArray) (i n : Nat) (what : String) : Except String Unit :=
  if i + n ≤ b.size then pure () else throw s!"font.file.malformed: GPOS {what} out of bounds"
private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def i16 (b : ByteArray) (i : Nat) : Int :=
  let v := u16 b i
  if v ≥ 32768 then (v : Int) - 65536 else v
private def tagAt (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (b.get! (i + k)).toNat)

/-- Coverage index of a glyph, if covered. A coverage table is sorted by glyph (OpenType common
layout tables), so this is a binary search; every read is inside the checked range, so a
table that is out of order at worst misses a glyph. (A linear scan took about 20 % of a first
page's layout on the Hub.) -/
def coverage (b : ByteArray) (off g : Nat) : Except String (Option Nat) := do
  need b off 4 "coverage"
  let fmt := u16 b off
  let n := u16 b (off + 2)
  if fmt == 1 then
    need b (off + 4) (2 * n) "coverage glyphs"
    let mut lo := 0
    let mut hi := n
    -- `n` is at most 65535, so 17 halvings reach an empty range.
    for _ in [0:17] do
      if lo ≥ hi then break
      let mid := (lo + hi) / 2
      let v := u16 b (off + 4 + 2 * mid)
      if v == g then return some mid
      if v < g then lo := mid + 1 else hi := mid
    return none
  else if fmt == 2 then
    need b (off + 4) (6 * n) "coverage ranges"
    let mut lo := 0
    let mut hi := n
    for _ in [0:17] do
      if lo ≥ hi then break
      let mid := (lo + hi) / 2
      let r := off + 4 + 6 * mid
      let start := u16 b r
      let stop := u16 b (r + 2)
      if g < start then hi := mid
      else if g > stop then lo := mid + 1
      else return some (u16 b (r + 4) + g - start)
    return none
  else throw s!"font.file.malformed: coverage format {fmt}"

/-- Class of a glyph; 0 when not listed. -/
def classOf (b : ByteArray) (off g : Nat) : Except String Nat := do
  need b off 4 "class definition"
  let fmt := u16 b off
  if fmt == 1 then
    need b off 6 "class format 1"
    let start := u16 b (off + 2)
    let n := u16 b (off + 4)
    need b (off + 6) (2 * n) "class format 1 values"
    if start ≤ g && g < start + n then return u16 b (off + 6 + 2 * (g - start)) else return 0
  else if fmt == 2 then
    let n := u16 b (off + 2)
    need b (off + 4) (6 * n) "class ranges"
    -- The ranges are sorted by first glyph (OpenType ClassDef format 2), so a binary
    -- search finds the range, as HarfBuzz does: this runs for each glyph of each lookup
    -- of each word. 17 halvings cover 65536 ranges; a loop, not recursion.
    let mut lo := 0
    let mut hi := n
    for _ in [0:17] do
      if lo ≥ hi then break
      let mid := (lo + hi) / 2
      let r := off + 4 + 6 * mid
      if g < u16 b r then hi := mid
      else if u16 b (r + 2) < g then lo := mid + 1
      else return u16 b (r + 4)
    return 0
  else throw s!"font.file.malformed: class definition format {fmt}"

/-- GDEF glyph class (1 base, 2 ligature, 3 mark, 4 component) and mark
attachment class of a glyph; (0, 0) when there is no GDEF. -/
def gdefClasses (b : ByteArray) (gdef? : Option Nat) (g : Nat) : Except String (Nat × Nat) := do
  match gdef? with
  | none => pure (0, 0)
  | some gd => do
    need b gd 12 "GDEF header"
    let cd := u16 b (gd + 4)
    let md := u16 b (gd + 10)
    let gc ← if cd == 0 then pure 0 else classOf b (gd + cd) g
    let mc ← if md == 0 then pure 0 else classOf b (gd + md) g
    pure (gc, mc)

/-- Whether lookup flag `flag` skips a glyph with these GDEF classes. -/
def skips (flag : Nat) (c : Nat × Nat) : Bool :=
  let attach := flag / 256
  (flag &&& 2 != 0 && c.1 == 1) || (flag &&& 4 != 0 && c.1 == 2) || (flag &&& 8 != 0 && c.1 == 3) ||
  (attach != 0 && c.1 == 3 && c.2 != attach)

/-- Mark filtering set index of the lookup at `lk` with `nsub` subtables,
when its flag has UseMarkFilteringSet (0x10). -/
def lookupMarkSet (b : ByteArray) (lk nsub flag : Nat) : Except String (Option Nat) := do
  if flag &&& 0x10 == 0 then return none
  need b (lk + 6 + 2 * nsub) 2 "mark filtering set"
  return some (u16 b (lk + 6 + 2 * nsub))

/-- Whether mark glyph set `set` of GDEF covers glyph `g`. A GDEF before
version 1.2, or with no MarkGlyphSetsDef, covers nothing, as in HarfBuzz. -/
def markSetCovers (b : ByteArray) (gdef? : Option Nat) (set g : Nat) : Except String Bool := do
  let some gd := gdef? | return false
  need b gd 12 "GDEF header"
  if u16 b (gd + 2) < 2 then return false
  need b gd 14 "GDEF 1.2 header"
  let ms := u16 b (gd + 12)
  if ms == 0 then return false
  let t := gd + ms
  need b t 4 "mark glyph sets"
  let n := u16 b (t + 2)
  if set ≥ n then return false
  need b (t + 4 + 4 * set) 4 "mark glyph set offset"
  return (← coverage b (t + u32 b (t + 4 + 4 * set)) g).isSome

/-- `skips` with the lookup's mark filtering set (HarfBuzz
`match_properties_mark`): the ignore flags come first; then a mark is kept
only when the set covers it, and the attachment type is not checked. -/
def skipsWithSet (b : ByteArray) (gdef? : Option Nat) (flag : Nat) (set? : Option Nat)
    (c : Nat × Nat) (g : Nat) : Except String Bool := do
  match set? with
  | some set =>
    if (flag &&& 2 != 0 && c.1 == 1) || (flag &&& 4 != 0 && c.1 == 2) || (flag &&& 8 != 0 && c.1 == 3) then
      return true
    if c.1 == 3 then return !(← markSetCovers b gdef? set g)
    return false
  | none => return skips flag c

/-- Size in bytes of a value record of this format. -/
def valueSize (fmt : Nat) : Nat := 2 * ((List.range 8).filter fun k => fmt / 2 ^ k % 2 == 1).length

/-- (x placement, x advance) of a value record; device tables are ignored,
as HarfBuzz does at the default pixels-per-em of an unhinted font. -/
def valueX (b : ByteArray) (fmt off : Nat) : Int × Int :=
  let xPl : Int := if fmt % 2 == 1 then i16 b off else 0
  let skipY := (if fmt % 2 == 1 then 2 else 0) + (if fmt / 2 % 2 == 1 then 2 else 0)
  let xAdv : Int := if fmt / 4 % 2 == 1 then i16 b (off + skipY) else 0
  (xPl, xAdv)

structure PairResult where
  first : Int × Int
  second : Int × Int
  /-- The second glyph's value record is not empty, so the next pair starts after it. -/
  skipSecond : Bool
  /-- y placements of the two value records. -/
  firstY : Int := 0
  secondY : Int := 0

/-- y placement of a value record (0 when the format has none). -/
def valueY (b : ByteArray) (fmt off : Nat) : Int :=
  if fmt / 2 % 2 == 1 then i16 b (off + (if fmt % 2 == 1 then 2 else 0)) else 0

/-- Apply one PairPos subtable to the pair (g1, g2). -/
def pairPos (b : ByteArray) (sub g1 g2 : Nat) : Except String (Option PairResult) := do
  need b sub 10 "PairPos header"
  let fmt := u16 b sub
  let some ci ← coverage b (sub + u16 b (sub + 2)) g1 | return none
  let vf1 := u16 b (sub + 4)
  let vf2 := u16 b (sub + 6)
  let s1 := valueSize vf1
  let s2 := valueSize vf2
  let result (rec_ : Nat) : Except String (Option PairResult) := do
    need b rec_ (s1 + s2) "pair value record"
    return some ⟨valueX b vf1 rec_, valueX b vf2 (rec_ + s1), vf2 != 0,
      valueY b vf1 rec_, valueY b vf2 (rec_ + s1)⟩
  if fmt == 1 then
    let n := u16 b (sub + 8)
    if ci ≥ n then throw "font.file.malformed: PairPos coverage index beyond pair sets"
    need b (sub + 10) (2 * n) "pair set offsets"
    let ps := sub + u16 b (sub + 10 + 2 * ci)
    need b ps 2 "pair set"
    let count := u16 b ps
    let stride := 2 + s1 + s2
    need b (ps + 2) (stride * count) "pair value records"
    for k in [0:count] do
      let r := ps + 2 + stride * k
      if u16 b r == g2 then return ← result (r + 2)
    return none
  else if fmt == 2 then
    need b sub 16 "PairPos format 2 header"
    let c1 := ← classOf b (sub + u16 b (sub + 8)) g1
    let c2 := ← classOf b (sub + u16 b (sub + 10)) g2
    let n1 := u16 b (sub + 12)
    let n2 := u16 b (sub + 14)
    if c1 ≥ n1 || c2 ≥ n2 then return none
    result (sub + 16 + (c1 * n2 + c2) * (s1 + s2))
  else throw s!"font.file.malformed: PairPos format {fmt}"

/-- The OpenType script tag HarfBuzz uses for a buffer whose first letter is `c`. -/
def scriptTag (text : String) : String :=
  match text.toList.find? (fun c => c.isAlpha || 0x370 ≤ c.toNat) with
  | some c =>
    let n := c.toNat
    if 0x370 ≤ n && n ≤ 0x3FF then "grek"
    else if 0x400 ≤ n && n ≤ 0x52F then "cyrl"
    else if n < 0x250 || (0x1E00 ≤ n && n ≤ 0x1EFF) then "latn"
    else "DFLT"
  | none => "DFLT"

/-- The script of a text as HarfBuzz guesses it: the Script property of the
first character that is not Common, Inherited or Unknown (ISO 15924). -/
def textScript (text : String) : Option String :=
  (text.toList.map fun c => L4Factoidal.Unicode.ScriptData.scriptOf c.toNat).find?
    fun s => s != "Zyyy" && s != "Zinh" && s != "Zzzz"

/-- OpenType script tags to try, in order: HarfBuzz `hb_ot_all_tags_from_script`
(the version 3 and 2 Indic tags first, then the old tag), then the
`hb_ot_layout_table_choose_script` fallbacks `DFLT`, `dflt`, `latn`. -/
def scriptTags (text : String) : List String :=
  let fallback := ["DFLT", "dflt", "latn"]
  match textScript text with
  | none => fallback
  | some iso =>
    let newTag : Option String := match iso with
      | "Beng" => some "bng2" | "Deva" => some "dev2" | "Gujr" => some "gjr2"
      | "Guru" => some "gur2" | "Knda" => some "knd2" | "Mlym" => some "mlm2"
      | "Orya" => some "ory2" | "Taml" => some "tml2" | "Telu" => some "tel2"
      | "Mymr" => some "mym2" | _ => none
    let old := match iso with
      | "Hira" => "kana" | "Laoo" => "lao " | "Yiii" => "yi  " | "Nkoo" => "nko "
      | "Vaii" => "vai " | s => s.toLower
    let news := match newTag with
      | some t => (if t == "mym2" then [] else [(t.take 3).toString ++ "3"]) ++ [t]
      | none => []
    news ++ [old] ++ fallback

#guard scriptTags "a" == ["latn", "DFLT", "dflt", "latn"]
#guard scriptTags "\u0915" == ["dev3", "dev2", "deva", "DFLT", "dflt", "latn"]
#guard scriptTags "1" == ["DFLT", "dflt", "latn"]

/-- The lookup list indices of the `kern` feature in the default language
system of the first of `tags` that GPOS has, in lookup list order. -/
def kernLookups (b : ByteArray) (gpos : Nat) (tags : List String) : Except String (List Nat) := do
  need b gpos 10 "header"
  let scripts := gpos + u16 b (gpos + 4)
  let features := gpos + u16 b (gpos + 6)
  need b scripts 2 "script list"
  let ns := u16 b scripts
  need b (scripts + 2) (6 * ns) "script records"
  let find (tag : String) : Option Nat :=
    (List.range ns).findSome? fun k =>
      if tagAt b (scripts + 2 + 6 * k) == tag then some (scripts + u16 b (scripts + 2 + 6 * k + 4)) else none
  let some s := tags.findSome? find | return []
  need b s 4 "script table"
  let ls := u16 b s
  if ls == 0 then return []
  let lang := s + ls
  need b lang 6 "language system"
  let nf := u16 b (lang + 4)
  need b (lang + 6) (2 * nf) "feature indices"
  need b features 2 "feature list"
  let nfl := u16 b features
  need b (features + 2) (6 * nfl) "feature records"
  -- One flag for each possible lookup index; reading the flags in order
  -- gives the sorted, distinct list with no recursion.
  let mut used : Array Bool := Array.replicate 65536 false
  for k in [0:nf] do
    let fi := u16 b (lang + 6 + 2 * k)
    if fi ≥ nfl then throw "font.file.malformed: GPOS feature index"
    let r := features + 2 + 6 * fi
    if tagAt b r == "kern" then
      let f := features + u16 b (r + 4)
      need b f 4 "feature table"
      let nl := u16 b (f + 2)
      need b (f + 4) (2 * nl) "feature lookups"
      for j in [0:nl] do
        used := used.set! (u16 b (f + 4 + 2 * j)) true
  let mut out : Array Nat := #[]
  for l in [0:65536] do
    if used[l]! then out := out.push l
  return out.toList

/-- Positioned glyph after kerning: advance and x offset in font units. -/
structure Positioned where
  id : Nat
  advance : Int
  xOffset : Int
  cluster : Nat
  deriving Repr, BEq, Inhabited

/-- Apply the `kern` feature to a nominal run. -/
def kern (b : ByteArray) (dir : Array TableRecord) (text : String) (run : Array NominalGlyph)
    (limits : Limits := {}) : Except String (Array Positioned) := do
  let mut out : Array Positioned := run.map fun g => ⟨g.id, g.advance, 0, g.cluster⟩
  let some gposRec := dir.find? (·.tag == "GPOS") | return out
  let gpos := gposRec.offset
  let lookups ← kernLookups b gpos (scriptTags text)
  let lookupList := gpos + u16 b (gpos + 8)
  need b lookupList 2 "lookup list"
  let nl := u16 b lookupList
  -- GDEF glyph classes: 1 base, 2 ligature, 3 mark, 4 component.
  let gdef? := (dir.find? (·.tag == "GDEF")).map (·.offset)
  let classes ← run.mapM fun g => gdefClasses b gdef? g.id
  let mut ops := 0
  for l in lookups do
    if l ≥ nl then throw "font.file.malformed: GPOS lookup index"
    need b (lookupList + 2 + 2 * l) 2 "lookup offset"
    let lk := lookupList + u16 b (lookupList + 2 + 2 * l)
    need b lk 6 "lookup"
    let ltype := u16 b lk
    let flag := u16 b (lk + 2)
    let nsub := u16 b (lk + 4)
    need b (lk + 6) (2 * nsub) "subtable offsets"
    let set? ← lookupMarkSet b lk nsub flag
    let skipArr ← (Array.range run.size).mapM fun k => skipsWithSet b gdef? flag set? classes[k]! run[k]!.id
    let skipped (k : Nat) : Bool := skipArr[k]!
    -- Resolve extension subtables to their type 2 targets.
    let mut subs : Array Nat := #[]
    for k in [0:nsub] do
      let s := lk + u16 b (lk + 6 + 2 * k)
      if ltype == 9 then
        need b s 8 "extension"
        if u16 b (s + 2) != 2 then throw s!"font.layout.unsupported: kern extension of lookup type {u16 b (s + 2)}"
        subs := subs.push (s + u32 b (s + 4))
      else if ltype == 2 then subs := subs.push s
      else throw s!"font.layout.unsupported: kern lookup type {ltype}"
    let mut i := 0
    -- At most one step for each glyph: each step advances i by 1 or 2.
    for _ in [0:out.size] do
      if i + 1 ≥ out.size then break
      ops := ops + 1
      if ops > limits.lookupOperationsPerRun then
        throw s!"font.layout.limit: more than {limits.lookupOperationsPerRun} lookup operations in one run"
      if skipped i then
        i := i + 1
        continue
      -- The second glyph is the next glyph that the lookup flags do not skip.
      let j := ((List.range (out.size - i - 1)).map (i + 1 + ·)).find? (!skipped ·)
      let some j := j | break
      ops := ops + (j - i - 1)
      let g1 := out[i]!.id
      let g2 := out[j]!.id
      let mut hit : Option PairResult := none
      for s in subs do
        if let some r ← pairPos b s g1 g2 then
          hit := some r
          break
      match hit with
      | none => i := j
      | some r =>
        let a := out[i]!
        let c := out[j]!
        out := out.set! i { a with xOffset := a.xOffset + r.first.1, advance := a.advance + r.first.2 }
        out := out.set! j { c with xOffset := c.xOffset + r.second.1, advance := c.advance + r.second.2 }
        i := if r.skipSecond then j + 1 else j
  return out

end L4Factoidal.Rendering.SfntKern
