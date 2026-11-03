import L4Factoidal.Rendering.SfntMetrics

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
  mark filtering sets are refused;
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

/-- Coverage index of a glyph, if covered. -/
def coverage (b : ByteArray) (off g : Nat) : Except String (Option Nat) := do
  need b off 4 "coverage"
  let fmt := u16 b off
  let n := u16 b (off + 2)
  if fmt == 1 then
    need b (off + 4) (2 * n) "coverage glyphs"
    for k in [0:n] do
      if u16 b (off + 4 + 2 * k) == g then return some k
    return none
  else if fmt == 2 then
    need b (off + 4) (6 * n) "coverage ranges"
    for k in [0:n] do
      let r := off + 4 + 6 * k
      if u16 b r ≤ g && g ≤ u16 b (r + 2) then return some (u16 b (r + 4) + g - u16 b r)
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
    for k in [0:n] do
      let r := off + 4 + 6 * k
      if u16 b r ≤ g && g ≤ u16 b (r + 2) then return u16 b (r + 4)
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
    return some ⟨valueX b vf1 rec_, valueX b vf2 (rec_ + s1), vf2 != 0⟩
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

/-- The lookup list indices of the `kern` feature in the default language
system of `script` (or `DFLT`), in lookup list order. -/
def kernLookups (b : ByteArray) (gpos : Nat) (script : String) : Except String (List Nat) := do
  need b gpos 10 "header"
  let scripts := gpos + u16 b (gpos + 4)
  let features := gpos + u16 b (gpos + 6)
  need b scripts 2 "script list"
  let ns := u16 b scripts
  need b (scripts + 2) (6 * ns) "script records"
  let find (tag : String) : Option Nat :=
    (List.range ns).findSome? fun k =>
      if tagAt b (scripts + 2 + 6 * k) == tag then some (scripts + u16 b (scripts + 2 + 6 * k + 4)) else none
  let some s := (find script).orElse (fun _ => find "DFLT") | return []
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
  let mut out : List Nat := []
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
        let l := u16 b (f + 4 + 2 * j)
        unless out.contains l do out := l :: out
  return (out.toArray.qsort (· < ·)).toList

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
  let lookups ← kernLookups b gpos (scriptTag text)
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
    if flag &&& 0x10 != 0 then
      throw s!"font.layout.unsupported: kern lookup {l} uses a mark filtering set (https://github.com/danbri/factoidal/issues/1233)"
    let skipped (k : Nat) : Bool := skips flag classes[k]!
    let nsub := u16 b (lk + 4)
    need b (lk + 6) (2 * nsub) "subtable offsets"
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
