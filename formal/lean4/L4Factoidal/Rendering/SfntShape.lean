import L4Factoidal.Rendering.SfntNormalize
import L4Factoidal.Rendering.SfntFallback
import L4Factoidal.Unicode.Segmentation

/-!
# The Lean shaper pipeline

One left-to-right run through every stage of the Lean shaper
(https://github.com/danbri/factoidal/issues/1233): font-aware normalization,
nominal glyphs, cluster merging at HarfBuzz's monotone-grapheme level, GSUB,
GPOS. Clusters are given as UTF-8 byte offsets into the input text, as in the
`factoidal-font-data-v1` record.

Refused, with a message: a strong right-to-left character (the RTL shaper is
not implemented), and everything the stages refuse. A font with no GPOS table
gets HarfBuzz's fallback mark positioning (`SfntFallback`).
-/
namespace L4Factoidal.Rendering.SfntShape
open FontPolicy SfntMetrics SfntGpos SfntFallback

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

/-- A default feature list with user settings (tag, on) applied in order; the
last setting of a tag wins, as in HarfBuzz for whole-text features. -/
def withSettings (defaults : List String) (settings : List (String × Bool)) : List String :=
  settings.foldl (fun acc (tag, on) => if on then (if acc.contains tag then acc else acc ++ [tag])
    else acc.filter (· != tag)) defaults

/-- `withSettings` for GSUB stages: a feature turned on that no stage names
joins the last stage (HarfBuzz adds user features last). -/
def stagesWithSettings (stages : List (List String)) (settings : List (String × Bool)) : List (List String) :=
  settings.foldl (fun acc (tag, on) =>
    if on then (if acc.any (·.contains tag) then acc
      else (acc.dropLast) ++ [(acc.getLastD []) ++ [tag]])
    else acc.map (·.filter (· != tag))) stages

/-- Scripts that HarfBuzz gives to the USE shaper (`hb_ot_shaper_categorize`). -/
def useScripts : List String :=
  ["Tibt", "Mong", "Sinh", "Buhd", "Hano", "Tglg", "Tagb", "Limb", "Tale", "Bugi", "Khar", "Sylo",
   "Tfng", "Bali", "Nkoo", "Phag", "Cham", "Kali", "Lepc", "Rjng", "Saur", "Sund", "Egyp", "Java",
   "Kthi", "Mtei", "Lana", "Tavt", "Batk", "Brah", "Mand", "Cakm", "Plrd", "Shrd", "Takr", "Dupl",
   "Gran", "Khoj", "Sind", "Mahj", "Mani", "Modi", "Hmng", "Phlp", "Sidd", "Tirh", "Ahom", "Mult",
   "Adlm", "Bhks", "Marc", "Newa", "Gonm", "Soyo", "Zanb", "Dogr", "Gong", "Rohg", "Maka", "Medf",
   "Sogo", "Sogd", "Elym", "Nand", "Hmnp", "Wcho", "Chrs", "Diak", "Kits", "Yezi", "Cpmn", "Ougr",
   "Tnsa", "Toto", "Vith", "Kawi", "Nagm", "Gara", "Gukh", "Krai", "Onao", "Sunu", "Todr", "Tutg",
   "Berf", "Sidt", "Tayo", "Tols", "Jurc", "Pcun", "Seal"]

/-- Scripts with another HarfBuzz shaper that Lean does not have yet
(Indic, Khmer, Myanmar, Thai and Lao, Hangul, Hebrew). -/
def otherComplexScripts : List String :=
  ["Beng", "Deva", "Gujr", "Guru", "Knda", "Mlym", "Orya", "Taml", "Telu",
   "Khmr", "Mymr", "Thai", "Laoo", "Hang", "Hebr"]

inductive ShaperKind where
  | default
  | use
  /-- A shaper Lean does not have: shape with the default shaper on `DFLT`,
  as HarfBuzz does for a font with no table for the script
  (https://github.com/danbri/factoidal/issues/1233). -/
  | dfltOnly
  deriving BEq

/-- HarfBuzz's shaper choice from the text's script and the GSUB script it
chose. For Indic, Myanmar and USE scripts a chosen `DFLT` or `latn` means the
default shaper; an Indic version 3 tag means USE; Myanmar `mymr` means default. -/
def shaperKind (iso : Option String) (gsubTag : Option String) : ShaperKind :=
  let generic := gsubTag == none || gsubTag == some "DFLT" || gsubTag == some "latn"
  match iso with
  | none => .default
  | some s =>
    if useScripts.contains s then (if generic then .default else .use)
    else if ["Beng", "Deva", "Gujr", "Guru", "Knda", "Mlym", "Orya", "Taml", "Telu"].contains s then
      (if generic then .default
       else if (gsubTag.getD "").endsWith "3" then .use else .dfltOnly)
    else if s == "Mymr" then (if generic || gsubTag == some "mymr" then .default else .dfltOnly)
    else if otherComplexScripts.contains s then .dfltOnly
    else .default

/-- Parse HarfBuzz feature syntax for whole-text settings: `tag`, `+tag`,
`-tag`, `tag=0`, `tag=1`, comma-separated. A range or another value is refused. -/
def parseFeatures (s : String) : Except String (List (String × Bool)) := do
  let mut out : List (String × Bool) := []
  for item0 in s.splitOn "," do
    let item := item0.trimAscii.toString
    if item.isEmpty then continue
    if item.contains '[' then throw s!"font.layout.unsupported: feature range in '{item}'"
    let (on, rest) :=
      if item.startsWith "-" then (false, (item.drop 1).toString)
      else if item.startsWith "+" then (true, (item.drop 1).toString) else (true, item)
    let (tag0, on) ← match rest.splitOn "=" with
      | [t] => pure (t, on)
      | [t, "0"] => pure (t, false)
      | [t, "1"] => pure (t, on)
      | _ => throw s!"font.layout.unsupported: feature value in '{item}'"
    let tag := tag0.trimAscii.toString
    if tag.isEmpty || tag.length > 4 then throw s!"font.layout.unsupported: feature tag '{tag}'"
    out := out ++ [(tag ++ String.ofList (List.replicate (4 - tag.length) ' '), on)]
  return out

def shape (b : ByteArray) (dir : Array TableRecord) (face : Face) (text : String)
    (limits : Limits := {}) (settings : List (String × Bool) := []) : Except String Shaped := do
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
  -- The shaper HarfBuzz would choose, and the script tags Lean uses.
  let tags0 := SfntKern.scriptTags text
  let gsubTag ← match dir.find? (·.tag == "GSUB") with
    | some r => do pure ((← SfntSubst.chooseScript b r.offset tags0).map (·.1))
    | none => pure none
  let kind := shaperKind (SfntKern.textScript text) gsubTag
  let tags := if kind == .dfltOnly then ["DFLT"] else tags0
  let mut run ← SfntSubst.substitute face b dir text nominal limits
    (stagesWithSettings (if kind == .use then SfntSubst.useStages else SfntSubst.defaultStages) settings) tags
    isUnicodeMark
  -- Hide default ignorables before positioning (HarfBuzz
  -- `hb_ot_hide_default_ignorables`): the space glyph, or deleted when the
  -- font has no space glyph.
  let ignorableN (g : NominalGlyph) : Bool := isDefaultIgnorable g.codepoint && !g.substituted
  if spaceGlyph != 0 then
    run := run.map fun g => if ignorableN g then { g with id := spaceGlyph, advance := face.advances[spaceGlyph]! } else g
  else
    run := run.filter (!ignorableN ·)
  -- Space fallback widths, before GPOS as in HarfBuzz `hb_ot_position_default`
  -- (`_hb_ot_shape_fallback_spaces`).
  let upem := face.unitsPerEm
  let advanceOf (c : Char) : Except String (Option Nat) := do
    let g ← face.glyph b c
    return if g == 0 then none else some face.advances[g]!
  let mut figure : Option Nat := none
  for d in "0123456789".toList do
    if figure.isNone then figure ← advanceOf d
  let punct ← match ← advanceOf '.' with
    | some a => pure (some a)
    | none => advanceOf ','
  for k in [0:run.size] do
    let g := run[k]!
    if g.spaceFallback != 0 && !g.ligated then
      let st := g.spaceFallback
      let adv : Nat :=
        if st ≤ 16 then (upem + st / 2) / st
        else if st == 17 then upem * 4 / 18
        else if st == 19 then figure.getD g.advance
        else if st == 20 then punct.getD g.advance
        else if st == 21 then g.advance / 2
        else g.advance
      run := run.set! k { g with advance := adv }
  let mut glyphs ← position b dir text run limits (withSettings SfntGpos.defaultFeatures settings) tags
  -- HarfBuzz `hb_ot_zero_width_default_ignorables`.
  glyphs := glyphs.map fun g =>
    if isDefaultIgnorable g.codepoint && !g.substituted then { g with advance := 0, xOffset := 0 } else g
  -- HarfBuzz fallback mark positioning, for a font with no GPOS table.
  if !dir.any (·.tag == "GPOS") then
    glyphs ← SfntFallback.position b dir face.unitsPerEm face.advances (fun g => isUnicodeMark g.codepoint) glyphs
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
