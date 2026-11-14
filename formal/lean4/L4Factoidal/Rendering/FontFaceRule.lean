import L4Factoidal.Rendering.Style

/-! # CSS `@font-face` rules and font matching (CSS Fonts 4 §4 and §5)

A page names its own fonts with `@font-face` rules. This module reads the rules of
the page's sheets (`CSS.fontFaceBlocks`), and decides, for the text of a document,
which faces the text uses: the host fetches only those (lazy loading, CSS Fonts 4
§4.8: "user agents must download only the faces that are used").

Profile:

* descriptors `font-family`, `src` (`url()` with an optional `format()`; `local()`
  is never matched: there are no system fonts), `font-weight` (one value or a range),
  `font-style` and `unicode-range`; others are read and ignored;
* formats: `truetype`, `opentype`, `collection` and a source with no format; WOFF,
  WOFF 2, SVG fonts and EOT need a decoder that the engine does not have, so such a
  source is passed over (§4.3: an unsupported format is skipped);
* matching (§5.2): the faces of a family are narrowed by style, then by weight, then
  each character takes the last defined face whose `unicode-range` holds it.
  The element style of this profile has no `font-weight` or `font-style`, so the
  wanted face is weight 400, style normal.

The host fetches the bytes of a used face (same origin, size limits), and gives them
to Lean, which checks each font with the font safety policy before it holds it. A
face whose bytes do not come, or that the policy refuses, is not used: its text falls
back to the next family, as §5 says for a face that fails to load. -/
namespace L4Factoidal.Rendering.FontFaceRule
open DOM

private def trim (s : String) := s.trimAscii.toString

/-- One `@font-face` rule. `sources` are the URLs of `src` in order, those of a
format this engine can not read left out, resolved against the base of the sheet. -/
structure Face where
  family : String
  sources : List String
  weight : Nat × Nat := (400,400)
  style : String := "normal"
  /-- Inclusive code point ranges; all of Unicode when the rule gives none. -/
  ranges : List (Nat × Nat) := [(0,0x10FFFF)]
  deriving Repr, BEq, Inhabited

/-- Formats with an sfnt in them (§4.3.1, `<font-format>`). -/
def readableFormat (format : String) : Bool :=
  ["truetype","opentype","collection"].contains format.toLower

private def unquote (s : String) : String :=
  let s := trim s
  if s.length ≥ 2 && ((s.startsWith "\"" && s.endsWith "\"") || (s.startsWith "'" && s.endsWith "'"))
  then ((s.drop 1).dropEnd 1).toString else s

/-- The argument of a function token `name(...)` at the start of `s`, and the rest. -/
private def functionArg (name s : String) : Option (String × String) := do
  let s := trim s
  if !(s.toLower.startsWith (name ++ "(")) then none
  let body := (s.drop (name.length+1)).toString
  let close ← body.toList.findIdx? (· == ')')
  some ((body.take close).toString,(body.drop (close+1)).toString)

/-- One item of `src` (§4.3): the URL of a `url()` whose `format()`, when given, is
readable. `local()`, an unreadable format and a `tech()` give none. -/
def sourceURL (item : String) : Option String := do
  let (url,rest) ← functionArg "url" item
  let url := unquote url
  if url.isEmpty then none
  let rest := trim rest
  if rest.isEmpty then return url
  let (format,after) ← functionArg "format" rest
  if !(trim after).isEmpty then none
  if readableFormat (unquote format) then some url else none

/-- `font-weight` of `@font-face` (§4.5): `normal`, `bold`, a number from 1 to 1000,
or two of them as a range. -/
def weightRange (value : String) : Option (Nat × Nat) := do
  let one := fun (w : String) => match w.toLower with
    | "normal" => some 400 | "bold" => some 700
    | other => match other.toNat? with
      | some n => if 1 ≤ n && n ≤ 1000 then some n else none
      | none => none
  match ((trim value).splitOn " ").filter (!·.isEmpty) with
  | [w] => let n ← one w; some (n,n)
  | [a,b] => let x ← one a; let y ← one b; some (min x y,max x y)
  | _ => none

/-- `font-style` of `@font-face` (§4.4): `normal`, `italic` or `oblique` (angles are
read as `oblique`). -/
def styleValue (value : String) : Option String :=
  match (((trim value).splitOn " ").filter (!·.isEmpty)).head? with
  | some "normal" => some "normal"
  | some "italic" => some "italic"
  | some "oblique" => some "oblique"
  | _ => none

private def hexValue (s : String) : Option Nat :=
  if s.isEmpty || s.length > 6 then none else
  s.toList.foldlM (fun acc c =>
    if '0' ≤ c && c ≤ '9' then some (acc*16+(c.toNat-'0'.toNat))
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (acc*16+(c.toLower.toNat-'a'.toNat+10))
    else none) 0

/-- One `<urange>` (CSS Syntax 3 §7.1): `U+41`, `U+0-7F`, or `U+4??` (wildcards). -/
def urange (item : String) : Option (Nat × Nat) := do
  let s := trim item
  if !(s.startsWith "U+" || s.startsWith "u+") then none
  let body := (s.drop 2).toString
  match body.splitOn "-" with
  | [a,b] =>
    let lo ← hexValue a
    let hi ← hexValue b
    if lo ≤ hi && hi ≤ 0x10FFFF then some (lo,hi) else none
  | [a] =>
    let stem := a.takeWhile (· != '?') |>.toString
    let wild := a.length-stem.length
    if wild > 0 && !(a.drop stem.length).toString.all (· == '?') then none
    if a.isEmpty || a.length > 6 then none
    let lo ← if stem.isEmpty then some 0 else hexValue stem
    let lo := lo*16^wild
    let hi := lo+16^wild-1
    if hi ≤ 0x10FFFF then some (lo,hi) else none
  | _ => none

/-- `unicode-range` (§4.6): a comma list of ranges; none when an item is invalid. -/
def rangeList (value : String) : Option (List (Nat × Nat)) :=
  ((value.splitOn ",").mapM urange).bind fun rs => if rs.isEmpty then none else some rs

/-- The rule of one `@font-face` block, with its URLs resolved by `resolve`. A rule
with no `font-family`, or with no source that this engine can read, is no face
(§4: such a rule is invalid, or never loads). Invalid descriptors are dropped. -/
def ofBlock (resolve : String → String) (block : String) : Option Face := do
  let decls := (CSS.declarations block).toOption.getD []
  let get := fun (key : String) => (decls.reverse.find? (·.property == key)).map (·.value)
  let family ← (get "font-family").bind CSS.familyNames
  let [family] := family | none
  let sources := ((get "src").map CSS.splitTopCommas).getD [] |>.filterMap sourceURL
  if sources.isEmpty then none
  some {
    family, sources := sources.map resolve,
    weight := ((get "font-weight").bind weightRange).getD (400,400),
    style := ((get "font-style").bind styleValue).getD "normal",
    ranges := ((get "unicode-range").bind rangeList).getD [(0,0x10FFFF)] }

/-- Most `@font-face` rules read for a document. -/
def maxFaces : Nat := 64

/-- The faces of sheets given as (base URL, source) pairs, in document order. -/
def ofSheets (medium : String) (resolve : String → String → String) (sheets : List (String × String)) :
    Array Face := Id.run do
  let mut out : Array Face := #[]
  for (base,source) in sheets do
    for block in CSS.fontFaceBlocks medium source do
      if out.size < maxFaces then
        if let some face := ofBlock (resolve base) block then out := out.push face
  return out

/-! ### Matching (§5.2) -/

def inRanges (ranges : List (Nat × Nat)) (c : Nat) : Bool :=
  ranges.any fun (lo,hi) => lo ≤ c && c ≤ hi

/-- How far a face's weight range is from the wanted weight, as an order key (less
is better): §5.2 step 4, `font-weight`. -/
def weightRank (wanted : Nat) (range : Nat × Nat) : Nat × Nat :=
  let (lo,hi) := range
  if lo ≤ wanted && wanted ≤ hi then (0,0)
  else if 400 ≤ wanted && wanted ≤ 500 then
    if wanted < lo && lo ≤ 500 then (1,lo-wanted)
    else if hi < wanted then (2,wanted-hi)
    else (3,lo-500)
  else if wanted < 400 then
    if hi < wanted then (1,wanted-hi) else (2,lo-wanted)
  else
    if wanted < lo then (1,lo-wanted) else (2,wanted-hi)

/-- The order of styles to try for a wanted style (§5.2, `font-style`). -/
def styleOrder : String → List String
  | "italic" => ["italic","oblique","normal"]
  | "oblique" => ["oblique","italic","normal"]
  | _ => ["normal","oblique","italic"]

private def lexLess (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

/-- The indices of the faces of `family` that §5.2 selects for weight `weight` and
style `style`, last defined first: the faces that `unicode-range` then chooses from.
Empty when the family has no face. -/
def selected (faces : Array Face) (family : String) (weight : Nat := 400) (style : String := "normal") :
    List Nat := Id.run do
  let family := family.toLower
  let ofFamily := (List.range faces.size).filter fun i => (faces[i]!).family.toLower == family
  if ofFamily.isEmpty then return []
  let some st := (styleOrder style).find? (fun st => ofFamily.any fun i => (faces[i]!).style == st) | return []
  let styled := ofFamily.filter fun i => (faces[i]!).style == st
  let best := styled.foldl (fun (acc : Option (Nat × Nat)) i =>
    let r := weightRank weight (faces[i]!).weight
    match acc with
    | some b => if lexLess r b then some r else some b
    | none => some r) none
  return (styled.filter fun i => some (weightRank weight (faces[i]!).weight) == best).reverse

/-- Families that name no `@font-face` face but end the search: the generic families
and the fonts the engine holds (`held`, lower case). -/
def endsSearch (held : List String) (family : String) : Bool :=
  ["serif","sans-serif","monospace","cursive","fantasy","system-ui","ui-serif","ui-sans-serif",
    "ui-monospace","ui-rounded","math","emoji","fangsong"].contains family.toLower ||
  held.contains family.toLower

/-- The face that draws character `c` in an element of family list `families`: the
first family with a selected face whose range holds `c`. `none` when a generic or
held family comes first, or when no face holds it. -/
def faceFor (faces : Array Face) (held : List String) (families : List String) (c : Nat) : Option Nat := Id.run do
  for family in families do
    if let some i := (selected faces family).find? (fun i => inRanges (faces[i]!).ranges c) then return some i
    if endsSearch held family then return none
  return none

/-- The faces used by `text` in an element of family list `families`, added to `used`.
Each distinct character is looked at once. White space uses a face only when the text
has other characters, and only through them: it is drawn with the word's face. -/
def usedBy (faces : Array Face) (held : List String) (families : List String) (text : String)
    (used : Array Bool) : Array Bool := Id.run do
  if faces.isEmpty then return used
  let mut seen : Std.TreeMap Nat Unit := {}
  let mut out := used
  for ch in text.toList do
    let c := ch.toNat
    if ch.isWhitespace || seen.contains c then continue
    seen := seen.insert c ()
    if let some i := faceFor faces held families c then out := out.set! i true
  return out

/-! ### The text of a document -/

/-- The family list of an SVG text node, as the SVG text reader takes it
(`NativeSVGText.TextState`): the `font-family` attribute or `style` property of the
nearest SVG element that has one. `none` outside SVG or with neither. -/
def svgFamily (dom : Dom) (id : Nat) : Option (List String) := Id.run do
  let mut at_ := (dom.get id).parent
  for _ in [:dom.size+1] do
    let some p := at_ | return none
    let n := dom.get p
    if n.ns != some DOM.svgNS then return none
    let attr := CSS.attrValue n "font-family"
    let fromStyle := ((CSS.declarations (CSS.attrValue n "style")).toOption.getD []).reverse.find?
      (·.property == "font-family") |>.map (·.value)
    match fromStyle.orElse (fun _ => if attr.isEmpty then none else some attr) with
    | some value => return CSS.familyNames value
    | none => at_ := n.parent
  return none

/-- A text node is rendered: no ancestor element has `display: none` (styles from
`CSS.computeAll`). -/
def rendered (dom : Dom) (styles : Array CSS.Computed) (id : Nat) : Bool := Id.run do
  let mut at_ := (dom.get id).parent
  for _ in [:dom.size+1] do
    let some p := at_ | return true
    if (styles[p]?.map (·.display == .none)).getD false then return false
    at_ := (dom.get p).parent
  return true

/-- The faces that the rendered text of `dom` uses (§4.8), as flags by face index:
HTML text by the computed `font-family`, SVG text by its own `font-family`. `held`
lists the families of the fonts the engine holds. -/
def usedFaces (faces : Array Face) (held : List String) (dom : Dom) (styles : Array CSS.Computed) : Array Bool := Id.run do
  let mut used := Array.replicate faces.size false
  if faces.isEmpty then return used
  let held := held.map (·.toLower)
  for id in [:dom.size] do
    let n := dom.get id
    if n.type != .text || n.data.all Char.isWhitespace then continue
    if !rendered dom styles id then continue
    let families := match svgFamily dom id with
      | some names => names
      | none => match n.parent with
        | some p => if (dom.get p).ns == some DOM.svgNS then [] else
            CSS.familyList ((styles[id]?.map (·.fontFamily)).getD "")
        | none => []
    used := usedBy faces held families n.data used
  return used

/-- The faces whose family a `font-family` declaration of the page's rules names (the
`font` shorthand is read into `font-family` by the cascade). A page that builds its text
from script after it loads has no text naming its fonts yet, so `usedFaces` alone would
fetch none of them; a face its own rules name is fetched as well. -/
def declaredFaces (faces : Array Face) (rules : List CSS.Rule) : Array Bool :=
  if faces.isEmpty then #[] else
  let families : List String := rules.foldl (fun acc r => r.declarations.foldl (fun acc d =>
    if d.property == "font-family" then ((CSS.familyNames d.value).getD []).map (·.toLower) ++ acc else acc) acc) []
  faces.map fun f => families.contains f.family.toLower

/-- Kind: totality. Says: one answer for each face. -/
theorem declaredFaces_size (faces : Array Face) (rules : List CSS.Rule) :
    (declaredFaces faces rules).size = faces.size ∨ faces.size = 0 := by
  unfold declaredFaces
  split
  · right; simp_all
  · left; simp

#guard ((CSS.parse ".g{font:10px/1 Ahem}").toOption.map fun rs =>
  declaredFaces #[{family := "Ahem", sources := ["a.ttf"]}, {family := "Other", sources := ["b.ttf"]}] rs) ==
  some #[true, false]
#guard ((CSS.parse ".g{font-family:'Ahem', serif}").toOption.map fun rs =>
  declaredFaces #[{family := "ahem", sources := ["a.ttf"]}] rs) == some #[true]

end L4Factoidal.Rendering.FontFaceRule
