/-
L4Factoidal.PageCanvas.Text: the `font` attribute and text of Canvas 2D (HTML §4.12.5.1.6,
§4.12.5.1.13 "text preparation algorithm"; record docs/designissues/2026-11-08-canvas-2d.md).

`parseFont` reads the CSS `font` shorthand (CSS Fonts 4 §2.8) as the canvas uses it:
style, variant, weight, stretch, size (with relative sizes against 10px, the canvas
default), an optional line height (dropped), and the family list. Text is shaped by the
Lean shaper (`Rendering.SfntProfile.wordIn`) with the fonts the engine holds, and its
glyph outlines become a path.
-/
import L4Factoidal.PageCanvas.State
import L4Factoidal.Rendering.SfntProfile

namespace L4Factoidal.PageCanvas
open L4Factoidal.Rendering

namespace Text

def words (s : String) : List String := ((s.split Color.isSpace).toList.map (·.toString)).filter (· != "")

/-- A CSS length for `font-size`, in px; relative units against `base` (10px). -/
def sizePx? (s : String) (base : Float := 10) : Option Float :=
  let kw : List (String × Float) := [("xx-small", 9), ("x-small", 10), ("small", 13), ("medium", 16),
    ("large", 18), ("x-large", 24), ("xx-large", 32), ("xxx-large", 48), ("larger", base * 1.2), ("smaller", base / 1.2)]
  match kw.find? (·.1 == s) with
  | some (_, v) => some v
  | none =>
    let unit := fun (u : String) (k : Float) =>
      if s.endsWith u then (· * k) <$> Color.number? (s.dropEnd u.length).toString else none
    (unit "px" 1).orElse fun _ => (unit "pt" (4/3)).orElse fun _ => (unit "pc" 16).orElse fun _ =>
    (unit "rem" 10).orElse fun _ => (unit "em" base).orElse fun _ => (unit "%" (base / 100)).orElse fun _ =>
    (unit "in" 96).orElse fun _ => (unit "cm" (96 / 2.54)).orElse fun _ => (unit "mm" (96 / 25.4)).orElse fun _ =>
    (unit "q" (96 / 101.6)).orElse fun _ => (unit "ex" (base / 2)).orElse fun _ => (unit "ch" (base / 2))

/-- A number as CSS prints a whole number, or with up to six decimals. -/
def num (v : Float) : String :=
  if !v.isFinite then toString v else
  let neg := v < 0
  let a := v.abs
  let whole := a.floor
  let frac := ((a - whole) * 1000000).round
  let (whole, frac) := if frac >= 1000000 then (whole + 1, 0) else (whole, frac)
  let ft := toString frac.toUInt64.toNat
  let ft := "".pushn '0' (6 - ft.length) ++ ft
  let ft := String.ofList (ft.toList.reverse.dropWhile (· == '0')).reverse
  (if neg && (whole > 0 || !ft.isEmpty) then "-" else "") ++ toString whole.toUInt64.toNat ++ (if ft.isEmpty then "" else "." ++ ft)

/-- The generic families (CSS Fonts 4 §2.1.3), serialised in lower case. -/
def generics : List String := ["serif", "sans-serif", "cursive", "fantasy", "monospace", "system-ui", "math",
  "emoji", "fangsong", "ui-serif", "ui-sans-serif", "ui-monospace", "ui-rounded"]

/-- The family list, with spaces after commas as CSS serialises it, generic names in lower
case. `none` for a list CSS does not accept (an empty name, a CSS-wide keyword, or a
character that is not part of a name). -/
def familyText? (s : String) : Option String := do
  let names := (s.splitOn ",").map Color.trim
  let out ← names.mapM fun n => do
    if n.isEmpty then none
    let low := Color.asciiLower n
    if ["inherit", "initial", "unset", "default", "revert", "revert-layer"].contains low then none
    if n.startsWith "\"" || n.startsWith "'" then return n
    if n.any (fun c => "{}()[];!@#$%^&*=+<>?/\\|`~".toList.contains c) then none
    return if generics.contains low then low else n
  return ", ".intercalate out

/-- The words before the size, the size word, and the words after it. -/
def splitAtSize (pre : List String) : List String → Option (List String × String × List String)
  | [] => none
  | w :: rest =>
    let lw := Color.asciiLower w
    let sizePart := (lw.splitOn "/").headD ""
    if (sizePx? sizePart).isSome && !(["normal", "bold", "bolder", "lighter", "italic", "oblique", "small-caps"].contains lw)
      && !(lw.toList.all Char.isDigit && lw.length == 3) then some (pre.reverse, w, rest)
    else splitAtSize (w :: pre) rest

/-- Parse a CSS `font` value. `none` when it is not a font (the attribute keeps its value). -/
def parseFont? (source : String) : Option Font := do
  let s := Color.trim source
  if s.isEmpty then none
  let lower := Color.asciiLower s
  -- System fonts are not supported by this engine.
  if ["caption", "icon", "menu", "message-box", "small-caption", "status-bar"].contains lower then none
  -- The size is the first word that is a size; before it, style, variant, weight, stretch.
  let ws := words s
  let (pre, sizeWord, rest) ← splitAtSize [] ws
  let mut bold := false
  let mut italic := false
  let mut smallCaps := false
  let mut weight : Option String := none
  let mut stretch : Option String := none
  for w in pre do
    let lw := Color.asciiLower w
    if lw == "normal" then continue
    else if lw == "italic" || lw == "oblique" then italic := true
    else if lw == "small-caps" then smallCaps := true
    else if lw == "bold" || lw == "bolder" then
      bold := true
      weight := some "bold"
    else if lw == "lighter" then weight := some "lighter"
    else if lw.length == 3 && lw.toList.all Char.isDigit then
      if lw == "700" then
        bold := true
        weight := some "bold"
      else if lw != "400" then
        bold := lw.toNat! ≥ 600
        weight := some lw
    else if ["ultra-condensed", "extra-condensed", "condensed", "semi-condensed", "semi-expanded", "expanded",
        "extra-expanded", "ultra-expanded"].contains lw then stretch := some lw
    else none
  let lsize := Color.asciiLower sizeWord
  let parts := lsize.splitOn "/"
  let size ← sizePx? (parts.headD "")
  if size < 0 then none
  -- A line height may follow, attached or as the next word.
  let (rest, _) := match parts, rest with
    | [_], "/" :: _ :: more => (more, ())
    | [_], w :: more => if w.startsWith "/" then ((if w == "/" then more.drop 1 else more), ()) else (w :: more, ())
    | _, r => (r, ())
  let family := Color.trim (" ".intercalate rest)
  if family.isEmpty then none
  let lead := (if italic then "italic " else "") ++ (if smallCaps then "small-caps " else "") ++
    (match weight with | some w => w ++ " " | none => "") ++ (match stretch with | some t => t ++ " " | none => "")
  let fam ← familyText? family
  return { text := lead ++ num size ++ "px " ++ fam, size, bold, italic, family := fam }

/-- The held fonts in the order the family list asks: a held font whose family is named
goes first. -/
def fontsFor (fonts : Array SfntProfile.Font) (family : String) : Array SfntProfile.Font :=
  let names := (family.splitOn ",").map fun n => Color.asciiLower ((Color.trim n).replace "\"" "" |>.replace "'" "")
  match fonts.findIdx? (fun f => names.contains (Color.asciiLower f.family)) with
  | some i => match fonts[i]? with
    | some f => #[f] ++ (fonts.eraseIdx! i)
    | none => fonts
  | none => fonts

/-- The shaped text: its glyphs, advance and metrics, in font units, and the scale
from font units to CSS pixels. -/
structure Shaped where
  word : FontProvider.Word
  scale : Float

/-- Text replaced as HTML §4.12.5.1.13 says (every ASCII whitespace becomes a space). -/
def prepare (s : String) : String := s.map fun c => if Color.isSpace c then ' ' else c

def shape (fonts : Array SfntProfile.Font) (font : Font) (text : String) : Option Shaped := do
  if fonts.isEmpty || font.size <= 0 then none
  let fs := fontsFor fonts font.family
  let px := max 1 (min 512 font.size.round.toUInt64.toNat)
  match SfntProfile.wordIn fs (prepare text) px with
  | .ok w => some ⟨w, font.size / w.unitsPerEm⟩
  | .error _ => none

/-- Where the baseline of the text goes, below `y` (HTML §4.12.5.1.13 step 11, with
the em box from the font's ascent and descent). -/
def baselineShift (b : Baseline) (s : Shaped) : Float :=
  let a := s.word.ascent * s.scale
  let d := s.word.descent * s.scale
  match b with
  | .alphabetic => 0
  | .top => a
  | .hanging => a * 0.8
  | .middle => (a - d) / 2
  | .ideographic | .bottom => -d

/-- The x of the start of the text, for an anchor `x` (HTML step 10). -/
def alignShift (a : Align) (dir : Direction) (width : Float) : Float :=
  let rtl := dir == .rtl
  match a with
  | .left => 0
  | .right => -width
  | .center => -width / 2
  | .start => if rtl then -width else 0
  | .end_ => if rtl then 0 else -width

private def segOf (k sx ox oy : Float) (x0 y0 : Float) : Rendering.PathSegment → Seg
  | .line p => .line (x0 + (ox + p.x) * k * sx) (y0 + (oy + p.y) * k)
  | .quadratic c p => .quad (x0 + (ox + c.x) * k * sx) (y0 + (oy + c.y) * k) (x0 + (ox + p.x) * k * sx) (y0 + (oy + p.y) * k)
  | .cubic a b p => .cubic (x0 + (ox + a.x) * k * sx) (y0 + (oy + a.y) * k) (x0 + (ox + b.x) * k * sx) (y0 + (oy + b.y) * k)
      (x0 + (ox + p.x) * k * sx) (y0 + (oy + p.y) * k)
  | .arc _ _ _ _ _ p => .line (x0 + (ox + p.x) * k * sx) (y0 + (oy + p.y) * k)

/-- The glyph outlines of shaped text as a path in user space: the word's top-left at
`(x0, y0)`, its x scaled by `sx` (for `maxWidth`). -/
def outlinePath (s : Shaped) (x0 y0 sx : Float) : Path := Id.run do
  let k := s.scale
  let mut p : Path := {}
  for g in s.word.glyphs do
    for geo in g.geometry do
      match geo with
      | .path contours =>
        for c in contours do
          match c with
          | .empty _ => pure ()
          | .path st segs closed =>
            p := p.moveTo (x0 + (g.x + st.x) * k * sx) (y0 + (g.y + st.y) * k)
            for sg in segs do
              match segOf k sx g.x g.y x0 y0 sg with
              | .line x y => p := p.lineTo x y
              | .quad cx cy x y => p := p.quadTo cx cy x y
              | .cubic ax ay bx by_ x y => p := p.cubicTo ax ay bx by_ x y
              | _ => pure ()
            if closed then p := p.close
      | _ => pure ()
  return p

end Text
end L4Factoidal.PageCanvas
