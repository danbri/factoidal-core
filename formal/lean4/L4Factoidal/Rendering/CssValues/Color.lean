/-
L4Factoidal.Rendering.CssValues.Color — the CSS `<color>` type (CSS Color 4 and 5): parsing
of one component value into a colour, and its canonical serialisation (CSSOM §6.7.2,
CSS Color 4 §15), in exact rational arithmetic.

What is covered: named colours, `transparent`, `currentcolor`, system colours, hex
colours, `rgb()`/`rgba()`, `hsl()`/`hsla()`, `hwb()`, `lab()`, `lch()`, `oklab()`,
`oklch()`, `color()` for the predefined spaces, `color-mix()` (kept as a function in the
specified value; resolved in the computed value when the mixing space is `srgb`, `hsl` or
`hwb` and every colour is in the sRGB family), relative colours (kept in the specified
value; resolved when origin and target are in the sRGB family), and `light-dark()`.

Conversions that need a cube root or a transfer function (to and from `lab`, `lch`,
`oklab`, `oklch`, `srgb-linear`, the `xyz` spaces and the wide-gamut RGB spaces) are not
done here: no `Float` is used in `CssValues`.

The reference for the serialised text is Chrome, as recorded in the expectations of the
web-platform-tests under `css/css-color/parsing/`.
-/
import L4Factoidal.Rendering.CssValues.Token

namespace L4Factoidal.Rendering.CssValues.Color

open L4Factoidal.Rendering.CssValues

/-! ### Interface types -/

/-- One component of a colour function as the caller resolved it. -/
inductive Comp where
  | num (v : Rat) | pct (v : Rat) | angle (deg : Rat) | none
  deriving Repr, DecidableEq

/-- Reads one component value as a colour component; the caller passes a reader that also
evaluates `calc()`. -/
abbrev Reader := CV → Option Comp

/-- Degrees in one radian, 180/π, as the rational 57.29577951308232 (the nearest double,
written out in decimal). It is an approximation: π is irrational. The serialised text keeps
six significant digits, so the error (below 1e-14 relative) is never visible. -/
def radToDeg : Rat := (5729577951308232 : Rat) / 100000000000000

/-- Literal tokens only: a number, a percentage, an angle dimension (deg, grad, rad, turn),
the keyword `none`. Radians use the rational approximation `radToDeg`. -/
def literalReader : Reader
  | .tok (.num v _) => some (.num v)
  | .tok (.pct v) => some (.pct v)
  | .tok (.dim v _ u) =>
    let u := lower u
    if u == "deg" then some (.angle v)
    else if u == "grad" then some (.angle (v * 9 / 10))
    else if u == "rad" then some (.angle (v * radToDeg))
    else if u == "turn" then some (.angle (v * 360))
    else Option.none
  | .tok (.ident s) => if lower s == "none" then some Comp.none else Option.none
  | _ => Option.none

structure Opts where
  /-- Computed-value form: `currentcolor` is replaced by `current` when that is given, and
  colour functions are resolved (`color-mix()`, relative colours, `light-dark()` with `dark`). -/
  computed : Bool := false
  current : Option String := none
  dark : Bool := false
  read : Reader := literalReader

/-- The colour space a colour is held in. `rgb` is the legacy sRGB form (`rgb()`, hex and
named colours: serialised as `rgb(r, g, b)`); `srgb` is `color(srgb ...)`. -/
inductive Space where
  | rgb | hsl | hwb | lab | lch | oklab | oklch
  | srgb | srgbLinear | displayP3 | displayP3Linear | a98Rgb | prophotoRgb | rec2020
  | xyzD50 | xyzD65
  deriving Repr, DecidableEq

/-- A colour: three components and alpha, each a number or missing (`none`).
Units: `rgb` and the `color()` spaces hold numbers where 0 to 1 is the nominal range (`rgb`
is clamped to it); `hsl` holds the hue in degrees in `[0, 360)` and saturation and
lightness as percentages (0 to 100); `hwb` the hue, whiteness and blackness likewise;
`lab` and `lch` hold lightness 0 to 100, `oklab` and `oklch` 0 to 1; a hue is in degrees.
Alpha is in `[0, 1]`. -/
structure Color where
  space : Space
  c1 : Option Rat
  c2 : Option Rat
  c3 : Option Rat
  alpha : Option Rat := some 1
  deriving Repr, DecidableEq

/-- A colour of the sRGB family with no missing component: channels where 0 to 1 is the
nominal range, not clamped; alpha in `[0, 1]`. -/
structure Rgba where
  r : Rat
  g : Rat
  b : Rat
  a : Rat
  deriving Repr, DecidableEq

/-! ### Arithmetic -/

def rmin (a b : Rat) : Rat := if a < b then a else b
def rmax (a b : Rat) : Rat := if a < b then b else a

/-- `x` limited to `[0, 1]`. -/
def clamp01 (x : Rat) : Rat := if x < 0 then 0 else if 1 < x then 1 else x

/-- `x` limited to be at least 0. -/
def clampPos (x : Rat) : Rat := if x < 0 then 0 else x

/-- `x` modulo `m` (for `m > 0`): in `[0, m)`. -/
def rmod (x m : Rat) : Rat := x - m * ((x / m).floor : Int)

/-- Rounding to the nearest integer, halves upwards. -/
def roundHalfUp (x : Rat) : Int := (x + (1 : Rat) / 2).floor

/-- The 8-bit value of a channel or alpha where 1 is full: clamped, times 255, rounded
halves upwards. -/
def byteOf (x : Rat) : Nat := Nat.min 255 (roundHalfUp (clamp01 x * 255)).toNat

/-- CSS Color 4 §7.1: one channel of the sRGB colour of an HSL colour (`h` in degrees, `s`
and `l` as fractions); `n` is 0 for red, 8 for green, 4 for blue. -/
def hslChan (h s l n : Rat) : Rat :=
  let k := rmod (n + h / 30) 12
  let a := s * rmin l (1 - l)
  l - a * rmax (-1) (rmin (rmin (k - 3) (9 - k)) 1)

/-- CSS Color 4 §7.1: HSL to sRGB, exact. -/
def hslToRgb (h s l : Rat) : Rat × Rat × Rat :=
  (hslChan h s l 0, hslChan h s l 8, hslChan h s l 4)

/-- CSS Color 4 §8.1: HWB to sRGB, exact (`w` and `b` as fractions). When whiteness and
blackness add up to 1 or more the colour is a grey. -/
def hwbToRgb (h w b : Rat) : Rat × Rat × Rat :=
  if 1 ≤ w + b then
    let g := w / (w + b)
    (g, g, g)
  else
    let (r, g, bl) := hslToRgb h 1 ((1 : Rat) / 2)
    (r * (1 - w - b) + w, g * (1 - w - b) + w, bl * (1 - w - b) + w)

/-- The hue in degrees of an sRGB colour, or `none` for a grey. -/
def rgbToHue (r g b : Rat) : Option Rat :=
  let mx := rmax r (rmax g b)
  let mn := rmin r (rmin g b)
  let d := mx - mn
  if d == 0 then none
  else if mx == r then some (rmod ((g - b) / d * 60) 360)
  else if mx == g then some ((b - r) / d * 60 + 120)
  else some ((r - g) / d * 60 + 240)

/-- CSS Color 4 §7.2: sRGB to HSL (hue in degrees, saturation and lightness as percentages). -/
def rgbToHsl (r g b : Rat) : Option Rat × Rat × Rat :=
  let mx := rmax r (rmax g b)
  let mn := rmin r (rmin g b)
  let l := (mx + mn) / 2
  let m := rmin l (1 - l)
  let s := if m == 0 then 0 else (mx - l) / m
  (rgbToHue r g b, s * 100, l * 100)

/-- CSS Color 4 §8.2: sRGB to HWB (hue in degrees, whiteness and blackness as percentages). -/
def rgbToHwb (r g b : Rat) : Option Rat × Rat × Rat :=
  (rgbToHue r g b, rmin r (rmin g b) * 100, (1 - rmax r (rmax g b)) * 100)

/-! ### Tables -/

/-- The named colours of CSS Color 4 §6.1 with their 8-bit channels. -/
def namedColors : List (String × Nat × Nat × Nat) := [
  ("aliceblue", 240, 248, 255), ("antiquewhite", 250, 235, 215), ("aqua", 0, 255, 255),
  ("aquamarine", 127, 255, 212), ("azure", 240, 255, 255), ("beige", 245, 245, 220),
  ("bisque", 255, 228, 196), ("black", 0, 0, 0), ("blanchedalmond", 255, 235, 205),
  ("blue", 0, 0, 255), ("blueviolet", 138, 43, 226), ("brown", 165, 42, 42),
  ("burlywood", 222, 184, 135), ("cadetblue", 95, 158, 160), ("chartreuse", 127, 255, 0),
  ("chocolate", 210, 105, 30), ("coral", 255, 127, 80), ("cornflowerblue", 100, 149, 237),
  ("cornsilk", 255, 248, 220), ("crimson", 220, 20, 60), ("cyan", 0, 255, 255),
  ("darkblue", 0, 0, 139), ("darkcyan", 0, 139, 139), ("darkgoldenrod", 184, 134, 11),
  ("darkgray", 169, 169, 169), ("darkgreen", 0, 100, 0), ("darkgrey", 169, 169, 169),
  ("darkkhaki", 189, 183, 107), ("darkmagenta", 139, 0, 139), ("darkolivegreen", 85, 107, 47),
  ("darkorange", 255, 140, 0), ("darkorchid", 153, 50, 204), ("darkred", 139, 0, 0),
  ("darksalmon", 233, 150, 122), ("darkseagreen", 143, 188, 143), ("darkslateblue", 72, 61, 139),
  ("darkslategray", 47, 79, 79), ("darkslategrey", 47, 79, 79), ("darkturquoise", 0, 206, 209),
  ("darkviolet", 148, 0, 211), ("deeppink", 255, 20, 147), ("deepskyblue", 0, 191, 255),
  ("dimgray", 105, 105, 105), ("dimgrey", 105, 105, 105), ("dodgerblue", 30, 144, 255),
  ("firebrick", 178, 34, 34), ("floralwhite", 255, 250, 240), ("forestgreen", 34, 139, 34),
  ("fuchsia", 255, 0, 255), ("gainsboro", 220, 220, 220), ("ghostwhite", 248, 248, 255),
  ("gold", 255, 215, 0), ("goldenrod", 218, 165, 32), ("gray", 128, 128, 128),
  ("green", 0, 128, 0), ("greenyellow", 173, 255, 47), ("grey", 128, 128, 128),
  ("honeydew", 240, 255, 240), ("hotpink", 255, 105, 180), ("indianred", 205, 92, 92),
  ("indigo", 75, 0, 130), ("ivory", 255, 255, 240), ("khaki", 240, 230, 140),
  ("lavender", 230, 230, 250), ("lavenderblush", 255, 240, 245), ("lawngreen", 124, 252, 0),
  ("lemonchiffon", 255, 250, 205), ("lightblue", 173, 216, 230), ("lightcoral", 240, 128, 128),
  ("lightcyan", 224, 255, 255), ("lightgoldenrodyellow", 250, 250, 210),
  ("lightgray", 211, 211, 211), ("lightgreen", 144, 238, 144), ("lightgrey", 211, 211, 211),
  ("lightpink", 255, 182, 193), ("lightsalmon", 255, 160, 122), ("lightseagreen", 32, 178, 170),
  ("lightskyblue", 135, 206, 250), ("lightslategray", 119, 136, 153),
  ("lightslategrey", 119, 136, 153), ("lightsteelblue", 176, 196, 222),
  ("lightyellow", 255, 255, 224), ("lime", 0, 255, 0), ("limegreen", 50, 205, 50),
  ("linen", 250, 240, 230), ("magenta", 255, 0, 255), ("maroon", 128, 0, 0),
  ("mediumaquamarine", 102, 205, 170), ("mediumblue", 0, 0, 205), ("mediumorchid", 186, 85, 211),
  ("mediumpurple", 147, 112, 219), ("mediumseagreen", 60, 179, 113),
  ("mediumslateblue", 123, 104, 238), ("mediumspringgreen", 0, 250, 154),
  ("mediumturquoise", 72, 209, 204), ("mediumvioletred", 199, 21, 133),
  ("midnightblue", 25, 25, 112), ("mintcream", 245, 255, 250), ("mistyrose", 255, 228, 225),
  ("moccasin", 255, 228, 181), ("navajowhite", 255, 222, 173), ("navy", 0, 0, 128),
  ("oldlace", 253, 245, 230), ("olive", 128, 128, 0), ("olivedrab", 107, 142, 35),
  ("orange", 255, 165, 0), ("orangered", 255, 69, 0), ("orchid", 218, 112, 214),
  ("palegoldenrod", 238, 232, 170), ("palegreen", 152, 251, 152),
  ("paleturquoise", 175, 238, 238), ("palevioletred", 219, 112, 147),
  ("papayawhip", 255, 239, 213), ("peachpuff", 255, 218, 185), ("peru", 205, 133, 63),
  ("pink", 255, 192, 203), ("plum", 221, 160, 221), ("powderblue", 176, 224, 230),
  ("purple", 128, 0, 128), ("red", 255, 0, 0), ("rosybrown", 188, 143, 143),
  ("royalblue", 65, 105, 225), ("saddlebrown", 139, 69, 19), ("salmon", 250, 128, 114),
  ("sandybrown", 244, 164, 96), ("seagreen", 46, 139, 87), ("seashell", 255, 245, 238),
  ("sienna", 160, 82, 45), ("silver", 192, 192, 192), ("skyblue", 135, 206, 235),
  ("slateblue", 106, 90, 205), ("slategray", 112, 128, 144), ("slategrey", 112, 128, 144),
  ("snow", 255, 250, 250), ("springgreen", 0, 255, 127), ("steelblue", 70, 130, 180),
  ("tan", 210, 180, 140), ("teal", 0, 128, 128), ("thistle", 216, 191, 216),
  ("tomato", 255, 99, 71), ("turquoise", 64, 224, 208), ("violet", 238, 130, 238),
  ("wheat", 245, 222, 179), ("white", 255, 255, 255), ("whitesmoke", 245, 245, 245),
  ("yellow", 255, 255, 0), ("yellowgreen", 154, 205, 50),
  ("rebeccapurple", 102, 51, 153)]

/-- The system colours of CSS Color 4 §6.2 (and the deprecated ones of Appendix A) with
the values Chrome uses in the light colour scheme. -/
def systemColors : List (String × Nat × Nat × Nat) := [
  ("accentcolor", 0, 117, 255), ("accentcolortext", 255, 255, 255),
  ("activetext", 255, 0, 0), ("buttonborder", 118, 118, 118),
  ("buttonface", 239, 239, 239), ("buttontext", 0, 0, 0),
  ("canvas", 255, 255, 255), ("canvastext", 0, 0, 0),
  ("field", 255, 255, 255), ("fieldtext", 0, 0, 0),
  ("graytext", 128, 128, 128), ("highlight", 181, 213, 255),
  ("highlighttext", 0, 0, 0), ("linktext", 0, 0, 238),
  ("mark", 255, 255, 0), ("marktext", 0, 0, 0),
  ("selecteditem", 25, 103, 210), ("selecteditemtext", 255, 255, 255),
  ("visitedtext", 85, 26, 139),
  ("activeborder", 118, 118, 118), ("activecaption", 255, 255, 255),
  ("appworkspace", 255, 255, 255), ("background", 255, 255, 255),
  ("buttonhighlight", 239, 239, 239), ("buttonshadow", 239, 239, 239),
  ("captiontext", 0, 0, 0), ("inactiveborder", 118, 118, 118),
  ("inactivecaption", 255, 255, 255), ("inactivecaptiontext", 128, 128, 128),
  ("infobackground", 255, 255, 255), ("infotext", 0, 0, 0),
  ("menu", 255, 255, 255), ("menutext", 0, 0, 0),
  ("scrollbar", 255, 255, 255), ("threeddarkshadow", 118, 118, 118),
  ("threedface", 239, 239, 239), ("threedhighlight", 118, 118, 118),
  ("threedlightshadow", 118, 118, 118), ("threedshadow", 118, 118, 118),
  ("window", 255, 255, 255), ("windowframe", 118, 118, 118),
  ("windowtext", 0, 0, 0)]

def lookup (table : List (String × Nat × Nat × Nat)) (k : String) : Option (Nat × Nat × Nat) :=
  (table.find? (·.1 == k)).map (·.2)

/-- The legacy sRGB colour of three 8-bit channels and an 8-bit alpha. -/
def ofBytes (r g b : Nat) (a : Nat := 255) : Color :=
  ⟨.rgb, some ((r : Rat) / 255), some ((g : Rat) / 255), some ((b : Rat) / 255),
    some ((a : Rat) / 255)⟩

/-- The predefined spaces of `color()` by name (`xyz` is `xyz-d65`). -/
def predefined (name : String) : Option Space :=
  if name == "srgb" then some .srgb
  else if name == "srgb-linear" then some .srgbLinear
  else if name == "display-p3" then some .displayP3
  else if name == "display-p3-linear" then some .displayP3Linear
  else if name == "a98-rgb" then some .a98Rgb
  else if name == "prophoto-rgb" then some .prophotoRgb
  else if name == "rec2020" then some .rec2020
  else if name == "xyz-d50" then some .xyzD50
  else if name == "xyz-d65" || name == "xyz" then some .xyzD65
  else none

def Space.name : Space → String
  | .rgb => "rgb" | .hsl => "hsl" | .hwb => "hwb" | .lab => "lab" | .lch => "lch"
  | .oklab => "oklab" | .oklch => "oklch" | .srgb => "srgb" | .srgbLinear => "srgb-linear"
  | .displayP3 => "display-p3" | .displayP3Linear => "display-p3-linear"
  | .a98Rgb => "a98-rgb" | .prophotoRgb => "prophoto-rgb" | .rec2020 => "rec2020"
  | .xyzD50 => "xyz-d50" | .xyzD65 => "xyz-d65"

/-! ### Serialisation -/

def fmtOpt : Option Rat → String
  | some v => fmtRat v
  | none => "none"

def fmtOptPct : Option Rat → String
  | some v => fmtRat v ++ "%"
  | none => "none"

/-- The alpha of the modern syntax: nothing when it is 1. -/
def alphaSuffix : Option Rat → String
  | some a => if a == 1 then "" else " / " ++ fmtRat a
  | none => " / none"

/-- CSS Color 4 §15.2 (CSSOM "serialize an alpha value") for the legacy syntax: the alpha
as an 8-bit value, written with two decimals when those give the same 8-bit value back,
with three otherwise. -/
def legacyAlpha (a : Rat) : String :=
  let byte := byteOf a
  let two : Rat := ((roundHalfUp ((byte : Rat) * 100 / 255) : Int) : Rat) / 100
  if byteOf two == byte then fmtRat two
  else fmtRat (((roundHalfUp ((byte : Rat) * 1000 / 255) : Int) : Rat) / 1000)

/-- The legacy text `rgb(r, g, b)` or `rgba(r, g, b, a)` of an sRGB colour. -/
def legacyCss (r g b a : Rat) : String :=
  let body := toString (byteOf r) ++ ", " ++ toString (byteOf g) ++ ", " ++ toString (byteOf b)
  if a == 1 then "rgb(" ++ body ++ ")" else "rgba(" ++ body ++ ", " ++ legacyAlpha a ++ ")"

/-- The sRGB colour of a colour of the sRGB family (`rgb`, `hsl`, `hwb`, `color(srgb)`)
with no missing component. -/
def Color.rgba? (c : Color) : Option Rgba :=
  match c.c1, c.c2, c.c3, c.alpha with
  | some x, some y, some z, some a =>
    match c.space with
    | .rgb => some ⟨x, y, z, a⟩
    | .srgb => some ⟨x, y, z, a⟩
    | .hsl => let (r, g, b) := hslToRgb x (y / 100) (z / 100); some ⟨r, g, b, a⟩
    | .hwb => let (r, g, b) := hwbToRgb x (y / 100) (z / 100); some ⟨r, g, b, a⟩
    | _ => none
  | _, _, _, _ => none

/-- The canonical text of a colour (CSS Color 4 §15). Legacy sRGB, HSL and HWB colours
are `rgb()`/`rgba()`; with a missing component, sRGB is `color(srgb ...)` and HSL and HWB
keep their own function; the others are written in their own syntax. -/
def Color.css (c : Color) : String :=
  let three := fmtOpt c.c1 ++ " " ++ fmtOpt c.c2 ++ " " ++ fmtOpt c.c3 ++ alphaSuffix c.alpha
  match c.space with
  | .rgb =>
    match c.rgba? with
    | some v => legacyCss v.r v.g v.b v.a
    | none => "color(srgb " ++ three ++ ")"
  | .hsl | .hwb =>
    match c.rgba? with
    | some v => legacyCss v.r v.g v.b v.a
    | none => c.space.name ++ "(" ++ fmtOpt c.c1 ++ " " ++ fmtOptPct c.c2 ++ " " ++ fmtOptPct c.c3
        ++ alphaSuffix c.alpha ++ ")"
  | .lab | .lch | .oklab | .oklch => c.space.name ++ "(" ++ three ++ ")"
  | _ => "color(" ++ c.space.name ++ " " ++ three ++ ")"

/-! ### Parsing of the colour functions -/

/-- The arguments of a colour function: the three components, the alpha if given, and
whether the legacy (comma) syntax was used. -/
structure Split where
  comps : List CV
  alpha : Option CV
  legacy : Bool

def splitArgs (args : List CV) : Option Split :=
  match stripWs args with
  | [x, .tok .comma, y, .tok .comma, z] => some ⟨[x, y, z], none, true⟩
  | [x, .tok .comma, y, .tok .comma, z, .tok .comma, w] => some ⟨[x, y, z], some w, true⟩
  | [x, y, z] => some ⟨[x, y, z], none, false⟩
  | [x, y, z, .tok (.delim '/'), w] => some ⟨[x, y, z], some w, false⟩
  | _ => none

/-- The alpha: a number or a percentage, clamped to `[0, 1]`; `none` in the modern syntax
only; 1 when it is not given. -/
def readAlpha (o : Opts) (legacy : Bool) : Option CV → Option (Option Rat)
  | none => some (some 1)
  | some cv =>
    match o.read cv with
    | some (.num v) => some (some (clamp01 v))
    | some (.pct p) => some (some (clamp01 (p / 100)))
    | some Comp.none => if legacy then none else some none
    | _ => none

/-- A component that is a number or a percentage (of `ref`) or `none`. -/
def numOrPct (ref : Rat) (f : Rat → Rat) : Comp → Option (Option Rat)
  | .num v => some (some (f v))
  | .pct p => some (some (f (p * ref / 100)))
  | .none => some none
  | .angle _ => none

/-- A hue: a number or an angle, in degrees modulo 360, or `none`. -/
def hueOf : Comp → Option (Option Rat)
  | .num v => some (some (rmod v 360))
  | .angle d => some (some (rmod d 360))
  | .none => some none
  | .pct _ => none

def clampTo (hi : Rat) (x : Rat) : Rat := if x < 0 then 0 else if hi < x then hi else x

/-- The three components read. -/
def readComps (o : Opts) (sp : Split) : Option (Comp × Comp × Comp) :=
  match sp.comps.map o.read with
  | [some x, some y, some z] => some (x, y, z)
  | _ => none

/-- `rgb()` and `rgba()`: the legacy syntax takes three numbers or three percentages; the
modern one any mix, and `none`. -/
def parseRgb (o : Opts) (args : List CV) : Option Color := do
  let sp ← splitArgs args
  let a ← readAlpha o sp.legacy sp.alpha
  let (x, y, z) ← readComps o sp
  if sp.legacy then
    match x, y, z with
    | .num r, .num g, .num b =>
      some ⟨.rgb, some (clamp01 (r / 255)), some (clamp01 (g / 255)), some (clamp01 (b / 255)), a⟩
    | .pct r, .pct g, .pct b =>
      some ⟨.rgb, some (clamp01 (r / 100)), some (clamp01 (g / 100)), some (clamp01 (b / 100)), a⟩
    | _, _, _ => none
  else
    let r ← numOrPct 255 (fun v => clamp01 (v / 255)) x
    let g ← numOrPct 255 (fun v => clamp01 (v / 255)) y
    let b ← numOrPct 255 (fun v => clamp01 (v / 255)) z
    some ⟨.rgb, r, g, b, a⟩

/-- `hsl()` and `hsla()`: the legacy syntax takes a hue and two percentages. -/
def parseHsl (o : Opts) (args : List CV) : Option Color := do
  let sp ← splitArgs args
  let a ← readAlpha o sp.legacy sp.alpha
  let (x, y, z) ← readComps o sp
  if sp.legacy then
    match x, y, z with
    | .none, _, _ => none
    | _, .pct s, .pct l =>
      let h ← hueOf x
      some ⟨.hsl, h, some (clampPos s), some l, a⟩
    | _, _, _ => none
  else
    let h ← hueOf x
    let s ← numOrPct 100 clampPos y
    let l ← numOrPct 100 id z
    some ⟨.hsl, h, s, l, a⟩

/-- `hwb()`: the modern syntax only. -/
def parseHwb (o : Opts) (args : List CV) : Option Color := do
  let sp ← splitArgs args
  if sp.legacy then none
  let a ← readAlpha o false sp.alpha
  let (x, y, z) ← readComps o sp
  let h ← hueOf x
  let w ← numOrPct 100 id y
  let b ← numOrPct 100 id z
  some ⟨.hwb, h, w, b, a⟩

/-- `lab()` and `oklab()`: lightness clamped to `[0, lMax]`; 100% of `a` or `b` is `abRef`. -/
def parseLab (o : Opts) (space : Space) (lMax abRef : Rat) (args : List CV) : Option Color := do
  let sp ← splitArgs args
  if sp.legacy then none
  let al ← readAlpha o false sp.alpha
  let (x, y, z) ← readComps o sp
  let l ← numOrPct lMax (clampTo lMax) x
  let a ← numOrPct abRef id y
  let b ← numOrPct abRef id z
  some ⟨space, l, a, b, al⟩

/-- `lch()` and `oklch()`: lightness clamped to `[0, lMax]`, chroma to at least 0; 100% of
chroma is `cRef`. -/
def parseLch (o : Opts) (space : Space) (lMax cRef : Rat) (args : List CV) : Option Color := do
  let sp ← splitArgs args
  if sp.legacy then none
  let al ← readAlpha o false sp.alpha
  let (x, y, z) ← readComps o sp
  let l ← numOrPct lMax (clampTo lMax) x
  let c ← numOrPct cRef clampPos y
  let h ← hueOf z
  some ⟨space, l, c, h, al⟩

/-- `color(<space> c1 c2 c3 / alpha)`: numbers as they are, 100% is 1; not clamped. -/
def parseColorFn (o : Opts) (args : List CV) : Option Color :=
  match stripWs args with
  | .tok (.ident s) :: rest => do
    let space ← predefined (lower s)
    let sp ← splitArgs rest
    if sp.legacy then none
    let al ← readAlpha o false sp.alpha
    let (x, y, z) ← readComps o sp
    let c1 ← numOrPct 1 id x
    let c2 ← numOrPct 1 id y
    let c3 ← numOrPct 1 id z
    some ⟨space, c1, c2, c3, al⟩
  | _ => none

/-- The colour of one of the plain colour functions (no nested colour). -/
def parseFn (o : Opts) (n : String) (args : List CV) : Option Color :=
  if n == "rgb" || n == "rgba" then parseRgb o args
  else if n == "hsl" || n == "hsla" then parseHsl o args
  else if n == "hwb" then parseHwb o args
  else if n == "lab" then parseLab o .lab 100 125 args
  else if n == "oklab" then parseLab o .oklab 1 ((2 : Rat) / 5) args
  else if n == "lch" then parseLch o .lch 100 150 args
  else if n == "oklch" then parseLch o .oklch 1 ((2 : Rat) / 5) args
  else if n == "color" then parseColorFn o args
  else none

/-- A hex colour: 3, 4, 6 or 8 hexadecimal digits. -/
def parseHex (s : String) : Option Color :=
  match s.toList.map hexVal with
  | [some r, some g, some b] => some (ofBytes (17 * r) (17 * g) (17 * b))
  | [some r, some g, some b, some a] => some (ofBytes (17 * r) (17 * g) (17 * b) (17 * a))
  | [some r1, some r2, some g1, some g2, some b1, some b2] =>
    some (ofBytes (16 * r1 + r2) (16 * g1 + g2) (16 * b1 + b2))
  | [some r1, some r2, some g1, some g2, some b1, some b2, some a1, some a2] =>
    some (ofBytes (16 * r1 + r2) (16 * g1 + g2) (16 * b1 + b2) (16 * a1 + a2))
  | _ => none

/-- Whether a lower-case identifier is a colour keyword. -/
def isKeyword (k : String) : Bool :=
  k == "transparent" || k == "currentcolor" || (lookup namedColors k).isSome
    || (lookup systemColors k).isSome

/-- The colour of a keyword other than `currentcolor`. -/
def keywordColor (k : String) : Option Color :=
  if k == "transparent" then some (ofBytes 0 0 0 0)
  else match lookup namedColors k with
    | some (r, g, b) => some (ofBytes r g b)
    | none => (lookup systemColors k).map fun (r, g, b) => ofBytes r g b
end L4Factoidal.Rendering.CssValues.Color
