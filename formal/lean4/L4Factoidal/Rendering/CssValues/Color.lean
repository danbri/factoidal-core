/-
L4Factoidal.Rendering.CssValues.Color — the CSS `<color>` type (CSS Color 4 and 5): parsing
of one component value into a colour, and its canonical serialisation (CSSOM §6.7.2,
CSS Color 4 §15), in exact rational arithmetic.

What is covered: named colours, `transparent`, `currentcolor`, system colours, hex
colours, `rgb()`/`rgba()`, `hsl()`/`hsla()`, `hwb()`, `lab()`, `lch()`, `oklab()`,
`oklch()`, `color()` for the predefined spaces, `color-mix()`, relative colours and
`light-dark()` (the last three are kept as functions in the specified value and resolved
in the computed value).

Exact and approximate: parsing, clamping, rounding to 8 bits, the conversions inside the
sRGB family (`rgb`, `hsl`, `hwb`, `color(srgb)`) and interpolation are exact rational
arithmetic. The conversions to and from the other spaces (`lab`, `lch`, `oklab`, `oklch`,
`srgb-linear`, the `xyz` spaces, the wide-gamut RGB spaces) need powers, cube roots and
trigonometric functions: they are rational approximations (see "Conversions between
colour spaces" below), used only by `color-mix()` and relative colours across spaces. No
floating-point type is used.

The reference for the serialised text is Chrome, as recorded in the expectations of the
web-platform-tests under `css/css-color/parsing/`.
-/
import L4Factoidal.Rendering.CssValues.Token
import L4Factoidal.Rendering.CssValues.Approx
import L4Factoidal.Rendering.CssValues.Numeric

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

/-- The hue in degrees of an sRGB colour (0 for a grey). -/
def rgbHue (r g b : Rat) : Rat :=
  let mx := rmax r (rmax g b)
  let mn := rmin r (rmin g b)
  let d := mx - mn
  if d == 0 then 0
  else if mx == r then rmod ((g - b) / d * 60) 360
  else if mx == g then (b - r) / d * 60 + 120
  else (r - g) / d * 60 + 240

/-- CSS Color 4 §7.2: sRGB to HSL (hue in degrees, saturation and lightness as
percentages). A negative saturation (a colour outside the sRGB gamut) is made positive
with the hue turned by 180 degrees. The hue is missing (powerless) when the saturation is
0.001% or less, as in Chrome; Chrome computes in single precision, so the threshold is
taken here with a margin of a thousandth of itself. -/
def rgbToHsl (r g b : Rat) : Option Rat × Rat × Rat :=
  let mx := rmax r (rmax g b)
  let mn := rmin r (rmin g b)
  let l := (mx + mn) / 2
  let m := rmin l (1 - l)
  let s := if m == 0 then 0 else (mx - l) / m
  let h := rgbHue r g b
  let (h, s) := if s < 0 then (rmod (h + 180) 360, -s) else (h, s)
  (if s ≤ (1001 : Rat) / 100000000 then none else some h, s * 100, l * 100)

/-- CSS Color 4 §8.2: sRGB to HWB (hue in degrees, whiteness and blackness as
percentages). The hue is missing (powerless) when whiteness and blackness add up to
99.999% or more, as in Chrome. -/
def rgbToHwb (r g b : Rat) : Option Rat × Rat × Rat :=
  let mx := rmax r (rmax g b)
  let mn := rmin r (rmin g b)
  (if mx - mn ≤ (1 : Rat) / 100000 then none else some (rgbHue r g b), mn * 100, (1 - mx) * 100)

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
modern one any mix, and `none`. `cl` limits a channel of the modern syntax (`clamp01`, or
nothing for a relative colour). -/
def parseRgb (o : Opts) (cl : Rat → Rat) (args : List CV) : Option Color := do
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
    let r ← numOrPct 255 (fun v => cl (v / 255)) x
    let g ← numOrPct 255 (fun v => cl (v / 255)) y
    let b ← numOrPct 255 (fun v => cl (v / 255)) z
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
def parseFn (o : Opts) (n : String) (args : List CV) (cl : Rat → Rat := clamp01) : Option Color :=
  if n == "rgb" || n == "rgba" then parseRgb o cl args
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

/-! ### Conversions between colour spaces (CSS Color 4 §10): rational approximations

The conversions inside the sRGB family (`rgb`, `hsl`, `hwb`, `color(srgb)`) above are exact.
The others need a transfer function (a power), a cube root, or sine, cosine and arctangent:
their values are irrational in general. They are computed here as rational approximations
with series, each step rounded to 18 decimal places; a converted colour is then rounded to
10 decimal places. So a converted component is an approximation (within about 1e-10 of the
real value), never an exact value, and no theorem below speaks about it. The matrices and
constants are those of the sample code of CSS Color 4 §18. -/

abbrev V3 := Rat × Rat × Rat
abbrev M3 := V3 × V3 × V3

def mulV (m : M3) (v : V3) : V3 :=
  let dot (r : V3) : Rat := r.1 * v.1 + r.2.1 * v.2.1 + r.2.2 * v.2.2
  (dot m.1, dot m.2.1, dot m.2.2)

def map3 (f : Rat → Rat) (v : V3) : V3 := (f v.1, f v.2.1, f v.2.2)

def linSrgbToXyz : M3 :=
  (((506752 : Rat) / 1228815, (87881 : Rat) / 245763, (12673 : Rat) / 70218),
   ((87098 : Rat) / 409605, (175762 : Rat) / 245763, (12673 : Rat) / 175545),
   ((7918 : Rat) / 409605, (87881 : Rat) / 737289, (1001167 : Rat) / 1053270))

def xyzToLinSrgb : M3 :=
  (((12831 : Rat) / 3959, (-329 : Rat) / 214, (-1974 : Rat) / 3959),
   ((-851781 : Rat) / 878810, (1648619 : Rat) / 878810, (36519 : Rat) / 878810),
   ((705 : Rat) / 12673, (-2585 : Rat) / 12673, (705 : Rat) / 667))

def linP3ToXyz : M3 :=
  (((608311 : Rat) / 1250200, (189793 : Rat) / 714400, (198249 : Rat) / 1000160),
   ((35783 : Rat) / 156275, (247089 : Rat) / 357200, (198249 : Rat) / 2500400),
   (0, (32229 : Rat) / 714400, (5220557 : Rat) / 5000800))

def xyzToLinP3 : M3 :=
  (((446124 : Rat) / 178915, (-333277 : Rat) / 357830, (-72051 : Rat) / 178915),
   ((-14852 : Rat) / 17905, (63121 : Rat) / 35810, (423 : Rat) / 17905),
   ((11844 : Rat) / 330415, (-50337 : Rat) / 660830, (316169 : Rat) / 330415))

def linProphotoToXyz50 : M3 :=
  ((0.79776664490064230, 0.13518129740053308, 0.03134773412839220),
   (0.28807482881940130, 0.71183523424187300, 0.00008993693872564),
   (0, 0, 0.82510460251046020))

def xyz50ToLinProphoto : M3 :=
  ((1.34578688164715830, -0.25557208737979464, -0.05110186497554526),
   (-0.54463070512490190, 1.50824774284514680, 0.02052744743642139),
   (0, 0, 1.21196754563894520))

def linA98ToXyz : M3 :=
  (((573536 : Rat) / 994567, (263643 : Rat) / 1420810, (187206 : Rat) / 994567),
   ((591459 : Rat) / 1989134, (6239551 : Rat) / 9945670, (374412 : Rat) / 4972835),
   ((53769 : Rat) / 1989134, (351524 : Rat) / 4972835, (4929758 : Rat) / 4972835))

def xyzToLinA98 : M3 :=
  (((1829569 : Rat) / 896150, (-506331 : Rat) / 896150, (-308931 : Rat) / 896150),
   ((-851781 : Rat) / 878810, (1648619 : Rat) / 878810, (36519 : Rat) / 878810),
   ((16779 : Rat) / 1248040, (-147721 : Rat) / 1248040, (1266979 : Rat) / 1248040))

def lin2020ToXyz : M3 :=
  (((63426534 : Rat) / 99577255, (20160776 : Rat) / 139408157, (47086771 : Rat) / 278816314),
   ((26158966 : Rat) / 99577255, (472592308 : Rat) / 697040785, (8267143 : Rat) / 139408157),
   (0, (19567812 : Rat) / 697040785, (295819943 : Rat) / 278816314))

def xyzToLin2020 : M3 :=
  (((30757411 : Rat) / 17917100, (-6372589 : Rat) / 17917100, (-4539589 : Rat) / 17917100),
   ((-19765991 : Rat) / 29648200, (47925759 : Rat) / 29648200, (467509 : Rat) / 29648200),
   ((792561 : Rat) / 44930125, (-1921689 : Rat) / 44930125, (42328811 : Rat) / 44930125))

def d65ToD50 : M3 :=
  ((1.0479297925449969, 0.022946870601609652, -0.05019226628920524),
   (0.02962780877005599, 0.9904344267538799, -0.017073799063418826),
   (-0.009243040646204504, 0.015055191490298152, 0.7518742814281371))

def d50ToD65 : M3 :=
  ((0.955473421488075, -0.02309845494876471, 0.06325924320057072),
   (-0.0283697093338637, 1.0099953980813041, 0.021041441191917323),
   (0.012314014864481998, -0.020507649298898964, 1.330365926242124))

def xyzToLms : M3 :=
  ((0.8190224379967030, 0.3619062600528904, -0.1288737815209879),
   (0.0329836539323885, 0.9292868615863434, 0.0361446663506424),
   (0.0481771893596242, 0.2642395317527308, 0.6335478284694309))

def lmsToOklab : M3 :=
  ((0.2104542683093140, 0.7936177747023054, -0.0040720430116193),
   (1.9779985324311684, -2.4285922420485799, 0.4505937096174110),
   (0.0259040424655478, 0.7827717124575296, -0.8086757549230774))

def lmsToXyz : M3 :=
  ((1.2268798758459243, -0.5578149944602171, 0.2813910456659647),
   (-0.0405757452148008, 1.1122868032803170, -0.0717110580655164),
   (-0.0763729366746601, -0.4214933324022432, 1.5869240198367816))

def oklabToLms : M3 :=
  ((1, 0.3963377773761749, 0.2158037573099136),
   (1, -0.1055613458156586, -0.0638541728258133),
   (1, -0.0894841775298119, -1.2914855480194092))

/-- The D50 white point (CIE chromaticities 0.3457, 0.3585). -/
def whiteD50 : V3 := ((3457 : Rat) / 3585, 1, (2958 : Rat) / 3585)

def linSrgb (v : Rat) : Rat :=
  signed (fun a => if a ≤ (4045 : Rat) / 100000 then a * 100 / 1292
    else powApprox ((a + (55 : Rat) / 1000) * 1000 / 1055) ((12 : Rat) / 5)) v

def gamSrgb (v : Rat) : Rat :=
  signed (fun a => if (31308 : Rat) / 10000000 < a
    then (1055 : Rat) / 1000 * powApprox a ((5 : Rat) / 12) - (55 : Rat) / 1000
    else a * 1292 / 100) v

def linProphoto (v : Rat) : Rat :=
  signed (fun a => if a ≤ (16 : Rat) / 512 then a / 16 else powApprox a ((9 : Rat) / 5)) v

def gamProphoto (v : Rat) : Rat :=
  signed (fun a => if (1 : Rat) / 512 ≤ a then powApprox a ((5 : Rat) / 9) else 16 * a) v

def labToXyz50 (v : V3) : V3 :=
  let κ : Rat := (24389 : Rat) / 27
  let ε : Rat := (216 : Rat) / 24389
  let (l, a, b) := v
  let f1 := (l + 16) / 116
  let f0 := f1 + a / 500
  let f2 := f1 - b / 200
  let x := if ε < f0 * f0 * f0 then f0 * f0 * f0 else (116 * f0 - 16) / κ
  let y := if κ * ε < l then f1 * f1 * f1 else l / κ
  let z := if ε < f2 * f2 * f2 then f2 * f2 * f2 else (116 * f2 - 16) / κ
  (x * whiteD50.1, y * whiteD50.2.1, z * whiteD50.2.2)

def xyz50ToLab (v : V3) : V3 :=
  let κ : Rat := (24389 : Rat) / 27
  let ε : Rat := (216 : Rat) / 24389
  let f (t : Rat) : Rat := if ε < t then cbrtApprox t else (κ * t + 16) / 116
  let f0 := f (v.1 / whiteD50.1)
  let f1 := f (v.2.1 / whiteD50.2.1)
  let f2 := f (v.2.2 / whiteD50.2.2)
  (116 * f1 - 16, 500 * (f0 - f1), 200 * (f1 - f2))

/-- A colour of a rectangular space as XYZ D65 (approximation). -/
def toXyz (s : Space) (v : V3) : V3 :=
  match s with
  | .srgbLinear => mulV linSrgbToXyz v
  | .displayP3 => mulV linP3ToXyz (map3 linSrgb v)
  | .displayP3Linear => mulV linP3ToXyz v
  | .a98Rgb => mulV linA98ToXyz (map3 (signed fun a => powApprox a ((563 : Rat) / 256)) v)
  | .prophotoRgb => mulV d50ToD65 (mulV linProphotoToXyz50 (map3 linProphoto v))
  | .rec2020 => mulV lin2020ToXyz (map3 (signed fun a => powApprox a ((12 : Rat) / 5)) v)
  | .xyzD50 => mulV d50ToD65 v
  | .xyzD65 => v
  | .lab => mulV d50ToD65 (labToXyz50 v)
  | .oklab => mulV lmsToXyz (map3 (fun c => c * c * c) (mulV oklabToLms v))
  | _ => mulV linSrgbToXyz (map3 linSrgb v)

/-- XYZ D65 as a colour of a rectangular space (approximation). -/
def fromXyz (s : Space) (v : V3) : V3 :=
  match s with
  | .srgbLinear => mulV xyzToLinSrgb v
  | .displayP3 => map3 gamSrgb (mulV xyzToLinP3 v)
  | .displayP3Linear => mulV xyzToLinP3 v
  | .a98Rgb => map3 (signed fun a => powApprox a ((256 : Rat) / 563)) (mulV xyzToLinA98 v)
  | .prophotoRgb => map3 gamProphoto (mulV xyz50ToLinProphoto (mulV d65ToD50 v))
  | .rec2020 => map3 (signed fun a => powApprox a ((5 : Rat) / 12)) (mulV xyzToLin2020 v)
  | .xyzD50 => mulV d65ToD50 v
  | .xyzD65 => v
  | .lab => xyz50ToLab (mulV d65ToD50 v)
  | .oklab => mulV lmsToOklab (map3 cbrtApprox (mulV xyzToLms v))
  | _ => map3 gamSrgb (mulV xyzToLinSrgb v)

/-- The rectangular space a space is a form of: `lab` for `lch`, `oklab` for `oklch`,
`srgb` for `rgb`, `hsl` and `hwb`. -/
def rectOf : Space → Space
  | .lch => .lab
  | .oklch => .oklab
  | .rgb | .hsl | .hwb => .srgb
  | s => s

/-- The components of a colour (none missing) in another space; a hue that is powerless
there is missing. Exact inside the sRGB family, an approximation rounded to 10 decimal
places otherwise. -/
def convertV (src dst : Space) (v : V3) : Option Rat × Option Rat × Option Rat :=
  let (c1, c2, c3) := v
  let rect : V3 := match src with
    | .hsl => hslToRgb c1 (c2 / 100) (c3 / 100)
    | .hwb => hwbToRgb c1 (c2 / 100) (c3 / 100)
    | .lch | .oklch => let (s, c) := sinCosDeg c3; (c1, c2 * c, c2 * s)
    | _ => v
  let r := if rectOf src == rectOf dst then rect
    else map3 (roundTo 10) (fromXyz (rectOf dst) (toXyz (rectOf src) rect))
  let polar (eps : Rat) : Option Rat × Option Rat × Option Rat :=
    let (l, a, b) := r
    if src == dst then (some c1, some c2, some c3)
    else
      let ch := roundTo 10 (powApprox (a * a + b * b) ((1 : Rat) / 2))
      (some l, some ch, if ch ≤ eps then none else some (roundTo 10 (atan2Deg b a)))
  match dst with
  | .hsl => let (h, s, l) := rgbToHsl r.1 r.2.1 r.2.2; (h, some s, some l)
  | .hwb => let (h, w, b) := rgbToHwb r.1 r.2.1 r.2.2; (h, some w, some b)
  | .lch => polar ((15 : Rat) / 10000)
  | .oklch => polar ((4 : Rat) / 1000000)
  | _ => (some r.1, some r.2.1, some r.2.2)

/-! ### `color-mix()` (CSS Color 5 §3) -/

inductive HueMethod where
  | shorter | longer | increasing | decreasing
  deriving Repr, DecidableEq

/-- The interpolation method of a `color-mix()`: the canonical name of the space, the hue
method, and whether it was written. -/
structure Method where
  space : String
  hue : HueMethod := .shorter
  given : Bool := true

/-- The canonical name of a space `color-mix()` can interpolate in. -/
def mixSpaceName (s : String) : Option String :=
  if s == "hsl" || s == "hwb" || s == "lab" || s == "lch" || s == "oklab" || s == "oklch" then some s
  else (predefined s).map Space.name

def isPolar (s : String) : Bool := s == "hsl" || s == "hwb" || s == "lch" || s == "oklch"

def hueMethod (s : String) : Option HueMethod :=
  if s == "shorter" then some .shorter
  else if s == "longer" then some .longer
  else if s == "increasing" then some .increasing
  else if s == "decreasing" then some .decreasing
  else none

def HueMethod.text : HueMethod → String
  | .shorter => "" | .longer => " longer hue" | .increasing => " increasing hue"
  | .decreasing => " decreasing hue"

/-- The first argument of a `color-mix()` read as `in <space> [<method> hue]`: `none` when
it starts with `in` and is malformed; `some none` when it is not an interpolation method. -/
def parseMethod (g : List CV) : Option (Option Method) :=
  match stripWs g with
  | .tok (.ident i) :: rest =>
    if lower i != "in" then some none
    else match rest with
      | [.tok (.ident s)] => (mixSpaceName (lower s)).map fun n => some { space := n }
      | [.tok (.ident s), .tok (.ident m), .tok (.ident h)] =>
        if lower h == "hue" && isPolar (lower s) then
          (hueMethod (lower m)).map fun hm => some { space := lower s, hue := hm }
        else none
      | _ => none
  | _ => some none

/-- The values between the top-level commas. -/
def splitCommas (cvs : List CV) : List (List CV) :=
  let (cur, acc) := cvs.foldl (fun (st : List CV × List (List CV)) cv =>
    match cv with
    | .tok .comma => ([], st.1.reverse :: st.2)
    | cv => (cv :: st.1, st.2)) ([], [])
  (cur.reverse :: acc).reverse

/-- One colour of a `color-mix()` with its percentage (before or after it, 0% to 100%). -/
def parseItem (o : Opts) (g : List CV) : Option (CV × Option Rat) :=
  let pct (cv : CV) : Option Rat :=
    match o.read cv with
    | some (.pct p) => if 0 ≤ p && p ≤ 100 then some p else none
    | _ => none
  match stripWs g with
  | [c] => some (c, none)
  | [a, b] =>
    match o.read a with
    | some (.pct _) => (pct a).map fun p => (b, some p)
    | _ => (pct b).map fun p => (a, some p)
  | _ => none

/-- The percentages with the ones left out filled in: they share what is left of 100%. -/
def fillPcts (ps : List (Option Rat)) : List Rat :=
  let given := ps.filterMap id
  let sum := given.foldl (· + ·) 0
  let missing := ps.length - given.length
  let share := if missing == 0 then 0 else clampPos ((100 - sum) / (missing : Rat))
  ps.map (·.getD share)

/-- The method and the colours of a `color-mix()`. -/
def mixParts (o : Opts) (args : List CV) : Option (Method × List (CV × Option Rat)) := do
  let groups := splitCommas args
  let (method, groups) ← (match groups with
    | g :: rest =>
      match parseMethod g with
      | none => none
      | some none => some (({ space := "oklab", given := false } : Method), groups)
      | some (some m) => some (m, rest)
    | [] => none)
  let items ← groups.mapM (parseItem o)
  if items.isEmpty then none
  some (method, items)

/-- The specified value of a `color-mix()`: kept as a function. The default method
(`in oklab`) and the default hue method are left out; percentages are left out when none
was written, when the two are 50%, or when the only one is 100%, and are written for
every colour otherwise. -/
def mixSpec (spec : CV → Option String) (o : Opts) (args : List CV) : Option String := do
  let (method, items) ← mixParts o args
  let texts ← items.mapM fun it => spec it.1
  let ps := items.map (·.2)
  let shown : List (Option Rat) :=
    if ps.all (·.isNone) then ps
    else
      let f := fillPcts ps
      if f == [50, 50] then [none, none] else if f == [100] then [none] else f.map some
  let parts := (texts.zip shown).map fun (t, p) =>
    match p with
    | some p => t ++ " " ++ fmtRat p ++ "%"
    | none => t
  let head :=
    if !method.given || (method.space == "oklab") then ""
    else "in " ++ method.space ++ method.hue.text ++ ", "
  some ("color-mix(" ++ head ++ ", ".intercalate parts ++ ")")

/-- Missing components and alpha taken as 0 and 1. -/
def fill0 (c : Color) : Color :=
  { c with c1 := some (c.c1.getD 0), c2 := some (c.c2.getD 0), c3 := some (c.c3.getD 0),
           alpha := some (c.alpha.getD 1) }

/-- The kind of each component of a space, for carrying missing components over (CSS
Color 4 §12.2, analogous components): 1 red or X, 2 green or Y, 3 blue or Z, 4 hue,
5 colourfulness, 6 lightness, 7 and 8 the opponent axes, 0 no analogue. -/
def kinds : Space → Nat × Nat × Nat
  | .hsl => (4, 5, 6)
  | .hwb => (4, 0, 0)
  | .lab | .oklab => (6, 7, 8)
  | .lch | .oklch => (6, 5, 4)
  | _ => (1, 2, 3)

/-- A colour in the space `target`, with its missing components carried over as Chrome
does: a colour already in that space keeps them; a colour with all three missing keeps all
three missing; a missing component stays missing in the analogous component of the target;
when both components other than the hue of a polar colour are missing, every component
of the target other than the hue is missing; when both opponent axes of a `lab` or `oklab`
colour are missing, the colourfulness and the hue of the target are missing; when chroma
and hue of an `lch` or `oklch` colour are missing, the opponent axes of the target are. A powerless hue of the converted colour is missing. The conversion is exact inside
the sRGB family and an approximation otherwise (see `convertV`). -/
def toMixSpace (target : Space) (c : Color) : Option Color :=
  let polar (s : Space) : Bool := s == .hsl || s == .hwb
  if c.space == target then some c
  else if c.c1.isNone && c.c2.isNone && c.c3.isNone then some ⟨target, none, none, none, c.alpha⟩
  else
    -- A chroma at or below the threshold of CSS Color 4 §10 counts as 0 (a grey).
    let chroma := c.c2.getD 0
    let chroma := if (c.space == .lch && chroma ≤ (15 : Rat) / 10000)
      || (c.space == .oklch && chroma ≤ (4 : Rat) / 1000000) then 0 else chroma
    let (x, y, z) := convertV c.space target (c.c1.getD 0,
      if c.space == .lch || c.space == .oklch then chroma else c.c2.getD 0, c.c3.getD 0)
    let (k1, k2, k3) := kinds c.space
    let missing (k : Nat) : Bool :=
      k != 0 && ((k == k1 && c.c1.isNone) || (k == k2 && c.c2.isNone) || (k == k3 && c.c3.isNone))
    let (t1, t2, t3) := kinds target
    -- A polar colour with both components other than the hue missing.
    let both := (polar c.space && c.c2.isNone && c.c3.isNone)
      || ((c.space == .lch || c.space == .oklch) && c.c1.isNone && c.c2.isNone)
    -- A `lab` or `oklab` colour with both opponent axes missing.
    let noAxes := (c.space == .lab || c.space == .oklab) && c.c2.isNone && c.c3.isNone
    -- An `lch` or `oklch` colour with chroma and hue missing.
    let noChroma := (c.space == .lch || c.space == .oklch) && c.c2.isNone && c.c3.isNone
    let gone (k : Nat) : Bool :=
      missing k || (both && k != 4) || (noAxes && (k == 4 || k == 5))
        || (noChroma && (k == 7 || k == 8))
    some ⟨target, if gone t1 then none else x, if gone t2 then none else y,
      if gone t3 then none else z, c.alpha⟩

/-- CSS Color 4 §12.4: the two hues adjusted for a hue interpolation method. -/
def fixHue (m : HueMethod) (a b : Rat) : Rat × Rat :=
  let d := b - a
  match m with
  | .shorter => if 180 < d then (a + 360, b) else if d < -180 then (a, b + 360) else (a, b)
  | .longer =>
    if 0 < d && d < 180 then (a + 360, b)
    else if -180 < d && d ≤ 0 then (a, b + 360) else (a, b)
  | .increasing => if d < 0 then (a, b + 360) else (a, b)
  | .decreasing => if 0 < d then (a + 360, b) else (a, b)

def fillFrom (a b : Option Rat) : Option Rat :=
  match a with
  | some v => some v
  | none => b

/-- CSS Color 4 §12: two colours of the same space interpolated with weights `p` and `q`
(`p + q = 1`): a component missing in one is taken from the other; the components other
than the hue are premultiplied by alpha (and are 0 when the resulting alpha is 0). -/
def mixPair (hm : HueMethod) (x y : Color) (p q : Rat) : Color :=
  let hueIdx : Nat := match x.space with
    | .hsl | .hwb => 1
    | .lch | .oklch => 3
    | _ => 0
  let ax := fillFrom x.alpha y.alpha
  let ay := fillFrom y.alpha x.alpha
  let pa := ax.getD 1
  let qa := ay.getD 1
  let alpha := pa * p + qa * q
  let lin (i : Nat) (u v : Option Rat) : Option Rat :=
    match fillFrom u v, fillFrom v u with
    | some u, some v =>
      if i == hueIdx then
        let (u, v) := fixHue hm u v
        some (rmod (u * p + v * q) 360)
      else if alpha == 0 then some 0
      else some ((u * pa * p + v * qa * q) / alpha)
    | _, _ => none
  ⟨x.space, lin 1 x.c1 y.c1, lin 2 x.c2 y.c2, lin 3 x.c3 y.c3,
    match ax, ay with
    | some _, some _ => some alpha
    | _, _ => none⟩

/-- The colours mixed one after the other, each with its share of the weight so far (in
equal shares while the weight so far is 0). -/
def mixFold (hm : HueMethod) : Color → Rat → List (Color × Rat) → Color
  | acc, _, [] => acc
  | acc, w, (c, wc) :: rest =>
    let tot := w + wc
    let acc' := if tot == 0 then mixPair hm acc c ((1 : Rat) / 2) ((1 : Rat) / 2)
      else mixPair hm acc c (w / tot) (wc / tot)
    mixFold hm acc' tot rest

/-- A result of interpolation in `hsl` or `hwb` as `color(srgb ...)`; with a missing
component or alpha it stays as it is. -/
def polarToSrgb (c : Color) : Color :=
  match c.space with
  | .hsl | .hwb =>
    match c.rgba? with
    | some v => ⟨.srgb, some v.r, some v.g, some v.b, c.alpha⟩
    | none => c
  | _ => c

/-- The space a colour function makes. -/
def fnSpace (n : String) : Option Space :=
  if n == "rgb" || n == "rgba" then some .rgb
  else if n == "hsl" || n == "hsla" then some .hsl
  else if n == "hwb" then some .hwb
  else if n == "lab" then some .lab
  else if n == "lch" then some .lch
  else if n == "oklab" then some .oklab
  else if n == "oklch" then some .oklch
  else none

/-- The computed value of a `color-mix()` (CSS Color 5 §3.1): every colour is converted to
the interpolation space (`toMixSpace`); percentages are normalised to add up to 100%; when
they add up to less, alpha is scaled by the sum. A result in `hsl` or `hwb` is given as
`color(srgb ...)`. `none` when a colour cannot be resolved. -/
def mixResolve (res : CV → Option Color) (o : Opts) (args : List CV) : Option Color := do
  let (method, items) ← mixParts o args
  let space ← (match fnSpace method.space with
    | some s => some s
    | none => predefined method.space)
  let cols ← items.mapM fun it => (res it.1).bind (toMixSpace space)
  let ps := fillPcts (items.map (·.2))
  let sum := ps.foldl (· + ·) 0
  let ws := ps.map fun p => if sum == 0 then 0 else p / sum
  let mult : Rat := if sum < 100 then sum / 100 else 1
  match cols.zip ws with
  | [] => none
  | (c, w) :: rest =>
    let m := mixFold method.hue c w rest
    some (polarToSrgb { m with alpha := m.alpha.map (· * mult) })

/-! ### Relative colours (CSS Color 5 §4) -/

/-- The channel keywords of a relative colour in a space. -/
def channelNames : Space → List String
  | .hsl => ["h", "s", "l"]
  | .hwb => ["h", "w", "b"]
  | .lab | .oklab => ["l", "a", "b"]
  | .lch | .oklch => ["l", "c", "h"]
  | .xyzD50 | .xyzD65 => ["x", "y", "z"]
  | _ => ["r", "g", "b"]

/-- The parts of a relative colour. -/
structure Rel where
  origin : CV
  space : Space
  comps : List CV
  alpha : Option CV

/-- `fn(from <color> c1 c2 c3 [/ alpha])` and `color(from <color> <space> c1 c2 c3 [/ alpha])`. -/
def relParts (n : String) (args : List CV) : Option Rel :=
  match stripWs args with
  | .tok (.ident f) :: origin :: rest =>
    if lower f != "from" then none
    else do
      let (space, rest) ← (if n == "color" then
          match rest with
          | .tok (.ident s) :: r => (predefined (lower s)).map fun sp => (sp, r)
          | _ => none
        else (fnSpace n).map fun sp => (sp, rest))
      match rest with
      | [x, y, z] => some ⟨origin, space, [x, y, z], none⟩
      | [x, y, z, .tok (.delim '/'), w] => some ⟨origin, space, [x, y, z], some w⟩
      | _ => none
  | _ => none

/-- Channel keywords replaced by their numbers, also inside functions (`calc()`). -/
def substF : Nat → (String → Option Rat) → CV → CV
  | 0, _, cv => cv
  | fuel + 1, env, cv =>
    match cv with
    | .tok (.ident k) =>
      match env (lower k) with
      | some v => .tok (.num v false)
      | none => cv
    | .fn n args => .fn n (args.map (substF fuel env))
    | .block c body => .block c (body.map (substF fuel env))
    | cv => cv

/-- The text of one component of a relative colour in the specified value: a channel
keyword or `none` in lower case, a number, percentage or angle, or a function as written. -/
def relCompText (o : Opts) (names : List String) (hue : Bool) (cv : CV) : Option String :=
  -- the type a component may have (CSS Color 5 §4.1): an angle only for a hue, a
  -- percentage for the other components; the channel keywords are numbers, so a `calc()`
  -- that adds a percentage or an angle to one is not a component
  let typed := fun (c : Comp) => match c with
    | .angle _ => hue
    | .pct _ => !hue
    | _ => true
  match cv with
  | .tok (.ident k) =>
    let k := lower k
    if k == "none" || k == "alpha" || names.contains k then some k else none
  | .tok _ => (o.read cv).bind fun c => if typed c then some (serialize [cv]) else none
  | .fn _ _ =>
    let zero := fun (k : String) => if k == "alpha" || names.contains k then some (0 : Rat) else none
    let cv' := substF 32 zero cv
    let ok := (numeric (some {}) { kind := .number } cv').isSome ||
      (!hue && (numeric (some {}) { kind := .percent } cv').isSome) ||
      (hue && (numeric (some {}) { kind := .angle } cv').isSome)
    if ok then some (serialize [cv]) else none
  | _ => none

/-- The position of the hue among the components of a space (`hsl`, `hwb`: first; `lch`,
`oklch`: third). -/
def hueIndex : Space → Option Nat
  | .hsl | .hwb => some 0
  | .lch | .oklch => some 2
  | _ => none

/-- The specified value of a relative colour: kept as a function, the origin colour in its
own specified form. -/
def relSpec (spec : CV → Option String) (o : Opts) (n : String) (r : Rel) : Option String := do
  let origin ← spec r.origin
  let names := channelNames r.space
  let comps ← (r.comps.zipIdx).mapM fun (c, i) => relCompText o names (hueIndex r.space == some i) c
  let alpha ← (match r.alpha with
    | some a => (relCompText o names false a).map fun t => " / " ++ t
    | none => some "")
  let head := if n == "color" then "color(from " ++ origin ++ " " ++ r.space.name
    else r.space.name ++ "(from " ++ origin
  some (head ++ " " ++ " ".intercalate comps ++ alpha ++ ")")

/-- The origin colour in the target space, as the channel keywords see it (`rgb` channels
are 0 to 255). -/
def originChannels (target : Space) (c : Color) : Option Color :=
  if target == .rgb then
    (toMixSpace .srgb c).map fun s =>
      { s with c1 := s.c1.map (· * 255), c2 := s.c2.map (· * 255), c3 := s.c3.map (· * 255) }
  else toMixSpace target c

/-- The computed value of a relative colour whose origin is already resolved: the channel
keywords are replaced by the origin's channels and the function is read as usual, without
clamping of `rgb` channels. A keyword that stands alone for a missing channel gives `none`;
inside a function a missing channel is 0. The result is not a legacy colour: `rgb`, `hsl`
and `hwb` give `color(srgb ...)`. -/
def relResolve (o : Opts) (n : String) (r : Rel) (origin : Color) : Option Color := do
  let oc ← originChannels r.space origin
  let names := channelNames r.space
  let chan (k : String) : Option (Option Rat) :=
    if k == "alpha" then some oc.alpha
    else match names with
      | [n1, n2, n3] =>
        if k == n1 then some oc.c1 else if k == n2 then some oc.c2
        else if k == n3 then some oc.c3 else none
      | _ => none
  let env (k : String) : Option Rat := (chan k).map (·.getD 0)
  let sub (cv : CV) : CV :=
    match cv with
    | .tok (.ident k) =>
      match chan (lower k) with
      | some none => .tok (.ident "none")
      | _ => substF 16 env cv
    | cv => substF 16 env cv
  let sep : List CV := [.tok .ws]
  let comps := (r.comps.map sub).foldr (fun cv acc => cv :: sep ++ acc) []
  let alphaCv : CV := match r.alpha with
    | some w => sub w
    | none => match oc.alpha with
      | some a => .tok (.num a false)
      | none => .tok (.ident "none")
  let args := (if n == "color" then [CV.tok (.ident r.space.name), .tok .ws] else [])
    ++ comps ++ [.tok (.delim '/'), .tok .ws, alphaCv]
  let c ← parseFn o n args id
  match c.space with
  | .rgb => some { c with space := .srgb }
  | _ => some (polarToSrgb c)

/-! ### The colour of a component value -/

/-- The two colours of `light-dark(a, b)`. -/
def lightDarkParts (args : List CV) : Option (CV × CV) :=
  match (splitCommas args).map stripWs with
  | [[a], [b]] => some (a, b)
  | _ => none

/-- The specified value: keywords in lower case, colour functions in canonical form,
`color-mix()`, relative colours and `light-dark()` kept as functions. -/
def specF : Nat → Opts → CV → Option String
  | 0, _, _ => none
  | fuel + 1, o, cv =>
    match cv with
    | .tok (.ident s) =>
      let k := lower s
      if isKeyword k then some k else none
    | .tok (.hash s _) => (parseHex s).map Color.css
    | .fn name args =>
      let n := lower name
      if n == "color-mix" then mixSpec (specF fuel o) o args
      else if n == "light-dark" then
        match lightDarkParts args with
        | some (a, b) => do
          let ta ← specF fuel o a
          let tb ← specF fuel o b
          some ("light-dark(" ++ ta ++ ", " ++ tb ++ ")")
        | none => none
      else match relParts n args with
        | some r => relSpec (specF fuel o) o n r
        | none => (parseFn o n args).map Color.css
    | _ => none

/-- The colour a component value resolves to, when it can be resolved here. -/
def resolveF : Nat → Opts → CV → Option Color
  | 0, _, _ => none
  | fuel + 1, o, cv =>
    match cv with
    | .tok (.ident s) =>
      let k := lower s
      if k == "currentcolor" then
        match o.current.map fun t => trimWs (CV.parse t) with
        | some [c] => resolveF fuel { o with current := none } c
        | _ => none
      else keywordColor k
    | .tok (.hash s _) => parseHex s
    | .fn name args =>
      let n := lower name
      if n == "color-mix" then mixResolve (resolveF fuel o) o args
      else if n == "light-dark" then
        match lightDarkParts args with
        | some (a, b) => resolveF fuel o (if o.dark then b else a)
        | none => none
      else match relParts n args with
        | some r => (resolveF fuel o r.origin).bind (relResolve o n r)
        | none => parseFn o n args
    | _ => none

/-- The colour that component value `cv` is: `none` for an invalid colour, and for a
colour that depends on `currentcolor` when `o.current` is not given. System colours have
their light-scheme values; `light-dark()` follows `o.dark`. -/
def resolve (o : Opts) (cv : CV) : Option Color := resolveF 32 o cv

/-- The canonical text of the colour that component value `cv` is (one component value: an
ident, a hash token or a function), or `none` when it is not a valid `<color>`. In the
computed form a colour that cannot be resolved (it depends on `currentcolor` and
`o.current` is not given) keeps its specified text. -/
def parse (o : Opts) (cv : CV) : Option String :=
  match specF 32 o cv with
  | none => none
  | some spec =>
    if o.computed then
      match cv with
      | .tok (.ident s) =>
        if lower s == "currentcolor" then some (o.current.getD "currentcolor")
        else ((resolve o cv).map Color.css).getD spec
      | _ => ((resolve o cv).map Color.css).getD spec
    else some spec

/-! ### Tests

Each `#guard` is a test (one input, one expected text), not a proof. The expected texts are
those of the web-platform-tests named in the comments. -/

/-- The specified value of a colour text (test helper). -/
def specOf (s : String) : Option String :=
  match trimWs (CV.parse s) with
  | [cv] => parse {} cv
  | _ => none

/-- The computed value of a colour text where `currentcolor` is `rgb(255, 0, 0)` (test
helper). -/
def computedOf (s : String) : Option String :=
  match trimWs (CV.parse s) with
  | [cv] => parse { computed := true, current := some "rgb(255, 0, 0)" } cv
  | _ => none

-- css/css-color/parsing/color-valid.html, color-computed.html, color-invalid.html
#guard specOf "currentcolor" == some "currentcolor"
#guard specOf "transparent" == some "transparent"
#guard specOf "#234" == some "rgb(34, 51, 68)"
#guard specOf "#FEDCBA" == some "rgb(254, 220, 186)"
#guard specOf "rgba(2, 3, 4, 50%)" == some "rgba(2, 3, 4, 0.5)"
#guard specOf "hsla(120, 100%, 50%, 0.25)" == some "rgba(0, 255, 0, 0.25)"
#guard specOf "rgb(20, 10, 0, -10)" == some "rgba(20, 10, 0, 0)"
#guard specOf "rgb(100%, 200%, 300%)" == some "rgb(255, 255, 255)"
#guard specOf "light-dark(black, white)" == some "light-dark(black, white)"
#guard computedOf "currentcolor" == some "rgb(255, 0, 0)"
#guard computedOf "transparent" == some "rgba(0, 0, 0, 0)"
#guard computedOf "magenta" == some "rgb(255, 0, 255)"
#guard specOf "auto" == none
#guard specOf "rgb(10%, 20, 30%)" == none
#guard specOf "rgb(1,2,3,4,5)" == none
-- color-computed-named-color.html, color-invalid-named-color.html, color-valid-system-color.html
#guard computedOf "TransParent" == some "rgba(0, 0, 0, 0)"
#guard computedOf "rebeccapurple" == some "rgb(102, 51, 153)"
#guard specOf "blac\u212A" == none
#guard specOf "AccentColorText" == some "accentcolortext"
#guard computedOf "LinkText" == some "rgb(0, 0, 238)"
-- color-computed-hex-color.html, color-invalid-hex-color.html, css/CSS2/syntax/colors-007.html
#guard computedOf "#ffffffff" == some "rgb(255, 255, 255)"
#guard computedOf "#FFCc99" == some "rgb(255, 204, 153)"
#guard specOf "#1000" == some "rgba(17, 0, 0, 0)"
#guard specOf "#fffff" == none
#guard specOf "#ffg" == none
-- color-valid-rgb.html, color-computed-rgb.html, color-invalid-rgb.html
#guard specOf "rgb(128 none none)" == some "color(srgb 0.501961 none none)"
#guard specOf "rgb(none none none / 50%)" == some "color(srgb none none none / 0.5)"
#guard specOf "rgba(-20% 20% 40% / 50%)" == some "rgba(0, 51, 102, 0.5)"
#guard specOf "rgb(250% 51 40%)" == some "rgb(255, 51, 102)"
#guard computedOf "rgb(42%, 3%, 50%)" == some "rgb(107, 8, 128)"
#guard computedOf "rgba(0, 51, 255, 0.42)" == some "rgba(0, 51, 255, 0.42)"
#guard computedOf "rgb(2.5, 3.4, 4.6)" == some "rgb(3, 3, 5)"
#guard specOf "rgb(none, none, none)" == none
#guard specOf "rgb(0, 0 0)" == none
#guard specOf "rgb(257, 0, 5 / 0)" == none
-- color-computed-hsl.html, color-valid-hsl.html, color-invalid-hsl.html
#guard computedOf "hsl(120 30% 50% / 0.5)" == some "rgba(89, 166, 89, 0.5)"
#guard computedOf "hsl(-300, 100%, 37.5%)" == some "rgb(191, 191, 0)"
#guard computedOf "hsla(0, 12.5%, 12.5%, 0)" == some "rgba(36, 28, 28, 0)"
#guard computedOf "hsl(30deg, 100%, 100%)" == some "rgb(255, 255, 255)"
#guard specOf "hsl(120 30 none / 0.5)" == some "hsl(120 30% none / 0.5)"
#guard specOf "hsl(30 -50 60)" == some "rgb(153, 153, 153)"
#guard specOf "hsl(0, 50, 30%)" == none
#guard specOf "hsl(none, 100%, 50%)" == none
-- color-computed-hwb.html, color-valid-hwb.html, color-invalid-hwb.html
#guard specOf "hwb(320deg 30% 40%)" == some "rgb(153, 77, 128)"
#guard computedOf "hwb(0 70% 60%)" == some "rgb(137, 137, 137)"
#guard computedOf "hwb(120 none 50%)" == some "hwb(120 none 50%)"
#guard specOf "hwb(90deg, 50%, 50%)" == none
-- color-valid-lab.html, color-invalid-lab.html
#guard specOf "lab(400 0 10/50%)" == some "lab(100 0 10 / 0.5)"
#guard specOf "lab(50% 50% -20%)" == some "lab(50 62.5 -25)"
#guard specOf "oklab(20% 70% -80%/0.5)" == some "oklab(0.2 0.28 -0.32 / 0.5)"
#guard specOf "lch(10 20 1.28rad)" == some "lch(10 20 73.3386)"
#guard specOf "oklch(0.5 -20% -20)" == some "oklch(0.5 0 340)"
#guard specOf "lab(0% 0 0 1)" == none
-- color-valid-color-function.html, color-invalid-color-function.html
#guard specOf "color(xyz 20% 0 10/50%)" == some "color(xyz-d65 0.2 0 10 / 0.5)"
#guard specOf "color(display-p3 -200 -200 -200 / -200)" == some "color(display-p3 -200 -200 -200 / 0)"
#guard specOf "color(srgb 10% none none / none)" == some "color(srgb 0.1 none none / none)"
#guard specOf "color(srgb 0, 0, 0)" == none
#guard specOf "color(displayp3 1 1 1)" == none
-- color-valid-color-mix-function.html, color-computed-color-mix-function.html,
-- color-invalid-color-mix-function.html
#guard specOf "color-mix(in srgb, 70% red, 50% blue)" == some "color-mix(in srgb, red 70%, blue 50%)"
#guard specOf "color-mix(in hsl, red 50%, blue)" == some "color-mix(in hsl, red, blue)"
#guard specOf "color-mix(in lch decreasing hue, red, hsl(120, 100%, 50%))"
  == some "color-mix(in lch decreasing hue, red, rgb(0, 255, 0))"
#guard specOf "color-mix(in srgb, red 60%, green, blue 40%)"
  == some "color-mix(in srgb, red 60%, green 0%, blue 40%)"
#guard computedOf "color-mix(in hsl, hsl(120deg 10% 20%), hsl(30deg 30% 40%))"
  == some "color(srgb 0.33 0.36 0.24)"
#guard computedOf "color-mix(in hsl longer hue, hsl(40deg 50% 50%), hsl(60deg 50% 50%))"
  == some "color(srgb 0.25 0.333333 0.75)"
#guard computedOf "color-mix(in hwb, transparent, hwb(30deg 30% 40%))"
  == some "color(srgb 0.6 0.45 0.3 / 0.5)"
#guard computedOf "color-mix(in srgb, red 10%, blue)" == some "color(srgb 0.1 0 0.9)"
#guard computedOf "color-mix(in srgb, red 0%, green 0%, blue 50%)" == some "color(srgb 0 0 1 / 0.5)"
#guard specOf "color-mix(in hsl, hsl(120deg 10% 20%) 150%, hsl(30deg 30% 40%))" == none
#guard specOf "color-mix(in lab longer hue, lab(10 20 30), lab(50 60 70))" == none
-- color-invalid-relative-color.html: a component of the wrong type
#guard specOf "rgb(from rebeccapurple r 10deg 10)" == none
#guard specOf "rgb(from rebeccapurple calc(r + 1%) g b)" == none
#guard specOf "hsl(from rebeccapurple 10% s l)" == none
#guard specOf "lch(from lch(.70 45 30) l c calc(h + 1deg))" == none
#guard specOf "color(from color(srgb 0.7 0.5 0.3) srgb r g b / 10deg)" == none
#guard (specOf "hsl(from rebeccapurple calc(h + 1) s l)").isSome && (specOf "lch(from lch(.70 45 30) l c 10deg)").isSome
#guard (specOf "rgb(from rebeccapurple calc(r * 0.5) 10% g)").isSome
-- color-valid-relative-color.html, color-computed-relative-color.html, color-computed-none.html
#guard specOf "rgba(from rgb(20%, 40%, 60%, 80%) r g b / 0)"
  == some "rgb(from rgba(51, 102, 153, 0.8) r g b / 0)"
#guard computedOf "rgb(from rebeccapurple r g b)" == some "color(srgb 0.4 0.2 0.6)"
#guard computedOf "hwb(from rebeccapurple 0 w b / alpha)" == some "color(srgb 0.6 0.2 0.2)"
#guard computedOf "hwb(from hwb(120deg 20% 50% / .5) h w none / alpha)"
  == some "hwb(120 20% none / 0.5)"
#guard computedOf "lab(from lab(25 20 50) l a a / a)" == some "lab(25 20 20)"
#guard computedOf "hsl(from hwb(none 25% 25%) h s l)" == some "hsl(none 50% 50%)"
#guard computedOf "light-dark(rgb(from rebeccapurple r g b), rgb(from rebeccapurple r g b))"
  == some "color(srgb 0.4 0.2 0.6)"
-- color-computed-color-mix-function.html, color-computed-relative-color.html,
-- color-computed-none.html: conversions outside the sRGB family (approximations; the
-- tests compare numbers within 0.01, the texts here are this module's own digits)
#guard computedOf "color-mix(in hsl, lch(100% 0 0), blue)" == some "color(srgb 0.625 0.625 0.875)"
#guard computedOf "color-mix(in oklch, oklab(0.5 none 0.1))" == some "oklch(0.5 0.1 90)"
#guard computedOf "lch(from hsl(0 0 0) l c h)" == some "lch(0 0 none)"
#guard computedOf "color(from color(srgb-linear 0.25 0.5 0.75) srgb r g b)"
  == some "color(srgb 0.537099 0.735357 0.880825)"
#guard computedOf "oklch(from color(srgb 0.25 0.5 0.75) l c h)"
  == some "oklch(0.58555 0.118266 250.532)"

/-! ### Theorems -/

/-- Kind: range. Says: `clamp01` always lands in `[0, 1]`. Does not say: anything about
rounding to 8 bits (see `byteOf_le`). -/
theorem clamp01_range (x : Rat) : 0 ≤ clamp01 x ∧ clamp01 x ≤ 1 := by
  unfold clamp01
  split
  · decide
  · split
    · decide
    · rename_i h0 h1
      exact ⟨Rat.not_lt.mp h0, Rat.not_lt.mp h1⟩

/-- Kind: structure. Says: clamping to `[0, 1]` twice is the same as clamping once. Does
not say: that clamping commutes with any conversion between colour spaces. -/
theorem clamp01_idem (x : Rat) : clamp01 (clamp01 x) = clamp01 x := by
  have h := clamp01_range x
  generalize clamp01 x = y at h
  unfold clamp01
  rw [if_neg (Rat.not_lt.mpr h.1), if_neg (Rat.not_lt.mpr h.2)]

/-- Kind: range. Says: the 8-bit value of any channel or alpha is at most 255. Does not
say: which of two neighbouring bytes a value near a half is rounded to (the `#guard`s on
`rgb(42%, 3%, 50%)` and `hwb(320deg 30% 40%)` test halves going up). -/
theorem byteOf_le (x : Rat) : byteOf x ≤ 255 := Nat.min_le_left _ _

/-- Kind: functional. Says: with saturation 0 every channel of the HSL conversion is the
lightness, for any hue. Does not say: anything about saturations near 0. -/
theorem hslChan_grey (h l n : Rat) : hslChan h 0 l n = l := by
  simp [hslChan, Rat.zero_mul, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]

/-- Kind: functional. Says: an HSL colour of saturation 0 is the grey `r = g = b = l`.
Does not say: that the result is in `[0, 1]` (the lightness is not clamped here). -/
theorem hslToRgb_grey (h l : Rat) : hslToRgb h 0 l = (l, l, l) := by
  simp [hslToRgb, hslChan_grey]

/-- Kind: functional. Says: when whiteness and blackness add up to 1 or more, the HWB
conversion is the grey `w / (w + b)` in all three channels, for any hue. Does not say:
anything for `w + b < 1`. -/
theorem hwbToRgb_grey (h w b : Rat) (hwb : 1 ≤ w + b) :
    hwbToRgb h w b = (w / (w + b), w / (w + b), w / (w + b)) := by
  simp [hwbToRgb, hwb]

set_option maxRecDepth 100000 in
/-- Kind: table. Says: the table of named colours has the 148 names of CSS Color 4 §6.1
and every channel in it is an 8-bit value. Does not say: that the values are the right
ones (the 455 subtests of `color-computed-named-color.html` test that, outside the build). -/
theorem namedColors_bytes :
    namedColors.length = 148
      ∧ namedColors.all (fun e => e.2.1 < 256 && e.2.2.1 < 256 && e.2.2.2 < 256) = true := by
  decide

/-- The hexadecimal digit (lower case) of a value below 16. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Kind: round trip. Says: the hexadecimal digit of every value below 16 reads back as
that value. Does not say: anything about upper-case digits (the `#guard` on `#FEDCBA`
tests those). -/
theorem hexVal_hexDigit : ∀ n : Fin 16, hexVal (hexDigit n.val) = some n.val := by
  decide

set_option maxRecDepth 100000 in
/-- Kind: round trip. Says: the two hexadecimal digits of every byte read back as the
byte. Does not say: that `parseHex` is applied to them (see `parseHex_bytes`). -/
theorem hexPair_roundtrip : ∀ b : Fin 256,
    (hexVal (hexDigit (b.val / 16))).bind (fun hi =>
      (hexVal (hexDigit (b.val % 16))).map (fun lo => 16 * hi + lo)) = some b.val := by
  decide

set_option maxRecDepth 100000 in
/-- Kind: round trip. Says: for every byte, the channel `b / 255` has the 8-bit value `b`:
a legacy colour made of bytes is serialised with the same bytes. Does not say: that the
text `rgb(r, g, b)` is parsed back by `parse` (the `#guard`s test that on examples). -/
theorem byteOf_ofByte : ∀ b : Fin 256, byteOf ((b.val : Rat) / 255) = b.val := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Kind: range. Says: for every byte `b`, the channel `b / 255` is not changed by
clamping. Does not say: anything about channels that are not a byte over 255. -/
theorem clamp01_byte : ∀ b : Fin 256, clamp01 ((b.val : Rat) / 255) = (b.val : Rat) / 255 := by
  decide +kernel

/-- Kind: round trip. Says: the component values of the canonical text `rgb(r, g, b)` of
an opaque 8-bit colour are read by `parseRgb` (with the literal reader) as that same
colour, for all bytes `r`, `g`, `b`; with `byteOf_ofByte` its text is then the same again.
Does not say: that the tokenizer makes exactly these component values from the text (the
`#guard`s test the path through the tokenizer on examples), nor anything about colours
with alpha below 1. -/
theorem parseRgb_bytes (r g b : Fin 256) :
    parseRgb {} clamp01 [.tok (.num (r.val : Rat) true), .tok .comma, .tok .ws,
      .tok (.num (g.val : Rat) true), .tok .comma, .tok .ws, .tok (.num (b.val : Rat) true)]
      = some (ofBytes r.val g.val b.val) := by
  simp [parseRgb, splitArgs, stripWs, CV.isWs, readAlpha, readComps, literalReader, ofBytes,
    clamp01_byte]
  decide +kernel

/-- Kind: round trip. Says: the six hexadecimal digits of three bytes are read by
`parseHex` as the opaque legacy colour of those bytes, for all bytes. Does not say:
anything about the 3-, 4- and 8-digit forms or upper-case digits (tested by `#guard`s). -/
theorem parseHex_bytes (r g b : Fin 256) :
    parseHex (String.ofList [hexDigit (r.val / 16), hexDigit (r.val % 16), hexDigit (g.val / 16),
      hexDigit (g.val % 16), hexDigit (b.val / 16), hexDigit (b.val % 16)])
      = some (ofBytes r.val g.val b.val) := by
  have d (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := hexVal_hexDigit ⟨n, h⟩
  have e (n : Nat) : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
  simp [parseHex, d _ (by omega : r.val / 16 < 16), d _ (by omega : r.val % 16 < 16),
    d _ (by omega : g.val / 16 < 16), d _ (by omega : g.val % 16 < 16),
    d _ (by omega : b.val / 16 < 16), d _ (by omega : b.val % 16 < 16), e]

/-- Kind: range. Says: for two hues in `[0, 360)`, the `shorter` fix-up leaves them at
most 180 degrees apart. Does not say: that the interpolated hue is in `[0, 360)` (`mixPair`
reduces it modulo 360 afterwards). -/
theorem fixHue_shorter (a b : Rat) (ha : 0 ≤ a) (ha' : a < 360) (hb : 0 ≤ b) (hb' : b < 360) :
    (fixHue .shorter a b).2 - (fixHue .shorter a b).1 ≤ 180
      ∧ -180 ≤ (fixHue .shorter a b).2 - (fixHue .shorter a b).1 := by
  simp only [fixHue]
  split <;> (try split) <;> grind

/-- Kind: range. Says: for two hues in `[0, 360)`, the `increasing` fix-up makes the second
hue at least the first and less than a full turn above it. Does not say: anything about
hues outside `[0, 360)`. -/
theorem fixHue_increasing (a b : Rat) (ha : 0 ≤ a) (ha' : a < 360) (hb : 0 ≤ b) (hb' : b < 360) :
    0 ≤ (fixHue .increasing a b).2 - (fixHue .increasing a b).1
      ∧ (fixHue .increasing a b).2 - (fixHue .increasing a b).1 < 360 := by
  simp only [fixHue]
  split <;> grind

/-- Kind: range. Says: for two hues in `[0, 360)`, the `decreasing` fix-up makes the second
hue at most the first and less than a full turn below it. Does not say: anything about
hues outside `[0, 360)`. -/
theorem fixHue_decreasing (a b : Rat) (ha : 0 ≤ a) (ha' : a < 360) (hb : 0 ≤ b) (hb' : b < 360) :
    (fixHue .decreasing a b).2 - (fixHue .decreasing a b).1 ≤ 0
      ∧ -360 < (fixHue .decreasing a b).2 - (fixHue .decreasing a b).1 := by
  simp only [fixHue]
  split <;> grind

/-- Kind: functional. Says: in a `color-mix()` of two colours where only the first
percentage `p ≤ 100%` is written, the second is `100% - p`. Does not say: anything about
more than two colours or about percentages that add up to more or less than 100%. -/
theorem fillPcts_one (p : Rat) (h : p ≤ 100) : fillPcts [some p, none] = [p, 100 - p] := by
  simp [fillPcts, clampPos]
  grind

/-- Kind: functional. Says: the alpha of two interpolated colours that both have an alpha
is the weighted sum of the two alphas. Does not say: anything about the other components
(they are premultiplied) or about a missing alpha. -/
theorem mixPair_alpha (hm : HueMethod) (x y : Color) (p q a b : Rat)
    (hx : x.alpha = some a) (hy : y.alpha = some b) :
    (mixPair hm x y p q).alpha = some (a * p + b * q) := by
  simp [mixPair, fillFrom, hx, hy]

end L4Factoidal.Rendering.CssValues.Color
