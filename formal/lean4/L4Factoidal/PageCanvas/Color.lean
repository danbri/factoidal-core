/-
L4Factoidal.PageCanvas.Color: CSS colours for Canvas 2D (`fillStyle`, `strokeStyle`,
`shadowColor`, `addColorStop`), parsed and serialised by Lean
(record: docs/designissues/2026-11-08-canvas-2d.md).

CSS Color 4: the named colours and `transparent` (§6.1), hex notation (§5.2), `rgb()` and
`rgba()` (§5.1, legacy and modern syntax), `hsl()` and `hsla()` (§7), `hwb()` (§8).
`currentcolor` is black, as for a canvas that is not in a document (HTML §4.12.5.1.1:
the computed colour of the canvas element is not known to the context in this engine).
Serialisation is HTML §4.12.5.1.5 "serialization of a color": `#rrggbb` when opaque,
otherwise `rgba(r, g, b, a)` with the alpha as CSS Color 4 §15.2 says (two decimals when
they give back the same 8-bit alpha, else three).
-/
namespace L4Factoidal.PageCanvas

/-- A natural number as a Float, through the machine conversion (`Nat.toFloat` goes
through `OfScientific`, which is slow in a pixel loop). Exact below 2^53. -/
@[inline] def nf (n : Nat) : Float := n.toUInt64.toFloat

/-- `n` zero Floats, pushed (an `Array.replicate` of Floats boxes each one first). -/
def fzeros (n : Nat) : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity n
  for _ in [0:n] do a := a.push 0
  return a

/-- `n` zero bytes, pushed. -/
def bzeros (n : Nat) : ByteArray := Id.run do
  let mut a := ByteArray.emptyWithCapacity n
  for _ in [0:n] do a := a.push 0
  return a

/-- A colour: red, green, blue in 0..255 (whole numbers after parsing), alpha in 0..1. -/
structure RGBA where
  r : Float
  g : Float
  b : Float
  a : Float
  deriving Repr, Inhabited, BEq

def RGBA.black : RGBA := ⟨0,0,0,1⟩
def RGBA.transparent : RGBA := ⟨0,0,0,0⟩

namespace Color

/-- CSS Color 4 §6.1, the named colours, as `0xRRGGBB`. -/
def named : List (String × Nat) := [
  ("aliceblue",0xf0f8ff),("antiquewhite",0xfaebd7),("aqua",0x00ffff),("aquamarine",0x7fffd4),
  ("azure",0xf0ffff),("beige",0xf5f5dc),("bisque",0xffe4c4),("black",0x000000),
  ("blanchedalmond",0xffebcd),("blue",0x0000ff),("blueviolet",0x8a2be2),("brown",0xa52a2a),
  ("burlywood",0xdeb887),("cadetblue",0x5f9ea0),("chartreuse",0x7fff00),("chocolate",0xd2691e),
  ("coral",0xff7f50),("cornflowerblue",0x6495ed),("cornsilk",0xfff8dc),("crimson",0xdc143c),
  ("cyan",0x00ffff),("darkblue",0x00008b),("darkcyan",0x008b8b),("darkgoldenrod",0xb8860b),
  ("darkgray",0xa9a9a9),("darkgreen",0x006400),("darkgrey",0xa9a9a9),("darkkhaki",0xbdb76b),
  ("darkmagenta",0x8b008b),("darkolivegreen",0x556b2f),("darkorange",0xff8c00),("darkorchid",0x9932cc),
  ("darkred",0x8b0000),("darksalmon",0xe9967a),("darkseagreen",0x8fbc8f),("darkslateblue",0x483d8b),
  ("darkslategray",0x2f4f4f),("darkslategrey",0x2f4f4f),("darkturquoise",0x00ced1),("darkviolet",0x9400d3),
  ("deeppink",0xff1493),("deepskyblue",0x00bfff),("dimgray",0x696969),("dimgrey",0x696969),
  ("dodgerblue",0x1e90ff),("firebrick",0xb22222),("floralwhite",0xfffaf0),("forestgreen",0x228b22),
  ("fuchsia",0xff00ff),("gainsboro",0xdcdcdc),("ghostwhite",0xf8f8ff),("gold",0xffd700),
  ("goldenrod",0xdaa520),("gray",0x808080),("green",0x008000),("greenyellow",0xadff2f),
  ("grey",0x808080),("honeydew",0xf0fff0),("hotpink",0xff69b4),("indianred",0xcd5c5c),
  ("indigo",0x4b0082),("ivory",0xfffff0),("khaki",0xf0e68c),("lavender",0xe6e6fa),
  ("lavenderblush",0xfff0f5),("lawngreen",0x7cfc00),("lemonchiffon",0xfffacd),("lightblue",0xadd8e6),
  ("lightcoral",0xf08080),("lightcyan",0xe0ffff),("lightgoldenrodyellow",0xfafad2),("lightgray",0xd3d3d3),
  ("lightgreen",0x90ee90),("lightgrey",0xd3d3d3),("lightpink",0xffb6c1),("lightsalmon",0xffa07a),
  ("lightseagreen",0x20b2aa),("lightskyblue",0x87cefa),("lightslategray",0x778899),("lightslategrey",0x778899),
  ("lightsteelblue",0xb0c4de),("lightyellow",0xffffe0),("lime",0x00ff00),("limegreen",0x32cd32),
  ("linen",0xfaf0e6),("magenta",0xff00ff),("maroon",0x800000),("mediumaquamarine",0x66cdaa),
  ("mediumblue",0x0000cd),("mediumorchid",0xba55d3),("mediumpurple",0x9370db),("mediumseagreen",0x3cb371),
  ("mediumslateblue",0x7b68ee),("mediumspringgreen",0x00fa9a),("mediumturquoise",0x48d1cc),("mediumvioletred",0xc71585),
  ("midnightblue",0x191970),("mintcream",0xf5fffa),("mistyrose",0xffe4e1),("moccasin",0xffe4b5),
  ("navajowhite",0xffdead),("navy",0x000080),("oldlace",0xfdf5e6),("olive",0x808000),
  ("olivedrab",0x6b8e23),("orange",0xffa500),("orangered",0xff4500),("orchid",0xda70d6),
  ("palegoldenrod",0xeee8aa),("palegreen",0x98fb98),("paleturquoise",0xafeeee),("palevioletred",0xdb7093),
  ("papayawhip",0xffefd5),("peachpuff",0xffdab9),("peru",0xcd853f),("pink",0xffc0cb),
  ("plum",0xdda0dd),("powderblue",0xb0e0e6),("purple",0x800080),("rebeccapurple",0x663399),
  ("red",0xff0000),("rosybrown",0xbc8f8f),("royalblue",0x4169e1),("saddlebrown",0x8b4513),
  ("salmon",0xfa8072),("sandybrown",0xf4a460),("seagreen",0x2e8b57),("seashell",0xfff5ee),
  ("sienna",0xa0522d),("silver",0xc0c0c0),("skyblue",0x87ceeb),("slateblue",0x6a5acd),
  ("slategray",0x708090),("slategrey",0x708090),("snow",0xfffafa),("springgreen",0x00ff7f),
  ("steelblue",0x4682b4),("tan",0xd2b48c),("teal",0x008080),("thistle",0xd8bfd8),
  ("tomato",0xff6347),("turquoise",0x40e0d0),("violet",0xee82ee),("wheat",0xf5deb3),
  ("white",0xffffff),("whitesmoke",0xf5f5f5),("yellow",0xffff00),("yellowgreen",0x9acd32)]

def asciiLower (s : String) : String := s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def trim (s : String) : String := String.ofList ((s.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

private def digit? (c : Char) : Option Nat := if '0' ≤ c && c ≤ '9' then some (c.toNat - 48) else none

/-- A CSS `<number>` (CSS Syntax 3 §4.3.13): sign, digits, fraction, exponent. -/
def number? (s : String) : Option Float := Id.run do
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let intDigits := cs.takeWhile (digit? · |>.isSome)
  let cs := cs.drop intDigits.length
  let (fracDigits, cs) := match cs with
    | '.' :: r => let d := r.takeWhile (digit? · |>.isSome); (some d, r.drop d.length)
    | r => (none, r)
  if intDigits.isEmpty && (fracDigits.map List.isEmpty).getD true then return none
  if fracDigits == some [] then return none
  let mantissa := (intDigits ++ fracDigits.getD []).foldl (fun n c => n * 10 + (c.toNat - 48)) 0
  let mut exp : Int := -(Int.ofNat (fracDigits.getD []).length)
  match cs with
  | [] => pure ()
  | e :: r =>
    if e != 'e' && e != 'E' then return none
    let (eneg, r) := match r with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
    if r.isEmpty || !r.all (digit? · |>.isSome) then return none
    let ev := r.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
    exp := exp + (if eneg then -(Int.ofNat ev) else Int.ofNat ev)
  let m := nf mantissa
  let v := if exp ≥ 0 then m * nf (10 ^ exp.toNat) else m / nf (10 ^ (-exp).toNat)
  return some (if neg then -v else v)

private def hex? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

def clamp01 (x : Float) : Float := if x.isNaN then 0 else max 0 (min 1 x)
def clamp255 (x : Float) : Float := if x.isNaN then 0 else (max 0 (min 255 x)).round

/-- CSS Color 4 §7.1: hue in degrees, saturation and lightness in 0..1, to 0..255. -/
def hslToRgb (h s l : Float) : Float × Float × Float :=
  let h := h - 360 * (h / 360).floor
  let f := fun (n : Float) =>
    let k := (n + h / 30) - 12 * ((n + h / 30) / 12).floor
    let a := s * min l (1 - l)
    l - a * max (-1) (min (k - 3) (min (9 - k) 1))
  (f 0 * 255, f 8 * 255, f 4 * 255)

/-- CSS Color 4 §8: hue, whiteness, blackness. -/
def hwbToRgb (h w b : Float) : Float × Float × Float :=
  if w + b ≥ 1 then let g := w / (w + b) * 255; (g, g, g) else
  let (r, g, bl) := hslToRgb h 1 0.5
  let k := fun (c : Float) => (c / 255 * (1 - w - b) + w) * 255
  (k r, k g, k bl)

/-- An angle (`deg`, `rad`, `grad`, `turn`, or a number of degrees). -/
def angle? (s : String) : Option Float :=
  if s.endsWith "deg" then number? (s.dropEnd 3).toString
  else if s.endsWith "grad" then (· * 0.9) <$> number? (s.dropEnd 4).toString
  else if s.endsWith "rad" then (· * 180 / 3.141592653589793) <$> number? (s.dropEnd 3).toString
  else if s.endsWith "turn" then (· * 360) <$> number? (s.dropEnd 4).toString
  else number? s

/-- A percentage, as a fraction. -/
def percent? (s : String) : Option Float :=
  if s.endsWith "%" then (· / 100) <$> number? (s.dropEnd 1).toString else none

/-- An alpha value: a number or a percentage, clamped to 0..1. -/
def alpha? (s : String) : Option Float :=
  match percent? s with
  | some p => some (clamp01 p)
  | none => clamp01 <$> number? s

/-- The arguments of a colour function: either all comma-separated (legacy), or
space-separated with an optional `/ alpha`. Gives the channels and the alpha text. -/
def args? (inner : String) : Option (List String × Option String) :=
  let inner := trim inner
  if inner.any (· == ',') then
    let parts := (inner.splitOn ",").map trim
    if parts.any (·.isEmpty) || parts.any (fun p => p.any isSpace) then none
    else match parts with
      | [a, b, c] => some ([a, b, c], none)
      | [a, b, c, d] => some ([a, b, c], some d)
      | _ => none
  else
    let (main, alpha) := match inner.splitOn "/" with
      | [m] => (m, none)
      | [m, a] => (m, some (trim a))
      | _ => ("", none)
    let parts := ((main.split isSpace).toList.map (·.toString)).filter (· != "")
    if parts.length != 3 || alpha == some "" then none else some (parts, alpha)

/-- A colour function `name(inner)`. -/
def function? (name inner : String) : Option RGBA := do
  let (cs, a) ← args? inner
  let alpha ← match a with | some t => alpha? t | none => some 1
  match name, cs with
  | "rgb", [r, g, b] | "rgba", [r, g, b] =>
    let pct := [r, g, b].map percent?
    if pct.all Option.isSome then
      let v := pct.map fun p => clamp255 (p.getD 0 * 255)
      return ⟨v[0]!, v[1]!, v[2]!, alpha⟩
    -- Legacy syntax does not mix numbers and percentages.
    let ns ← [r, g, b].mapM number?
    let v := ns.map clamp255
    return ⟨v[0]!, v[1]!, v[2]!, alpha⟩
  | "hsl", [h, s, l] | "hsla", [h, s, l] =>
    let h ← angle? h
    -- The legacy (comma) syntax takes percentages only (CSS Color 4 §7).
    let legacy := inner.any (· == ',')
    let s ← (percent? s).orElse fun _ => if legacy then none else (· / 100) <$> number? s
    let l ← (percent? l).orElse fun _ => if legacy then none else (· / 100) <$> number? l
    let (r, g, b) := hslToRgb h (clamp01 s) (clamp01 l)
    return ⟨clamp255 r, clamp255 g, clamp255 b, alpha⟩
  | "hwb", [h, w, b] =>
    let h ← angle? h
    let w ← percent? w
    let b ← percent? b
    let (r, g, bl) := hwbToRgb h (clamp01 w) (clamp01 b)
    return ⟨clamp255 r, clamp255 g, clamp255 bl, alpha⟩
  | _, _ => none

/-- Parse a CSS colour. `none` when the text is not a colour (the attribute keeps its
value, HTML §4.12.5.1.5). -/
def parse? (source : String) : Option RGBA := do
  let s := asciiLower (trim source)
  if s == "transparent" then return RGBA.transparent
  if s == "currentcolor" then return RGBA.black
  if let some (_, v) := named.find? (·.1 == s) then
    return ⟨nf (v / 65536), nf (v / 256 % 256), nf (v % 256), 1⟩
  if s.startsWith "#" then
    let ds ← (s.drop 1).toString.toList.mapM hex?
    match ds with
    | [r, g, b] => return ⟨nf (r * 17), nf (g * 17), nf (b * 17), 1⟩
    | [r, g, b, a] => return ⟨nf (r * 17), nf (g * 17), nf (b * 17), nf (a * 17) / 255⟩
    | [r1, r2, g1, g2, b1, b2] =>
      return ⟨nf (r1 * 16 + r2), nf (g1 * 16 + g2), nf (b1 * 16 + b2), 1⟩
    | [r1, r2, g1, g2, b1, b2, a1, a2] =>
      return ⟨nf (r1 * 16 + r2), nf (g1 * 16 + g2), nf (b1 * 16 + b2),
        nf (a1 * 16 + a2) / 255⟩
    | _ => none
  let open_ ← (s.splitOn "(").head?
  if !s.any (· == '(') then none
  -- CSS Syntax 3 §5.4.8: a function that the input ends inside is closed there.
  let s := if s.endsWith ")" then s else s ++ ")"
  let inner := ((s.drop (open_.length + 1)).toString.dropEnd 1).toString
  function? (trim open_) inner

/-- The 8-bit alpha of a colour. -/
def alpha8 (c : RGBA) : Nat := (clamp01 c.a * 255).round.toUInt64.toNat

/-- CSS Color 4 §15.2: an 8-bit alpha as the shortest decimal (two places, or three when
two do not give back the same byte). -/
def alphaText (a8 : Nat) : String :=
  if a8 == 0 then "0" else
  let two := (nf a8 / 255 * 100).round
  let back := (two / 100 * 255).round.toUInt64.toNat
  let (v, places) := if back == a8 then (two.toUInt64.toNat, 2) else ((nf a8 / 255 * 1000).round.toUInt64.toNat, 3)
  let digits := toString v
  let padded := "".pushn '0' (places - digits.length) ++ digits
  let trimmed := String.ofList (padded.toList.reverse.dropWhile (· == (Char.ofNat 48))).reverse
  "0." ++ trimmed

private def hex2 (n : Nat) : String :=
  let d := fun (k : Nat) => if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
  String.ofList [d (n / 16 % 16), d (n % 16)]

def byte (x : Float) : Nat := (clamp255 x).toUInt64.toNat

/-- HTML §4.12.5.1.5, the serialisation of a colour. -/
def serialize (c : RGBA) : String :=
  let a8 := alpha8 c
  if a8 == 255 then "#" ++ hex2 (byte c.r) ++ hex2 (byte c.g) ++ hex2 (byte c.b)
  else s!"rgba({byte c.r}, {byte c.g}, {byte c.b}, {alphaText a8})"

end Color
end L4Factoidal.PageCanvas
