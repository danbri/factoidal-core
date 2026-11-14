/-
L4Factoidal.HTML.InputColor — the value of a colour well (`<input type=color>`, HTML
§4.10.5.1.15 "update a color"): the value is parsed as a CSS `<color>` (CSS Color 4, in
`Rendering.CssValues.Color`; anything else, `currentcolor` and the CSS-wide keywords are
black), converted to the element's colour space and serialised:

- `limited-srgb` (the default): 8-bit sRGB channels; without the `alpha` attribute a valid
  lowercase simple colour `#rrggbb`, with it `color(srgb r g b / a)` (alpha 8-bit too);
- `display-p3`: `color(display-p3 r g b / a)`, not clamped (out-of-gamut values stay).

Alpha is 1 without the `alpha` attribute. Numbers are written rounded to six decimal places.
-/
import L4Factoidal.Rendering.CssValues.Color

namespace L4Factoidal.HTML.InputColor
open L4Factoidal.Rendering.CssValues
open L4Factoidal.Rendering.CssValues.Color

/-- The colour a value is, or none (not one `<color>` component value, or one that does not
resolve, as `currentcolor` does not here). -/
def parseColor (s : String) : Option Color :=
  match trimWs (CV.parse s) with
  | [cv] => resolve {} cv
  | _ => none

def black : Color := { space := .srgb, c1 := some 0, c2 := some 0, c3 := some 0 }

/-- The channels of `c` in the rectangular space `dst` (a missing component is 0). -/
def channels (c : Color) (dst : Space) : Rat × Rat × Rat :=
  let src := if c.space == .rgb then Space.srgb else c.space
  let (a, b, d) := convertV src dst (c.c1.getD 0, c.c2.getD 0, c.c3.getD 0)
  (a.getD 0, b.getD 0, d.getD 0)

def hexDigitOf (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Two lowercase hexadecimal digits of a byte. -/
def hex2 (n : Nat) : String := String.ofList [hexDigitOf (n / 16 % 16), hexDigitOf (n % 16)]

/-- A number as the serialisation writes it: rounded to six decimal places. -/
def num (x : Rat) : String := fmtRat (roundTo 6 x)

def alphaText (a : Rat) : String := if a == 1 then "" else " / " ++ num a

/-- "Update a color": the value of a colour well whose value attribute or set value is `v`. -/
def update (v : String) (displayP3 alpha : Bool) : String :=
  let c := (parseColor v).getD black
  let a := if alpha then clamp01 (c.alpha.getD 0) else 1
  if displayP3 then
    let (r, g, b) := channels c .displayP3
    "color(display-p3 " ++ num r ++ " " ++ num g ++ " " ++ num b ++ alphaText a ++ ")"
  else
    let (r, g, b) := channels c .srgb
    let (r, g, b) := (byteOf r, byteOf g, byteOf b)
    if !alpha then "#" ++ hex2 r ++ hex2 g ++ hex2 b
    else
      let q := fun (n : Nat) => num ((n : Rat) / 255)
      "color(srgb " ++ q r ++ " " ++ q g ++ " " ++ q b ++ alphaText ((byteOf a : Rat) / 255) ++ ")"

/-! ## What is proved -/

theorem hex2_length (n : Nat) : (hex2 n).length = 2 := by
  simp [hex2]

/-- Says: without `alpha` and in `limited-srgb` the value is always seven characters (`#`
and six hexadecimal digits), a valid simple colour, whatever the page sets. -/
theorem update_hex_length (v : String) : (update v false false).length = 7 := by
  have h1 : "#".length = 1 := by decide
  simp [update, hex2_length, h1]

/-! ## Tests (html/semantics/forms/the-input-element/color.window.js) -/

#guard update "" false false == "#000000" && update "#FFFFFF" false false == "#ffffff"
#guard update "#fff" false false == "#ffffff" && update " #ffffff " false false == "#ffffff"
#guard update "crimson" false false == "#dc143c" && update "rgb(1,1,1,0.5)" false false == "#010101"
#guard update "#ffffff;" false false == "#000000" && update "inherit" false false == "#000000"
#guard update "currentColor" false false == "#000000" && update "fffffff" false false == "#000000"
#guard update "#ffffff08" false true == "color(srgb 1 1 1 / 0.031373)"
#guard update "rgb(1,1,1,0.5)" false true == "color(srgb 0.003922 0.003922 0.003922 / 0.501961)"
#guard update "transparent" false true == "color(srgb 0 0 0 / 0)"
#guard update "white" true false == "color(display-p3 1 1 1)" && update "blue" false true == "color(srgb 0 0 1)"
#guard update "color(display-p3 3 none .2 / .6)" true true == "color(display-p3 3 0 0.2 / 0.6)"

end L4Factoidal.HTML.InputColor
