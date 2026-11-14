/-
L4Factoidal.DOM.Editing.Style — the style values that the editing algorithms read.

Specification: the W3C Editing APIs draft ("execCommand", w3c/editing, the text that
`editing/include/implementation.js` of the Web Platform Tests follows), which reads these
CSS properties of a node: `display`, `font-weight`, `font-style`, `text-decoration`,
`color`, `background-color`, `font-family`, `font-size`, `text-align`, `white-space`.
The values are resolved here from three sources, lowest priority first: the HTML
rendering defaults and presentational hints of the element (HTML §15), the declarations
the page's style sheets give the element (`Env.sheet`, supplied by the host from the
engine's cascade), and the element's `style` attribute.

The inline style of an element is a list of (property, value) pairs: `parseDecls` reads
the attribute, `serializeDecls` writes it, and `setDecl`, `removeDecl` and `getDecl`
change and read the list. Colours are `Color` (red, green, blue, alpha in thousandths);
font sizes are thousandths of a CSS pixel.

Proved here: the list laws of the inline style (`getDecl_setDecl`, `getDecl_removeDecl`,
`setDecl_idem`), that a legacy font size keeps its number (`cssSizeToLegacy_legacySizeToCss`),
and that an opaque colour survives its hexadecimal form (`parseHex_toHex`, tested on all
channel values by `#guard` at the corners). Tested only: the parsers of colours and lengths.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM

/-! ## Small string tools (ASCII) -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def trimL : List Char → List Char
  | c :: cs => if isWs c then trimL cs else c :: cs
  | [] => []

def trimChars (cs : List Char) : List Char := (trimL (trimL cs).reverse).reverse

def trimStr (s : String) : String := String.ofList (trimChars s.toList)

def lowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def lower (s : String) : String := String.ofList (s.toList.map lowerChar)

/-- Split at the top-level occurrences of `sep`: not inside parentheses or quotes. -/
def splitTop (sep : Char) (cs : List Char) : List (List Char) := Id.run do
  let mut out : List (List Char) := []
  let mut cur : List Char := []
  let mut depth : Nat := 0
  let mut quote : Option Char := none
  for c in cs do
    match quote with
    | some q =>
      cur := c :: cur
      if c == q then quote := none
    | none =>
      if c == '"' || c == '\'' then quote := some c; cur := c :: cur
      else if c == '(' then depth := depth + 1; cur := c :: cur
      else if c == ')' then depth := depth - 1; cur := c :: cur
      else if c == sep && depth == 0 then out := cur.reverse :: out; cur := []
      else cur := c :: cur
  return (cur.reverse :: out).reverse

/-- The part before the first `sep` and the part after it. -/
def cutAt (sep : Char) (cs : List Char) : Option (List Char × List Char) :=
  match cs.span (· != sep) with
  | (_, []) => none
  | (a, _ :: rest) => some (a, rest)

/-! ## The inline style as a list of declarations -/

abbrev Decls := List (String × String)

/-- The value of property `k`. -/
def getDecl : Decls → String → Option String
  | [], _ => none
  | (k', v') :: rest, k => if k' == k then some v' else getDecl rest k

/-- Set property `k` to `v`: in place when the property is there, else at the end. -/
def setDecl : Decls → String → String → Decls
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v => if k' == k then (k, v) :: rest else (k', v') :: setDecl rest k v

def removeDecl : Decls → String → Decls
  | [], _ => []
  | (k', v') :: rest, k => if k' == k then removeDecl rest k else (k', v') :: removeDecl rest k

/-- Law of the inline style. Says: after `setDecl ds k v`, reading `k` gives `v`.
Does not say: anything about the text of the `style` attribute (`parseDecls`). -/
theorem getDecl_setDecl (ds : Decls) (k v : String) : getDecl (setDecl ds k v) k = some v := by
  induction ds with
  | nil => simp [setDecl, getDecl]
  | cons h t ih =>
    obtain ⟨k', v'⟩ := h
    by_cases hk : (k' == k) = true
    · simp [setDecl, getDecl, hk]
    · simp [setDecl, getDecl, hk, ih]

/-- Law of the inline style. Says: after `removeDecl ds k`, reading `k` gives nothing.
Does not say: that other properties keep their values (true, not stated here). -/
theorem getDecl_removeDecl (ds : Decls) (k : String) : getDecl (removeDecl ds k) k = none := by
  induction ds with
  | nil => simp [removeDecl, getDecl]
  | cons h t ih =>
    obtain ⟨k', v'⟩ := h
    by_cases hk : (k' == k) = true
    · simp [removeDecl, hk, ih]
    · simp [removeDecl, getDecl, hk, ih]

/-- Law of the inline style. Says: setting a property twice to one value is setting it once.
Does not say: that the order of the other declarations matters to any reader. -/
theorem setDecl_idem (ds : Decls) (k v : String) : setDecl (setDecl ds k v) k v = setDecl ds k v := by
  induction ds with
  | nil => simp [setDecl]
  | cons h t ih =>
    obtain ⟨k', v'⟩ := h
    by_cases hk : (k' == k) = true
    · simp [setDecl, hk]
    · simp [setDecl, hk, ih]

/-- The most declarations read from one `style` attribute (the rest are dropped): it
bounds the recursion of `setDecl` and `removeDecl`. -/
def maxDecls : Nat := 1024

/-- The declarations of a `style` attribute value: split at top-level `;`, each at its
first `:`; names in ASCII lowercase; a later declaration of a property takes the place of
the earlier one (CSSOM "set a CSS declaration", without `!important`). -/
def parseDecls (s : String) : Decls :=
  ((splitTop ';' s.toList).take maxDecls).foldl (fun ds part =>
    match cutAt ':' part with
    | some (k, v) =>
      let k := lower (String.ofList (trimChars k))
      let v := String.ofList (trimChars v)
      if k.isEmpty || v.isEmpty then ds else setDecl ds k v
    | none => ds) []

/-- The text of a `style` attribute: `name: value` joined by `; `. -/
def serializeDecls (ds : Decls) : String := "; ".intercalate (ds.map fun (k, v) => k ++ ": " ++ v)

#guard parseDecls "font-weight: bold; COLOR:red;" == [("font-weight", "bold"), ("color", "red")]
#guard parseDecls "color: rgb(1, 2, 3); color: blue" == [("color", "blue")]
#guard parseDecls "background: url(a;b)" == [("background", "url(a;b)")]
#guard serializeDecls [("font-weight", "bold"), ("color", "red")] == "font-weight: bold; color: red"
#guard parseDecls (serializeDecls [("font-weight", "bold"), ("color", "rgb(0, 0, 255)")]) ==
  [("font-weight", "bold"), ("color", "rgb(0, 0, 255)")]

/-! ## Colours -/

/-- A colour: channels 0 to 255, alpha in thousandths (1000 is opaque). -/
structure Color where
  r : Nat
  g : Nat
  b : Nat
  a : Nat := 1000
  deriving BEq, DecidableEq, Repr, Inhabited

def Color.black : Color := ⟨0, 0, 0, 1000⟩
def Color.transparent : Color := ⟨0, 0, 0, 0⟩

def namedColors : List (String × Nat) := [
  ("aliceblue", 0xf0f8ff), ("antiquewhite", 0xfaebd7), ("aqua", 0x00ffff), ("aquamarine", 0x7fffd4),
  ("azure", 0xf0ffff), ("beige", 0xf5f5dc), ("bisque", 0xffe4c4), ("black", 0x000000),
  ("blanchedalmond", 0xffebcd), ("blue", 0x0000ff), ("blueviolet", 0x8a2be2), ("brown", 0xa52a2a),
  ("burlywood", 0xdeb887), ("cadetblue", 0x5f9ea0), ("chartreuse", 0x7fff00), ("chocolate", 0xd2691e),
  ("coral", 0xff7f50), ("cornflowerblue", 0x6495ed), ("cornsilk", 0xfff8dc), ("crimson", 0xdc143c),
  ("cyan", 0x00ffff), ("darkblue", 0x00008b), ("darkcyan", 0x008b8b), ("darkgoldenrod", 0xb8860b),
  ("darkgray", 0xa9a9a9), ("darkgreen", 0x006400), ("darkgrey", 0xa9a9a9), ("darkkhaki", 0xbdb76b),
  ("darkmagenta", 0x8b008b), ("darkolivegreen", 0x556b2f), ("darkorange", 0xff8c00), ("darkorchid", 0x9932cc),
  ("darkred", 0x8b0000), ("darksalmon", 0xe9967a), ("darkseagreen", 0x8fbc8f), ("darkslateblue", 0x483d8b),
  ("darkslategray", 0x2f4f4f), ("darkslategrey", 0x2f4f4f), ("darkturquoise", 0x00ced1), ("darkviolet", 0x9400d3),
  ("deeppink", 0xff1493), ("deepskyblue", 0x00bfff), ("dimgray", 0x696969), ("dimgrey", 0x696969),
  ("dodgerblue", 0x1e90ff), ("firebrick", 0xb22222), ("floralwhite", 0xfffaf0), ("forestgreen", 0x228b22),
  ("fuchsia", 0xff00ff), ("gainsboro", 0xdcdcdc), ("ghostwhite", 0xf8f8ff), ("gold", 0xffd700),
  ("goldenrod", 0xdaa520), ("gray", 0x808080), ("green", 0x008000), ("greenyellow", 0xadff2f),
  ("grey", 0x808080), ("honeydew", 0xf0fff0), ("hotpink", 0xff69b4), ("indianred", 0xcd5c5c),
  ("indigo", 0x4b0082), ("ivory", 0xfffff0), ("khaki", 0xf0e68c), ("lavender", 0xe6e6fa),
  ("lavenderblush", 0xfff0f5), ("lawngreen", 0x7cfc00), ("lemonchiffon", 0xfffacd), ("lightblue", 0xadd8e6),
  ("lightcoral", 0xf08080), ("lightcyan", 0xe0ffff), ("lightgoldenrodyellow", 0xfafad2), ("lightgray", 0xd3d3d3),
  ("lightgreen", 0x90ee90), ("lightgrey", 0xd3d3d3), ("lightpink", 0xffb6c1), ("lightsalmon", 0xffa07a),
  ("lightseagreen", 0x20b2aa), ("lightskyblue", 0x87cefa), ("lightslategray", 0x778899), ("lightslategrey", 0x778899),
  ("lightsteelblue", 0xb0c4de), ("lightyellow", 0xffffe0), ("lime", 0x00ff00), ("limegreen", 0x32cd32),
  ("linen", 0xfaf0e6), ("magenta", 0xff00ff), ("maroon", 0x800000), ("mediumaquamarine", 0x66cdaa),
  ("mediumblue", 0x0000cd), ("mediumorchid", 0xba55d3), ("mediumpurple", 0x9370db), ("mediumseagreen", 0x3cb371),
  ("mediumslateblue", 0x7b68ee), ("mediumspringgreen", 0x00fa9a), ("mediumturquoise", 0x48d1cc), ("mediumvioletred", 0xc71585),
  ("midnightblue", 0x191970), ("mintcream", 0xf5fffa), ("mistyrose", 0xffe4e1), ("moccasin", 0xffe4b5),
  ("navajowhite", 0xffdead), ("navy", 0x000080), ("oldlace", 0xfdf5e6), ("olive", 0x808000),
  ("olivedrab", 0x6b8e23), ("orange", 0xffa500), ("orangered", 0xff4500), ("orchid", 0xda70d6),
  ("palegoldenrod", 0xeee8aa), ("palegreen", 0x98fb98), ("paleturquoise", 0xafeeee), ("palevioletred", 0xdb7093),
  ("papayawhip", 0xffefd5), ("peachpuff", 0xffdab9), ("peru", 0xcd853f), ("pink", 0xffc0cb),
  ("plum", 0xdda0dd), ("powderblue", 0xb0e0e6), ("purple", 0x800080), ("rebeccapurple", 0x663399),
  ("red", 0xff0000), ("rosybrown", 0xbc8f8f), ("royalblue", 0x4169e1), ("saddlebrown", 0x8b4513),
  ("salmon", 0xfa8072), ("sandybrown", 0xf4a460), ("seagreen", 0x2e8b57), ("seashell", 0xfff5ee),
  ("sienna", 0xa0522d), ("silver", 0xc0c0c0), ("skyblue", 0x87ceeb), ("slateblue", 0x6a5acd),
  ("slategray", 0x708090), ("slategrey", 0x708090), ("snow", 0xfffafa), ("springgreen", 0x00ff7f),
  ("steelblue", 0x4682b4), ("tan", 0xd2b48c), ("teal", 0x008080), ("thistle", 0xd8bfd8),
  ("tomato", 0xff6347), ("turquoise", 0x40e0d0), ("violet", 0xee82ee), ("wheat", 0xf5deb3),
  ("white", 0xffffff), ("whitesmoke", 0xf5f5f5), ("yellow", 0xffff00), ("yellowgreen", 0x9acd32)]

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `#rgb`, `#rgba`, `#rrggbb`, `#rrggbbaa` without the `#`. -/
def parseHex : List Char → Option Color
  | [r, g, b] => do
    let r ← hexVal r; let g ← hexVal g; let b ← hexVal b
    some ⟨r * 17, g * 17, b * 17, 1000⟩
  | [r, g, b, a] => do
    let r ← hexVal r; let g ← hexVal g; let b ← hexVal b; let a ← hexVal a
    some ⟨r * 17, g * 17, b * 17, a * 17 * 1000 / 255⟩
  | [r1, r2, g1, g2, b1, b2] => do
    let r1 ← hexVal r1; let r2 ← hexVal r2; let g1 ← hexVal g1; let g2 ← hexVal g2
    let b1 ← hexVal b1; let b2 ← hexVal b2
    some ⟨r1 * 16 + r2, g1 * 16 + g2, b1 * 16 + b2, 1000⟩
  | [r1, r2, g1, g2, b1, b2, a1, a2] => do
    let r1 ← hexVal r1; let r2 ← hexVal r2; let g1 ← hexVal g1; let g2 ← hexVal g2
    let b1 ← hexVal b1; let b2 ← hexVal b2; let a1 ← hexVal a1; let a2 ← hexVal a2
    some ⟨r1 * 16 + r2, g1 * 16 + g2, b1 * 16 + b2, (a1 * 16 + a2) * 1000 / 255⟩
  | _ => none

/-- The six hexadecimal digits of an opaque colour. -/
def Color.hexDigits (c : Color) : List Char :=
  [hexDigit (c.r / 16), hexDigit (c.r % 16), hexDigit (c.g / 16), hexDigit (c.g % 16),
   hexDigit (c.b / 16), hexDigit (c.b % 16)]

/-- A decimal number `int.frac` (no sign, no exponent) in thousandths. -/
def parseMilli (cs : List Char) : Option Nat :=
  let cs := trimChars cs
  let (ip, fp) := match cutAt '.' cs with
    | some (a, b) => (a, b)
    | none => (cs, [])
  if ip.isEmpty && fp.isEmpty then none
  else if !(ip.all Char.isDigit) || !(fp.all Char.isDigit) then none
  else
    let i := ip.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
    let f3 := (fp ++ ['0', '0', '0']).take 3
    some (i * 1000 + f3.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

/-- One channel of `rgb()`: a number 0 to 255 or a percentage. -/
def parseChannel (cs : List Char) : Option Nat :=
  let cs := trimChars cs
  match cs.reverse with
  | '%' :: rest => (parseMilli rest.reverse).map fun m => min 255 ((m * 255 + 50000) / 100000)
  | _ => (parseMilli cs).map fun m => min 255 ((m + 500) / 1000)

def parseAlpha (cs : List Char) : Option Nat :=
  let cs := trimChars cs
  match cs.reverse with
  | '%' :: rest => (parseMilli rest.reverse).map fun m => min 1000 (m / 100)
  | _ => (parseMilli cs).map fun m => min 1000 m

/-- The arguments of a functional notation: split at commas, or at spaces and `/`. -/
def colorArgs (cs : List Char) : List (List Char) :=
  if cs.contains ',' then (splitTop ',' cs).map trimChars
  else
    let (main, alpha) := match cutAt '/' cs with
      | some (a, b) => (a, [trimChars b])
      | none => (cs, [])
    ((splitTop ' ' main).map trimChars).filter (!·.isEmpty) ++ alpha

/-- HSL to RGB (CSS Color 4 §7.1), hue in degrees, saturation and lightness in
thousandths: integer arithmetic, channels rounded. -/
def hslToRgb (h s l : Nat) : Nat × Nat × Nat :=
  let h := h % 360
  let c := (1000 - (if 2 * l ≥ 1000 then 2 * l - 1000 else 1000 - 2 * l)) * s / 1000
  let hp := h * 1000 / 60
  let m2 := hp % 2000
  let x := c * (1000 - (if m2 ≥ 1000 then m2 - 1000 else 1000 - m2)) / 1000
  let (r1, g1, b1) :=
    if h < 60 then (c, x, 0) else if h < 120 then (x, c, 0) else if h < 180 then (0, c, x)
    else if h < 240 then (0, x, c) else if h < 300 then (x, 0, c) else (c, 0, x)
  let m := l - c / 2
  let ch := fun (v : Nat) => min 255 (((v + m) * 255 + 500) / 1000)
  (ch r1, ch g1, ch b1)

/-- A CSS colour value. `none` for `currentcolor` and for what is not a colour. -/
def parseColor (s : String) : Option Color :=
  let cs := (trimChars s.toList).map lowerChar
  match cs with
  | '#' :: rest => parseHex rest
  | _ =>
    let str := String.ofList cs
    if str == "transparent" then some Color.transparent
    else match namedColors.find? (·.1 == str) with
    | some (_, v) => some ⟨v / 65536, v / 256 % 256, v % 256, 1000⟩
    | none =>
      match cutAt '(' cs with
      | some (fn, rest) =>
        match rest.reverse with
        | ')' :: inner =>
          let args := colorArgs inner.reverse
          let fnName := String.ofList fn
          if fnName == "rgb" || fnName == "rgba" then
            match args with
            | [r, g, b] => do some ⟨← parseChannel r, ← parseChannel g, ← parseChannel b, 1000⟩
            | [r, g, b, a] => do some ⟨← parseChannel r, ← parseChannel g, ← parseChannel b, ← parseAlpha a⟩
            | _ => none
          else if fnName == "hsl" || fnName == "hsla" then
            let pct := fun (x : List Char) => match x.reverse with
              | '%' :: r => (parseMilli r.reverse).map fun m => min 1000 (m / 100)
              | _ => none
            let hue := fun (x : List Char) =>
              let x := if (String.ofList x).endsWith "deg" then x.take (x.length - 3) else x
              (parseMilli x).map (· / 1000)
            match args with
            | [h, sa, l] => do
              let (r, g, b) := hslToRgb (← hue h) (← pct sa) (← pct l)
              some ⟨r, g, b, 1000⟩
            | [h, sa, l, a] => do
              let (r, g, b) := hslToRgb (← hue h) (← pct sa) (← pct l)
              some ⟨r, g, b, ← parseAlpha a⟩
            | _ => none
          else none
        | _ => none
      | none => none

/-- Thousandths as a decimal number with no trailing zeros: 500 is "0.5". -/
def milliText (m : Nat) : String :=
  let i := m / 1000
  let f := m % 1000
  if f == 0 then toString i
  else
    let ds := [Char.ofNat (48 + f / 100), Char.ofNat (48 + f / 10 % 10), Char.ofNat (48 + f % 10)]
    let ds := (ds.reverse.dropWhile (· == '0')).reverse
    toString i ++ "." ++ String.ofList ds

/-- The resolved value of a colour (CSSOM): `rgb(r, g, b)`, or `rgba(r, g, b, a)` when not opaque. -/
def Color.text (c : Color) : String :=
  if c.a ≥ 1000 then s!"rgb({c.r}, {c.g}, {c.b})" else s!"rgba({c.r}, {c.g}, {c.b}, {milliText c.a})"

/-- "Simple color" of the editing draft: `#rrggbb` for an opaque colour, else nothing. -/
def simpleColor (s : String) : Option String :=
  match parseColor s with
  | some c => if c.a ≥ 1000 then some (String.ofList ('#' :: c.hexDigits)) else none
  | none => none

#guard parseColor "blue" == some ⟨0, 0, 255, 1000⟩
#guard parseColor "#00F" == some ⟨0, 0, 255, 1000⟩
#guard parseColor "#0000ff" == some ⟨0, 0, 255, 1000⟩
#guard parseColor "rgb(0, 0, 255)" == some ⟨0, 0, 255, 1000⟩
#guard parseColor "rgba(0, 0, 255, 0.5)" == some ⟨0, 0, 255, 500⟩
#guard parseColor "rgb(0 0 255 / 50%)" == some ⟨0, 0, 255, 500⟩
#guard parseColor "hsl(240, 100%, 50%)" == some ⟨0, 0, 255, 1000⟩
#guard parseColor "hsla(240, 100%, 50%, 0.5)" == some ⟨0, 0, 255, 500⟩
#guard parseColor "currentColor" == none
#guard parseColor "transparent" == some ⟨0, 0, 0, 0⟩
#guard (⟨0, 0, 255, 500⟩ : Color).text == "rgba(0, 0, 255, 0.5)"
#guard (⟨165, 42, 42, 1000⟩ : Color).text == "rgb(165, 42, 42)"
#guard simpleColor "brown" == some "#a52a2a"
#guard simpleColor "rgba(0, 0, 255, 0.5)" == none

/-- A hexadecimal digit reads back as its value. -/
theorem hexVal_hexDigit (n : Fin 16) : hexVal (hexDigit n.val) = some n.val := by
  revert n; decide

/-- Round trip of the hexadecimal form. Says: for channels below 256, reading the six
digits that `Color.hexDigits` writes gives the opaque colour back. Does not say: anything
about colours with alpha, or about the other notations (tested by `#guard`). -/
theorem parseHex_toHex (r g b : Nat) (hr : r < 256) (hg : g < 256) (hb : b < 256) :
    parseHex (Color.hexDigits ⟨r, g, b, 1000⟩) = some ⟨r, g, b, 1000⟩ := by
  have e := fun (n : Nat) (h : n < 16) => hexVal_hexDigit ⟨n, h⟩
  have r1 := e (r / 16) (by omega); have r2 := e (r % 16) (by omega)
  have g1 := e (g / 16) (by omega); have g2 := e (g % 16) (by omega)
  have b1 := e (b / 16) (by omega); have b2 := e (b % 16) (by omega)
  simp only [Color.hexDigits, parseHex, r1, r2, g1, g2, b1, b2, Option.bind_some,
    bind, Option.some.injEq, Color.mk.injEq, and_true]
  omega

/-! ## Font sizes (thousandths of a pixel) -/

def sizeKeywords : List (String × Nat) :=
  [("xx-small", 9000), ("x-small", 10000), ("small", 13000), ("medium", 16000), ("large", 18000),
   ("x-large", 24000), ("xx-large", 32000), ("xxx-large", 48000)]

/-- Legacy font size 1 to 7 as a CSS keyword (HTML §15.3.4, the `font` element). -/
def legacySizeToCss (n : Nat) : String :=
  match n with
  | 1 => "x-small" | 2 => "small" | 3 => "medium" | 4 => "large" | 5 => "x-large" | 6 => "xx-large"
  | _ => "xxx-large"

def cssSizeToLegacy (s : String) : Option Nat :=
  if s == "x-small" then some 1 else if s == "small" then some 2 else if s == "medium" then some 3
  else if s == "large" then some 4 else if s == "x-large" then some 5 else if s == "xx-large" then some 6
  else if s == "xxx-large" then some 7 else none

/-- Round trip of the legacy font sizes. Says: a size 1 to 7 written as a keyword reads
back as the same size. Does not say: anything about pixel sizes (`legacyOfPx`). -/
theorem cssSizeToLegacy_legacySizeToCss (n : Nat) (h1 : 1 ≤ n) (h7 : n ≤ 7) :
    cssSizeToLegacy (legacySizeToCss n) = some n := by
  have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases this with h | h | h | h | h | h | h <;> subst h <;> decide

/-- Thousandths of a pixel as CSS text: "16px", "13.333px". -/
def pxText (m : Nat) : String := milliText m ++ "px"

/-- A font-size value in thousandths of a pixel, given the parent's size. -/
def parseFontSize (parent : Nat) (v : String) : Option Nat :=
  let v := lower (trimStr v)
  match sizeKeywords.find? (·.1 == v) with
  | some (_, px) => some px
  | none =>
    if v == "larger" then some (parent * 6 / 5)
    else if v == "smaller" then some (parent * 5 / 6)
    else
      let cs := v.toList
      let num := cs.takeWhile fun c => c.isDigit || c == '.'
      let unit := String.ofList (cs.dropWhile fun c => c.isDigit || c == '.')
      match parseMilli num with
      | none => none
      | some m =>
        if unit == "px" then some m
        else if unit == "pt" then some (m * 4 / 3)
        else if unit == "pc" then some (m * 16)
        else if unit == "in" then some (m * 96)
        else if unit == "cm" then some (m * 9600 / 254)
        else if unit == "mm" then some (m * 960 / 254)
        else if unit == "em" then some (m * parent / 1000)
        else if unit == "rem" then some (m * 16)
        else if unit == "ex" then some (m * parent / 2000)
        else if unit == "%" then some (m * parent / 100000)
        else none

/-- The legacy font size 1 to 7 of a pixel size (the editing draft, "legacy font size
for"): the largest size whose midpoint with the next one is not above it. The pixel size
is truncated to a whole pixel, as the draft's algorithm does. -/
def legacyOfPx (m : Nat) : Nat :=
  let px := m / 1000
  if 2 * px < 10 + 13 then 1 else if 2 * px < 13 + 16 then 2 else if 2 * px < 16 + 18 then 3
  else if 2 * px < 18 + 24 then 4 else if 2 * px < 24 + 32 then 5 else if 2 * px < 32 + 48 then 6 else 7

#guard legacyOfPx 16000 == 3
#guard legacyOfPx 13000 == 2
#guard legacyOfPx 48000 == 7
#guard legacyOfPx 10000 == 1
#guard parseFontSize 16000 "large" == some 18000
#guard parseFontSize 16000 "2em" == some 32000
#guard parseFontSize 16000 "12pt" == some 16000
#guard pxText 13333 == "13.333px"

/-- Monotone. Says: a larger pixel size never has a smaller legacy size. Does not say:
that the seven sizes are the pixel sizes any font really has. -/
theorem legacyOfPx_mono (a b : Nat) (h : a ≤ b) : legacyOfPx a ≤ legacyOfPx b := by
  have hd : a / 1000 ≤ b / 1000 := Nat.div_le_div_right h
  unfold legacyOfPx
  simp only
  repeat' split
  all_goals omega

/-! ## Resolved styles -/

/-- What the host gives: the declarations the page's style sheets give an element, lowest
priority first (the winners of the cascade without the `style` attribute). -/
structure Env where
  sheet : Dom → NodeId → Decls := fun _ _ => []

/-- The style values of one element that editing reads. -/
structure CStyle where
  display : String := "inline"
  /-- 100 to 900. -/
  fontWeight : Nat := 400
  fontStyle : String := "normal"
  /-- The element's own `text-decoration` (not inherited). -/
  textDecoration : String := "none"
  color : Color := Color.black
  /-- The element's own `background-color` (not inherited). -/
  background : Color := Color.transparent
  fontFamily : String := "serif"
  fontSize : Nat := 16000
  textAlign : String := "start"
  whiteSpace : String := "normal"
  deriving Repr, Inhabited

def attrOf (x : Node) (name : String) : Option String :=
  (x.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

def blockTags : List String :=
  ["html", "body", "address", "blockquote", "center", "dialog", "div", "figure", "figcaption", "footer", "form",
   "header", "hr", "legend", "listing", "main", "p", "plaintext", "pre", "search", "xmp", "article", "aside",
   "h1", "h2", "h3", "h4", "h5", "h6", "hgroup", "nav", "section", "dir", "dd", "dl", "dt", "menu", "ol", "ul",
   "details", "summary", "fieldset", "optgroup", "option", "frameset", "frame"]

def hiddenTags : List String :=
  ["head", "link", "meta", "script", "style", "title", "area", "base", "basefont", "datalist", "noembed",
   "noframes", "param", "rp", "template"]

/-- The `display` of an HTML element with no author style (HTML §15.3). -/
def defaultDisplay (tag : String) : String :=
  if blockTags.contains tag then "block"
  else if hiddenTags.contains tag then "none"
  else match tag with
  | "li" => "list-item" | "table" => "table" | "caption" => "table-caption"
  | "colgroup" => "table-column-group" | "col" => "table-column" | "thead" => "table-header-group"
  | "tbody" => "table-row-group" | "tfoot" => "table-footer-group" | "tr" => "table-row"
  | "td" => "table-cell" | "th" => "table-cell" | "ruby" => "ruby" | "rt" => "ruby-text"
  | "input" => "inline-block" | "button" => "inline-block" | "select" => "inline-block"
  | "textarea" => "inline-block" | "marquee" => "inline-block" | "meter" => "inline-block"
  | "progress" => "inline-block"
  | _ => "inline"

/-- The rendering defaults and presentational hints of an HTML element (HTML §15), as
declarations. -/
def uaDecls (x : Node) : Decls := Id.run do
  let tag := x.lname
  let mut ds : Decls := [("display", if (attrOf x "hidden").isSome then "none" else defaultDisplay tag)]
  if ["b", "strong", "h1", "h2", "h3", "h4", "h5", "h6", "th"].contains tag then ds := ds ++ [("font-weight", "bold")]
  if ["i", "cite", "em", "var", "address", "dfn"].contains tag then ds := ds ++ [("font-style", "italic")]
  if ["u", "ins"].contains tag then ds := ds ++ [("text-decoration", "underline")]
  if ["s", "strike", "del"].contains tag then ds := ds ++ [("text-decoration", "line-through")]
  if tag == "a" && (attrOf x "href").isSome then ds := ds ++ [("color", "#0000ee"), ("text-decoration", "underline")]
  if tag == "mark" then ds := ds ++ [("background-color", "yellow"), ("color", "black")]
  if ["pre", "listing", "plaintext", "xmp", "tt", "code", "kbd", "samp"].contains tag then
    ds := ds ++ [("font-family", "monospace")]
  if ["pre", "listing", "plaintext", "xmp"].contains tag then ds := ds ++ [("white-space", "pre")]
  if tag == "textarea" then ds := ds ++ [("white-space", "pre-wrap")]
  if tag == "nobr" then ds := ds ++ [("white-space", "nowrap")]
  if (tag == "td" || tag == "th") && (attrOf x "nowrap").isSome then ds := ds ++ [("white-space", "nowrap")]
  if tag == "big" then ds := ds ++ [("font-size", "larger")]
  if ["small", "sub", "sup"].contains tag then ds := ds ++ [("font-size", "smaller")]
  match tag with
  | "h1" => ds := ds ++ [("font-size", "2em")]
  | "h2" => ds := ds ++ [("font-size", "1.5em")]
  | "h3" => ds := ds ++ [("font-size", "1.17em")]
  | "h5" => ds := ds ++ [("font-size", "0.83em")]
  | "h6" => ds := ds ++ [("font-size", "0.67em")]
  | _ => pure ()
  if tag == "center" then ds := ds ++ [("text-align", "center")]
  if tag == "th" then ds := ds ++ [("text-align", "center")]
  match attrOf x "align" with
  | some a =>
    let a := lower (trimStr a)
    if ["left", "right", "center", "justify"].contains a &&
        ["div", "p", "h1", "h2", "h3", "h4", "h5", "h6", "td", "th", "tr", "thead", "tbody", "tfoot", "caption",
         "col", "colgroup"].contains tag then
      ds := ds ++ [("text-align", a)]
  | none => pure ()
  if tag == "font" then
    match attrOf x "color" with
    | some c => if (parseColor c).isSome then ds := ds ++ [("color", c)]
    | none => pure ()
    match attrOf x "face" with
    | some f => ds := ds ++ [("font-family", f)]
    | none => pure ()
    match attrOf x "size" with
    | some sz =>
      let cs := (trimChars sz.toList)
      let (sign, digits) := match cs with
        | '+' :: r => (1, r)
        | '-' :: r => (2, r)
        | r => (0, r)
      let digits := digits.takeWhile Char.isDigit
      if !digits.isEmpty then
        let n := digits.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
        let n := if sign == 1 then 3 + n else if sign == 2 then 3 - n else n
        let n := max 1 (min 7 n)
        ds := ds ++ [("font-size", legacySizeToCss n)]
    | none => pure ()
  return ds

/-- The last declaration of one of `names` in `ds`. -/
def lastDecl (ds : Decls) (names : List String) : Option String :=
  (ds.reverse.find? fun (k, _) => names.contains k).map (·.2)

/-- The first word of a `background` shorthand that is a colour. -/
def backgroundColorOf (v : String) : Option Color :=
  ((splitTop ' ' v.toList).filterMap fun w => parseColor (String.ofList w)).head?

def fontWeightOf (parent : Nat) (v : String) : Option Nat :=
  let v := lower (trimStr v)
  if v == "normal" then some 400 else if v == "bold" then some 700
  else if v == "bolder" then some (if parent < 350 then 400 else if parent < 550 then 700 else 900)
  else if v == "lighter" then some (if parent < 550 then 100 else if parent < 750 then 400 else 700)
  else match v.toNat? with
    | some n => if 1 ≤ n && n ≤ 1000 then some n else none
    | none => none

/-- An inherited property: the parent's value with no declaration (or `inherit`). -/
def inheritOr {α : Type} (v : Option String) (parentV initial : α) (f : String → Option α) : α :=
  match v with
  | none => parentV
  | some s => if s == "inherit" then parentV else if s == "initial" then initial else (f s).getD parentV

/-- A property that is not inherited: the initial value with no declaration. -/
def own {α : Type} (v : Option String) (parentV initial : α) (f : String → Option α) : α :=
  match v with
  | none => initial
  | some s => if s == "inherit" then parentV else if s == "initial" then initial else (f s).getD initial

/-- The style of an element from its parent's style and its declarations (defaults and
hints, then the style sheets, then the `style` attribute). Inherited properties take the
parent's value when no declaration gives one. -/
def styleStep (env : Env) (d : Dom) (parent : CStyle) (n : NodeId) : CStyle :=
  let x := d.get n
  let html := x.ns == some htmlNS
  let ds : Decls := (if html then uaDecls x else [("display", "inline")]) ++ env.sheet d n ++
    parseDecls ((attrOf x "style").getD "")
  let pick := fun (names : List String) => (lastDecl ds names).map fun v => lower (trimStr v)
  { display := own (pick ["display"]) parent.display "inline" some
    fontWeight := inheritOr (pick ["font-weight"]) parent.fontWeight 400 (fontWeightOf parent.fontWeight)
    fontStyle := inheritOr (pick ["font-style"]) parent.fontStyle "normal"
      (fun s => if ["normal", "italic", "oblique"].contains s then some s else none)
    textDecoration := own (pick ["text-decoration", "text-decoration-line"]) parent.textDecoration "none" some
    color := inheritOr (lastDecl ds ["color"]) parent.color Color.black
      (fun s => if lower (trimStr s) == "currentcolor" then some parent.color else parseColor s)
    background := own (lastDecl ds ["background-color", "background"]) parent.background Color.transparent
      (fun s => (parseColor s).orElse fun _ => backgroundColorOf s)
    fontFamily := inheritOr ((lastDecl ds ["font-family"]).map trimStr) parent.fontFamily "serif" some
    fontSize := inheritOr (lastDecl ds ["font-size"]) parent.fontSize 16000 (parseFontSize parent.fontSize)
    textAlign := inheritOr (pick ["text-align"]) parent.textAlign "start" some
    whiteSpace := inheritOr (pick ["white-space"]) parent.whiteSpace "normal" some }

/-- The inclusive ancestors of `n` that are elements, outermost first. -/
def elementChain (d : Dom) (n : NodeId) : List NodeId := Id.run do
  let mut out : List NodeId := []
  let mut cur := some n
  for _ in [0:d.size + 1] do
    match cur with
    | some c =>
      if (d.get c).type == .element then out := c :: out
      cur := (d.get c).parent
    | none => break
  return out

/-- The resolved style of element `n`: the cascade down its ancestors. For a node that is
not an element, the style of its parent element. -/
def styleOf (env : Env) (d : Dom) (n : NodeId) : CStyle :=
  (elementChain d n).foldl (styleStep env d) {}

end L4Factoidal.DOM.Editing
