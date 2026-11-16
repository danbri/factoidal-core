import L4Factoidal.XML.NamespaceView
import L4Factoidal.Rendering.CssValues.Color

/-! # CSS Color 4 colours in the SVG of a page (2026-11-15)

The SVG reader (`SVG.lean`) reads hex, comma `rgb()`, named and system colours, and refuses the
rest. A page's SVG (inline `svg`, or an SVG document) uses all of CSS Color 4: `hsl()`, `hwb()`,
`lab()`, `lch()`, `oklab()`, `oklch()`, `color()`, space-separated `rgb()`, `#rgba`. Before the
page path gives its SVG to the reader (`WebRender.makeReplacedIn`), this pass rewrites each such
colour of a colour property (presentation attributes, `style` attributes, `<style>` sheets) to
`#rrggbb`, resolved by the page's CSS colour parser (`CssValues.Color`, exact rationals,
rounded to 8 bits). Only opaque colours: a colour with alpha below 1, `currentcolor` or an
invalid colour is left as written (the reader then decides, as before). A value the reader
already reads is left as written.

The pass lives here, not in the reader, so that the small SVG Wasm engine (`build-engines.sh`)
does not take the CSS value closure. Measured: 18 WPT svg reftests that drew a blank fill. -/
namespace NativeSVGCssColour

open L4Factoidal.XML
open L4Factoidal.Rendering.CssValues

/-- The properties whose value is a colour. -/
def colourProperties : List String :=
  ["fill", "stroke", "color", "stop-color", "flood-color", "lighting-color", "solid-color"]

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
private def hexByte (n : Nat) : String := String.ofList [hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- Whether the SVG reader reads `v` as it is: a named or system colour, hex of 3 or 6 digits,
or comma `rgb()` (so nothing it reads changes). -/
def readerReads (v : String) : Bool :=
  let s := v.trimAscii.toString.toLower
  if s.startsWith "#" then s.length == 4 || s.length == 7
  else if s.startsWith "rgb(" then (s.splitOn ",").length == 3
  else !s.contains '('

/-- The `#rrggbb` of an opaque CSS colour that the reader does not read; `none` otherwise. -/
def rewrite? (v : String) : Option String :=
  if readerReads v then none else
  match trimWs (CV.parse v) with
  | [cv] =>
    match Color.resolve {} cv with
    | none => none
    | some c =>
      if c.alpha != some 1 then none else
      match Color.toMixSpace .srgb c with
      | some ⟨_, some r, some g, some b, _⟩ =>
        some ("#" ++ hexByte (Color.byteOf r) ++ hexByte (Color.byteOf g) ++ hexByte (Color.byteOf b))
      | _ => none
  | _ => none

/-- One declaration `prop: value`, with its value rewritten when `prop` is a colour property. -/
def declaration (d : String) : String :=
  match d.splitOn ":" with
  | [k, v] =>
    if colourProperties.contains k.trimAscii.toString.toLower then
      match rewrite? v with
      | some hex =>
        -- the white space around the value is kept
        let lead := String.ofList (v.toList.takeWhile Char.isWhitespace)
        let trail := String.ofList ((v.toList.reverse.takeWhile Char.isWhitespace).reverse)
        k ++ ":" ++ lead ++ hex ++ trail
      | none => d
    else d
  | _ => d

/-- The declarations of a `style` attribute (no braces) or of each rule of a style sheet
(`selector { declarations }`) rewritten (`declaration`). -/
def sheet (text : String) : String :=
  let decls := fun (body : String) => ";".intercalate ((body.splitOn ";").map declaration)
  if !text.contains '{' then decls text else
  "}".intercalate ((text.splitOn "}").map fun part =>
    match part.splitOn "{" with
    | sel :: body :: more => sel ++ "{" ++ decls ("{".intercalate (body :: more))
    | _ => part)

/-- The tree with its colours rewritten; `fuel` bounds the depth (deeper content is kept as
written). -/
def tree : Nat → NamespaceNode → NamespaceNode
  | 0, n => n
  | fuel + 1, .element name attrs children =>
    let attrs := attrs.map fun a =>
      if a.name.namespace_.isNone then
        if colourProperties.contains a.name.localPart then
          match rewrite? a.value with
          | some hex => { a with value := hex }
          | none => a
        else if a.name.localPart == "style" then { a with value := sheet a.value }
        else a
      else a
    let isStyle := name.localPart == "style"
    let children := children.map fun c => match c with
      | .other (.text t) => if isStyle then .other (.text (sheet t)) else c
      | .other (.cdata t) => if isStyle then .other (.cdata (sheet t)) else c
      | _ => tree fuel c
    .element name attrs children
  | _, n => n

-- Tests (inputs and expected texts; Chrome draws these colours with the same bytes)
#guard rewrite? "hsl(120 100% 25%)" == some "#008000"
#guard rewrite? "rgb(0 0 255)" == some "#0000ff"
#guard rewrite? "#00f8" == none
#guard rewrite? "#00ff" == some "#0000ff"
#guard rewrite? "rgba(0,0,255,0.5)" == none
#guard rewrite? "green" == none
#guard rewrite? "rgb(0, 128, 0)" == none
#guard rewrite? "currentcolor" == none
#guard rewrite? "url(#g)" == none
#guard declaration " fill: hwb(120 0% 50%)" == " fill: #008000"
#guard declaration "fill:lab(46.28 -47.55 48.59) " == "fill:#008000 "
#guard declaration "width: hsl(120 100% 25%)" == "width: hsl(120 100% 25%)"
#guard sheet "#test { fill: hsl(120 100% 25%); stroke: blue }" == "#test { fill: #008000; stroke: blue }"
#guard sheet "a { fill: hsl(120 100% 25%) } b { stroke: rgb(0 0 255) }" == "a { fill: #008000 } b { stroke: #0000ff }"

end NativeSVGCssColour
