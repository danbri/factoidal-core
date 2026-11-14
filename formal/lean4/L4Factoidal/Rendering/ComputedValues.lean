/-
L4Factoidal.Rendering.ComputedValues — the resolved values of `getComputedStyle` (CSSOM
§9.1 "resolved value"), from the computed style of `Rendering.CSS` (`Style.lean`).

For each property of the style profile (`htmlProperties`, as longhands) the CSS text of
its computed value: lengths in `px`, colors as `rgb(r, g, b)` (CSS Color 4 §15.2,
serializing sRGB values; a transparent background is `rgba(0, 0, 0, 0)`), keywords as
written. `width` and `height` are resolved values: the used value when the element has a
box (the page asks the layout for those, `usedBox`), else the computed value.

A property the profile does not compute is not in the answer: the page's
CSSStyleDeclaration answers "" for it.
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.FloatFormat

namespace L4Factoidal.Rendering.ComputedValues
open L4Factoidal.Rendering.CSS

def px (x : Float) : String := FloatFormat.format x ++ "px"

def length : CSS.Length → String
  | .auto => "auto"
  | .px v => px v
  -- a percentage and the viewport units are kept as fractions (`CSS.length`)
  | .percent v => FloatFormat.format (v * 100) ++ "%"
  | .vw v => FloatFormat.format (v * 100) ++ "vw"
  | .vh v => FloatFormat.format (v * 100) ++ "vh"
  | .calc p v => "calc(" ++ FloatFormat.format (p * 100) ++ "% + " ++ px v ++ ")"
  | .minContent => "min-content"
  | .maxContent => "max-content"
  | .fitContent => "fit-content"
  | .stretch => "stretch"

/-- `none` for a maximum that is `auto` here (CSS 2.1 §10.4, §10.7). -/
def maxLength : CSS.Length → String
  | .auto => "none"
  | l => length l

def channel (x : Float) : String := toString (max 0 (min 255 (x * 255).round)).toUInt64.toNat

/-- CSS Color 4 §15.2: `rgb(r, g, b)`. -/
def color (c : Color) : String := s!"rgb({channel c.r}, {channel c.g}, {channel c.b})"

def display : Display → String
  | .none => "none" | .block => "block" | .inline => "inline" | .inlineBlock => "inline-block"
  | .table => "table" | .inlineTable => "inline-table" | .tableRowGroup => "table-row-group"
  | .tableHeaderGroup => "table-header-group" | .tableFooterGroup => "table-footer-group"
  | .tableRow => "table-row" | .tableCell => "table-cell" | .tableCaption => "table-caption"
  | .tableColumn => "table-column" | .tableColumnGroup => "table-column-group"
  | .flex => "flex" | .inlineFlex => "inline-flex" | .grid => "grid" | .inlineGrid => "inline-grid"

def borderStyle : BorderStyle → String
  | .none => "none" | .solid => "solid" | .inset => "inset" | .outset => "outset"

def textAlign : TextAlign → String
  | .start => "start" | .right => "right" | .center => "center" | .left => "left" | .end_ => "end"

def verticalAlign : VerticalAlign → String
  | .baseline => "baseline" | .top => "top" | .middle => "middle" | .bottom => "bottom"

def objectFit : ObjectFit → String
  | .fill => "fill" | .contain => "contain" | .cover => "cover" | .none => "none" | .scaleDown => "scale-down"

def unicodeBidi : UnicodeBidi → String
  | .normal => "normal" | .embed => "embed" | .isolate => "isolate" | .bidiOverride => "bidi-override"
  | .isolateOverride => "isolate-override" | .plaintext => "plaintext"

/-- The properties with their computed values, in the order of the profile, as longhands. -/
def values (c : Computed) : List (String × String) :=
  let edges := fun (name : String) (e : Edges) (f : Float → String) =>
    [(s!"{name}-top", f e.top), (s!"{name}-right", f e.right), (s!"{name}-bottom", f e.bottom), (s!"{name}-left", f e.left)]
  let bw := c.borderEdges
  let bc := color (c.borderColor.getD c.color)
  [("display", display c.display), ("width", length c.width), ("height", length c.height)] ++
  edges "margin" c.margin px ++ edges "padding" c.padding px ++
  [("color", color c.color),
   ("background-color", match c.background with | some b => color b | none => "rgba(0, 0, 0, 0)"),
   ("font-size", px c.fontSize), ("font-family", c.fontFamily),
   ("line-height", match c.lineHeightFactor with | some _ => "normal" | none => px c.lineHeight),
   ("visibility", if c.visible then "visible" else "hidden"),
   ("overflow", if c.clipOverflow then "hidden" else "visible"),
   ("text-decoration-line", if c.underline then "underline" else "none"),
   ("border-top-width", px bw.top), ("border-right-width", px bw.right),
   ("border-bottom-width", px bw.bottom), ("border-left-width", px bw.left)] ++
  ["top", "right", "bottom", "left"].map (fun s => (s!"border-{s}-style", borderStyle c.borderStyle)) ++
  ["top", "right", "bottom", "left"].map (fun s => (s!"border-{s}-color", bc)) ++
  [("border-spacing", if c.borderSpacingX == c.borderSpacingY then px c.borderSpacingX
      else px c.borderSpacingX ++ " " ++ px c.borderSpacingY),
   ("border-collapse", if c.borderCollapse then "collapse" else "separate"),
   ("caption-side", if c.captionBottom then "bottom" else "top"),
   ("vertical-align", verticalAlign c.verticalAlign),
   ("table-layout", if c.tableFixed then "fixed" else "auto"),
   ("min-width", match c.minWidth with | .auto => "auto" | l => length l),
   ("max-width", maxLength c.maxWidth),
   ("min-height", match c.minHeight with | .auto => "auto" | l => length l),
   ("max-height", maxLength c.maxHeight),
   ("object-fit", objectFit c.objectFit), ("text-align", textAlign c.textAlign),
   ("direction", if c.direction == .rtl then "rtl" else "ltr"),
   ("unicode-bidi", unicodeBidi c.unicodeBidi)]

/-- The answer of a page's `getComputedStyle` read: name U+0000 value U+0000 per property. -/
def text (c : Computed) : String :=
  (values c).foldl (fun acc (k, v) => acc ++ k ++ "\x00" ++ v ++ "\x00") ""

#guard (values {}).lookup "display" == some "inline"
#guard (values { color := ⟨1, 0, 0⟩ }).lookup "color" == some "rgb(255, 0, 0)"
#guard (values {}).lookup "background-color" == some "rgba(0, 0, 0, 0)"
#guard (values { width := .px 10 }).lookup "width" == some "10px"
#guard (values { width := .percent 0.5 }).lookup "width" == some "50%"

end L4Factoidal.Rendering.ComputedValues
