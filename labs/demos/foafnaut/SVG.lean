import Graphics
import GraphicsPrepared
import SVGPath
import SVGCurves
import SVGReferences
import SVGCSS
import SVGDash
import SVGDashUnits
import SVGStroke
import L4Factoidal.Math.Affine
import L4Factoidal.Tdb2.Format
import L4Factoidal.Rendering.FloatFormat
import L4Factoidal.Rendering.Scene
import L4Factoidal.XML.NamespaceView

/- Isolated strict SVG document reader, not SVG Tiny/full conformance.
   XML and expanded names come from the current Factoidal XML implementation.
   Geometry, paint inheritance, viewBox mapping, shader generation and reference
   sampling are Lean computations; hosts only transfer artifacts and pixels. -/
namespace NativeSVG

-- Bounded storage-backed profile, sized from generated 8/16-person scenes.
def maxInputChars : Nat := 1048576
def maxPrimitives : Nat := 49152
def maxDataFloats : Nat := 1048576
def maxInspectorNodes : Nat := 16384
open NativeGraphics
open L4Factoidal.XML
private def svgURI := "http://www.w3.org/2000/svg"
private def trim (s : String) : String := s.trimAscii.toString
private def error (s : String) : Except String α := .error s
private def need (value : Option α) (message : String) : Except String α :=
  match value with | some x => pure x | none => error message
private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\r" "\\r" |>.replace "\t" "\\t") ++ "\""
private def jsonArray (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def pow10 (n : Nat) : Float := (List.range n).foldl (fun x _ => x*10) 1

/-- Strict signed decimal/exponent lexer. Relative units and non-finite values
are errors; bounded magnitudes keep this profile within useful f32 precision. -/
def number (input : String) : Except String Float := do
  let s := trim input
  if s.length > 48 then error "numeric token exceeds 48 characters" else do
    let chars := s.toList
    let (negative, chars) := match chars with
      | '-'::rest => (true,rest) | '+'::rest => (false,rest) | _ => (false,chars)
    let (whole,rest) := chars.span Char.isDigit
    let (fraction,rest) := match rest with
      | '.'::tail => tail.span Char.isDigit | _ => ([],rest)
    if whole.isEmpty && fraction.isEmpty then throw s!"invalid SVG number: {s}"
    let (expNegative,expDigits,rest) := match rest with
      | 'e'::tail | 'E'::tail =>
        let (negative,tail) := match tail with
          | '-'::xs => (true,xs) | '+'::xs => (false,xs) | _ => (false,tail)
        let (digits,remaining) := tail.span Char.isDigit
        (negative,digits,remaining)
      | _ => (false,[],rest)
    if !rest.isEmpty then throw s!"invalid SVG number or unsupported unit: {s}"
    if (s.contains 'e' || s.contains 'E') && expDigits.isEmpty then throw "exponent requires digits"
    if whole.length+fraction.length > 24 || expDigits.length > 2 then throw "numeric precision exceeds profile bound"
    let exponent := (String.ofList expDigits).toNat?.getD 0
    if exponent > 12 then throw "numeric exponent exceeds profile bound"
    let integer := Float.ofNat ((String.ofList whole).toNat?.getD 0)
    let decimal := Float.ofNat ((String.ofList fraction).toNat?.getD 0) / pow10 fraction.length
    let unsigned := (integer+decimal) * (if expNegative then 1/pow10 exponent else pow10 exponent)
    let value := if negative then -unsigned else unsigned
    if !value.isFinite || value.abs > 1000000 then throw "numeric magnitude exceeds profile bound"
    return value
private def lengthNumber (input : String) : Except String Float :=
  let s := trim input
  number (if s.endsWith "px" then String.ofList (s.toList.take (s.length-2)) else s)
private def numbers (input : String) : Except String (List Float) := do
  let groups := input.splitOn ","
  if groups.any (fun g => (trim g).isEmpty) then throw "empty or trailing numeric list item"
  let parts := groups.flatMap fun g =>
    ((g.replace "\t" " " |>.replace "\n" " " |>.replace "\r" " ").splitOn " ").filter (· != "")
  parts.mapM number

/- Column-vector affine matrices: parent.compose local applies local first.
   Sampling uses the inverse CTM, so nonuniform scale/shear also transform
   local stroke outlines rather than merely scaling a stroke-width scalar. -/
abbrev Transform := L4Factoidal.Math.Affine2 Float
private def floatOps : L4Factoidal.Math.AffineScalarOps Float :=
  .float
private def identityTransform : Transform := L4Factoidal.Math.Affine2.identity floatOps
private def Transform.compose (p q : Transform) : Transform := L4Factoidal.Math.Affine2.compose floatOps p q
private def Transform.det (t : Transform) : Float := L4Factoidal.Math.Affine2.determinant floatOps t
private def Transform.inverse (t : Transform) : Transform :=
  -- A singular CTM paints nothing; its harmless identity record is never painted.
  (L4Factoidal.Math.Affine2.inverse? floatOps t).getD identityTransform
private def Transform.identity (t : Transform) : Bool :=
  t.a == 1 && t.b == 0 && t.c == 0 && t.d == 1 && t.e == 0 && t.f == 0
private def Transform.apply (t : Transform) (x y : Float) : Float × Float :=
  L4Factoidal.Math.Affine2.applyPoint floatOps t x y
private def checkedTransform (t : Transform) : Except String Transform := do
  let values (m : Transform) := [m.a,m.b,m.c,m.d,m.e,m.f]
  if !(values t).all (fun x => x.isFinite && x.abs <= 1000000000) || !t.det.isFinite then
    throw "transform matrix exceeds finite profile bound"
  if t.det != 0 && !(values t.inverse).all (fun x => x.isFinite && x.abs <= 1000000000) then
    throw "inverse transform exceeds finite profile bound"
  return t
private def transformFunction (name : String) (values : List Float) : Except String Transform := do
  let translate (x y : Float) : Transform := ⟨1,0,0,1,x,y⟩
  let rotate (degrees : Float) : Transform :=
    let angle := degrees*3.141592653589793/180
    ⟨angle.cos,angle.sin,-angle.sin,angle.cos,0,0⟩
  let result ← match name, values with
    | "matrix",[a,b,c,d,e,f] => pure (⟨a,b,c,d,e,f⟩ : Transform)
    | "translate",[x] => pure (translate x 0)
    | "translate",[x,y] => pure (translate x y)
    | "scale",[x] => pure (⟨x,0,0,x,0,0⟩ : Transform)
    | "scale",[x,y] => pure (⟨x,0,0,y,0,0⟩ : Transform)
    | "rotate",[a] => pure (rotate a)
    | "rotate",[a,x,y] => pure ((translate x y).compose (rotate a) |>.compose (translate (-x) (-y)))
    | "skewX",[a] => pure (⟨1,0,(a*3.141592653589793/180).tan,1,0,0⟩ : Transform)
    | "skewY",[a] => pure (⟨1,(a*3.141592653589793/180).tan,0,1,0,0⟩ : Transform)
    | _,_ => throw s!"unsupported transform function/arity: {name}"
  checkedTransform result
private def transformList (source : String) : Except String Transform := do
  let source := trim source
  if source.isEmpty then return identityTransform
  let parts := source.splitOn ")"
  if trim (parts.getLast!) != "" then throw "unterminated/invalid transform list"
  if parts.length > 33 then throw "transform list exceeds 32 functions"
  let mut result : Transform := identityTransform
  for (part,i) in parts.dropLast.zipIdx do
    let part := trim part
    let part := if i > 0 && part.startsWith "," then trim (String.ofList (part.toList.drop 1)) else part
    let [name,args] := part.splitOn "(" | throw "invalid transform syntax"
    let nextTransform ← transformFunction (trim name) (← numbers args)
    result ← checkedTransform (result.compose nextTransform)
  return result

/-- The transform of an element under `parent`, its CTM below the root mapping.
    SVG Tiny 1.2 §7.7.5: `ref(svg)` and `ref(svg, x, y)` are the whole value. The
    CTM of the element is then the root `viewBox` mapping and the translation by
    x and y, so the local transform is the inverse of `parent` and that
    translation. No user agent transform exists here, so the only effect is to
    leave the transforms of the ancestors out. -/
private def elementTransform (parent : Transform) (source : String) : Except String Transform := do
  let s := trim source
  if !s.startsWith "ref" then return ← transformList s
  let open_ := trim (s.drop 3).toString
  if !open_.startsWith "(" || !open_.endsWith ")" then throw "invalid ref transform syntax"
  let inner := trim ((open_.drop 1).toString.dropEnd 1).toString
  if !inner.startsWith "svg" then throw s!"unsupported ref transform: {source}"
  let rest := trim (inner.drop 3).toString
  let rest := if rest.startsWith "," then (rest.drop 1).toString else rest
  let offset : Transform ← match ← (if (trim rest).isEmpty then pure [] else numbers rest) with
    | [] => pure identityTransform
    | [x,y] => pure ⟨1,0,0,1,x,y⟩
    | _ => throw "ref(svg) takes no number or two numbers"
  if parent.det == 0 then throw "ref(svg) needs an invertible parent transform"
  checkedTransform (parent.inverse.compose offset)

abbrev Color := NativeGraphics.FloatRGB
private def rgb (r g b : Nat) : Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
private def hex (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat-'0'.toNat)
  else if c >= 'a' && c <= 'f' then some (c.toNat-'a'.toNat+10) else none
private def named : List (String × (Nat × Nat × Nat)) := [
  ("black",(0,0,0)),("silver",(192,192,192)),("gray",(128,128,128)),("white",(255,255,255)),
  ("maroon",(128,0,0)),("red",(255,0,0)),("purple",(128,0,128)),("fuchsia",(255,0,255)),
  ("green",(0,128,0)),("lime",(0,255,0)),("olive",(128,128,0)),("yellow",(255,255,0)),
  ("navy",(0,0,128)),("blue",(0,0,255)),("teal",(0,128,128)),("aqua",(0,255,255)),("orange",(255,165,0)),
  ("aliceblue",(240,248,255)),("antiquewhite",(250,235,215)),("aquamarine",(127,255,212)),("azure",(240,255,255)),
  ("beige",(245,245,220)),("bisque",(255,228,196)),("blanchedalmond",(255,235,205)),("blueviolet",(138,43,226)),
  ("brown",(165,42,42)),("burlywood",(222,184,135)),("cadetblue",(95,158,160)),("chartreuse",(127,255,0)),
  ("chocolate",(210,105,30)),("coral",(255,127,80)),("cornflowerblue",(100,149,237)),("cornsilk",(255,248,220)),
  ("crimson",(220,20,60)),("cyan",(0,255,255)),("darkblue",(0,0,139)),("darkcyan",(0,139,139)),
  ("darkgoldenrod",(184,134,11)),("darkgray",(169,169,169)),("darkgreen",(0,100,0)),("darkgrey",(169,169,169)),
  ("darkkhaki",(189,183,107)),("darkmagenta",(139,0,139)),("darkolivegreen",(85,107,47)),("darkorange",(255,140,0)),
  ("darkorchid",(153,50,204)),("darkred",(139,0,0)),("darksalmon",(233,150,122)),("darkseagreen",(143,188,143)),
  ("darkslateblue",(72,61,139)),("darkslategray",(47,79,79)),("darkslategrey",(47,79,79)),("darkturquoise",(0,206,209)),
  ("darkviolet",(148,0,211)),("deeppink",(255,20,147)),("deepskyblue",(0,191,255)),("dimgray",(105,105,105)),
  ("dimgrey",(105,105,105)),("dodgerblue",(30,144,255)),("firebrick",(178,34,34)),("floralwhite",(255,250,240)),
  ("forestgreen",(34,139,34)),("gainsboro",(220,220,220)),("ghostwhite",(248,248,255)),("gold",(255,215,0)),
  ("goldenrod",(218,165,32)),("greenyellow",(173,255,47)),("grey",(128,128,128)),("honeydew",(240,255,240)),
  ("hotpink",(255,105,180)),("indianred",(205,92,92)),("indigo",(75,0,130)),("ivory",(255,255,240)),
  ("khaki",(240,230,140)),("lavender",(230,230,250)),("lavenderblush",(255,240,245)),("lawngreen",(124,252,0)),
  ("lemonchiffon",(255,250,205)),("lightblue",(173,216,230)),("lightcoral",(240,128,128)),("lightcyan",(224,255,255)),
  ("lightgoldenrodyellow",(250,250,210)),("lightgray",(211,211,211)),("lightgreen",(144,238,144)),("lightgrey",(211,211,211)),
  ("lightpink",(255,182,193)),("lightsalmon",(255,160,122)),("lightseagreen",(32,178,170)),("lightskyblue",(135,206,250)),
  ("lightslategray",(119,136,153)),("lightslategrey",(119,136,153)),("lightsteelblue",(176,196,222)),("lightyellow",(255,255,224)),
  ("limegreen",(50,205,50)),("linen",(250,240,230)),("magenta",(255,0,255)),("mediumaquamarine",(102,205,170)),
  ("mediumblue",(0,0,205)),("mediumorchid",(186,85,211)),("mediumpurple",(147,112,219)),("mediumseagreen",(60,179,113)),
  ("mediumslateblue",(123,104,238)),("mediumspringgreen",(0,250,154)),("mediumturquoise",(72,209,204)),("mediumvioletred",(199,21,133)),
  ("midnightblue",(25,25,112)),("mintcream",(245,255,250)),("mistyrose",(255,228,225)),("moccasin",(255,228,181)),
  ("navajowhite",(255,222,173)),("oldlace",(253,245,230)),("olivedrab",(107,142,35)),("orangered",(255,69,0)),
  ("orchid",(218,112,214)),("palegoldenrod",(238,232,170)),("palegreen",(152,251,152)),("paleturquoise",(175,238,238)),
  ("palevioletred",(219,112,147)),("papayawhip",(255,239,213)),("peachpuff",(255,218,185)),("peru",(205,133,63)),
  ("pink",(255,192,203)),("plum",(221,160,221)),("powderblue",(176,224,230)),("rosybrown",(188,143,143)),
  ("royalblue",(65,105,225)),("saddlebrown",(139,69,19)),("salmon",(250,128,114)),("sandybrown",(244,164,96)),
  ("seagreen",(46,139,87)),("seashell",(255,245,238)),("sienna",(160,82,45)),("skyblue",(135,206,235)),
  ("slateblue",(106,90,205)),("slategray",(112,128,144)),("slategrey",(112,128,144)),("snow",(255,250,250)),
  ("springgreen",(0,255,127)),("steelblue",(70,130,180)),("tan",(210,180,140)),("thistle",(216,191,216)),
  ("tomato",(255,99,71)),("turquoise",(64,224,208)),("violet",(238,130,238)),("wheat",(245,222,179)),
  ("whitesmoke",(245,245,245)),("yellowgreen",(154,205,50))]
private def color (input : String) : Except String Color := do
  let s := (trim input).toLower
  if s.startsWith "#" then
    let digits ← need ((s.toList.drop 1).mapM hex) "invalid hex color"
    match digits with
    | [a,b,c] => return rgb (a*17) (b*17) (c*17)
    | [a,b,c,d,e,f] => return rgb (a*16+b) (c*16+d) (e*16+f)
    | _ => throw "hex colors require 3 or 6 digits"
  else if s.startsWith "rgb(" && s.endsWith ")" then
    let inside := String.ofList (s.toList.drop 4 |>.take (s.length-5))
    let parts := inside.splitOn "," |>.map trim
    if parts.length != 3 then throw "rgb() requires three comma-separated components"
    let percentages := parts.map (·.endsWith "%")
    if percentages.any id && !percentages.all id then throw "mixed rgb() component units unsupported"
    let components ← parts.mapM fun p => do
      let percent := p.endsWith "%"
      let value ← number (if percent then String.ofList (p.toList.take (p.length-1)) else p)
      pure (max 0 (min 1 (value/(if percent then 100 else 255))))
    match components with
    | [r,g,b] => return ⟨r,g,b⟩
    | _ => throw "rgb() component count"
  else
    match named.find? (fun item => item.1 == s) with
    | some (_,r,g,b) => return rgb r g b
    | none => throw s!"unsupported color: {input}"
abbrev Gradient := L4Factoidal.Rendering.Gradient
abbrev GradientStop := L4Factoidal.Rendering.GradientStop
abbrev GradientRecord := L4Factoidal.Rendering.GradientRecord
inductive Paint where
  | none | solid (color : Color) | current
  /-- A paint server as read from the document, for any primitive. -/
  | gradient (source : Gradient)
  /-- The server lowered for this primitive, at a word offset of the paint table. -/
  | gradientRecord (cursor : Nat) (record : GradientRecord)
  deriving Repr
inductive FillRule where | nonzero | evenodd
  deriving Repr, BEq
/-- A line has pieces whenever it has a stroke, so only a round cap needs a mark. -/
def LineCap.headerModeBit : LineCap → Nat
  | .round => 1
  | _ => 0
structure Style where
  fill : Paint := .solid (rgb 0 0 0)
  stroke : Paint := .none
  currentColor : Color := rgb 0 0 0
  strokeWidth : Float := 1
  dashArray : List NativeSVGDash.Length := []
  dashOffset : NativeSVGDash.Length := ⟨0,false⟩
  fillOpacity : Float := 1
  strokeOpacity : Float := 1
  visible : Bool := true
  rule : FillRule := .nonzero
  lineCap : LineCap := .butt
  lineJoin : LineJoin := .miter
  miterLimit : Float := 4
  deriving Repr
private def attr (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? (fun a => a.name.namespace_.isNone && a.name.localPart == key)).map (·.value)
/-- SVG 2 §8.9: percentage bases belong to the viewport's user space. -/
private structure LengthContext where
  width : Float
  height : Float
private def LengthContext.diagonal (c : LengthContext) : Float :=
  Float.sqrt ((c.width*c.width+c.height*c.height)/2)
private def relativeLength (source : String) (base : Float) : Except String Float := do
  let s := trim source
  if s.endsWith "%" then
    pure ((← number (String.ofList (s.toList.take (s.length-1))))/100*base)
  else lengthNumber s

private def common := ["id","fill","stroke","color","fill-opacity","stroke-opacity","stroke-width",
  "stroke-linecap","stroke-linejoin","stroke-miterlimit","fill-rule","stroke-dasharray","stroke-dashoffset",
  "display","visibility","stop-color","stop-opacity","solid-color","solid-opacity"]
/-- SVG Tiny 1.2 §11.13 and §11.16: elements that define a paint and draw nothing. -/
private def paintServers := ["linearGradient","radialGradient","solidColor"]
private def validateAttrs (tag : String) (attrs : List NamespaceAttribute) (extra : List String) : Except String Unit := do
  for a in attrs do
    if let some uri := a.name.namespace_ then
      if uri == svgURI || (uri == "http://www.w3.org/1999/xlink" && !(["use","linearGradient","radialGradient"].contains tag && a.name.localPart == "href")) ||
          (uri == "http://www.w3.org/XML/1998/namespace" && !["lang","space","base"].contains a.name.localPart) then
        throw s!"qualified attribute unsupported on {tag}: {a.name.localPart}"
    else if !(common++extra).contains a.name.localPart then throw s!"unsupported attribute on {tag}: {a.name.localPart}"
private def cssProperties := (common.filter (· != "id")) ++ ["opacity","overflow"]
private def sheetProperties := cssProperties ++ ["width","height"]
private def displaySuppressed (attrs : List NamespaceAttribute) : Bool :=
  (attr attrs "display").any (fun value => (trim value).toLower == "none")
private def cssAttribute (d : NativeSVGCSS.Declaration) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=d.property},value:=d.value}
private def applyCSSWith (validate : NativeSVGCSS.Declaration → Except String Unit) (rules : List NativeSVGCSS.Rule)
    (tag : String) (attrs : List NamespaceAttribute) (nested : Bool := false) : Except String (List NamespaceAttribute) := do
  let presentation := attrs.filterMap fun a =>
    if a.name.namespace_.isNone && cssProperties.contains a.name.localPart then
      some ({property:=a.name.localPart,value:=a.value} : NativeSVGCSS.Declaration) else none
  let inlineStyle ← NativeSVGCSS.parseDeclarations sheetProperties ((attr attrs "style").getD "")
  let ignoredDimension := fun (d : NativeSVGCSS.Declaration) =>
    (["use","symbol"].contains tag || (tag == "svg" && nested)) && ["width","height"].contains d.property
  let inlineStyle := inlineStyle.filter (!ignoredDimension ·)
  let rules := rules.map fun rule => {rule with declarations:=rule.declarations.filter (!ignoredDimension ·)}
  let winning ← NativeSVGCSS.cascade validate tag presentation rules inlineStyle
  pure (attrs.filter (fun a => !(a.name.namespace_.isNone && (cssProperties.contains a.name.localPart || a.name.localPart=="style"))) ++ winning.map cssAttribute)

/-- Document data that a paint reference needs. -/
private structure PaintContext where
  references : NativeSVGReferences.Index
  rules : List NativeSVGCSS.Rule
  document : NamespaceNode

/-- Attributes of an element that a paint server depends on, after the cascade.
    Values are checked where they are read, so that an unrelated property of an
    ancestor does not refuse the paint. -/
private def serverAttrs (paints : PaintContext) (tag : String) (attrs : List NamespaceAttribute) :
    Except String (List NamespaceAttribute) :=
  applyCSSWith (fun _ => pure ()) paints.rules tag attrs

/-- Attributes of the SVG ancestors of the element at `path`, nearest first. A
    paint server takes inherited values from where it stands, not from where it
    is used (SVG Tiny 1.2 §6.7). -/
private def ancestorAttrs (paints : PaintContext) (path : List Nat) :
    Except String (List (List NamespaceAttribute)) := do
  let mut node := paints.document
  let mut chain : List (List NamespaceAttribute) := []
  for index in path do
    match node with
    | .other _ => throw "paint server path enters a non-element"
    | .element name attrs children =>
      if name.namespace_ == some svgURI then
        chain := (← serverAttrs paints name.localPart attrs) :: chain
      else chain := []
      let some child := children[index]? | throw "paint server path is outside the document"
      node := child
  return chain

/-- The `color` property: inherited, with black as this reader's initial value. -/
private def computedColor : List (List NamespaceAttribute) → Except String Color
  | [] => pure (rgb 0 0 0)
  | attrs::rest =>
    match attr attrs "color" with
    | none => computedColor rest
    | some value =>
      if ["inherit","currentcolor"].contains (trim value).toLower then computedColor rest
      else color value

/-- A property that does not inherit unless its value is `inherit`. -/
private def computedProperty (key : String) (initial : α)
    (read : String → List (List NamespaceAttribute) → Except String α) :
    List (List NamespaceAttribute) → Except String α
  | [] => pure initial
  | attrs::rest =>
    match attr attrs key with
    | none => pure initial
    | some value =>
      if trim value == "inherit" then computedProperty key initial read rest
      else read value (attrs::rest)

private def paintColor (source : String) (chain : List (List NamespaceAttribute)) : Except String Color :=
  if (trim source).toLower == "currentcolor" then computedColor chain else color source
private def paintOpacity (source : String) (_ : List (List NamespaceAttribute)) : Except String Float := do
  return max 0 (min 1 (← number source))
private def renderingColor (c : Color) : L4Factoidal.Rendering.Color := ⟨c.r,c.g,c.b⟩

/-- SVG Tiny 1.2 §11.16: a number or a percentage; clamping is in `normalizeStops`. -/
private def stopOffset (source : Option String) : Except String Float := do
  let some source := source | return 0
  let s := trim source
  if s.endsWith "%" then
    return (← number (String.ofList (s.toList.take (s.length-1))))/100
  number s

private def readStops (paints : PaintContext) (chain : List (List NamespaceAttribute))
    (children : List NamespaceNode) : Except String (List GradientStop) := do
  let mut stops : Array GradientStop := #[]
  for child in children do
    let .element name raw _ := child | continue
    if name.namespace_ != some svgURI || name.localPart != "stop" then continue
    if stops.size >= L4Factoidal.Rendering.maxGradientStops then
      throw s!"gradient stop count exceeds {L4Factoidal.Rendering.maxGradientStops}"
    let attrs ← serverAttrs paints "stop" raw
    let own := attrs::chain
    stops := stops.push {
      offset := ← stopOffset (attr attrs "offset")
      color := renderingColor (← computedProperty "stop-color" (rgb 0 0 0) paintColor own)
      opacity := ← computedProperty "stop-opacity" 1 paintOpacity own }
  return L4Factoidal.Rendering.normalizeStops stops.toList

private structure ServerLink where
  entry : NativeSVGReferences.Entry
  tag : String
  attrs : List NamespaceAttribute
  children : List NamespaceNode

/-- SVG Tiny 1.2 §11.15: the gradient, then the gradients its `xlink:href` chain
    names. A target that is not a gradient ends the chain; a cycle is refused. -/
private def gradientChain (paints : PaintContext) (start : String) : Except String (List ServerLink) := do
  let mut links : Array ServerLink := #[]
  let mut seen : List String := []
  let mut next := some start
  for _ in [:33] do
    let some id := next | return links.toList
    if seen.contains id then throw s!"gradient xlink:href cycle at {id}"
    seen := id::seen
    let some entry := paints.references.get? id | return links.toList
    let .element name raw children := entry.node | return links.toList
    if name.namespace_ != some svgURI || !["linearGradient","radialGradient"].contains name.localPart then
      return links.toList
    let attrs ← serverAttrs paints name.localPart raw
    let extra := ["x1","y1","x2","y2","cx","cy","r","gradientUnits","gradientTransform","href"] ++
      (if (attr attrs "spreadMethod").any (trim · == "pad") then ["spreadMethod"] else [])
    validateAttrs name.localPart attrs extra
    links := links.push {entry,tag:=name.localPart,attrs,children}
    next := match NativeSVGReferences.href attrs with
      | none => none
      | some source => (NativeSVGReferences.fragment source paints.references.documentURL entry.parentBase).toOption.join
  throw "gradient xlink:href chain exceeds 32"

/-- SVG Tiny 1.2 §11.15: a percentage is of the viewport in user space, and of
    the bounding box (where 100% is 1) in bounding box units. -/
private def gradientLength (lengths : LengthContext) (boundingBox : Bool) (key source : String) : Except String Float := do
  let base := if ["x1","x2","cx"].contains key then lengths.width
    else if ["y1","y2","cy"].contains key then lengths.height else lengths.diagonal
  relativeLength source (if boundingBox then 1 else base)

private def readGradient (lengths : LengthContext) (paints : PaintContext)
    (fallback : L4Factoidal.Rendering.FallbackPaint) (id : String) : Except String Gradient := do
  let links ← gradientChain paints id
  let some first := links.head? | throw "paint server is not a gradient"
  let value := fun (key : String) => links.findSome? (attr ·.attrs key)
  let units := (value "gradientUnits").map trim |>.getD "objectBoundingBox"
  if !["objectBoundingBox","userSpaceOnUse"].contains units then
    throw s!"unsupported attribute on {first.tag}: gradientUnits"
  let boundingBox := units == "objectBoundingBox"
  -- A coordinate comes only from a gradient of the same kind.
  let coordinate := fun (key fallback : String) =>
    gradientLength lengths boundingBox key
      ((links.filter (·.tag == first.tag) |>.findSome? (attr ·.attrs key)).getD fallback)
  let shape ← if first.tag == "linearGradient" then
      pure (L4Factoidal.Rendering.GradientShape.linear (← coordinate "x1" "0%") (← coordinate "y1" "0%")
        (← coordinate "x2" "100%") (← coordinate "y2" "0%"))
    else do
      let r ← coordinate "r" "50%"
      if r < 0 then throw "negative radialGradient r"
      pure (.radial (← coordinate "cx" "50%") (← coordinate "cy" "50%") r)
  let transform ← checkedTransform (← transformList ((value "gradientTransform").getD ""))
  -- The first gradient of the chain that has stops gives all of them.
  let holder := links.find? fun link => link.children.any fun
    | .element name _ _ => name.namespace_ == some svgURI && name.localPart == "stop"
    | _ => false
  let stops ← match holder with
    | none => pure []
    | some link => do
      let ancestors ← ancestorAttrs paints link.entry.path
      readStops paints (link.attrs::ancestors) link.children
  return {shape,boundingBoxUnits:=boundingBox,transform,stops,fallback}

/-- SVG Tiny 1.2 §11.13: a solid colour is a one-stop gradient in user space. -/
private def readSolidColor (paints : PaintContext) (entry : NativeSVGReferences.Entry)
    (raw : List NamespaceAttribute) : Except String Gradient := do
  let attrs ← serverAttrs paints "solidColor" raw
  let own := attrs :: (← ancestorAttrs paints entry.path)
  return {shape:=.linear 0 0 1 0,boundingBoxUnits:=false,stops:=[{
    offset:=0
    color:=renderingColor (← computedProperty "solid-color" (rgb 0 0 0) paintColor own)
    opacity:=← computedProperty "solid-opacity" 1 paintOpacity own}]}

private def readPaint (lengths : LengthContext) (paints : PaintContext) (source : String) : Except String Paint := do
  let s := trim source
  if s.startsWith "url(" then
    let pieces := s.splitOn ")"
    let [target, fallback] := pieces | throw "unsupported paint URL syntax"
    let target := trim (String.ofList (target.toList.drop 4))
    let target := if (target.startsWith "\"" && target.endsWith "\"") ||
        (target.startsWith "'" && target.endsWith "'") then
        String.ofList (target.toList.drop 1 |>.take (target.length-2)) else target
    if !target.startsWith "#" || target.length < 2 then throw "external/unsupported paint URL"
    let id := String.ofList (target.toList.drop 1)
    if !id.toList.all (fun c => c.isAlphanum && c.toNat < 128 || ['_','-',':','.'].contains c) then
      throw "unsupported paint fragment syntax/encoding"
    let fallback := trim fallback
    let fallbackPaint : Paint ←
      if fallback.isEmpty || fallback.toLower == "none" then pure .none
      else if fallback.toLower == "currentcolor" then pure .current
      else Paint.solid <$> color fallback
    let rendered : L4Factoidal.Rendering.FallbackPaint := match fallbackPaint with
      | .current => .current
      | .solid c => .solid (renderingColor c)
      | _ => .none
    -- §11.3: a target that is not a paint server gives the fallback.
    match paints.references.get? id with
    | some entry =>
      match entry.node with
      | .element name raw _ =>
        if name.namespace_ != some svgURI || !paintServers.contains name.localPart then pure fallbackPaint
        else if name.localPart == "solidColor" then
          pure (.gradient {← readSolidColor paints entry raw with fallback:=rendered})
        else pure (.gradient (← readGradient lengths paints rendered id))
      | _ => pure fallbackPaint
    | none => pure fallbackPaint
  else if s.toLower == "none" then pure .none
  else if s.toLower == "currentcolor" then pure .current
  else Paint.solid <$> color s
private def inheritedNumber (lengths : LengthContext) (attrs : List NamespaceAttribute) (key : String) (old : Float) : Except String Float :=
  match attr attrs key with
  | none => pure old
  | some value => if trim value == "inherit" then pure old else
      if key == "stroke-width" then relativeLength value lengths.diagonal else number value
private def dashArray (lengths : LengthContext) (source : String) : Except String (List NativeSVGDash.Length) := do
  if trim source == "none" then return []
  let groups := source.splitOn ","
  if groups.any (fun g => (trim g).isEmpty) then throw "empty dash list item"
  let tokens := groups.flatMap (fun g => (g.splitOn " " |>.flatMap (·.splitOn "\t") |>.flatMap (·.splitOn "\n") |>.flatMap (·.splitOn "\r")).filter (· != ""))
  if tokens.isEmpty then throw "empty dash list"
  if tokens.length > 64 then throw "dash pattern exceeds 64 entries"
  NativeSVGDash.normalizeLengths (← tokens.mapM fun token => do
    pure {value:= ← relativeLength token lengths.diagonal,percentage:=(trim token).endsWith "%"})
private def readStyle (lengths : LengthContext) (paints : PaintContext) (attrs : List NamespaceAttribute) (parent : Style) : Except String Style := do
  let mut style := parent
  if let some value := attr attrs "color" then
    if !["inherit","currentcolor"].contains (trim value).toLower then style := {style with currentColor:= ← color value}
  if let some value := attr attrs "fill" then
    if trim value != "inherit" then style := {style with fill:= ← readPaint lengths paints value}
  if let some value := attr attrs "stroke" then
    if trim value != "inherit" then style := {style with stroke:= ← readPaint lengths paints value}
  if let some value := attr attrs "stroke-dasharray" then
    if trim value != "inherit" then
      style := {style with dashArray:= ← dashArray lengths value}
  if let some value := attr attrs "stroke-dashoffset" then
    if trim value != "inherit" then
      match relativeLength value lengths.diagonal with
      | .ok offset => style := {style with dashOffset:={value:=offset,percentage:=(trim value).endsWith "%"}}
      | .error _ => throw s!"unsupported stroke-dashoffset: {value}"
  if let some value := attr attrs "visibility" then
    match (trim value).toLower with
    | "inherit" => pure ()
    | "visible" => style := {style with visible:=true}
    | "hidden" | "collapse" => style := {style with visible:=false}
    | _ => throw s!"unsupported visibility: {value}"
  let width ← inheritedNumber lengths attrs "stroke-width" parent.strokeWidth
  if width < 0 then throw "negative stroke-width"
  let fillOpacity ← inheritedNumber lengths attrs "fill-opacity" parent.fillOpacity
  let strokeOpacity ← inheritedNumber lengths attrs "stroke-opacity" parent.strokeOpacity
  style := {style with strokeWidth:=width,fillOpacity:=max 0 (min 1 fillOpacity),strokeOpacity:=max 0 (min 1 strokeOpacity)}
  if let some value := attr attrs "fill-rule" then
    match trim value with
    | "inherit" => pure () | "nonzero" => style := {style with rule:=.nonzero}
    | "evenodd" => style := {style with rule:=.evenodd} | _ => throw "unsupported fill-rule"
  if let some value := attr attrs "stroke-linecap" then
    match trim value with
    | "inherit" => pure () | "butt" => style := {style with lineCap:=.butt}
    | "round" => style := {style with lineCap:=.round}
    | "square" => style := {style with lineCap:=.square}
    | _ => throw s!"unsupported stroke-linecap: {value}"
  if let some value := attr attrs "stroke-linejoin" then
    match trim value with
    | "inherit" => pure () | "miter" => style := {style with lineJoin:=.miter}
    | "round" => style := {style with lineJoin:=.round}
    | "bevel" => style := {style with lineJoin:=.bevel}
    | _ => throw s!"unsupported stroke-linejoin: {value}"
  if let some value := attr attrs "stroke-miterlimit" then
    if trim value != "inherit" then
      -- SVG Tiny 1.2 §11.4: the value is a number of at least 1.
      match number value with
      | .ok limit => if limit >= 1 then style := {style with miterLimit:=limit}
                     else throw s!"unsupported stroke-miterlimit: {value}"
      | .error _ => throw s!"unsupported stroke-miterlimit: {value}"
  return style
private def applyCSS (lengths : LengthContext) (paints : PaintContext) (rules : List NativeSVGCSS.Rule)
    (tag : String) (attrs : List NamespaceAttribute) (nested : Bool := false) : Except String (List NamespaceAttribute) :=
  let validate := fun (d : NativeSVGCSS.Declaration) => do
    if d.property == "opacity" then let _ ← number d.value; pure ()
    else if d.property == "overflow" then
      if !["hidden","visible","scroll","auto"].contains (trim d.value) then throw "unsupported overflow"
    else if ["width","height"].contains d.property then throw "unsupported CSS geometry property"
    else let _ ← readStyle lengths paints [cssAttribute d] {}; pure ()
  applyCSSWith validate rules tag attrs nested

private def geometryNumber (lengths : LengthContext) (attrs : List NamespaceAttribute) (key : String) (fallback : Float := 0) : Except String Float :=
  match attr attrs key with | none => pure fallback | some s => relativeLength s (if ["x","x1","x2","cx","width","rx"].contains key then lengths.width
    else if ["y","y1","y2","cy","height","ry"].contains key then lengths.height else lengths.diagonal)
inductive Geometry (contourType : Type := NativeSVGPath.Contour) where
  | rect (x y width height : Float)
  | circle (cx cy radius : Float)
  | ellipse (cx cy rx ry : Float)
  | line (x1 y1 x2 y2 : Float)
  | polygon (points : List Point)
  | path (contours : List contourType)
  deriving Repr
abbrev BackendGeometry := Geometry NativeSVGPath.LinearContour

def Geometry.rectRecordTag : Nat := 1
def Geometry.circleRecordTag : Nat := 2
def Geometry.ellipseRecordTag : Nat := 3
def Geometry.lineRecordTag : Nat := 4
def Geometry.polygonRecordTag : Nat := 5
def Geometry.pathRecordTag : Nat := 6
def Geometry.recordTagCount : BackendGeometry → Nat × Nat
  | .rect .. => (rectRecordTag,0)
  | .circle .. => (circleRecordTag,0)
  | .ellipse .. => (ellipseRecordTag,0)
  | .line .. => (lineRecordTag,0)
  | .polygon points => (polygonRecordTag,points.length)
  | .path contours => (pathRecordTag,(NativeSVGPath.edges contours).length)
/-- An exact rectangular clip in its own Float coordinate frame. SVG 2 §8
    viewport clipping is tested through the inverse CTM, never a world AABB. -/
structure ClipRect where
  x : Float
  y : Float
  width : Float
  height : Float
  transform : Transform := identityTransform
  deriving Repr

def ClipRect.lowerUnder (parent : Transform) (clip : ClipRect) : ClipRect :=
  {clip with transform:=parent.compose clip.transform}

/-- Zero-area or singular clips have empty coverage. Invalid numeric values
    also cannot produce coverage or a divide by zero. -/
def ClipRect.valid (clip : ClipRect) : Bool :=
  let inverse := clip.transform.inverse
  [clip.x,clip.y,clip.width,clip.height,clip.transform.a,clip.transform.b,
    clip.transform.c,clip.transform.d,clip.transform.e,clip.transform.f].all
      (fun value => value.isFinite && value.abs <= 1000000000) &&
    clip.width > 0 && clip.height > 0 && clip.transform.det != 0 &&
    [inverse.a,inverse.b,inverse.c,inverse.d,inverse.e,inverse.f].all
      (fun value => value.isFinite && value.abs <= 1000000000)

def ClipRect.contains (clip : ClipRect) (x y : Float) : Bool :=
  if !clip.valid then false else
    let point := clip.transform.inverse.apply x y
    clip.x <= point.1 && point.1 <= clip.x+clip.width &&
      clip.y <= point.2 && point.2 <= clip.y+clip.height

structure Primitive (contourType : Type := NativeSVGPath.Contour) where
  geometry : Geometry contourType
  style : Style
  opacity : Float := 1
  transform : Transform := identityTransform
  dashParts : Option (List NativeSVGStroke.Piece) := none
  /-- Ordered enclosing SVG group IDs; `none` records an anonymous group.
      Geometry and transforms are still lowered to painter-ordered leaves. -/
  groupPath : List (Option String) := []
  clips : List ClipRect := []
  pathLength : Option Float := none
  deriving Repr

abbrev BackendPrimitive := Primitive NativeSVGPath.LinearContour

def Primitive.lowerUnder (parent : Transform) (groups : List (Option String))
    (primitive : Primitive) : Primitive := Id.run do
  let transformed := {primitive with
    transform := parent.compose primitive.transform
    clips := primitive.clips.map (ClipRect.lowerUnder parent)}
  return {transformed with groupPath := groups ++ primitive.groupPath}

theorem Primitive.lowerUnder_preserves_rendering_data (parent : Transform)
    (groups : List (Option String)) (items : List Primitive) :
    (items.map (Primitive.lowerUnder parent groups)).map
      (fun p => (p.geometry, p.style, p.opacity, p.transform, p.dashParts)) =
    items.map (fun p =>
      (p.geometry, p.style, p.opacity, parent.compose p.transform, p.dashParts)) := by
  simp [Primitive.lowerUnder]

theorem Primitive.lowerUnder_records_group_path (parent : Transform)
    (groups : List (Option String)) (primitive : Primitive) :
    (Primitive.lowerUnder parent groups primitive).groupPath = groups ++ primitive.groupPath := by
  simp [Primitive.lowerUnder]

def Primitive.addClip (clip : ClipRect) (primitive : Primitive) : Primitive :=
  {primitive with clips:=clip :: primitive.clips}

theorem Primitive.lowerUnder_clip_frames (parent : Transform)
    (groups : List (Option String)) (primitive : Primitive) :
    (primitive.lowerUnder parent groups).clips =
      primitive.clips.map (ClipRect.lowerUnder parent) := by
  simp [Primitive.lowerUnder]

/- Retained SVG tree. Transforms remain local here and are composed only in the
   compatibility lowering used by the current flat renderer. -/
inductive DisplayNode where
  | paint (primitive : Primitive)
  | group (id : Option String) (transform : Transform) (children : List DisplayNode)
  | clipped (id : Option String) (contentTransform : Transform) (clip : ClipRect) (children : List DisplayNode)
  deriving Repr

mutual
  def DisplayNode.paintCount : DisplayNode → Nat
    | .paint _ => 1
    | .group _ _ children | .clipped _ _ _ children => DisplayNode.paintCountList children
  termination_by node => sizeOf node

  def DisplayNode.paintCountList : List DisplayNode → Nat
    | [] => 0
    | node :: rest => node.paintCount + DisplayNode.paintCountList rest
  termination_by nodes => sizeOf nodes
end

mutual
  def DisplayNode.nodeCount : DisplayNode → Nat
    | .paint _ => 1
    | .group _ _ children | .clipped _ _ _ children => 1 + DisplayNode.listNodeCount children
  termination_by node => sizeOf node

  def DisplayNode.listNodeCount : List DisplayNode → Nat
    | [] => 0
    | node :: rest => node.nodeCount + DisplayNode.listNodeCount rest
  termination_by nodes => sizeOf nodes
end

mutual
  def DisplayNode.lower (parent : Transform) (groups : List (Option String)) :
      DisplayNode → List Primitive
    | .paint primitive => [primitive.lowerUnder parent groups]
    | .group id transform children =>
        DisplayNode.lowerList (parent.compose transform) (groups ++ [id]) children
    | .clipped id contentTransform clip children =>
        (DisplayNode.lowerList (parent.compose contentTransform) (groups ++ [id]) children).map
          (Primitive.addClip (clip.lowerUnder parent))
  termination_by node => sizeOf node

  def DisplayNode.lowerList (parent : Transform) (groups : List (Option String)) :
      List DisplayNode → List Primitive
    | [] => []
    | node :: rest => node.lower parent groups ++ DisplayNode.lowerList parent groups rest
  termination_by nodes => sizeOf nodes
end


/-- Same painter-ordered primitives as `lower`; sibling traversal uses a reverse
    accumulator. Recursive calls follow group depth, bounded by the parser at 32. -/
def DisplayNode.lowerTR (parent : Transform) (groups : List (Option String))
    (node : DisplayNode) : List Primitive :=
  match node with
  | .paint primitive => [primitive.lowerUnder parent groups]
  | .group id transform children =>
      (children.foldl (fun acc child =>
        (child.lowerTR (parent.compose transform) (groups ++ [id])).reverse ++ acc) []).reverse
  | .clipped id contentTransform clip children =>
      ((children.foldl (fun acc child =>
        (child.lowerTR (parent.compose contentTransform) (groups ++ [id])).reverse ++ acc) []).reverse).map
          (Primitive.addClip (clip.lowerUnder parent))
termination_by sizeOf node

/-- Exact paint count with a sibling fold; `paintCountTR_eq` retains the reference meaning. -/
def DisplayNode.paintCountTR (node : DisplayNode) : Nat :=
  match node with
  | .paint _ => 1
  | .group _ _ children | .clipped _ _ _ children => children.foldl (fun acc child => acc + child.paintCountTR) 0
termination_by sizeOf node

/-- Exact inspector node count with sibling folds, including each group itself. -/
def DisplayNode.nodeCountTR (node : DisplayNode) : Nat :=
  match node with
  | .paint _ => 1
  | .group _ _ children | .clipped _ _ _ children => children.foldl (fun acc child => acc + child.nodeCountTR) 1
termination_by sizeOf node

theorem DisplayNode.paintCountTR_eq (node : DisplayNode) :
    node.paintCountTR = node.paintCount := by
  refine DisplayNode.rec
    (motive_1 := fun node => node.paintCountTR = node.paintCount)
    (motive_2 := fun nodes => ∀ acc,
      nodes.foldl (fun acc child => acc + child.paintCountTR) acc =
        acc + DisplayNode.paintCountList nodes)
    ?_ ?_ ?_ ?_ ?_ node
  · intro primitive
    simp [DisplayNode.paintCountTR, DisplayNode.paintCount]
  · intro id transform children ih
    simpa [DisplayNode.paintCountTR, DisplayNode.paintCount] using ih 0
  · intro id transform clip children ih
    simpa [DisplayNode.paintCountTR, DisplayNode.paintCount] using ih 0
  · intro acc
    simp [DisplayNode.paintCountList]
  · intro head tail ihHead ihTail acc
    simp [List.foldl_cons, ihHead, ihTail, DisplayNode.paintCountList, Nat.add_assoc]

theorem DisplayNode.nodeCountTR_eq (node : DisplayNode) :
    node.nodeCountTR = node.nodeCount := by
  refine DisplayNode.rec
    (motive_1 := fun node => node.nodeCountTR = node.nodeCount)
    (motive_2 := fun nodes => ∀ acc,
      nodes.foldl (fun acc child => acc + child.nodeCountTR) acc =
        acc + DisplayNode.listNodeCount nodes)
    ?_ ?_ ?_ ?_ ?_ node
  · intro primitive
    simp [DisplayNode.nodeCountTR, DisplayNode.nodeCount]
  · intro id transform children ih
    simpa [DisplayNode.nodeCountTR, DisplayNode.nodeCount] using ih 1
  · intro id transform clip children ih
    simpa [DisplayNode.nodeCountTR, DisplayNode.nodeCount] using ih 1
  · intro acc
    simp [DisplayNode.listNodeCount]
  · intro head tail ihHead ihTail acc
    simp [List.foldl_cons, ihHead, ihTail, DisplayNode.listNodeCount, Nat.add_assoc]

theorem DisplayNode.lowerTR_eq (node : DisplayNode) :
    ∀ parent groups, node.lowerTR parent groups = node.lower parent groups := by
  refine DisplayNode.rec
    (motive_1 := fun node => ∀ parent groups,
      node.lowerTR parent groups = node.lower parent groups)
    (motive_2 := fun (nodes : List DisplayNode) => ∀ (parent : Transform) (groups : List (Option String)) (acc : List Primitive),
      (nodes.foldl (fun acc child => (child.lowerTR parent groups).reverse ++ acc) acc).reverse =
        acc.reverse ++ DisplayNode.lowerList parent groups nodes)
    ?_ ?_ ?_ ?_ ?_ node
  · intro primitive parent groups
    simp [DisplayNode.lowerTR, DisplayNode.lower]
  · intro id transform children ih parent groups
    simpa [DisplayNode.lowerTR, DisplayNode.lower] using
      ih (parent.compose transform) (groups ++ [id]) []
  · intro id transform clip children ih parent groups
    simpa only [DisplayNode.lowerTR, DisplayNode.lower, List.reverse_nil, List.nil_append] using
      congrArg (List.map (Primitive.addClip (clip.lowerUnder parent)))
        (ih (parent.compose transform) (groups ++ [id]) [])
  · intro parent groups acc
    simp [DisplayNode.lowerList]
  · intro head tail ihHead ihTail parent groups acc
    simp only [List.foldl_cons]
    rw [ihTail, List.reverse_append, List.reverse_reverse, ihHead]
    simp only [DisplayNode.lowerList, List.append_assoc]

/-- Reverse-accumulator sibling lowering using the fast recursive group twin. -/
def DisplayNode.lowerListTR (parent : Transform) (groups : List (Option String))
    (nodes : List DisplayNode) : List Primitive :=
  (nodes.foldl (fun acc node => (node.lowerTR parent groups).reverse ++ acc) []).reverse

private theorem lowerFold_eq (nodes : List DisplayNode) (parent : Transform)
    (groups : List (Option String)) (acc : List Primitive) :
    (nodes.foldl (fun acc node => (node.lowerTR parent groups).reverse ++ acc) acc).reverse =
      acc.reverse ++ DisplayNode.lowerList parent groups nodes := by
  induction nodes generalizing acc with
  | nil => simp [DisplayNode.lowerList]
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih, List.reverse_append, List.reverse_reverse, DisplayNode.lowerTR_eq]
      simp only [DisplayNode.lowerList, List.append_assoc]

/-- Exact total paint count over arbitrarily wide sibling lists. -/
def DisplayNode.paintCountListTR (nodes : List DisplayNode) : Nat :=
  nodes.foldl (fun acc node => acc + node.paintCountTR) 0

private theorem paintCountFold_eq (nodes : List DisplayNode) (acc : Nat) :
    nodes.foldl (fun acc node => acc + node.paintCountTR) acc =
      acc + DisplayNode.paintCountList nodes := by
  induction nodes generalizing acc with
  | nil => simp [DisplayNode.paintCountList]
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih, DisplayNode.paintCountTR_eq]
      simp only [DisplayNode.paintCountList, Nat.add_assoc]

/-- Exact total inspector count over arbitrarily wide sibling lists. -/
def DisplayNode.listNodeCountTR (nodes : List DisplayNode) : Nat :=
  nodes.foldl (fun acc node => acc + node.nodeCountTR) 0

private theorem nodeCountFold_eq (nodes : List DisplayNode) (acc : Nat) :
    nodes.foldl (fun acc node => acc + node.nodeCountTR) acc =
      acc + DisplayNode.listNodeCount nodes := by
  induction nodes generalizing acc with
  | nil => simp [DisplayNode.listNodeCount]
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rw [ih, DisplayNode.nodeCountTR_eq]
      simp only [DisplayNode.listNodeCount, Nat.add_assoc]

@[csimp] theorem DisplayNode.lower_eq_lowerTR : DisplayNode.lower = DisplayNode.lowerTR := by
  funext parent groups node
  exact (DisplayNode.lowerTR_eq node parent groups).symm

@[csimp] theorem DisplayNode.lowerList_eq_lowerListTR : DisplayNode.lowerList = DisplayNode.lowerListTR := by
  funext parent groups nodes
  exact (show DisplayNode.lowerListTR parent groups nodes = DisplayNode.lowerList parent groups nodes by
    simpa only [DisplayNode.lowerListTR, List.reverse_nil, List.nil_append] using
      lowerFold_eq nodes parent groups []).symm

@[csimp] theorem DisplayNode.paintCount_eq_paintCountTR : DisplayNode.paintCount = DisplayNode.paintCountTR := by
  funext node
  exact (DisplayNode.paintCountTR_eq node).symm

@[csimp] theorem DisplayNode.paintCountList_eq_paintCountListTR : DisplayNode.paintCountList = DisplayNode.paintCountListTR := by
  funext nodes
  exact (show DisplayNode.paintCountListTR nodes = DisplayNode.paintCountList nodes by
    simpa only [DisplayNode.paintCountListTR, Nat.zero_add] using paintCountFold_eq nodes 0).symm

@[csimp] theorem DisplayNode.nodeCount_eq_nodeCountTR : DisplayNode.nodeCount = DisplayNode.nodeCountTR := by
  funext node
  exact (DisplayNode.nodeCountTR_eq node).symm

@[csimp] theorem DisplayNode.listNodeCount_eq_listNodeCountTR : DisplayNode.listNodeCount = DisplayNode.listNodeCountTR := by
  funext nodes
  exact (show DisplayNode.listNodeCountTR nodes = DisplayNode.listNodeCount nodes by
    simpa only [DisplayNode.listNodeCountTR, Nat.zero_add] using nodeCountFold_eq nodes 0).symm


def DisplayNode.lowerFromRoot (node : DisplayNode) : List Primitive :=
  node.lower identityTransform []

def DisplayNode.lowerFromRootList (nodes : List DisplayNode) : List Primitive :=
  DisplayNode.lowerList identityTransform [] nodes

theorem DisplayNode.paintCount_eq_lowerLength (node : DisplayNode)
    (parent : Transform) (groups : List (Option String)) :
    node.paintCount = (node.lower parent groups).length := by
  refine DisplayNode.rec
    (motive_1 := fun node => ∀ parent groups,
      node.paintCount = (node.lower parent groups).length)
    (motive_2 := fun nodes => ∀ parent groups,
      DisplayNode.paintCountList nodes = (DisplayNode.lowerList parent groups nodes).length)
    ?_ ?_ ?_ ?_ ?_ node parent groups
  · intro primitive parent groups
    simp [DisplayNode.paintCount, DisplayNode.lower]
  · intro id transform children childrenCount parent groups
    simpa [DisplayNode.paintCount, DisplayNode.lower] using
      childrenCount (parent.compose transform) (groups ++ [id])
  · intro id transform clip children childrenCount parent groups
    simpa [DisplayNode.paintCount, DisplayNode.lower] using
      childrenCount (parent.compose transform) (groups ++ [id])
  · intro parent groups
    simp [DisplayNode.paintCountList, DisplayNode.lowerList]
  · intro node rest nodeCount restCount parent groups
    simp [DisplayNode.paintCountList, DisplayNode.lowerList,
      nodeCount parent groups, restCount parent groups, List.length_append]

theorem DisplayNode.paintCountList_eq_lowerLength (nodes : List DisplayNode)
    (parent : Transform) (groups : List (Option String)) :
    DisplayNode.paintCountList nodes = (DisplayNode.lowerList parent groups nodes).length := by
  induction nodes with
  | nil => simp [DisplayNode.paintCountList, DisplayNode.lowerList]
  | cons node rest ih =>
      simp [DisplayNode.paintCountList, DisplayNode.lowerList,
        DisplayNode.paintCount_eq_lowerLength node parent groups, ih, List.length_append]

theorem DisplayNode.lowerList_append (parent : Transform) (groups : List (Option String))
    (before after : List DisplayNode) :
    DisplayNode.lowerList parent groups (before ++ after) =
      DisplayNode.lowerList parent groups before ++ DisplayNode.lowerList parent groups after := by
  induction before with
  | nil => simp [DisplayNode.lowerList]
  | cons head tail ih => simp [DisplayNode.lowerList, ih, List.append_assoc]

theorem DisplayNode.lowerList_singletons (parent : Transform) (groups : List (Option String))
    (nodes : List DisplayNode) :
    List.flatten (nodes.map (fun node => node.lower parent groups)) =
      DisplayNode.lowerList parent groups nodes := by
  induction nodes with
  | nil => simp [DisplayNode.lowerList]
  | cons node rest ih => simp [DisplayNode.lowerList, ih]

theorem DisplayNode.lowerFromRootList_flatten (nodes : List DisplayNode) :
    List.flatten (nodes.map DisplayNode.lowerFromRoot) = DisplayNode.lowerFromRootList nodes := by
  change List.flatten (nodes.map (fun node => node.lower identityTransform [])) =
    DisplayNode.lowerList identityTransform [] nodes
  exact DisplayNode.lowerList_singletons identityTransform [] nodes

theorem DisplayNode.lower_group (parent : Transform) (groups : List (Option String))
    (id : Option String) (transform : Transform) (children : List DisplayNode) :
    DisplayNode.lower parent groups (.group id transform children) =
      DisplayNode.lowerList (parent.compose transform) (groups ++ [id]) children := by
  simp [DisplayNode.lower]

theorem DisplayNode.lower_clipped (parent : Transform) (groups : List (Option String))
    (id : Option String) (content : Transform) (clip : ClipRect) (children : List DisplayNode) :
    DisplayNode.lower parent groups (.clipped id content clip children) =
      (DisplayNode.lowerList (parent.compose content) (groups ++ [id]) children).map
        (Primitive.addClip (clip.lowerUnder parent)) := by
  simp [DisplayNode.lower]

private def strokeEnabled (style : Style) : Bool :=
  match style.stroke with | .none => false | _ => style.strokeWidth > 0

/-- SVG Tiny 1.2 §9.3 and §9.4: the outline of a circle or an ellipse starts at
    the 3 o'clock point and goes towards the 9 o'clock point through 6 o'clock.
    Dashes start there. -/
private def arcOutline (x y rx ry : Float) : String :=
  let n := fun (v : Float) => toString v
  let arc := fun (ex : Float) => s!"A{n rx} {n ry} 0 1 1 {n ex} {n y}"
  s!"M{n (x+rx)} {n y}" ++ arc (x-rx) ++ arc (x+rx) ++ "Z"

private def readGeometry (lengths : LengthContext) (tag : String) (attrs : List NamespaceAttribute) (style : Style) : Except String (Option Geometry) := do
  if tag == "rect" then
    let x ← geometryNumber lengths attrs "x"; let y ← geometryNumber lengths attrs "y"
    let w ← geometryNumber lengths attrs "width"; let h ← geometryNumber lengths attrs "height"
    if w < 0 || h < 0 then throw "negative rectangle dimensions"
    if w == 0 || h == 0 then return none
    -- SVG 2 §10.2: one missing radius takes the other; both clamp to half the box.
    let rx := match attr attrs "rx",attr attrs "ry" with
      | none,none => pure 0 | none,some _ => geometryNumber lengths attrs "ry"
      | _,_ => geometryNumber lengths attrs "rx"
    let ry := match attr attrs "ry",attr attrs "rx" with
      | none,none => pure 0 | none,some _ => geometryNumber lengths attrs "rx"
      | _,_ => geometryNumber lengths attrs "ry"
    let rx := min (max 0 (← rx)) (w/2); let ry := min (max 0 (← ry)) (h/2)
    if rx == 0 || ry == 0 then return some (.rect x y w h)
    let n := fun (v : Float) => toString v
    let arc := fun (ex ey : Float) => s!"A{n rx} {n ry} 0 0 1 {n ex} {n ey}"
    let source := s!"M{n (x+rx)} {n y}H{n (x+w-rx)}" ++ arc (x+w) (y+ry) ++ s!"V{n (y+h-ry)}" ++
      arc (x+w-rx) (y+h) ++ s!"H{n (x+rx)}" ++ arc x (y+h-ry) ++ s!"V{n (y+ry)}" ++ arc (x+rx) y ++ "Z"
    return some (.path (← NativeSVGPath.parse number source))
  else if tag == "circle" then
    let x ← geometryNumber lengths attrs "cx"; let y ← geometryNumber lengths attrs "cy"; let r ← geometryNumber lengths attrs "r"
    -- SVG 2 §10.3: an invalid negative r presentation value is ignored;
    -- the admitted attribute-only geometry cascade has initial r = 0.
    if r <= 0 then return none
    if strokeEnabled style && !style.dashArray.isEmpty then
      -- The circle primitive has no dashes; a path of two arcs does.
      return some (.path (← NativeSVGPath.parse number (arcOutline x y r r)))
    return some (.circle x y r)
  else if tag == "ellipse" then
    if (attr attrs "rx").isNone || (attr attrs "ry").isNone then throw "ellipse requires explicit numeric rx and ry; auto radii unsupported"
    let x ← geometryNumber lengths attrs "cx"; let y ← geometryNumber lengths attrs "cy"
    let rx ← geometryNumber lengths attrs "rx"; let ry ← geometryNumber lengths attrs "ry"
    if rx < 0 || ry < 0 then throw "negative ellipse radius"
    if rx == 0 || ry == 0 then return none
    if strokeEnabled style then
      -- The ellipse primitive has no stroke; a path of two arcs does.
      return some (.path (← NativeSVGPath.parse number (arcOutline x y rx ry)))
    return some (.ellipse x y rx ry)
  else if tag == "line" then
    let x1 ← geometryNumber lengths attrs "x1"; let y1 ← geometryNumber lengths attrs "y1"
    let x2 ← geometryNumber lengths attrs "x2"; let y2 ← geometryNumber lengths attrs "y2"
    return some (.line x1 y1 x2 y2)
  else if tag == "polygon" || tag == "polyline" then
    let source ← need (attr attrs "points") "polygon requires points"
    let values ← numbers source
    if values.length < (if tag=="polygon" then 6 else 4) || values.length%2 != 0 || values.length > 128 then throw "polygon/polyline requires 2–64 pairs (polygon at least 3)"
    let pairs := (List.range (values.length/2)).map fun i => Point.mk values[i*2]! values[i*2+1]!
    return if tag=="polygon" then some (.polygon pairs) else some (.path [NativeSVGPath.ofLinear ⟨pairs,false⟩])
  else if tag == "path" then
    let source := (attr attrs "d").getD ""
    if source.length > 65536 then throw "path data exceeds 65536 characters"
    if (trim source).toLower == "none" then return none
    let contours ← NativeSVGPath.parse number source
    return if contours.isEmpty then none else some (.path contours)
  else throw s!"unsupported SVG element: {tag}"
/-- One retained stroke union across all linear contours. Closedness and
    per-subpath dash phase are distinct from implicit fill closure. -/
private def Geometry.compile (screen : Transform) : Geometry → Except String BackendGeometry
  | .rect x y w h => pure (.rect x y w h)
  | .circle x y r => pure (.circle x y r)
  | .ellipse x y rx ry => pure (.ellipse x y rx ry)
  | .line x y u v => pure (.line x y u v)
  | .polygon points => pure (.polygon points)
  | .path contours => (fun result => (Geometry.path result : BackendGeometry)) <$> NativeSVGCurves.flatten screen contours

private def dashedParts (g : BackendGeometry) (style : Style) (authorLength : Option Float) : Except String (Option (List NativeSVGStroke.Piece)) := do
  if !strokeEnabled style then return none
  let contours ← match g with
    | .line x y u v => pure [NativeSVGPath.LinearContour.mk [Point.mk x y,Point.mk u v] false]
    | .rect x y w h => pure [NativeSVGPath.LinearContour.mk [Point.mk x y,Point.mk (x+w) y,Point.mk (x+w) (y+h),Point.mk x (y+h)] true]
    | .polygon points => pure [NativeSVGPath.LinearContour.mk points true]
    | .path contours => pure contours
    | _ => if style.dashArray.isEmpty then return none else throw "dashed curved strokes unsupported"
  let total : Float := contours.foldl (fun n c => n+NativeSVGStroke.length c) 0
  -- SVG 2 §9.6.1: percentage distances are exempt from pathLength calibration.
  let (pattern,offset) ← match authorLength with
    | none => pure (style.dashArray.map (·.value),style.dashOffset.value)
    | some author => do
      if style.dashArray.isEmpty then pure ([],0)
      else if author==0 then
        if style.dashArray.any (fun length => length.value != 0 && !length.percentage) ||
            (style.dashOffset.value != 0 && !style.dashOffset.percentage) then
          throw "zero pathLength infinite dash calibration unsupported"
        pure (style.dashArray.map (·.value),style.dashOffset.value)
      else
        let scale := total/author
        if !scale.isFinite then throw "pathLength calibration exceeds finite range"
        let pattern := style.dashArray.map (·.calibrated scale)
        pure (pattern,style.dashOffset.calibrated scale)
  return some (← NativeSVGStroke.retain contours pattern offset style.strokeWidth style.lineCap style.miterLimit style.lineJoin)

private def extraAttrs (tag : String) : List String :=
  match tag with
  | "rect" => ["x","y","width","height","rx","ry","opacity","transform","pathLength"]
  | "circle" => ["cx","cy","r","opacity","transform"]
  | "ellipse" => ["cx","cy","rx","ry","opacity","transform"]
  | "line" => ["x1","y1","x2","y2","opacity","transform","pathLength"]
  | "polygon" | "polyline" => ["points","opacity","transform","pathLength"]
  | "path" => ["d","opacity","transform","pathLength"]
  | _ => []
private def whitespace (s : String) : Bool := s.toList.all isXmlSpace
structure Mapping where
  sx : Float
  sy : Float
  tx : Float
  ty : Float
  minX : Float
  minY : Float
  viewportWidth : Float
  viewportHeight : Float
  deriving Repr

/-- SVG 2 §8.6: a negative viewBox extent invalidates the attribute;
    a zero extent is valid and disables rendering at its viewport boundary. -/
private def viewBoxValues (attrs : List NamespaceAttribute) : Except String (Option (Float × Float × Float × Float)) := do
  let some source := attr attrs "viewBox" | return none
  let [x,y,w,h] ← numbers source | throw "viewBox requires four numbers"
  return if w < 0 || h < 0 then none else some (x,y,w,h)

private def viewportMapping (w h : Float) (attrs : List NamespaceAttribute) : Except String Mapping := do
  let view ← viewBoxValues attrs
  let (x,y,vw,vh) := view.getD (0,0,w,h)
  if vw == 0 || vh == 0 then throw "zero viewBox must suppress its viewport before mapping"
  let preserve := (attr attrs "preserveAspectRatio").getD "xMidYMid meet" |>.splitOn " " |>.filter (· != "")
  let (align,mode) ← match preserve with
    | [a] => pure (a,"meet") | [a,m] => pure (a,m) | _ => throw "unsupported preserveAspectRatio syntax"
  if !["meet","slice"].contains mode then throw "unsupported viewBox fit mode"
  if align == "none" then return ⟨w/vw,h/vh,0,0,x,y,w,h⟩
  let alignments := [("xMinYMin",(0,0)),("xMidYMin",(1,0)),("xMaxYMin",(2,0)),
    ("xMinYMid",(0,1)),("xMidYMid",(1,1)),("xMaxYMid",(2,1)),
    ("xMinYMax",(0,2)),("xMidYMax",(1,2)),("xMaxYMax",(2,2))]
  let some (_,ax,ay) := alignments.find? (fun item => item.1 == align) | throw "unsupported viewBox alignment"
  let scale := if mode == "meet" then min (w/vw) (h/vh) else max (w/vw) (h/vh)
  return ⟨scale,scale,(w-vw*scale)*Float.ofNat ax/2,(h-vh*scale)*Float.ofNat ay/2,x,y,w,h⟩


private def metadata (node : NamespaceNode) : Except String Unit := do
  match node with
  | .other (.text _) | .other (.cdata _) | .other (.comment _) => pure ()
  | _ => throw "descriptive metadata only supports text/comments"

private structure ReadContext where
  lengths : LengthContext
  parent : Transform
  style : Style
  path : List Nat
  ancestors : List (List Nat)
  instanceRoot : Bool := false
  baseURL : Option String := none

private def readListWith (read : NamespaceNode → Nat → Except String (List DisplayNode))
    (nodes : List NamespaceNode) : Except String (List DisplayNode) := do
  let mut out : Array DisplayNode := #[]
  let mut count := 0
  for (node,index) in nodes.zipIdx do
    let chunk ← read node index
    count := count + DisplayNode.paintCountList chunk
    if count > maxPrimitives then throw "painted primitive count exceeds 49152"
    out := out ++ chunk.toArray
  return out.toList

private def replaceAttr (attrs : List NamespaceAttribute) (key value : String) : List NamespaceAttribute :=
  attrs.filter (fun a => !(a.name.namespace_.isNone && a.name.localPart == key)) ++
    [{name:={namespace_:=none,localPart:=key},value}]

/-- Non-inherited container opacity requires an offscreen group surface for
    values strictly between zero and one; do not approximate it per leaf. -/
private def containerVisible (attrs : List NamespaceAttribute) : Except String Bool := do
  let opacity ← match attr attrs "opacity" with | none => pure 1 | some value => number value
  if opacity > 0 && opacity < 1 then throw "container opacity requires compositing surface"
  return !displaySuppressed attrs && opacity > 0

/-- CSS Masking 1 §6: `clip-path` naming a `clipPath` of one untransformed
    `rect`. Any other clip shape stays a named refusal. -/
private def rectClip (lengths : LengthContext) (references : NativeSVGReferences.Index) (source : String) :
    Except String (Float × Float × Float × Float) := do
  if !(source.startsWith "url(#" && source.endsWith ")") then throw "unsupported clip-path syntax"
  let id := ((source.drop 5).toString.dropEnd 1).toString
  let some target := references.get? id | throw "clip-path target not found"
  let .element name attrs children := target.node | throw "clip-path target is not an element"
  if name.namespace_ != some svgURI || name.localPart != "clipPath" then throw "clip-path target is not clipPath"
  if (attr attrs "clipPathUnits").getD "userSpaceOnUse" != "userSpaceOnUse" || (attr attrs "transform").isSome then
    throw "unsupported clipPath attributes"
  let shapes := children.filter fun | .element .. => true | _ => false
  let [.element shapeName shape _] := shapes | throw "unsupported clipPath: one rect required"
  if shapeName.localPart != "rect" || (attr shape "transform").isSome then throw "unsupported clipPath: one rect required"
  return (← geometryNumber lengths shape "x",← geometryNumber lengths shape "y",
    ← geometryNumber lengths shape "width",← geometryNumber lengths shape "height")

/-- Namespace of an attribute that the forgiving pass writes on a glyph path. -/
def internalURI := "urn:factoidal:svg-internal"
/-- Attribute with the bounding box of the whole text: x, y, width and height. -/
def textBoxAttribute := "text-box"

/-- SVG Tiny 1.2 §11.13 and §7.11: a glyph path paints in the user space of its
    text and with the bounding box of its text. -/
private def Paint.ofText (frame : Transform) (box : Float × Float × Float × Float) : Paint → Paint
  | .gradient g => .gradient {g with frame,box:=some box}
  | paint => paint

private def textFrame (attrs : List NamespaceAttribute) (transform : Transform) (style : Style) : Except String Style := do
  let some mark := attrs.find? (fun a => a.name.namespace_ == some internalURI && a.name.localPart == textBoxAttribute)
    | return style
  let [x,y,w,h] ← numbers mark.value | throw "text box requires four numbers"
  return {style with fill:=style.fill.ofText transform (x,y,w,h),stroke:=style.stroke.ofText transform (x,y,w,h)}

private def readNode (references : NativeSVGReferences.Index) (rules : List NativeSVGCSS.Rule)
    (paints : PaintContext) : Nat → ReadContext → NamespaceNode → Except String (List DisplayNode)
  | 0,_,_ => throw "SVG group/instance nesting exceeds 32"
  | fuel+1,context,node => do
    let context := match node with
      | .element _ attrs _ => {context with baseURL:=NativeSVGReferences.elementBase attrs context.baseURL}
      | _ => context
    let {lengths,parent,style,path,ancestors,instanceRoot,baseURL} := context
    let active := path :: ancestors
    let readChildren := fun (lengths : LengthContext) (parent : Transform) (style : Style)
        (children : List NamespaceNode) =>
      readListWith (fun child i => readNode references rules paints fuel
        {lengths,parent,style,path:=path++[i],ancestors:=active,baseURL} child) children
    match node with
    | .other (.comment _) => pure []
    | .other (.text text) | .other (.cdata text) =>
      if whitespace text then pure [] else throw "text painting unsupported"
    | .other _ => throw "processing instructions/other XML nodes unsupported"
    | .element name rawAttrs children =>
      if name.namespace_ == some "http://www.w3.org/1999/xhtml" && name.localPart == "link" then
        if ![some "match",some "help",some "author"].contains (attr rawAttrs "rel") then
          throw "unsupported HTML link relation"
        if !children.isEmpty then throw "HTML metadata link must be empty"
        return []
      if name.namespace_ == some "http://www.w3.org/1999/xhtml" && name.localPart == "meta" then
        if (attr rawAttrs "http-equiv").isSome then throw "active HTML metadata unsupported"
        if !children.isEmpty then throw "HTML metadata must be empty"
        return []
      if name.namespace_ != some svgURI then throw s!"foreign/non-SVG element: {name.localPart}"
      let tag := name.localPart
      if ["style","metadata","defs","stop"].contains tag || paintServers.contains tag ||
          (tag == "symbol" && !instanceRoot) then return []
      let attrs ← applyCSS lengths paints rules tag rawAttrs true
      if tag == "title" || tag == "desc" then
        validateAttrs tag attrs ["id"]
        for child in children do metadata child
        return []
      else if tag == "use" then
        validateAttrs tag attrs ["href","x","y","width","height","transform","opacity"]
        if !(← containerVisible attrs) then return []
        let inherited ← readStyle lengths paints attrs style
        let x ← geometryNumber lengths attrs "x"
        let y ← geometryNumber lengths attrs "y"
        let transform ← checkedTransform ((← elementTransform parent ((attr attrs "transform").getD "")).compose ⟨1,0,0,1,x,y⟩)
        let cumulative ← checkedTransform (parent.compose transform)
        let some source := NativeSVGReferences.href attrs | return []
        let some id ← NativeSVGReferences.fragment source references.documentURL baseURL | return []
        let some target := references.get? id | return []
        if active.contains target.path then return []
        let .element targetName targetAttrs targetChildren := target.node | return []
        if targetName.namespace_ != some svgURI then return []
        let mut targetAttrs := targetAttrs
        if ["svg","symbol"].contains targetName.localPart then
          for key in ["width","height"] do
            if let some value := attr attrs key then
              if trim value != "auto" then
                let size ← relativeLength value (if key == "width" then lengths.width else lengths.height)
                if size < 0 then throw "negative use viewport dimensions unsupported"
                targetAttrs := replaceAttr targetAttrs key value
        let targetTree ← readNode references rules paints fuel
          {lengths,parent:=cumulative,style:=inherited,path:=target.path,ancestors:=active,instanceRoot:=true,baseURL:=target.parentBase}
          (.element targetName targetAttrs targetChildren)
        return [.group (attr attrs "id") transform targetTree]
      else if tag == "svg" || tag == "symbol" then
        validateAttrs tag attrs ["x","y","width","height","viewBox","preserveAspectRatio","overflow","transform","opacity","version"]
        if !(← containerVisible attrs) then return []
        let x ← geometryNumber lengths attrs "x"
        let y ← geometryNumber lengths attrs "y"
        let dimension := fun key base => do
          let value := (attr attrs key).getD "100%"
          if trim value == "auto" then pure base else relativeLength value base
        let w ← dimension "width" lengths.width
        let h ← dimension "height" lengths.height
        if w < 0 || h < 0 then throw "negative nested viewport dimensions"
        if w == 0 || h == 0 then return []
        let view ← viewBoxValues attrs
        if let some (_,_,vw,vh) := view then
          if vw == 0 || vh == 0 then return []
        let mapping ← viewportMapping w h attrs
        let viewportTransform ← checkedTransform ((← elementTransform parent ((attr attrs "transform").getD "")).compose ⟨1,0,0,1,x,y⟩)
        let contentTransform ← checkedTransform (viewportTransform.compose
          ⟨mapping.sx,0,0,mapping.sy,mapping.tx-mapping.minX*mapping.sx,mapping.ty-mapping.minY*mapping.sy⟩)
        let cumulative ← checkedTransform (parent.compose contentTransform)
        let childLengths : LengthContext := match view with
          | none => {width:=w,height:=h}
          | some (_,_,vw,vh) => {width:=vw,height:=vh}
        let inherited ← readStyle childLengths paints attrs style
        let retainedChildren ← readChildren childLengths cumulative inherited children
        let overflow := trim ((attr attrs "overflow").getD "hidden")
        if overflow == "visible" then
          return [.group (attr attrs "id") contentTransform retainedChildren]
        if !["hidden","scroll","auto"].contains overflow then throw "unsupported viewport overflow"
        return [.clipped (attr attrs "id") contentTransform ⟨0,0,w,h,viewportTransform⟩ retainedChildren]
      else if tag == "g" then
        validateAttrs tag attrs ["transform","clip-path"]
        let transform ← checkedTransform (← elementTransform parent ((attr attrs "transform").getD ""))
        let cumulative ← checkedTransform (parent.compose transform)
        let inherited ← readStyle lengths paints attrs style
        let retainedChildren ← readChildren lengths cumulative inherited children
        if displaySuppressed attrs then return []
        match attr attrs "clip-path" with
        | none => return [.group (attr attrs "id") transform retainedChildren]
        | some source =>
          let (x,y,w,h) ← rectClip lengths references (trim source)
          return [.clipped (attr attrs "id") transform ⟨x,y,w,h,transform⟩ retainedChildren]
      else
        validateAttrs tag attrs (extraAttrs tag)
        let transform ← checkedTransform (← elementTransform parent ((attr attrs "transform").getD ""))
        let cumulative ← checkedTransform (parent.compose transform)
        let inherited ← textFrame attrs transform (← readStyle lengths paints attrs style)
        let authorLength ← match attr attrs "pathLength" with
          | none => pure none
          | some source => do
            let value ← number source
            if value < 0 then throw "negative pathLength"
            pure (some value)
        let geometry ← readGeometry lengths tag attrs inherited
        for child in children do
          match child with
          | .element n _ _ =>
            if n.namespace_ == some svgURI && ["title","desc","metadata"].contains n.localPart then
              let _ ← readNode references rules paints fuel
                {lengths,parent:=cumulative,style:=inherited,path,ancestors:=active,baseURL} child
              pure ()
            else throw "graphics children unsupported"
          | .other (.comment _) => pure ()
          | .other (.text text) | .other (.cdata text) => if !whitespace text then throw "text painting unsupported"
          | _ => throw "processing instruction unsupported"
        let opacity ← match attr attrs "opacity" with | none => pure 1 | some value => number value
        let painted ← geometry.toList.mapM fun g => do
          let dashParts ← match g with
            | .path _ => pure none
            | _ => do dashedParts (← g.compile identityTransform) inherited authorLength
          pure (.paint {geometry:=g,style:=inherited,opacity:=max 0 (min 1 opacity),transform,dashParts,pathLength:=authorLength})
        if displaySuppressed attrs then return []
        return painted

/-- Rows admitted before allocating a scene buffer. It matches the packed
    backend record size; each primitive is counted cumulatively during compile. -/
def BackendPrimitive.storageRows (p : BackendPrimitive) : Nat :=
  let shapeRows := match p.geometry with
    | .polygon points => (points.length+1)/2
    | .path contours => (NativeSVGPath.edges contours).length
    | _ => 0
  5+shapeRows+(p.dashParts.getD []).length*5+
    (if p.transform.identity then 0 else 2)+p.clips.length*3

/-- Largest paint table of a scene, in 32-bit words. -/
def maxPaintTableWords : Nat := 1048576

private def pointBox (points : List Point) : Float × Float × Float × Float :=
  match points with
  | [] => (0,0,0,0)
  | p::rest =>
    let (x0,y0,x1,y1) := rest.foldl (fun (b : Float × Float × Float × Float) p =>
      (min b.1 p.x,min b.2.1 p.y,max b.2.2.1 p.x,max b.2.2.2 p.y)) (p.x,p.y,p.x,p.y)
    (x0,y0,x1-x0,y1-y0)

/-- Object bounding box of the geometry, in its local frame: x, y, width, height.
    Stroke width takes no part in it (SVG Tiny 1.2 §7.11). -/
private def Geometry.box : BackendGeometry → Float × Float × Float × Float
  | .rect x y w h => (x,y,w,h)
  | .circle cx cy r => (cx-r,cy-r,2*r,2*r)
  | .ellipse cx cy rx ry => (cx-rx,cy-ry,2*rx,2*ry)
  | .line x1 y1 x2 y2 => (min x1 x2,min y1 y2,(x2-x1).abs,(y2-y1).abs)
  | .polygon points => pointBox points
  | .path contours => pointBox (contours.flatMap (·.points))

private def fallbackPaint : L4Factoidal.Rendering.FallbackPaint → Paint
  | .none => .none
  | .current => .current
  | .solid c => .solid ⟨c.r,c.g,c.b⟩

/-- Lower a server for one primitive. No stops paint as `none` (§11.16); a server
    that paints nothing for this geometry gives its fallback paint. -/
private def lowerPaint (box : Float × Float × Float × Float) (cursor : Nat) : Paint → Except String Paint
  | .gradient g =>
    if g.stops.isEmpty then pure .none else
    match g.lower box with
    | none => pure (fallbackPaint g.fallback)
    | some record =>
      if !record.words.all (fun word => word.isFinite && word.toFloat32.isFinite) then
        throw "gradient map exceeds finite binary32 range"
      else pure (.gradientRecord cursor record)
  | paint => pure paint

def Paint.tableWords : Paint → List Float
  | .gradientRecord _ record => record.words
  | _ => []

/-- Words of this primitive in the scene's paint table: fill, then stroke. -/
def Primitive.paintWords (p : BackendPrimitive) : List Float :=
  p.style.fill.tableWords ++ p.style.stroke.tableWords

private def compilePrimitive (mapping : Mapping) (cursor : Nat) (p : Primitive) : Except String BackendPrimitive := do
  let root : Transform := ⟨mapping.sx,0,0,mapping.sy,
    mapping.tx-mapping.minX*mapping.sx,mapping.ty-mapping.minY*mapping.sy⟩
  let geometry ← p.geometry.compile (root.compose p.transform)
  let box := geometry.box
  let fill ← lowerPaint box cursor p.style.fill
  let stroke ← lowerPaint box (cursor+fill.tableWords.length) p.style.stroke
  let style := {p.style with fill,stroke}
  if cursor+fill.tableWords.length+stroke.tableWords.length > maxPaintTableWords then
    throw s!"paint table exceeds {maxPaintTableWords} words"
  let dashParts ← match p.dashParts,p.geometry with
    | some parts,_ => pure (some parts)
    | none,.path _ => dashedParts geometry style p.pathLength
    | none,_ => pure none
  return {geometry,style,opacity:=p.opacity,transform:=p.transform,dashParts,groupPath:=p.groupPath,clips:=p.clips,pathLength:=p.pathLength}

private def compilePrimitivesLoop (mapping : Mapping) : List Primitive →
    List BackendPrimitive → Nat → Nat → Except String (List BackendPrimitive)
  | [],acc,_,_ => pure acc.reverse
  | primitive::rest,acc,rows,cursor => do
    let compiled ← compilePrimitive mapping cursor primitive
    let rows := rows+compiled.storageRows
    if rows*4 > maxDataFloats then throw "storage data exceeds 1048576 floats"
    compilePrimitivesLoop mapping rest (compiled::acc) rows (cursor+compiled.paintWords.length)

/-- Canonical Float path geometry becomes checked linear backend geometry once,
    using the full viewport/primitive CTM and the existing cumulative budget.
    A non-flat or over-budget curve is an error, never a substituted chord. -/
def compilePrimitives (mapping : Mapping) (primitives : List Primitive) : Except String (List BackendPrimitive) :=
  compilePrimitivesLoop mapping primitives [] 2 0

private theorem compilePrimitivesLoop_length (mapping : Mapping) (source : List Primitive) :
    ∀ acc rows cursor compiled, compilePrimitivesLoop mapping source acc rows cursor = .ok compiled →
      compiled.length = source.length+acc.length := by
  induction source with
  | nil =>
    intro acc rows cursor compiled found
    have same : acc.reverse = compiled := Except.ok.inj found
    rw [← same,List.length_reverse]
    simp
  | cons primitive rest ih =>
    intro acc rows cursor compiled found
    cases one : compilePrimitive mapping cursor primitive with
    | error message => simp [compilePrimitivesLoop,one,bind,Except.bind] at found
    | ok value =>
      by_cases over : (rows+value.storageRows)*4 > maxDataFloats
      · simp [compilePrimitivesLoop,one,over,bind,Except.bind] at found
      · have tail : compilePrimitivesLoop mapping rest (value::acc) (rows+value.storageRows)
            (cursor+value.paintWords.length) = .ok compiled := by
          simpa [compilePrimitivesLoop,one,over,bind,pure,Except.bind,Except.pure] using found
        have count := ih (value::acc) (rows+value.storageRows) _ compiled tail
        simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using count

theorem compilePrimitives_length (mapping : Mapping) (source : List Primitive)
    (compiled : List BackendPrimitive) (found : compilePrimitives mapping source = .ok compiled) :
    compiled.length = source.length := by
  simpa [compilePrimitives] using compilePrimitivesLoop_length mapping source [] 2 0 compiled found

private theorem compilePrimitivesLoop_budget (mapping : Mapping) (source : List Primitive) :
    ∀ acc rows cursor compiled, rows = 2+(acc.map BackendPrimitive.storageRows).sum →
      rows*4 ≤ maxDataFloats → compilePrimitivesLoop mapping source acc rows cursor = .ok compiled →
      (2+(compiled.map BackendPrimitive.storageRows).sum)*4 ≤ maxDataFloats := by
  induction source with
  | nil =>
    intro acc rows cursor compiled invariant bounded found
    have same : acc.reverse = compiled := Except.ok.inj found
    subst compiled
    rw [invariant] at bounded
    simpa [List.map_reverse,List.sum_reverse] using bounded
  | cons primitive rest ih =>
    intro acc rows cursor compiled invariant bounded found
    cases one : compilePrimitive mapping cursor primitive with
    | error message => simp [compilePrimitivesLoop,one,bind,Except.bind] at found
    | ok value =>
      by_cases over : (rows+value.storageRows)*4 > maxDataFloats
      · simp [compilePrimitivesLoop,one,over,bind,Except.bind] at found
      · have tail : compilePrimitivesLoop mapping rest (value::acc) (rows+value.storageRows)
            (cursor+value.paintWords.length) = .ok compiled := by
          simpa [compilePrimitivesLoop,one,over,bind,pure,Except.bind,Except.pure] using found
        apply ih (value::acc) (rows+value.storageRows) (cursor+value.paintWords.length) compiled
        · simp only [List.map_cons,List.sum_cons]
          omega
        · omega
        · exact tail

theorem compilePrimitives_budget (mapping : Mapping) (source : List Primitive)
    (compiled : List BackendPrimitive) (found : compilePrimitives mapping source = .ok compiled) :
    (2+(compiled.map BackendPrimitive.storageRows).sum)*4 ≤ maxDataFloats := by
  exact compilePrimitivesLoop_budget mapping source [] 2 0 compiled rfl (by decide) found

structure Scene where
  width : Nat
  height : Nat
  mapping : Mapping
  tree : List DisplayNode
  /-- Painter-order lowering preserves the canonical geometry and all controls. -/
  primitives : List Primitive
  loweringCorrect : primitives = DisplayNode.lowerFromRootList tree
  /-- Explicitly admitted backend cache, separate from retained curve geometry. -/
  compiled : List BackendPrimitive
  compilationCorrect : compilePrimitives mapping primitives = .ok compiled
  deriving Repr

/-- All public sampling runs on an admitted scene. Failed geometry compilation
    propagates before an artifact, image, or successful scene can be returned. -/
def Scene.make (width height : Nat) (mapping : Mapping) (tree : List DisplayNode) : Except String Scene :=
  let primitives := DisplayNode.lowerFromRootList tree
  match found : compilePrimitives mapping primitives with
  | .error message => .error message
  | .ok compiled => .ok {width,height,mapping,tree,primitives,loweringCorrect:=rfl,compiled,compilationCorrect:=found}

theorem Scene.compiled_length (s : Scene) : s.compiled.length = s.primitives.length :=
  compilePrimitives_length s.mapping s.primitives s.compiled s.compilationCorrect

theorem Scene.make_existing (s : Scene) : Scene.make s.width s.height s.mapping s.tree = .ok s := by
  rcases s with ⟨width,height,mapping,tree,primitives,lowering,compiled,compilation⟩
  subst primitives
  simp only [Scene.make]
  split
  · rename_i message found
    rw [compilation] at found
    cases found
  · rename_i result found
    have same : result = compiled := Except.ok.inj (found.symm.trans compilation)
    subst result
    rfl

private def nodeIds (root : NamespaceNode) : Except String (List String) := do
  let mut pending := [(root,0)]
  let mut ids : Array String := #[]
  for _ in [:maxInputChars+1] do
    match pending with
    | [] => return ids.toList
    | (node,depth)::rest =>
      if depth > 32 then throw "SVG metadata/identifier nesting exceeds 32"
      match node with
      | .other _ => pending := rest
      | .element _ attrs children =>
        if let some id := attr attrs "id" then ids := ids.push id
        pending := children.map (fun child => (child,depth+1)) ++ rest
  throw "SVG identifier node count exceeds input bound"

/-- Collect inert author style elements in document order, with explicit profile
    refusals for non-CSS type or conditional media. No external resources. -/
private def styleRules (root : NamespaceNode) : Except String (List NativeSVGCSS.Rule) := do
  let mut pending := [root]
  let mut out : Array NativeSVGCSS.Rule := #[]
  for _ in [:maxInputChars+1] do
    match pending with
    | [] => return out.toList
    | node::rest =>
      pending := rest
      match node with
      | .other _ => pure ()
      | .element name attrs children =>
        if name.namespace_ == some svgURI && name.localPart == "style" then
          for a in attrs do
            if a.name.namespace_.isSome || !["id","type","media"].contains a.name.localPart then throw "unsupported style element attribute"
          let typ := trim ((attr attrs "type").getD "text/css") |>.toLower
          if !["","text/css"].contains typ then throw "unsupported stylesheet type"
          let media := trim ((attr attrs "media").getD "all") |>.toLower
          if !["","all"].contains media then throw "conditional stylesheet media unsupported"
          let mut text : Array String := #[]
          for child in children do
            match child with
            | .other (.text value) | .other (.cdata value) => text := text.push value
            | .other (.comment _) => pure ()
            | _ => throw "style requires text/CDATA"
          let parsed ← NativeSVGCSS.parseSheet sheetProperties (String.join text.toList)
          if out.size+parsed.length > 256 then throw "document CSS rule count exceeds 256"
          out := out ++ parsed.toArray
        else if !(name.namespace_ == some svgURI && ["metadata","title","desc"].contains name.localPart) then
          pending := children ++ pending
  throw "stylesheet traversal exceeds input bound"

/-- One source-bound, bounded document index shared by all SVG roots in an
    HTML document. Cached errors remain errors when a painting root needs them;
    a zero viewport can still suppress its subtree without style interpretation. -/
structure ReferenceContext where
  document : NamespaceNode
  documentURL : Option String
  initialBaseURL : Option String
  references : NativeSVGReferences.Index
  indexingCorrect : NativeSVGReferences.collect document (maxInputChars+1) documentURL initialBaseURL = .ok references
  idsResult : Except String (List String)
  idsCorrect : idsResult = nodeIds document
  rulesResult : Except String (List NativeSVGCSS.Rule)
  rulesCorrect : rulesResult = styleRules document

/-- The initial document base may come from the Lean HTML frontend. Retrieval
    URL identity remains separate for same-document IRI comparisons. -/
def ReferenceContext.create (document : NamespaceNode) (documentURL : Option String := none)
    (initialBaseURL : Option String := none) : Except String ReferenceContext :=
  match indexed : NativeSVGReferences.collect document (maxInputChars+1) documentURL initialBaseURL with
  | .error message => .error message
  | .ok references => .ok {
      document := document
      documentURL := documentURL
      initialBaseURL := initialBaseURL
      references := references
      indexingCorrect := indexed
      idsResult := nodeIds document
      idsCorrect := rfl
      rulesResult := styleRules document
      rulesCorrect := rfl }

theorem ReferenceContext.create_existing (context : ReferenceContext) :
    ReferenceContext.create context.document context.documentURL context.initialBaseURL = .ok context := by
  rcases context with ⟨document,url,base,references,indexed,ids,idsCorrect,rules,rulesCorrect⟩
  subst ids
  subst rules
  simp only [ReferenceContext.create]
  split
  · rename_i message found
    rw [indexed] at found
    cases found
  · rename_i cached found
    have same : cached = references := Except.ok.inj (found.symm.trans indexed)
    subst cached
    rfl

#print axioms ReferenceContext.create_existing

/-- SVG 2 §5.1: render an already namespace-expanded SVG fragment, including
    one supplied by an HTML foreign-content parser. The caller owns DOM parsing;
    root validation, SVG style, geometry and viewport semantics remain here. -/
private def parseRootWithContext (root : NamespaceNode) (outputWidth outputHeight : Nat)
    (inheritedStyle : Style)
    (referenceSource : Unit → Except String (ReferenceContext × List Nat × Option String)) : Except String Scene := do
  let .element name attrs children := root | throw "SVG root must be an element"
  if name.namespace_ != some svgURI || name.localPart != "svg" then throw "root must be svg in the SVG namespace"
  validateAttrs "svg" attrs ["width","height","viewBox","preserveAspectRatio","version","style"]
  if let some version := attr attrs "version" then
    if !["1.1","2.0"].contains version then throw "unsupported SVG version label"
  for key in ["width","height"] do
    if let some source := attr attrs key then
      let viewportUnit := (trim source).endsWith "vw" || (trim source).endsWith "vh"
      let size ← if (trim source).endsWith "%" || viewportUnit then
        if outputWidth == 0 || outputHeight == 0 then throw "percentage root dimensions require explicit host output viewport"
        -- The host output size already holds the viewport unit's computed value.
        else if viewportUnit then pure 0
        else relativeLength source (Float.ofNat (if key == "width" then outputWidth else outputHeight))
      else lengthNumber source
      if size < 0 then throw "negative root dimensions"
  let (w,h) ← if outputWidth > 0 && outputHeight > 0 then pure (Float.ofNat outputWidth,Float.ofNat outputHeight)
    else if outputWidth != 0 || outputHeight != 0 then throw "both output dimensions are required"
    else do
      let rw ← need (attr attrs "width") "root width required unless explicit output viewport is supplied"
      let rh ← need (attr attrs "height") "root height required unless explicit output viewport is supplied"
      pure (← lengthNumber rw,← lengthNumber rh)
  if w <= 0 || h <= 0 || w > 4096 || h > 4096 then throw "output viewport must be positive and at most 4096 pixels"
  let view ← viewBoxValues attrs
  if let some (_,_,vw,vh) := view then
    if vw == 0 || vh == 0 then
      -- Keep a finite identity mapping and the actual backing viewport;
      -- no zero-divisor or hidden subtree is sent to the backend compiler.
      return ← Scene.make w.ceil.toUInt32.toNat h.ceil.toUInt32.toNat (← viewportMapping w h []) []
  let mapping ← viewportMapping w h attrs
  let lengths : LengthContext := match view with
    | none => {width:=w,height:=h}
    | some (_,_,vw,vh) => {width:=vw,height:=vh}
  let (context,sourcePath,rootBase) ← referenceSource ()
  let _ ← context.idsResult
  let rules ← context.rulesResult
  let paints : PaintContext := {references:=context.references,rules,document:=context.document}
  let attrs ← applyCSS lengths paints rules "svg" attrs
  validateAttrs "svg" attrs ["width","height","viewBox","preserveAspectRatio","version"]
  let inherited ← readStyle lengths paints attrs inheritedStyle
  let ancestors := (List.range (sourcePath.length+1)).map (fun depth => sourcePath.take depth)
  let parsedTree ← readListWith (fun child i => readNode context.references rules paints 33
    {lengths,parent:=identityTransform,style:=inherited,path:=sourcePath ++ [i],ancestors,baseURL:=rootBase} child) children
  let tree := if displaySuppressed attrs then [] else parsedTree
  Scene.make w.ceil.toUInt32.toNat h.ceil.toUInt32.toNat mapping tree

/-- Standalone SVG keeps a local original document and the existing public API.
    Context creation is delayed until after zero-viewport suppression. -/
def parseRoot (root : NamespaceNode) (outputWidth outputHeight : Nat := 0)
    (inheritedStyle : Style := {}) (documentURL : Option String := none) : Except String Scene :=
  parseRootWithContext root outputWidth outputHeight inheritedStyle fun _ => do
    let context ← ReferenceContext.create root documentURL
    let base := match root with
      | .element _ attrs _ => NativeSVGReferences.elementBase attrs documentURL
      | _ => documentURL
    pure (context,[],base)

/-- Select an SVG root from the indexed original document in Lean. The caller
    may normalize only root attributes after its own Lean HTML/CSS computation;
    original children, reference targets, source identity and bases are retained. -/
def parseRootInContext (context : ReferenceContext) (rootSourcePath : List Nat)
    (outputWidth outputHeight : Nat := 0) (inheritedStyle : Style := {})
    (rootAttributeNormalizer : List NamespaceAttribute → Except String (List NamespaceAttribute) := fun attrs => .ok attrs) : Except String Scene := do
  let initialBase := context.initialBaseURL.orElse (fun _ => context.documentURL)
  let entry ← NativeSVGReferences.locate context.document rootSourcePath initialBase
  let .element name originalAttrs children := entry.node | throw "SVG root source path must select an element"
  let base := NativeSVGReferences.elementBase originalAttrs entry.parentBase
  let attrs ← rootAttributeNormalizer originalAttrs
  parseRootWithContext (.element name attrs children) outputWidth outputHeight inheritedStyle
    (fun _ => .ok (context,entry.path,base))

def parse (xml : String) (outputWidth outputHeight : Nat := 0)
    (documentURL : Option String := none) : Except String Scene := do
  if xml.length > maxInputChars then throw "SVG input exceeds 1048576 characters"
  let document ← (parseXML xml).mapError (fun e => s!"XML: {e.message} at {e.position}")
  if let some encoding := document.decl.bind (·.encoding) then
    if encoding.toLower != "utf-8" then throw "SVG host accepts UTF-8 input only"
  if document.doctype.isSome then throw "DOCTYPE/DTD unsupported in SVG profile"
  for node in document.prolog ++ document.epilog do
    match node with | .pi .. => throw "processing instruction unsupported" | _ => pure ()
  let root ← parseNamespaceView xml
  parseRoot root outputWidth outputHeight {} documentURL

/- Typed conditions reuse Graphics.Expr's CPU interpreter and WGSL lowering.
   The float scene is separate from the integer-only demo Shape representation. -/
inductive Test where
  | expr (expression : Expr .boolean)
  | not (a : Test)
  | both (a b : Test)
  | either (a b : Test)
private def Test.eval (env : Env) : Test → Bool
  | .expr e => e.eval env | .not a => !(a.eval env)
  | .both a b => a.eval env && b.eval env | .either a b => a.eval env || b.eval env
private def Test.prepare (data : Array Float) : Test → Prepared Bool
  | .expr e => e.prepare data
  | .not a => (a.prepare data).map Bool.not
  | .both a b => (a.prepare data).andThen (fun _ => b.prepare data)
  | .either a b => (a.prepare data).or (b.prepare data)
private theorem Test.prepare_correct (data : Array Float) (test : Test) (env : Env) :
    (test.prepare data).eval env = test.eval {env with data := data} := by
  induction test with
  | expr e => exact Expr.prepare_correct data e env
  | _ => simp_all only [Test.prepare,Test.eval,Prepared.eval_map,
      Prepared.eval_and,Prepared.eval_or,Prepared.eval_andThen]
private def Test.wgsl : Test → String
  | .expr e => e.wgsl | .not a => "!(" ++ a.wgsl ++ ")"
  | .both a b => "(" ++ a.wgsl ++ "&&" ++ b.wgsl ++ ")"
  | .either a b => "(" ++ a.wgsl ++ "||" ++ b.wgsl ++ ")"
private def scalar (base offset : Nat) : Expr .scalar := .param (base+offset)
private def point (base offset : Nat) : Expr .vec2 := .vec (scalar base offset) (scalar base (offset+1))
private def px : Expr .scalar := .dot (.var .position) (.vec (.lit 1) (.lit 0))
private def py : Expr .scalar := .dot (.var .position) (.vec (.lit 0) (.lit 1))
private def squared (e : Expr .vec2) : Expr .scalar := .dot e e
private def le (a b : Expr .scalar) : Test := .expr (.le a b)
private def box (x y w h : Expr .scalar) : Test :=
  .both (.both (le (.lit 0) w) (le (.lit 0) h))
    (.both (.both (le x px) (le px (.add x w))) (.both (le y py) (le py (.add y h))))
private def fillCondition (g : BackendGeometry) (base : Nat) : Test :=
  match g with
  | .rect .. => box (scalar base 0) (scalar base 1) (scalar base 2) (scalar base 3)
  | .circle .. => le (squared (.subV (.var .position) (point base 0))) (.mul (scalar base 2) (scalar base 2))
  | .ellipse .. =>
    let dx := Expr.divide (.sub px (scalar base 0)) (scalar base 2)
    let dy := Expr.divide (.sub py (scalar base 1)) (scalar base 3)
    le (.add (.mul dx dx) (.mul dy dy)) (.lit 1)
  | _ => le (.lit 1) (.lit 0)
private def strokeShapeCondition (g : BackendGeometry) (base : Nat) (cap : LineCap) : Test :=
  let half := Expr.divide (scalar base 16) (.lit 2)
  match g with
  | .rect .. =>
    .both (box (.sub (scalar base 0) half) (.sub (scalar base 1) half)
      (.add (scalar base 2) (scalar base 16)) (.add (scalar base 3) (scalar base 16)))
      (.not (box (.add (scalar base 0) half) (.add (scalar base 1) half)
        (.sub (scalar base 2) (scalar base 16)) (.sub (scalar base 3) (scalar base 16))))
  | .circle .. =>
    let d := squared (.subV (.var .position) (point base 0))
    let inner := Expr.maximum (.lit 0) (.sub (scalar base 2) half)
    let outer := Expr.add (scalar base 2) half
    .both (le (.mul inner inner) d) (le d (.mul outer outer))
  | .line .. =>
    let d := Expr.subV (point base 2) (point base 0)
    let delta := Expr.subV (.var .position) (point base 0)
    let len := squared d
    let h := Expr.divide (.dot delta d) (.maximum len (.divide (.lit 1) (.lit 1000000000000)))
    let butt := .both (.not (le len (.lit 0)))
      (.both (.both (le (.lit 0) h) (le h (.lit 1)))
        (le (squared (.subV delta (.scale h d))) (.mul half half)))
    if cap != .round then butt else
      -- Capsule = finite strip plus its endpoint disks. Cross multiplication
      -- avoids division, including the zero-length round-cap disk case.
      let projection := Expr.dot delta d
      let cross := Expr.sub
        (.mul (.sub px (scalar base 0)) (.sub (scalar base 3) (scalar base 1)))
        (.mul (.sub py (scalar base 1)) (.sub (scalar base 2) (scalar base 0)))
      let strip := Test.both (.not (le len (.lit 0)))
        (.both (.both (le (.lit 0) projection) (le projection len))
          (le (.mul cross cross) (.mul (.mul half half) len)))
      .either strip (.either
        (le (squared delta) (.mul half half))
        (le (squared (.subV (.var .position) (point base 2))) (.mul half half)))
  | _ => le (.lit 1) (.lit 0)
private def strokeCondition (g : BackendGeometry) (base : Nat) (cap : LineCap) : Test :=
  .both (.not (le (scalar base 16) (.lit 0))) (strokeShapeCondition g base cap)
private def triangleCondition (base : Nat) : Test :=
  let a := point base 0
  let b := point base 2
  let c := point base 8
  let cross := fun (u v : Expr .vec2) =>
    Expr.sub (.mul (.dot u (.vec (.lit 1) (.lit 0))) (.dot v (.vec (.lit 0) (.lit 1))))
      (.mul (.dot u (.vec (.lit 0) (.lit 1))) (.dot v (.vec (.lit 1) (.lit 0))))
  let edge := fun u v => cross (.subV v u) (.subV (.var .position) u)
  let ab := edge a b
  let bc := edge b c
  let ca := edge c a
  let area := cross (.subV b a) (.subV c a)
  .both (.not (le (.mul area area) (.lit 0)))
    (.either (.both (le (.lit 0) ab) (.both (le (.lit 0) bc) (le (.lit 0) ca)))
      (.both (le ab (.lit 0)) (.both (le bc (.lit 0)) (le ca (.lit 0)))))
private def pieceCondition (piece : NativeSVGStroke.Piece) (base : Nat) : Test :=
  match piece with
  | .strip .. => strokeCondition (.line 0 0 0 0) base .butt
  | .disk .. => fillCondition (.circle 0 0 0) base
  | .triangle .. => triangleCondition base
private def edgeConditions (a b : Expr .vec2) : Test × Test :=
  let ax := Expr.dot a (.vec (.lit 1) (.lit 0))
  let ay := Expr.dot a (.vec (.lit 0) (.lit 1))
  let bx := Expr.dot b (.vec (.lit 1) (.lit 0))
  let byy := Expr.dot b (.vec (.lit 0) (.lit 1))
  let cross := Expr.sub (.mul (.sub bx ax) (.sub py ay)) (.mul (.sub byy ay) (.sub px ax))
  (.both (.both (le ay py) (.not (le byy py))) (.not (le cross (.lit 0))),
   .both (.both (le byy py) (.not (le ay py))) (.not (le (.lit 0) cross)))
private def windingConditions (base count i : Nat) : Test × Test :=
  edgeConditions (point base (20+2*i)) (point base (20+2*((i+1)%count)))
private def pathConditions (base i : Nat) : Test × Test :=
  edgeConditions (point base (20+4*i)) (point base (22+4*i))
private def boundsCondition (base : Nat) : Test :=
  .both (.both (le (scalar base 0) px) (le px (scalar base 2)))
    (.both (le (scalar base 1) py) (le py (scalar base 3)))
private def windingHit (env : Env) (base count : Nat) (rule : FillRule) : Bool := Id.run do
  let mut winding : Int := 0
  for i in List.range count do
    let (up,down) := windingConditions base count i
    if up.eval env then winding := winding+1
    if down.eval env then winding := winding-1
  return if rule == .nonzero then winding != 0 else winding%2 != 0
private def pathHit (env : Env) (base count : Nat) (rule : FillRule) : Bool := Id.run do
  if !(boundsCondition base).eval env then return false
  let mut winding : Int := 0
  for i in List.range count do
    let (up,down) := pathConditions base i
    if up.eval env then winding := winding+1
    if down.eval env then winding := winding-1
  return if rule == .nonzero then winding != 0 else winding%2 != 0
private def windingWGSL (count : Nat) (conditions : Nat → Test × Test) (rule : FillRule) : String :=
  "var winding:i32=0;\n" ++ String.join ((List.range count).map fun i =>
    let (up,down) := conditions i
    "if " ++ up.wgsl ++ " {winding+=1;} if " ++ down.wgsl ++ " {winding-=1;}\n") ++
  (if rule == .nonzero then "let fillHit=winding!=0;\n" else "let fillHit=(winding%2)!=0;\n")
private def polygonWGSL (base count : Nat) (rule : FillRule) : String :=
  windingWGSL count (windingConditions base count) rule

private def resolved (paint : Paint) (style : Style) (alpha : Float) : List Float :=
  match paint with
  | .none => [0,0,0,0]
  | .solid c => [c.r,c.g,c.b,alpha]
  | .current => [style.currentColor.r,style.currentColor.g,style.currentColor.b,alpha]
  | .gradient _ => [0,0,0,0]
  -- A negative alpha marks a gradient: the shader finds its record in the table.
  | .gradientRecord cursor _ => [Float.ofNat cursor,alpha,0,-1]
private def pointBounds (points : List Point) : List Float :=
  match points with
  | [] => [0,0,0,0]
  | p::rest =>
    let bounds := rest.foldl (fun (b : Float × Float × Float × Float) p =>
      (min b.1 p.x,min b.2.1 p.y,max b.2.2.1 p.x,max b.2.2.2 p.y)) (p.x,p.y,p.x,p.y)
    [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]
theorem pointBounds_length (points : List Point) : (pointBounds points).length = 4 := by
  cases points <;> simp [pointBounds]
private def geometryRows : BackendGeometry → List Float
  | .rect x y w h | .ellipse x y w h => [x,y,w,h]
  | .circle x y r => [x,y,r,0]
  | .line x y u v => [x,y,u,v]
  | .polygon points => pointBounds points
  | .path contours => pointBounds (contours.flatMap (·.points))
theorem geometryRows_length (geometry : BackendGeometry) : (geometryRows geometry).length = 4 := by
  cases geometry <;> simp [geometryRows, pointBounds_length]
private theorem resolved_length (paint : Paint) (style : Style) (alpha : Float) :
    (resolved paint style alpha).length = 4 := by
  cases paint <;> simp [resolved]
private def Primitive.effectiveOpacity (p : BackendPrimitive) : Float :=
  if p.transform.det == 0 || !p.style.visible then 0 else p.opacity

theorem Primitive.effectiveOpacity_eq_zero_when_hidden (p : BackendPrimitive)
    (hidden : p.style.visible = false) : p.effectiveOpacity = 0 := by
  simp [Primitive.effectiveOpacity, hidden]
private theorem flatMap_fixed_length {α β : Type} (f : α → List β) (width : Nat)
    (hf : ∀ x, (f x).length = width) (xs : List α) :
    (xs.flatMap f).length = xs.length * width := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, hf x, ih,
      List.length_cons, Nat.succ_mul]
    exact Nat.add_comm _ _
def geometryTailRowCount : BackendGeometry → Nat
  | .polygon points => (points.length+1)/2
  | .path contours => (NativeSVGPath.edges contours).length
  | _ => 0
def geometryTailData : BackendGeometry → List Float
  | .polygon points => points.flatMap (fun p => [p.x,p.y]) ++
      (if points.length%2 == 1 then [0,0] else [])
  | .path contours => (NativeSVGPath.edges contours).flatMap fun (a,b) => [a.x,a.y,b.x,b.y]
  | _ => []
def shaderTailRowsFromHeader (tag count : Nat) : Nat :=
  if tag == Geometry.pathRecordTag then count else (count+1)/2
theorem Geometry.shaderTailRowsFromHeader_eq_tailRows (geometry : BackendGeometry) :
    shaderTailRowsFromHeader geometry.recordTagCount.1 geometry.recordTagCount.2 =
      geometryTailRowCount geometry := by
  cases geometry <;>
    simp [shaderTailRowsFromHeader, Geometry.recordTagCount, Geometry.pathRecordTag,
      Geometry.polygonRecordTag, geometryTailRowCount, Geometry.rectRecordTag,
      Geometry.circleRecordTag, Geometry.ellipseRecordTag, Geometry.lineRecordTag]
theorem geometryTailData_length (geometry : BackendGeometry) :
    (geometryTailData geometry).length = geometryTailRowCount geometry * 4 := by
  cases geometry with
  | rect x y w h => rfl
  | circle x y r => rfl
  | ellipse x y rx ry => rfl
  | line x1 y1 x2 y2 => rfl
  | polygon points =>
    have hflat := flatMap_fixed_length (fun p : Point => [p.x,p.y]) 2 (by intro; rfl) points
    by_cases hodd : points.length % 2 = 1
    · simp [geometryTailData, geometryTailRowCount, hflat, hodd]
      omega
    · have heven : points.length % 2 = 0 := by omega
      simp [geometryTailData, geometryTailRowCount, hflat, heven]
      omega
  | path contours =>
    have hflat := flatMap_fixed_length
      (fun edge : Point × Point => [edge.1.x,edge.1.y,edge.2.x,edge.2.y])
      4 (by intro; rfl) (NativeSVGPath.edges contours)
    simp [geometryTailData, geometryTailRowCount, hflat]
private def geometryTailSize (geometry : BackendGeometry) : Nat := geometryTailRowCount geometry * 4
def primitiveFixedRowCount : Nat := 5
def dashPieceRowCount : Nat := 5
/-- One path of the largest size, with its largest stroke, fits in a scene. -/
theorem maxStrokePath_within_storage :
    (primitiveFixedRowCount + NativeSVGPath.maxPathPoints +
      NativeSVGStroke.maxStrokePieces*dashPieceRowCount)*4 ≤ maxDataFloats := by decide
def affineTransformRowCount : Nat := L4Factoidal.Math.AffineRows.vec4RowCount
def clipRowCount : Nat := 3
def Primitive.headerModeCode (p : BackendPrimitive) : Nat :=
  p.style.lineCap.headerModeBit +
    (if p.transform.identity then 0 else 2) + 4*p.clips.length
theorem Primitive.headerModeCode_roundCap (p : BackendPrimitive) :
    p.headerModeCode % 2 = p.style.lineCap.headerModeBit := by
  cases hcap : p.style.lineCap <;> cases h : p.transform.identity <;>
    simp [Primitive.headerModeCode, LineCap.headerModeBit, hcap, h]
    <;> omega
theorem Primitive.headerModeCode_hasTransform (p : BackendPrimitive) :
    (p.headerModeCode % 4 >= 2) = (!p.transform.identity) := by
  cases hcap : p.style.lineCap <;> cases h : p.transform.identity <;>
    simp [Primitive.headerModeCode, LineCap.headerModeBit, hcap, h]
    <;> omega
theorem Primitive.headerModeCode_clipCount (p : BackendPrimitive) :
    p.headerModeCode / 4 = p.clips.length := by
  cases hcap : p.style.lineCap <;> cases h : p.transform.identity <;>
    simp [Primitive.headerModeCode, LineCap.headerModeBit, hcap, h]
    <;> omega
def Primitive.fixedRows (p : BackendPrimitive) : List Float :=
  let (tag,count) := p.geometry.recordTagCount
  geometryRows p.geometry ++ [Float.ofNat tag,Float.ofNat count,
    if p.style.rule == .evenodd then 1 else 0,Float.ofNat p.headerModeCode] ++
    resolved p.style.fill p.style p.style.fillOpacity ++
    resolved p.style.stroke p.style p.style.strokeOpacity ++
    [p.style.strokeWidth,p.effectiveOpacity,Float.ofNat (p.dashParts.getD []).length,if p.dashParts.isSome then 1 else 0]
theorem Primitive.fixedRows_length (p : BackendPrimitive) :
    p.fixedRows.length = primitiveFixedRowCount * 4 := by
  simp [Primitive.fixedRows, geometryRows_length, resolved_length, primitiveFixedRowCount]
def dashPieceData (width : Float) (piece : NativeSVGStroke.Piece) : List Float :=
  let (geometry,tag,extra) : List Float × Float × List Float := match piece with
    | .strip a b => ([a.x,a.y,b.x,b.y],4, [0,0,0,0])
    | .disk c r => ([c.x,c.y,r,0],2,[0,0,0,0])
    | .triangle a b c => ([a.x,a.y,b.x,b.y],7,[c.x,c.y,0,0])
  geometry ++ [tag,0,0,0] ++ extra ++ [0,0,0,0,width,0,0,0]
theorem dashPieceData_length (width : Float) (piece : NativeSVGStroke.Piece) :
    (dashPieceData width piece).length = dashPieceRowCount * 4 := by
  cases piece <;> simp [dashPieceData, dashPieceRowCount]
def dashPayloadData (width : Float) (pieces : List NativeSVGStroke.Piece) : List Float :=
  pieces.flatMap (dashPieceData width)
theorem dashPayloadData_length (width : Float) (pieces : List NativeSVGStroke.Piece) :
    (dashPayloadData width pieces).length = pieces.length * (dashPieceRowCount * 4) := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    change (dashPieceData width piece ++ dashPayloadData width rest).length = _
    rw [List.length_append, dashPieceData_length, ih]
    simp [Nat.add_mul, Nat.one_mul, Nat.add_comm]
/-- Optional inverse CTM tail, represented by the shared two-vec4 affine rows. -/
def Primitive.transformTailData (p : BackendPrimitive) : List Float :=
  if p.transform.identity then [] else
    let t := p.transform.inverse
    (t.toPackedRows floatOps).toVec4Rows.flatten
theorem Primitive.transformTailData_length (p : BackendPrimitive) :
    p.transformTailData.length = if p.transform.identity then 0 else affineTransformRowCount * 4 := by
  by_cases h : p.transform.identity
  · simp [Primitive.transformTailData, h]
  · simp only [Primitive.transformTailData, if_neg h]
    rw [L4Factoidal.Math.AffineRows.toVec4Rows_flatten_length]
    rfl
/-- Clip wire record: inverse affine rows (first w is an active flag), then
    local x/y/width/height. Empty/singular clips have a finite inactive record. -/
def ClipRect.rows (clip : ClipRect) : List Float :=
  let active := clip.valid
  let t := if active then clip.transform.inverse else identityTransform
  [t.a,t.c,t.e,if active then 1 else 0,t.b,t.d,t.f,0,
    if active then clip.x else 0,if active then clip.y else 0,
    if active then clip.width else 0,if active then clip.height else 0]

theorem ClipRect.rows_length (clip : ClipRect) : clip.rows.length = clipRowCount*4 := by
  simp [ClipRect.rows,clipRowCount]

def clipPayloadData (clips : List ClipRect) : List Float := clips.flatMap ClipRect.rows

theorem clipPayloadData_length (clips : List ClipRect) :
    (clipPayloadData clips).length = clips.length*(clipRowCount*4) := by
  induction clips with
  | nil => rfl
  | cons clip rest ih =>
      change (clip.rows ++ clipPayloadData rest).length = _
      rw [List.length_append,ClipRect.rows_length,ih]
      simp [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def Primitive.rows (p : BackendPrimitive) : List Float :=
  p.fixedRows ++
  geometryTailData p.geometry ++
  dashPayloadData p.style.strokeWidth (p.dashParts.getD []) ++
  p.transformTailData ++ clipPayloadData p.clips
def Primitive.rowCount (p : BackendPrimitive) : Nat :=
  primitiveFixedRowCount + geometryTailRowCount p.geometry +
  (p.dashParts.getD []).length * dashPieceRowCount +
  (if p.transform.identity then 0 else affineTransformRowCount) + p.clips.length*clipRowCount
theorem Primitive.rowCount_eq_storageRows (p : BackendPrimitive) : p.rowCount = p.storageRows := by
  rfl

def Primitive.shaderRowAdvance (p : BackendPrimitive) : Nat :=
  primitiveFixedRowCount +
  shaderTailRowsFromHeader p.geometry.recordTagCount.1 p.geometry.recordTagCount.2 +
  dashPieceRowCount * (p.dashParts.getD []).length +
  (if p.headerModeCode % 4 >= 2 then affineTransformRowCount else 0) +
  (p.headerModeCode / 4)*clipRowCount

theorem Primitive.clipOffsetRows (p : BackendPrimitive) :
    p.rowCount-p.clips.length*clipRowCount =
      primitiveFixedRowCount + geometryTailRowCount p.geometry +
        (p.dashParts.getD []).length*dashPieceRowCount +
        (if p.transform.identity then 0 else affineTransformRowCount) := by
  simp [Primitive.rowCount]

theorem Primitive.clipRows_within_record (p : BackendPrimitive) (index : Nat)
    (inside : index < p.clips.length) :
    (p.rowCount-p.clips.length*clipRowCount)*4 + (index+1)*(clipRowCount*4) ≤
      p.rowCount*4 := by
  rw [Primitive.clipOffsetRows]
  simp only [Primitive.rowCount,clipRowCount,Nat.add_mul]
  omega
theorem Primitive.shaderRowAdvance_eq_rowCount (p : BackendPrimitive) :
    p.shaderRowAdvance = p.rowCount := by
  cases h : p.transform.identity <;>
    simp [Primitive.shaderRowAdvance, Primitive.rowCount,
      Geometry.shaderTailRowsFromHeader_eq_tailRows,
      Primitive.headerModeCode_hasTransform, Primitive.headerModeCode_clipCount, h, Nat.mul_comm]
theorem Primitive.rows_length (p : BackendPrimitive) :
    p.rows.length = p.rowCount * 4 := by
  by_cases h : p.transform.identity
  · simp [Primitive.rows, Primitive.rowCount, h, Primitive.fixedRows_length,
      geometryTailData_length, dashPayloadData_length, Primitive.transformTailData_length, clipPayloadData_length,
      primitiveFixedRowCount, dashPieceRowCount, clipRowCount, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  · simp [Primitive.rows, Primitive.rowCount, h, Primitive.fixedRows_length,
      geometryTailData_length, dashPayloadData_length, Primitive.transformTailData_length, clipPayloadData_length,
      primitiveFixedRowCount, dashPieceRowCount, affineTransformRowCount, clipRowCount,
      L4Factoidal.Math.AffineRows.vec4RowCount,
      Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
theorem Primitive.rows_length_matches_shaderRowAdvance (p : BackendPrimitive) :
    p.rows.length = p.shaderRowAdvance * 4 := by
  rw [Primitive.rows_length, Primitive.shaderRowAdvance_eq_rowCount]

theorem Primitive.rows_offsets_eq_flattened_length (items : List BackendPrimitive) :
    (items.map fun p => p.rowCount*4).sum = (items.flatMap Primitive.rows).length := by
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro primitive _
  exact (Primitive.rows_length primitive).symm
theorem BackendPrimitive.data_length (items : List BackendPrimitive) :
    (items.flatMap Primitive.rows).length = (items.map BackendPrimitive.storageRows).sum*4 := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons]
    rw [Primitive.rows_length,Primitive.rowCount_eq_storageRows,ih]
    exact (Nat.add_mul _ _ _).symm

private def Scene.data (s : Scene) : Array Float :=
  ([s.mapping.sx,s.mapping.sy,s.mapping.tx,s.mapping.ty,
    s.mapping.minX,s.mapping.minY,s.mapping.viewportWidth,s.mapping.viewportHeight] ++
    s.compiled.flatMap Primitive.rows).toArray

theorem Scene.data_size_eq_record_cursor (s : Scene) :
    s.data.size = 8 + (s.compiled.map fun p => p.rowCount*4).sum := by
  change ([s.mapping.sx,s.mapping.sy,s.mapping.tx,s.mapping.ty,
    s.mapping.minX,s.mapping.minY,s.mapping.viewportWidth,s.mapping.viewportHeight] ++
    s.compiled.flatMap Primitive.rows).length = _
  simp only [List.length_append, List.length_cons, List.length_nil]
  rw [Primitive.rows_offsets_eq_flattened_length]
theorem Scene.data_within_storage_budget (s : Scene) : s.data.size ≤ maxDataFloats := by
  change ([s.mapping.sx,s.mapping.sy,s.mapping.tx,s.mapping.ty,
    s.mapping.minX,s.mapping.minY,s.mapping.viewportWidth,s.mapping.viewportHeight] ++
    s.compiled.flatMap Primitive.rows).length ≤ maxDataFloats
  simp only [List.length_append,List.length_cons,List.length_nil]
  rw [BackendPrimitive.data_length]
  simpa [Nat.add_mul] using compilePrimitives_budget s.mapping s.primitives s.compiled s.compilationCorrect

#print axioms compilePrimitives_length
#print axioms compilePrimitives_budget
#print axioms Scene.make_existing
#print axioms Scene.data_within_storage_budget

private def Primitive.wgsl (p : BackendPrimitive) (base : Nat) : String :=
  "{\n" ++
  (match p.geometry with
   | .polygon points => polygonWGSL base points.length p.style.rule
   | .path contours => windingWGSL (NativeSVGPath.edges contours).length (pathConditions base) p.style.rule
   | _ => "let fillHit=" ++ (fillCondition p.geometry base).wgsl ++ ";\n") ++
  "let strokeHit=" ++ (strokeCondition p.geometry base p.style.lineCap).wgsl ++ ";\n" ++
  s!"let fill=params.rows[{base/4+2}];let stroke=params.rows[{base/4+3}];\n" ++
  "var element=vec4f(0.0);\nif fillHit {element=vec4f(fill.rgb*fill.a,fill.a);}\n" ++
  "if strokeHit {element=vec4f(stroke.rgb*stroke.a,stroke.a)+element*(1.0-stroke.a);}\n" ++
  s!"let opacity=params.rows[{base/4+4}].y;\n" ++
  "rgb=element.rgb*opacity+rgb*(1.0-element.a*opacity);\n}\n"
-- Conditions retain the shared typed expression semantics; only their parameter
-- base is relocated to a runtime record row. No per-primitive shader expansion.
private def relativeCondition (test : Test) : String :=
  test.wgsl.replace "params.rows[" "params.rows[base+"
private def shaderCase (tag : Nat) (g : BackendGeometry) : String :=
  s!"case {tag}u: " ++ "{fillHit=" ++ relativeCondition (fillCondition g 0) ++
  ";strokeHit=" ++ relativeCondition (strokeCondition g 0 .butt) ++ ";}\n"
/-- Screen tile side in pixels for the primitive lists. -/
def tileSize : Nat := 32

/-- Limit on the list entries of all tiles; it bounds the artifact size. -/
def maxTileEntries : Nat := 1000000

/-- A conservative box of a compiled primitive in pixels: the local bounds,
widened for a stroke, through the transform and the page mapping, with a
margin. `none` means the box is not known, and the primitive joins every tile.
Clips can only shrink what is painted, so they are not used. -/
private def Primitive.screenBox (m : Mapping) (p : BackendPrimitive) :
    Option (Float × Float × Float × Float) :=
  let bounds : List Float := match p.geometry with
    | .rect x y w h => [min x (x+w),min y (y+h),max x (x+w),max y (y+h)]
    | .circle cx cy r => [cx-r,cy-r,cx+r,cy+r]
    | .ellipse cx cy rx ry => [cx-rx,cy-ry,cx+rx,cy+ry]
    | .line x1 y1 x2 y2 => [min x1 x2,min y1 y2,max x1 x2,max y1 y2]
    | .polygon points => pointBounds points
    | .path contours => pointBounds (contours.flatMap (·.points))
  match bounds with
  | [x0,y0,x1,y1] =>
    let pad : Float := match p.style.stroke with
      | .none => 0
      -- A miter tip is at most miterLimit*width/2 from its vertex, and a square
      -- cap's corner is less than width from its end.
      | _ => (max 2 (p.style.miterLimit/2))*p.style.strokeWidth+1
    let corners := [(x0-pad,y0-pad),(x1+pad,y0-pad),(x0-pad,y1+pad),(x1+pad,y1+pad)]
    let pixels := corners.map fun (x,y) =>
      let w := p.transform.apply x y
      ((w.1-m.minX)*m.sx+m.tx,(w.2-m.minY)*m.sy+m.ty)
    let xs := pixels.map (·.1)
    let ys := pixels.map (·.2)
    if m.sx <= 0 || m.sy <= 0 || (xs++ys).any (fun v => v.isNaN || v.isInf) then none
    else some (xs.foldl min (xs.headD 0)-2,ys.foldl min (ys.headD 0)-2,
               xs.foldl max (xs.headD 0)+2,ys.foldl max (ys.headD 0)+2)
  | _ => none

/-- The tile of a pixel coordinate, kept in `0..count-1`. -/
private def tileIndex (value : Float) (count : Nat) : Nat :=
  if value <= 0 then 0
  else min (count-1) (value/tileSize.toFloat).floor.toUInt64.toNat

/-- The words of all gradient records as binary32 bit patterns, in the order that
`compilePrimitives` gave their cursors, then the count of those words. -/
private def Scene.paintTableTail (s : Scene) : Array Nat :=
  let words := s.compiled.flatMap Primitive.paintWords
  (words.map (·.toFloat32.toBits.toNat)).toArray.push words.length

/-- Primitive lists for each screen tile, in paint order: tile size, tiles
across, tiles down, one start offset for each tile and a final end offset, then
the record row of each listed primitive, then the paint table. A primitive is left out of a tile only
when its conservative box does not touch the tile; there it can not change a
pixel, so the image does not change. -/
private def Scene.tiles (s : Scene) : Array Nat := Id.run do
  let tail := s.paintTableTail
  let across := (s.width+tileSize-1)/tileSize
  let down := (s.height+tileSize-1)/tileSize
  let mut lists : Array (Array Nat) := Array.replicate (across*down) #[]
  let mut base := 2
  for p in s.compiled do
    let (left,top,right,bottom) := match p.screenBox s.mapping with
      | some (x0,y0,x1,y1) => (tileIndex x0 across,tileIndex y0 down,tileIndex x1 across,tileIndex y1 down)
      | none => (0,0,across-1,down-1)
    for y in [top:bottom+1] do
      for x in [left:right+1] do
        lists := lists.modify (y*across+x) (·.push base)
    base := base+p.rowCount
  let mut offsets : Array Nat := #[]
  let mut total := 0
  for list in lists do
    offsets := offsets.push total
    total := total+list.size
  offsets := offsets.push total
  -- A very dense page: one tile that lists every primitive once, as before tiles.
  if total > maxTileEntries then
    let mut rows : Array Nat := #[]
    let mut row := 2
    for p in s.compiled do
      rows := rows.push row
      row := row+p.rowCount
    return #[max s.width s.height+1,1,1,0,rows.size] ++ rows ++ tail
  let mut out : Array Nat := #[tileSize,across,down] ++ offsets
  for list in lists do
    out := out ++ list
  return out ++ tail

/-- The shader does not depend on the scene: all scene values are storage data. -/
private def sceneShader : String :=
  "struct Params {rows:array<vec4f>};\n" ++
  "@group(0) @binding(0) var<storage,read> params:Params;\n" ++
  "@group(0) @binding(1) var<storage,read> tiles:array<u32>;\n" ++
  "fn parameter(base:u32,offset:u32)->f32{return params.rows[base+offset/4u][offset%4u];}\n" ++
  "fn windingContains(base:u32,count:u32,rule:u32,p:vec2f,stride:u32)->bool {var winding:i32=0;" ++
  "for(var i=0u;i<count;i++){let ai=select(2u*i,4u*i,stride==4u);let bi=select(2u*((i+1u)%count),4u*i+2u,stride==4u);" ++
  "let a=vec2f(parameter(base,20u+ai),parameter(base,21u+ai));" ++
  "let b=vec2f(parameter(base,20u+bi),parameter(base,21u+bi));" ++
  "let cross=(b.x-a.x)*(p.y-a.y)-(b.y-a.y)*(p.x-a.x);" ++
  "if(a.y<=p.y&&p.y<b.y&&cross>0.0){winding+=1;}" ++
  "if(b.y<=p.y&&p.y<a.y&&cross<0.0){winding-=1;}}" ++
  "if(rule==1u){return (winding%2)!=0;}return winding!=0; }\n" ++
  "fn withinBounds(base:u32,p:vec2f)->bool{let b=params.rows[base];return all(p>=b.xy)&&all(p<=b.zw);}" ++
  "fn word(i:u32)->f32{return bitcast<f32>(tiles[i]);}" ++
  "fn stopColor(s:u32)->vec4f{return vec4f(word(s+1u),word(s+2u),word(s+3u),word(s+4u));}" ++
  -- `GradientRecord.colorAt`: map, stop search, mix before premultiplying.
  "fn paintSample(row:vec4f,p:vec2f)->vec4f{if(row.w>=0.0){return row;}" ++
  "let last=arrayLength(&tiles)-1u;let r=last-tiles[last]+u32(row.x);" ++
  "let u=word(r)*p.x+word(r+1u)*p.y+word(r+2u);let v=word(r+4u)*p.x+word(r+5u)*p.y+word(r+6u);" ++
  "let t=select(u,sqrt(u*u+v*v),word(r+3u)==1.0);let n=u32(word(r+7u));" ++
  "var s=r+" ++ toString L4Factoidal.Rendering.gradientRecordHeaderWords ++ "u;var c=stopColor(s);" ++
  "for(var i=1u;i<n;i++){let q=s+" ++ toString L4Factoidal.Rendering.gradientStopWords ++ "u;let o0=word(s);let o1=word(q);" ++
  "if(t>=o1){c=stopColor(q);s=q;continue;}if(t>o0){let f=(t-o0)/(o1-o0);c=c*(1.0-f)+stopColor(q)*f;}break;}" ++
  "return vec4f(c.rgb,c.a*row.y);}\n" ++
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {" ++
  "let vertices=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(vertices[i],0,1); }\n" ++
  "fn samplePixel(pixel:vec4f)->vec4f {" ++
  "var rgb=vec3f(1.0);let rowLimit=arrayLength(&params.rows);if(rowLimit<2u){return vec4f(rgb,1.0);}if any(pixel.xy>=params.rows[1].zw){return vec4f(rgb,1.0);}" ++
  "let worldP=vec4f((pixel.xy-params.rows[0].zw)/params.rows[0].xy+params.rows[1].xy,0,1);" ++
  "let across=tiles[1];let down=tiles[2];let tile=min(u32(pixel.y)/tiles[0],down-1u)*across+min(u32(pixel.x)/tiles[0],across-1u);" ++
  "let listBase=4u+across*down;let listEnd=tiles[4u+tile];\n" ++
  "for(var item=tiles[3u+tile];item<listEnd;item++)" ++ "{var base=tiles[listBase+item];" ++
  "let remaining=rowLimit-base;if(remaining<5u){break;}let header=vec4u(params.rows[base+1u]);let tag=header.x;let count=header.y;" ++
  "if(count>2u*remaining){break;}let shapeRows=select((count+1u)/2u,count,tag==" ++ toString Geometry.pathRecordTag ++ "u);let dashCount=u32(params.rows[base+4u].z);let clipCount=header.w/4u;" ++
  "if(shapeRows>remaining||dashCount>remaining/" ++ toString dashPieceRowCount ++ "u||clipCount>remaining/" ++ toString clipRowCount ++ "u){break;}let tailRows=shapeRows+" ++ toString dashPieceRowCount ++ "u*dashCount;let affineRows=select(0u," ++ toString affineTransformRowCount ++ "u,(header.w%4u)>=2u);let recordRows=" ++ toString primitiveFixedRowCount ++ "u+tailRows+affineRows+" ++ toString clipRowCount ++ "u*clipCount;if(recordRows>remaining){break;}var p=worldP;if((header.w%4u)>=2u)" ++ "{let tb=base+" ++ toString primitiveFixedRowCount ++ "u+tailRows;let x=params.rows[tb];let y=params.rows[tb+1u];" ++
  "p=vec4f(dot(x.xy,worldP.xy)+x.z,dot(y.xy,worldP.xy)+y.z,0,1);}" ++
  "var clipHit=true;let clipBase=base+" ++ toString primitiveFixedRowCount ++ "u+tailRows+affineRows;for(var ci=0u;ci<clipCount;ci++){let cb=clipBase+" ++ toString clipRowCount ++ "u*ci;let x=params.rows[cb];let y=params.rows[cb+1u];let bounds=params.rows[cb+2u];let q=vec2f(dot(x.xy,worldP.xy)+x.z,dot(y.xy,worldP.xy)+y.z);if(x.w!=1.0||any(q<bounds.xy)||any(q>bounds.xy+bounds.zw)){clipHit=false;break;}}" ++
  "var fillHit=false;var strokeHit=false;switch tag {\n" ++
  shaderCase Geometry.rectRecordTag (.rect 0 0 0 0) ++ shaderCase Geometry.circleRecordTag (.circle 0 0 0) ++ shaderCase Geometry.ellipseRecordTag (.ellipse 0 0 0 0) ++
  s!"case {Geometry.lineRecordTag}u: " ++ "{if((header.w%2u)==1u){strokeHit=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .round) ++
  ";}else{strokeHit=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .butt) ++ ";}}\n" ++
  s!"case {Geometry.polygonRecordTag}u:" ++ "{if(withinBounds(base,p.xy)){fillHit=windingContains(base,count,header.z,p.xy,2u);}}" ++
  s!"case {Geometry.pathRecordTag}u:" ++ "{if(withinBounds(base,p.xy)){fillHit=windingContains(base,count,header.z,p.xy,4u);}} default:{} }\n" ++
  s!"if(params.rows[base+4u].w==1.0)" ++ "{strokeHit=false;let parentBase=base;for(var di=0u;di<dashCount;di++){base=parentBase+" ++ toString primitiveFixedRowCount ++ s!"u+shapeRows+di*{dashPieceRowCount}u;let dt=u32(params.rows[base+1u].x);var piece=false;" ++
  "if(dt==4u){piece=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .butt) ++ ";}" ++
  "else if(dt==2u){piece=" ++ relativeCondition (fillCondition (.circle 0 0 0) 0) ++ ";}" ++
  "else if(dt==7u){piece=" ++ relativeCondition (triangleCondition 0) ++ ";}strokeHit=strokeHit||piece;}base=parentBase;}" ++
  "fillHit=fillHit&&clipHit;strokeHit=strokeHit&&clipHit;var element=vec4f(0.0);" ++
  "if fillHit {let fill=paintSample(params.rows[base+2u],p.xy);element=vec4f(fill.rgb*fill.a,fill.a);}" ++
  "if strokeHit {let stroke=paintSample(params.rows[base+3u],p.xy);element=vec4f(stroke.rgb*stroke.a,stroke.a)+element*(1.0-stroke.a);}" ++
  "let opacity=params.rows[base+4u].y;rgb=element.rgb*opacity+rgb*(1.0-element.a*opacity);" ++
  "}return vec4f(rgb,1.0); }\n" ++
  "@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {var total=vec4f(0.0);" ++
  String.join (pixelSampleOffsets.map fun (x,y) =>
    "total+=samplePixel(vec4f(pixel.xy+vec2f(" ++ toString (x-0.5) ++ "," ++ toString (y-0.5) ++ "),0.0,1.0));") ++
  "return total/" ++ toString pixelSampleOffsets.length ++ ".0;}\n"

private def Scene.wgsl (_s : Scene) : String := sceneShader
/-- JSON text of the shader, made once for the process. -/
private def sceneShaderJSON : String := quote sceneShader


private def Primitive.coverageAt (primitive : BackendPrimitive) (data : Array Float)
    (base : Nat) (position : Float × Float) : Bool × Bool := Id.run do
  let clipCount := primitive.clips.length
  let mut clipBase := base + (primitive.rowCount-clipCount*clipRowCount)*4
  for _ in primitive.clips do
    if data[clipBase+3]! != 1 then return (false,false)
    let x := data[clipBase]! * position.1 + data[clipBase+1]! * position.2 + data[clipBase+2]!
    let y := data[clipBase+4]! * position.1 + data[clipBase+5]! * position.2 + data[clipBase+6]!
    if x < data[clipBase+8]! || y < data[clipBase+9]! ||
        x > data[clipBase+8]!+data[clipBase+10]! || y > data[clipBase+9]!+data[clipBase+11]! then
      return (false,false)
    clipBase := clipBase+clipRowCount*4
  let localPoint := primitive.transform.inverse.apply position.1 position.2
  let env : Env := {data,position:=localPoint}
  let fillHit := match primitive.geometry with
    | .polygon points => (boundsCondition base).eval env && windingHit env base points.length primitive.style.rule
    | .path contours => pathHit env base (NativeSVGPath.edges contours).length primitive.style.rule
    | _ => (fillCondition primitive.geometry base).eval env
  let strokeHit := match primitive.dashParts with
    | none => (strokeCondition primitive.geometry base primitive.style.lineCap).eval env
    | some pieces => Id.run do
      let mut hit := false
      let mut offset := base+20+geometryTailSize primitive.geometry
      for piece in pieces do
        hit := hit || (pieceCondition piece offset).eval env
        offset := offset+20
      return hit
  return (fillHit,strokeHit)

/-- `fillCondition` of a rectangle as plain code: the same Float operations in the same
    order, with no closures or boxed values. `rectHit_eq_fillCondition` ties the two. -/
private def rectHit (x y w h : Float) (q : Float × Float) : Bool :=
  let px := q.1*Float.ofNat 1+q.2*Float.ofNat 0
  let py := q.1*Float.ofNat 0+q.2*Float.ofNat 1
  (decide (Float.ofNat 0 <= w) && decide (Float.ofNat 0 <= h)) &&
    ((decide (x <= px) && decide (px <= x+w)) && (decide (y <= py) && decide (py <= y+h)))

private theorem rectHit_eq_fillCondition (data : Array Float) (base : Nat) (a b c d : Float)
    (q : Float × Float) :
    rectHit data[base+0]! data[base+1]! data[base+2]! data[base+3]! q =
      (fillCondition (.rect a b c d) base).eval {data,position := q} := rfl

/-- Prepare un-clipped, un-dashed geometry once. Winding paths retain the
    reference edge traversal, with its edge count shared across all samples.
    Clipped and dashed geometry keeps every existing coverage check. -/
private inductive PreparedCoverage where
  | rectFill (inverse : Transform) (x y w h : Float)
  | analytic (inverse : Transform) (data : Array Float) (fill stroke : Prepared Bool)
  | reference (primitive : BackendPrimitive) (data : Array Float) (base : Nat)

private def PreparedCoverage.eval : PreparedCoverage → (Float × Float) → Bool × Bool
  | .rectFill inverse x y w h,position =>
    (rectHit x y w h (inverse.apply position.1 position.2),false)
  | .analytic inverse data fill stroke,position =>
    let env : Env := {data,position := inverse.apply position.1 position.2}
    (fill.eval env,stroke.eval env)
  | .reference p data base,position => p.coverageAt data base position

private def Primitive.prepareCoverage (p : BackendPrimitive) (data : Array Float) (base : Nat) : PreparedCoverage :=
  match p.clips,p.dashParts,p.geometry with
  | [],none,.rect .. | [],none,.circle .. | [],none,.ellipse .. | [],none,.line .. =>
    .analytic p.transform.inverse data ((fillCondition p.geometry base).prepare data)
      ((strokeCondition p.geometry base p.style.lineCap).prepare data)
  | [],none,.polygon points =>
    let count := points.length
    .analytic p.transform.inverse data
      (((boundsCondition base).prepare data).and
        (.dynamic (fun env => windingHit env base count p.style.rule)))
      ((strokeCondition p.geometry base p.style.lineCap).prepare data)
  | [],none,.path contours =>
    let count := (NativeSVGPath.edges contours).length
    .analytic p.transform.inverse data
      (.dynamic (fun env => pathHit env base count p.style.rule))
      ((strokeCondition p.geometry base p.style.lineCap).prepare data)
  | _,_,_ => .reference p data base

private theorem Primitive.prepareCoverage_correct (p : BackendPrimitive) (data : Array Float)
    (base : Nat) (position : Float × Float) :
    (p.prepareCoverage data base).eval position = p.coverageAt data base position := by
  cases clips : p.clips with
  | cons clip rest => simp [Primitive.prepareCoverage,PreparedCoverage.eval,clips]
  | nil =>
    cases dash : p.dashParts with
    | some pieces => simp [Primitive.prepareCoverage,PreparedCoverage.eval,clips,dash]
    | none =>
      cases geo : p.geometry <;>
        simp [Primitive.prepareCoverage,PreparedCoverage.eval,Primitive.coverageAt,clips,dash,geo,
          Prepared.eval_and,Test.prepare_correct] <;> simp [Prepared.eval]

/-- Topmost geometric paint item at a viewport coordinate, in the same
    painter order and using the exact retained coverage predicates as sampling.
    The result is the zero-based index in `primitives`; it is a paint-item
    identity, not yet an XML element identity or a DOM event-target guarantee. -/
def Scene.hitTestAt (s : Scene) (screenX screenY : Float) : Option (Fin s.primitives.length) := Id.run do
  if screenX < 0 || screenY < 0 || screenX >= s.mapping.viewportWidth || screenY >= s.mapping.viewportHeight then
    return none
  let position := ((screenX-s.mapping.tx)/s.mapping.sx+s.mapping.minX,
    (screenY-s.mapping.ty)/s.mapping.sy+s.mapping.minY)
  let data := s.data
  let mut records : Array (Fin s.compiled.length × BackendPrimitive × Nat) := #[]
  let mut base := 8
  for (index,primitive) in (List.finRange s.compiled.length).zip s.compiled do
    records := records.push (index,primitive,base)
    base := base+primitive.rowCount*4
  for (index,primitive,recordBase) in records.toList.reverse do
    let (fillHit,strokeHit) := primitive.coverageAt data recordBase position
    if fillHit || strokeHit then
      return some ⟨index.val,by rw [← s.compiled_length]; exact index.isLt⟩
  return none

theorem Scene.hitTestAt_none_outside_viewport (s : Scene) (screenX screenY : Float)
    (outside : (screenX < 0 || screenY < 0 || screenX >= s.mapping.viewportWidth ||
      screenY >= s.mapping.viewportHeight) = true) :
    s.hitTestAt screenX screenY = none := by
  simp [Scene.hitTestAt, outside]

private def overColors (fill stroke : List Float) (opacity : Float)
    (hits : Bool × Bool) (result : Color) : Color :=
  let fa : Float := if hits.1 then fill[3]! else 0
  let sa : Float := if hits.2 then stroke[3]! else 0
  let premul : Color := ⟨stroke[0]!*sa+fill[0]!*fa*(1-sa),stroke[1]!*sa+fill[1]!*fa*(1-sa),stroke[2]!*sa+fill[2]!*fa*(1-sa)⟩
  let layer : NativeGraphics.PremultipliedLayer :=
    ⟨premul.r*opacity,premul.g*opacity,premul.b*opacity,(sa+fa*(1-sa))*opacity⟩
  layer.overOpaque result

/-- Paint `[r,g,b,a]` at a world position: the row of a plain paint, and the
    colour of a gradient at the primitive's local point. -/
private def Primitive.paintAt (p : BackendPrimitive) (paint : Paint) (alpha : Float)
    (position : Float × Float) : List Float :=
  match paint with
  | .gradientRecord _ record =>
    let q := p.transform.inverse.apply position.1 position.2
    let c := record.colorAt q.1 q.2
    [c[0]!,c[1]!,c[2]!,c[3]!*alpha]
  | _ => resolved paint p.style alpha

/-- `paintAt` with the work that does not depend on the position done once. -/
private def Primitive.preparePaint (p : BackendPrimitive) (paint : Paint) (alpha : Float) :
    Float × Float → List Float :=
  match paint with
  | .gradientRecord _ record =>
    let inverse := p.transform.inverse
    fun position =>
      let q := inverse.apply position.1 position.2
      let c := record.colorAt q.1 q.2
      [c[0]!,c[1]!,c[2]!,c[3]!*alpha]
  | _ => let row := resolved paint p.style alpha; fun _ => row

private theorem Primitive.preparePaint_correct (p : BackendPrimitive) (paint : Paint) (alpha : Float)
    (position : Float × Float) : p.preparePaint paint alpha position = p.paintAt paint alpha position := by
  cases paint <;> rfl

private def Primitive.sampleStep (p : BackendPrimitive) (data : Array Float) (base : Nat)
    (position : Float × Float) (result : Color) : Color :=
  overColors (p.paintAt p.style.fill p.style.fillOpacity position)
    (p.paintAt p.style.stroke p.style.strokeOpacity position) p.effectiveOpacity
    (p.coverageAt data base position) result

private structure PreparedSample where
  coverage : PreparedCoverage
  fill : Float × Float → List Float
  stroke : Float × Float → List Float
  opacity : Float

private def PreparedSample.apply (p : PreparedSample) (position : Float × Float) (result : Color) : Color :=
  overColors (p.fill position) (p.stroke position) p.opacity (p.coverage.eval position) result

/-- With no stroke paint the stroke's alpha is the literal 0 on both branches, so the
    stroke test cannot change a sample. Text rectangles are this case. -/
private theorem overColors_no_stroke (fill : List Float) (style : Style) (alpha opacity : Float)
    (hits : Bool × Bool) (result : Color) :
    overColors fill (resolved .none style alpha) opacity hits result =
      overColors fill (resolved .none style alpha) opacity (hits.1,false) result := by
  cases hits with
  | mk a b => cases b <;> rfl

private def Primitive.prepareSample (p : BackendPrimitive) (data : Array Float) (base : Nat) : PreparedSample :=
  let fill := p.preparePaint p.style.fill p.style.fillOpacity
  let stroke := p.preparePaint p.style.stroke p.style.strokeOpacity
  match p.clips,p.dashParts,p.geometry,p.style.stroke with
  | [],none,.rect ..,.none =>
    ⟨.rectFill p.transform.inverse data[base+0]! data[base+1]! data[base+2]! data[base+3]!,
      fill,stroke,p.effectiveOpacity⟩
  | _,_,_,_ => ⟨p.prepareCoverage data base,fill,stroke,p.effectiveOpacity⟩

private theorem Primitive.prepareSample_correct (p : BackendPrimitive) (data : Array Float)
    (base : Nat) (position : Float × Float) (result : Color) :
    (p.prepareSample data base).apply position result = p.sampleStep data base position result := by
  simp only [Primitive.prepareSample]
  split
  next a b c d clips dash geo noStroke =>
    have fillHit := rectHit_eq_fillCondition data base a b c d
      (p.transform.inverse.apply position.1 position.2)
    have covered : (p.coverageAt data base position).1 =
        (fillCondition (.rect a b c d) base).eval
          {data,position := p.transform.inverse.apply position.1 position.2} := by
      simp [Primitive.coverageAt,clips,dash,geo]
    simp only [PreparedSample.apply,PreparedCoverage.eval,Primitive.sampleStep,
      Primitive.preparePaint_correct,noStroke]
    change overColors _ (resolved .none p.style p.style.strokeOpacity) _ _ _ =
      overColors _ (resolved .none p.style p.style.strokeOpacity) _ _ _
    rw [overColors_no_stroke _ _ _ _ (p.coverageAt data base position),covered,fillHit]
  next => simp only [PreparedSample.apply,Primitive.sampleStep,Primitive.preparePaint_correct,
    Primitive.prepareCoverage_correct]

private def sampleFold (items : List BackendPrimitive) (data : Array Float) (position : Float × Float)
    (base : Nat) (initial : Color) : Color × Nat :=
  items.foldl (fun state p =>
    (p.sampleStep data state.2 position state.1,state.2+p.rowCount*4)) (initial,base)

private def Scene.sampleAt (s : Scene) (data : Array Float)
    (screenX screenY : Float) : Color := Id.run do
  if screenX >= s.mapping.viewportWidth || screenY >= s.mapping.viewportHeight then return rgb 255 255 255
  let position := ((screenX-s.mapping.tx)/s.mapping.sx+s.mapping.minX,
    (screenY-s.mapping.ty)/s.mapping.sy+s.mapping.minY)
  let mut result := rgb 255 255 255
  let mut base := 8
  for primitive in s.compiled do
    let (fillHit,strokeHit) := primitive.coverageAt data base position
    let fill := primitive.paintAt primitive.style.fill primitive.style.fillOpacity position
    let stroke := primitive.paintAt primitive.style.stroke primitive.style.strokeOpacity position
    let fa : Float := if fillHit then fill[3]! else 0
    let sa : Float := if strokeHit then stroke[3]! else 0
    -- Compose this element's fill/stroke in premultiplied form, then apply its
    -- non-inherited opacity once to the whole element, including their overlap.
    let premul : Color := ⟨stroke[0]!*sa+fill[0]!*fa*(1-sa),stroke[1]!*sa+fill[1]!*fa*(1-sa),stroke[2]!*sa+fill[2]!*fa*(1-sa)⟩
    let opacity := primitive.effectiveOpacity
    let layer : NativeGraphics.PremultipliedLayer :=
      ⟨premul.r*opacity,premul.g*opacity,premul.b*opacity,(sa+fa*(1-sa))*opacity⟩
    result := layer.overOpaque result
    base := base+primitive.rowCount*4
  return result

private def Scene.sampleAtFold (s : Scene) (data : Array Float)
    (screenX screenY : Float) : Color :=
  if screenX >= s.mapping.viewportWidth || screenY >= s.mapping.viewportHeight then rgb 255 255 255
  else
    let position := ((screenX-s.mapping.tx)/s.mapping.sx+s.mapping.minX,
      (screenY-s.mapping.ty)/s.mapping.sy+s.mapping.minY)
    (sampleFold s.compiled data position 8 (rgb 255 255 255)).1

private theorem Scene.sampleAt_eq_fold (s : Scene) (data : Array Float) (x y : Float) :
    s.sampleAt data x y = s.sampleAtFold data x y := by
  simp [Scene.sampleAt,Scene.sampleAtFold,sampleFold,Primitive.sampleStep,overColors]
  rfl

-- Prepare each primitive once, preserving its packed-data cursor and paint order.
private def prepareSamples (data : Array Float) : List BackendPrimitive → Nat → List PreparedSample
  | [],_ => []
  | p::ps,base => p.prepareSample data base :: prepareSamples data ps (base+p.rowCount*4)

private def prepareSamplesLoop (data : Array Float) : List BackendPrimitive → Nat →
    List PreparedSample → List PreparedSample
  | [],_,acc => acc.reverse
  | p::ps,base,acc => prepareSamplesLoop data ps (base+p.rowCount*4) (p.prepareSample data base::acc)

private theorem prepareSamplesLoop_correct (data : Array Float) (items : List BackendPrimitive)
    (base : Nat) (acc : List PreparedSample) :
    prepareSamplesLoop data items base acc = acc.reverse ++ prepareSamples data items base := by
  induction items generalizing base acc with
  | nil => simp [prepareSamplesLoop,prepareSamples]
  | cons p ps ih => simp [prepareSamplesLoop,prepareSamples,ih,List.reverse_cons,List.append_assoc]

private def prepareSamplesFast (data : Array Float) (items : List BackendPrimitive) (base : Nat) :=
  prepareSamplesLoop data items base []

@[csimp] private theorem prepareSamples_eq_loop :
    prepareSamples = prepareSamplesFast := by
  funext data items base
  simp [prepareSamplesFast,prepareSamplesLoop_correct]

private theorem preparedSamples_fold (data : Array Float) (items : List BackendPrimitive)
    (position : Float × Float) (base : Nat) (initial : Color) :
    (prepareSamples data items base).foldl (fun color run => run.apply position color) initial =
      (sampleFold items data position base initial).1 := by
  induction items generalizing base initial with
  | nil => rfl
  | cons p ps ih =>
    simp only [prepareSamples,List.foldl_cons,Primitive.prepareSample_correct]
    rw [ih]
    rfl

private def Scene.sampleAtPrepared (s : Scene)
    (prepared : List PreparedSample) (screenX screenY : Float) : Color :=
  if screenX >= s.mapping.viewportWidth || screenY >= s.mapping.viewportHeight then rgb 255 255 255
  else
    let position := ((screenX-s.mapping.tx)/s.mapping.sx+s.mapping.minX,
      (screenY-s.mapping.ty)/s.mapping.sy+s.mapping.minY)
    prepared.foldl (fun color run => run.apply position color) (rgb 255 255 255)

private theorem Scene.sampleAtPrepared_correct (s : Scene) (data : Array Float) (x y : Float) :
    s.sampleAtPrepared (prepareSamples data s.compiled 8) x y = s.sampleAt data x y := by
  rw [Scene.sampleAt_eq_fold]
  simp only [Scene.sampleAtPrepared,Scene.sampleAtFold,preparedSamples_fold]

private def Scene.sampleWithData (s : Scene) (data : Array Float) (x y : Nat) : Color := Id.run do
  let mut total : Color := ⟨0,0,0⟩
  for (dx,dy) in pixelSampleOffsets do
    let c := s.sampleAt data (Float.ofNat x+dx) (Float.ofNat y+dy)
    total := ⟨total.r+c.r,total.g+c.g,total.b+c.b⟩
  let n := Float.ofNat pixelSampleOffsets.length
  return ⟨total.r/n,total.g/n,total.b/n⟩

private def Scene.sampleWithPrepared (s : Scene)
    (prepared : List PreparedSample) (x y : Nat) : Color := Id.run do
  let mut total : Color := ⟨0,0,0⟩
  for (dx,dy) in pixelSampleOffsets do
    let c := s.sampleAtPrepared prepared (Float.ofNat x+dx) (Float.ofNat y+dy)
    total := ⟨total.r+c.r,total.g+c.g,total.b+c.b⟩
  let n := Float.ofNat pixelSampleOffsets.length
  return ⟨total.r/n,total.g/n,total.b/n⟩

private theorem Scene.sampleWithPrepared_correct (s : Scene) (data : Array Float) (x y : Nat) :
    s.sampleWithPrepared (prepareSamples data s.compiled 8) x y = s.sampleWithData data x y := by
  simp only [Scene.sampleWithPrepared,Scene.sampleWithData,Scene.sampleAtPrepared_correct]

private def Scene.samplesWithData (s : Scene) (data : Array Float) (coordinates : List (Nat × Nat)) : List Color :=
  coordinates.map (fun (x,y) => s.sampleWithData data x y)

private def Scene.samplesWithDataFast (s : Scene) (data : Array Float) (coordinates : List (Nat × Nat)) : List Color :=
  let prepared := prepareSamples data s.compiled 8
  coordinates.map (fun (x,y) => s.sampleWithPrepared prepared x y)

@[csimp] private theorem Scene.samplesWithData_eq_fast :
    Scene.samplesWithData = Scene.samplesWithDataFast := by
  funext s data coordinates
  simp only [Scene.samplesWithData,Scene.samplesWithDataFast,Scene.sampleWithPrepared_correct]

-- Audit the exact compiled replacements as well as their interpreter theorem.
#print axioms Scene.samplesWithData_eq_fast
#print axioms prepareSamples_eq_loop

private def Scene.sample (s : Scene) (x y : Nat) : Color :=
  s.sampleWithData s.data x y

private def Color.json (c : Color) : String := jsonArray ([c.r,c.g,c.b].map fun f => toString ((max 0 (min 255 (f*255))).round.toUInt32.toNat))
private def floatJSON (x : Float) : String :=
  let integer := x.toInt64.toInt
  if Float.ofInt integer == x then toString integer
  else L4Factoidal.Tdb2.javaDoubleString x.toBits

/-- Reference list formatting stays visible; compilation selects the proved
    memoized twin, preserving every decimal byte and the original order. -/
private def floatJSONList (xs : List Float) : List String := xs.map floatJSON

@[csimp] private theorem floatJSONList_eq_cached :
    floatJSONList = L4Factoidal.Rendering.FloatFormat.formatList := by
  funext xs
  change xs.map L4Factoidal.Rendering.FloatFormat.format = _
  exact (L4Factoidal.Rendering.FloatFormat.formatList_eq_map xs).symm

private def Geometry.name {contourType : Type} : Geometry contourType → String
  | .rect .. => "rect"
  | .circle .. => "circle"
  | .ellipse .. => "ellipse"
  | .line .. => "line"
  | .polygon .. => "polygon"
  | .path .. => "path"

mutual
  private def DisplayNode.json : DisplayNode → String
    | .paint primitive =>
        "{\"kind\":\"paint\",\"geometry\":" ++ quote primitive.geometry.name ++
        "}"
    | .group id transform children =>
        "{\"kind\":\"group\",\"id\":" ++
        (match id with | none => "null" | some value => quote value) ++
        ",\"transform\":" ++ jsonArray
          ([transform.a,transform.b,transform.c,transform.d,transform.e,transform.f].map floatJSON) ++
        ",\"children\":" ++ DisplayNode.listJSON children ++ "}"
    | .clipped id transform clip children =>
        "{\"kind\":\"group\",\"id\":" ++
        (match id with | none => "null" | some value => quote value) ++
        ",\"transform\":" ++ jsonArray
          ([transform.a,transform.b,transform.c,transform.d,transform.e,transform.f].map floatJSON) ++
        ",\"clip\":{\"bounds\":" ++ jsonArray ([clip.x,clip.y,clip.width,clip.height].map floatJSON) ++
        ",\"transform\":" ++ jsonArray
          ([clip.transform.a,clip.transform.b,clip.transform.c,clip.transform.d,clip.transform.e,clip.transform.f].map floatJSON) ++
        "},\"children\":" ++ DisplayNode.listJSON children ++ "}"
  termination_by node => sizeOf node

  private def DisplayNode.listJSON : List DisplayNode → String
    | [] => "[]"
    | node :: rest => "[" ++ DisplayNode.json node ++
        String.join (rest.map fun child => "," ++ DisplayNode.json child) ++ "]"
  termination_by nodes => sizeOf nodes
end

private def base64Table : ByteArray :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toUTF8

/-- Storage floats as the GPU reads them: IEEE 754 binary32, little-endian, in Base64.
Decimal text for these floats was 57% of a frame of the status page. The host stores
them as binary32 either way, so the text form carried nothing more. -/
def float32Base64 (data : Array Float) : String := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (data.size*4)
  for value in data do
    let bits := value.toFloat32.toBits
    bytes := bytes.push bits.toUInt8 |>.push (bits >>> 8).toUInt8
      |>.push (bits >>> 16).toUInt8 |>.push (bits >>> 24).toUInt8
  let whole := bytes.size/3*3
  let mut text := ByteArray.emptyWithCapacity ((bytes.size+2)/3*4)
  for index in [0:whole:3] do
    let a := bytes[index]!
    let b := bytes[index+1]!
    let c := bytes[index+2]!
    text := text.push base64Table[(a >>> 2).toNat]!
      |>.push base64Table[(((a &&& 3) <<< 4) ||| (b >>> 4)).toNat]!
      |>.push base64Table[(((b &&& 15) <<< 2) ||| (c >>> 6)).toNat]!
      |>.push base64Table[(c &&& 63).toNat]!
  if whole+1 == bytes.size then
    let a := bytes[whole]!
    text := text.push base64Table[(a >>> 2).toNat]!
      |>.push base64Table[((a &&& 3) <<< 4).toNat]! |>.push 61 |>.push 61
  else if whole+2 == bytes.size then
    let a := bytes[whole]!
    let b := bytes[whole+1]!
    text := text.push base64Table[(a >>> 2).toNat]!
      |>.push base64Table[(((a &&& 3) <<< 4) ||| (b >>> 4)).toNat]!
      |>.push base64Table[((b &&& 15) <<< 2).toNat]! |>.push 61
  return String.fromUTF8! text

#guard float32Base64 #[1.5,-2.0,0.1] == "AADAPwAAAMDNzMw9"

/-- Lean's expected colors for the GPU readback check. A frame of a page that is
already on screen (`live`) has one probe; each probe costs a pass over the scene. -/
private def Scene.checks (s : Scene) (data : Array Float) (live : Bool := false) : List String :=
  let rawProbes := if live then [(s.width/2,s.height/2)] else
    [(1,1),(s.width/4,s.height/4),(s.width/2,s.height/2),
     (s.width*3/4,s.height/2),(s.width/2,s.height*3/4),(s.width-2,s.height-2)]
  let probes := (rawProbes.map fun (x,y) => (min (s.width-1) x,min (s.height-1) y)).eraseDups
  (probes.zip (s.samplesWithData data probes)).map fun ((x,y),color) => "{\"x\":" ++ toString x ++ ",\"y\":" ++ toString y ++ ",\"rgb\":" ++ color.json ++ "}"

private def Scene.json (s : Scene) (live binary : Bool := false) : Except String String := do
  let data := s.data
  if data.size > maxDataFloats then throw "storage data exceeds 1048576 floats"
  let checks := s.checks data live
  let tree := if DisplayNode.listNodeCount s.tree <= maxInspectorNodes
    then DisplayNode.listJSON s.tree else "null"
  return "{\"abi\":\"lean-svg-v1\",\"profile\":\"painted-primitives-experiment\",\"binding\":\"read-only-storage\",\"width\":" ++ toString s.width ++
    ",\"height\":" ++ toString s.height ++ ",\"primitiveCount\":" ++ toString s.compiled.length ++
    ",\"tree\":" ++ tree ++
    (if binary then ",\"dataBase64\":\"" ++ float32Base64 data ++ "\""
     else ",\"data\":" ++ jsonArray (floatJSONList data.toList)) ++ ",\"tiles\":" ++ jsonArray (s.tiles.toList.map toString) ++ ",\"wgsl\":" ++ sceneShaderJSON ++ ",\"checks\":" ++ jsonArray checks ++ "}"
/-- Serialize an existing checked SVG scene through the same packed-data/WGSL
    producer as the string ABI; no XML serialization or reparsing is required. -/
def Scene.artifact (s : Scene) (live binary : Bool := false) : Except String String := s.json live binary

/-- Each part of the artifact as separate work, so that a tool can time it. A part
returns a size, so that the work is done. -/
def Scene.artifactParts (s : Scene) : List (String × (Unit → Nat)) :=
  let data := s.data
  [("compiled",fun _ => s.compiled.length),
   ("data",fun _ => s.data.size),
   ("checks",fun _ => (s.checks data).length),
   ("tree",fun _ => (DisplayNode.listJSON s.tree).utf8ByteSize),
   ("dataText",fun _ => (jsonArray (floatJSONList data.toList)).utf8ByteSize),
   ("tiles",fun _ => s.tiles.size),
   ("tilesText",fun _ => (jsonArray (s.tiles.toList.map toString)).utf8ByteSize),
   ("wgsl",fun _ => sceneShaderJSON.utf8ByteSize)]

/-- Four-quarter-point CPU reference color for an existing scene. SVG 2 §3
    rendering order and the lab's explicit sample grid match the string ABI. -/
def Scene.samplePixel (s : Scene) (x y : Nat) : Color := s.sample x y

/-- Batch the same CPU reference samples while constructing the packed scene
    array once. Coordinates and operation order within each sample are unchanged. -/
def Scene.samplePixels (s : Scene) (coordinates : List (Nat × Nat)) : List Color :=
  let data := s.data
  s.samplesWithData data coordinates

theorem Scene.samplePixels_eq_samplePixel (s : Scene) (coordinates : List (Nat × Nat)) :
    s.samplePixels coordinates = coordinates.map (fun (x,y) => s.samplePixel x y) := rfl

@[export svg_compile]
def compile (xml : String) (width height : UInt32) : String :=
  match parse xml width.toNat height.toNat >>= Scene.artifact with
  | .ok artifact => artifact | .error message => "{\"error\":" ++ quote message ++ "}"
/-- URL context is supplied by the host; reference resolution stays in Lean. -/
@[export svg_compile_url]
def compileWithURL (xml : String) (width height : UInt32) (documentURL : String) : String :=
  match parse xml width.toNat height.toNat (some documentURL) >>= Scene.artifact with
  | .ok artifact => artifact | .error message => "{\"error\":" ++ quote message ++ "}"
@[export svg_sample]
def sample (xml : String) (width height x y : UInt32) : String :=
  match parse xml width.toNat height.toNat with
  | .error message => "{\"error\":" ++ quote message ++ "}"
  | .ok s => "{\"rgb\":" ++ (s.samplePixel x.toNat y.toNat).json ++ "}"
@[export svg_hit]
def hit (xml : String) (width height : UInt32) (x y : Float) : String :=
  match parse xml width.toNat height.toNat with
  | .error message => "{\"error\":" ++ quote message ++ "}"
  | .ok s =>
    match s.hitTestAt x y with
    | none => "{\"paintIndex\":null}"
    | some index => "{\"paintIndex\":" ++ toString index.val ++ "}"
end NativeSVG
