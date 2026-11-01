import Graphics
import SVGPath
import SVGCSS
import SVGDash
import L4Factoidal.Math.Affine
import L4Factoidal.Tdb2.Format
import L4Factoidal.XML.NamespaceView

/- Isolated strict SVG document reader, not SVG Tiny/full conformance.
   XML and expanded names come from the current Factoidal XML implementation.
   Geometry, paint inheritance, viewBox mapping, shader generation and reference
   sampling are Lean computations; hosts only transfer artifacts and pixels. -/
namespace NativeSVG

-- Bounded storage-backed profile, sized from generated 8/16-person scenes.
def maxInputChars : Nat := 1048576
def maxPrimitives : Nat := 12288
def maxDataFloats : Nat := 262144
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

structure Color where
  r : Float
  g : Float
  b : Float
  deriving Repr
private def rgb (r g b : Nat) : Color := ⟨Float.ofNat r/255,Float.ofNat g/255,Float.ofNat b/255⟩
private def hex (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat-'0'.toNat)
  else if c >= 'a' && c <= 'f' then some (c.toNat-'a'.toNat+10) else none
private def named : List (String × (Nat × Nat × Nat)) := [
  ("black",(0,0,0)),("silver",(192,192,192)),("gray",(128,128,128)),("white",(255,255,255)),
  ("maroon",(128,0,0)),("red",(255,0,0)),("purple",(128,0,128)),("fuchsia",(255,0,255)),
  ("green",(0,128,0)),("lime",(0,255,0)),("olive",(128,128,0)),("yellow",(255,255,0)),
  ("navy",(0,0,128)),("blue",(0,0,255)),("teal",(0,128,128)),("aqua",(0,255,255)),("orange",(255,165,0))]
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
inductive Paint where
  | none | solid (color : Color) | current
  deriving Repr
inductive FillRule where | nonzero | evenodd
  deriving Repr, BEq
inductive LineCap where | butt | round
  deriving Repr, BEq
structure Style where
  fill : Paint := .solid (rgb 0 0 0)
  stroke : Paint := .none
  currentColor : Color := rgb 0 0 0
  strokeWidth : Float := 1
  dashArray : List Float := []
  dashPercent : List Bool := []
  dashOffset : Float := 0
  dashOffsetPercent : Bool := false
  fillOpacity : Float := 1
  strokeOpacity : Float := 1
  rule : FillRule := .nonzero
  lineCap : LineCap := .butt
  deriving Repr
private def readPaint (ids : List String) (source : String) : Except String Paint := do
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
    if ids.contains id then throw "referenced paint server unsupported"
    let fallback := trim fallback
    if fallback.isEmpty || fallback.toLower == "none" then pure .none
    else if fallback.toLower == "currentcolor" then pure .current
    else Paint.solid <$> color fallback
  else if s.toLower == "none" then pure .none
  else if s.toLower == "currentcolor" then pure .current
  else Paint.solid <$> color s
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
  "stroke-linecap","stroke-linejoin","stroke-miterlimit","fill-rule","stroke-dasharray","stroke-dashoffset"]
private def validateAttrs (tag : String) (attrs : List NamespaceAttribute) (extra : List String) : Except String Unit := do
  for a in attrs do
    if a.name.namespace_.isSome then throw s!"qualified attribute unsupported on {tag}: {a.name.localPart}"
    if !(common++extra).contains a.name.localPart then throw s!"unsupported attribute on {tag}: {a.name.localPart}"
private def inheritedNumber (lengths : LengthContext) (attrs : List NamespaceAttribute) (key : String) (old : Float) : Except String Float :=
  match attr attrs key with
  | none => pure old
  | some value => if trim value == "inherit" then pure old else
      if key == "stroke-width" then relativeLength value lengths.diagonal else number value
private def dashArray (lengths : LengthContext) (source : String) : Except String (List Float × List Bool) := do
  if trim source == "none" then return ([],[])
  let groups := source.splitOn ","
  if groups.any (fun g => (trim g).isEmpty) then throw "empty dash list item"
  let tokens := groups.flatMap (fun g => (g.splitOn " " |>.flatMap (·.splitOn "\t") |>.flatMap (·.splitOn "\n") |>.flatMap (·.splitOn "\r")).filter (· != ""))
  if tokens.isEmpty then throw "empty dash list"
  if tokens.length > 64 then throw "dash pattern exceeds 64 entries"
  let values ← NativeSVGDash.normalize (← tokens.mapM (fun t => relativeLength t lengths.diagonal))
  let percentages := tokens.map (fun t => (trim t).endsWith "%")
  return (values,if values.isEmpty then [] else if percentages.length%2==1 then percentages++percentages else percentages)
private def readStyle (lengths : LengthContext) (ids : List String) (attrs : List NamespaceAttribute) (parent : Style) : Except String Style := do
  let mut style := parent
  if let some value := attr attrs "color" then
    if !["inherit","currentcolor"].contains (trim value).toLower then style := {style with currentColor:= ← color value}
  if let some value := attr attrs "fill" then
    if trim value != "inherit" then style := {style with fill:= ← readPaint ids value}
  if let some value := attr attrs "stroke" then
    if trim value != "inherit" then style := {style with stroke:= ← readPaint ids value}
  if let some value := attr attrs "stroke-dasharray" then
    if trim value != "inherit" then
      let (values,percentages) ← dashArray lengths value
      style := {style with dashArray:=values,dashPercent:=percentages}
  if let some value := attr attrs "stroke-dashoffset" then
    if trim value != "inherit" then style := {style with dashOffset:= ← relativeLength value lengths.diagonal,dashOffsetPercent:=(trim value).endsWith "%"}
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
    | _ => throw s!"unsupported stroke-linecap: {value}"
  for (key,allowed) in [("stroke-linejoin",["miter","inherit"]),("stroke-miterlimit",["4","inherit"])] do
    if let some value := attr attrs key then
      if !allowed.contains (trim value) then throw s!"unsupported {key}: {value}"
  return style
private def cssProperties := (common.filter (· != "id")) ++ ["opacity"]
private def cssAttribute (d : NativeSVGCSS.Declaration) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=d.property},value:=d.value}
private def applyCSS (lengths : LengthContext) (ids : List String) (rules : List NativeSVGCSS.Rule)
    (tag : String) (attrs : List NamespaceAttribute) : Except String (List NamespaceAttribute) := do
  let presentation := attrs.filterMap fun a =>
    if a.name.namespace_.isNone && cssProperties.contains a.name.localPart then
      some ({property:=a.name.localPart,value:=a.value} : NativeSVGCSS.Declaration) else none
  let inlineStyle ← NativeSVGCSS.parseDeclarations cssProperties ((attr attrs "style").getD "")
  let validate := fun (d : NativeSVGCSS.Declaration) => do
    if d.property == "opacity" then let _ ← number d.value; pure ()
    else let _ ← readStyle lengths ids [cssAttribute d] {}; pure ()
  let winning ← NativeSVGCSS.cascade validate tag presentation rules inlineStyle
  pure (attrs.filter (fun a => !(a.name.namespace_.isNone && (cssProperties.contains a.name.localPart || a.name.localPart=="style"))) ++ winning.map cssAttribute)

private def geometryNumber (lengths : LengthContext) (attrs : List NamespaceAttribute) (key : String) (fallback : Float := 0) : Except String Float :=
  match attr attrs key with | none => pure fallback | some s => relativeLength s (if ["x","x1","x2","cx","width","rx"].contains key then lengths.width
    else if ["y","y1","y2","cy","height","ry"].contains key then lengths.height else lengths.diagonal)
inductive Geometry where
  | rect (x y width height : Float)
  | circle (cx cy radius : Float)
  | ellipse (cx cy rx ry : Float)
  | line (x1 y1 x2 y2 : Float)
  | polygon (points : List Point)
  | path (contours : List NativeSVGPath.Contour)
  deriving Repr
structure Primitive where
  geometry : Geometry
  style : Style
  opacity : Float := 1
  transform : Transform := identityTransform
  dashParts : Option (List Geometry) := none
  deriving Repr
private def strokeEnabled (style : Style) : Bool :=
  match style.stroke with | .none => false | _ => style.strokeWidth > 0

private def readGeometry (lengths : LengthContext) (tag : String) (attrs : List NamespaceAttribute) (style : Style) : Except String (Option Geometry) := do
  if tag == "rect" then
    let x ← geometryNumber lengths attrs "x"; let y ← geometryNumber lengths attrs "y"
    let w ← geometryNumber lengths attrs "width"; let h ← geometryNumber lengths attrs "height"
    if w < 0 || h < 0 then throw "negative rectangle dimensions"
    return if w == 0 || h == 0 then none else some (.rect x y w h)
  else if tag == "circle" then
    let x ← geometryNumber lengths attrs "cx"; let y ← geometryNumber lengths attrs "cy"; let r ← geometryNumber lengths attrs "r"
    if r < 0 then throw "negative circle radius"
    return if r == 0 then none else some (.circle x y r)
  else if tag == "ellipse" then
    if (attr attrs "rx").isNone || (attr attrs "ry").isNone then throw "ellipse requires explicit numeric rx and ry; auto radii unsupported"
    let x ← geometryNumber lengths attrs "cx"; let y ← geometryNumber lengths attrs "cy"
    let rx ← geometryNumber lengths attrs "rx"; let ry ← geometryNumber lengths attrs "ry"
    if rx < 0 || ry < 0 then throw "negative ellipse radius"
    if strokeEnabled style then throw "ellipse stroke unsupported"
    return if rx == 0 || ry == 0 then none else some (.ellipse x y rx ry)
  else if tag == "line" then
    let x1 ← geometryNumber lengths attrs "x1"; let y1 ← geometryNumber lengths attrs "y1"
    let x2 ← geometryNumber lengths attrs "x2"; let y2 ← geometryNumber lengths attrs "y2"
    return some (.line x1 y1 x2 y2)
  else if tag == "polygon" then
    if strokeEnabled style then throw "polygon stroke/joins unsupported"
    let source ← need (attr attrs "points") "polygon requires points"
    let values ← numbers source
    if values.length < 6 || values.length%2 != 0 || values.length > 128 then throw "polygon requires 3–64 coordinate pairs"
    let pairs := (List.range (values.length/2)).map fun i => Point.mk values[i*2]! values[i*2+1]!
    return some (.polygon pairs)
  else if tag == "path" then
    if strokeEnabled style then throw "linear path stroke/joins unsupported"
    let source := (attr attrs "d").getD ""
    if source.length > 65536 then throw "path data exceeds 65536 characters"
    if (trim source).toLower == "none" then return none
    let contours ← NativeSVGPath.parse number source
    return if contours.isEmpty then none else some (.path contours)
  else throw s!"unsupported SVG element: {tag}"
/-- Dashed stroke union, retained inside one painted primitive. Lines use butt
    strips; only actual dash ends receive caps. Rectangles keep perimeter phase. -/
private def dashedParts (g : Geometry) (style : Style) (authorLength : Option Float) : Except String (Option (List Geometry)) := do
  if style.dashArray.isEmpty || !strokeEnabled style then return none
  let half := style.strokeWidth/2
  let (vertices,closed) ← match g with
    | .line x y u v => pure ([Point.mk x y,Point.mk u v],false)
    | .rect x y w h => pure ([Point.mk x y,Point.mk (x+w) y,Point.mk (x+w) (y+h),Point.mk x (y+h),Point.mk x y],true)
    | _ => throw "dashed strokes currently support rect and line only"
  let edges := vertices.zip vertices.tail
  let lengths : List Float := edges.map (fun (a,b) => Float.sqrt ((b.x-a.x)*(b.x-a.x)+(b.y-a.y)*(b.y-a.y)))
  let total : Float := lengths.foldl (·+·) 0
  if style.dashArray.length != style.dashPercent.length then throw "dash unit provenance count mismatch"
  -- SVG 2 §9.6.1: percentage distances are exempt from pathLength calibration.
  let (pattern,offset) ← match authorLength with
    | none => pure (style.dashArray,style.dashOffset)
    | some author => do
      if author==0 then
        if (style.dashArray.zip style.dashPercent).any (fun (value,percent) => value != 0 && !percent) ||
            (style.dashOffset != 0 && !style.dashOffsetPercent) then
          throw "zero pathLength infinite dash calibration unsupported"
        pure (style.dashArray,style.dashOffset)
      else
        let scale := total/author
        if !scale.isFinite then throw "pathLength calibration exceeds finite range"
        let pattern := (style.dashArray.zip style.dashPercent).map (fun (value,percent) => if percent then value else value*scale)
        pure (pattern,if style.dashOffsetPercent then style.dashOffset else style.dashOffset*scale)
  let spans ← NativeSVGDash.intervals pattern offset total
  let seam := closed && spans.any (fun a => a.first==0 && a.last>0) && spans.any (fun a => a.last==total && a.first<total)
  let pointAt := fun (distance : Float) => Id.run do
    let mut left := distance
    for ((a,b),len) in edges.zip lengths do
      if left <= len then
        let t := if len==0 then 0 else left/len
        return Point.mk (a.x+(b.x-a.x)*t) (a.y+(b.y-a.y)*t)
      left := left-len
    return vertices.headD (Point.mk 0 0)
  let mut parts : Array Geometry := #[]
  for span in spans do
    let mut start := 0
    for ((a,b),len) in edges.zip lengths do
      let lo := max start span.first
      let hi := min (start+len) span.last
      if hi > lo && len > 0 then
        let t := (lo-start)/len
        let u := (hi-start)/len
        parts := parts.push (.line (a.x+(b.x-a.x)*t) (a.y+(b.y-a.y)*t) (a.x+(b.x-a.x)*u) (a.y+(b.y-a.y)*u))
      start := start+len
    if style.lineCap == .round then
      for endpoint in [span.first,span.last] do
        if !(seam && (endpoint==0 || endpoint==total)) then
          let q := pointAt endpoint
          parts := parts.push (.circle q.x q.y half)
  if closed then
    match g with
    | .rect x y w h =>
      for (distance,corner) in [(0,Geometry.rect (x-half) (y-half) half half),
          (w,Geometry.rect (x+w) (y-half) half half),
          (w+h,Geometry.rect (x+w) (y+h) half half),
          (2*w+h,Geometry.rect (x-half) (y+h) half half)] do
        if (distance==0 && seam) || spans.any (fun a => a.first < distance && a.last > distance) then
          parts := parts.push corner
    | _ => pure ()
  if parts.size > 4096 then throw "dash stroke union exceeds 4096 pieces"
  return some parts.toList

private def extraAttrs (tag : String) : List String :=
  match tag with
  | "rect" => ["x","y","width","height","opacity","transform","pathLength"]
  | "circle" => ["cx","cy","r","opacity","transform"]
  | "ellipse" => ["cx","cy","rx","ry","opacity","transform"]
  | "line" => ["x1","y1","x2","y2","opacity","transform","pathLength"]
  | "polygon" => ["points","opacity","transform"]
  | "path" => ["d","opacity","transform"]
  | _ => []
private def whitespace (s : String) : Bool := s.toList.all isXmlSpace
mutual
private def metadata (node : NamespaceNode) : Except String Unit := do
  match node with
  | .other (.text _) | .other (.cdata _) | .other (.comment _) => pure ()
  | _ => throw "descriptive metadata only supports text/comments"
private def readNode (rules : List NativeSVGCSS.Rule) (lengths : LengthContext) (ids : List String) (parent : Transform) (depth : Nat) (style : Style) (node : NamespaceNode) : Except String (List Primitive) := do
  if depth > 32 then throw "SVG group nesting exceeds 32"
  match node with
  | .other (.comment _) => pure []
  | .other (.text s) | .other (.cdata s) => if whitespace s then pure [] else throw "text painting unsupported"
  | .other _ => throw "processing instructions/other XML nodes unsupported"
  | .element name attrs children =>
    if name.namespace_ == some "http://www.w3.org/1999/xhtml" && name.localPart == "link" then
      -- Reftest match/help/author links are inert metadata, not graphics or stylesheets.
      if ![some "match", some "help", some "author"].contains (attr attrs "rel") then throw "unsupported HTML link relation"
      if !children.isEmpty then throw "HTML metadata link must be empty"
      return []
    if name.namespace_ != some svgURI then throw s!"foreign/non-SVG element: {name.localPart}"
    let tag := name.localPart
    if tag == "style" then return []
    let attrs ← applyCSS lengths ids rules tag attrs
    if tag == "metadata" then return []
    if tag == "title" || tag == "desc" then
      validateAttrs tag attrs ["id"]
      for child in children do metadata child
      return []
    else if tag == "g" then
      validateAttrs tag attrs ["transform"]
      let transform ← checkedTransform (parent.compose (← transformList ((attr attrs "transform").getD "")))
      let inherited ← readStyle lengths ids attrs style
      readChildren rules lengths ids transform (depth+1) inherited children
    else
      validateAttrs tag attrs (extraAttrs tag)
      let transform ← checkedTransform (parent.compose (← transformList ((attr attrs "transform").getD "")))
      let inherited ← readStyle lengths ids attrs style
      let authorLength ← match attr attrs "pathLength" with
        | none => pure none
        | some source => do
          let value ← number source
          if value < 0 then throw "negative pathLength"
          pure (some value)
      let geometry ← readGeometry lengths tag attrs inherited
      for child in children do
        match child with
        | .element n _ _ => if n.namespace_ == some svgURI && ["title","desc","metadata"].contains n.localPart then
                              let _ ← readNode rules lengths ids transform (depth+1) inherited child
                              pure ()
                            else throw "graphics children unsupported"
        | .other (.comment _) => pure ()
        | .other (.text s) | .other (.cdata s) => if !whitespace s then throw "text painting unsupported"
        | _ => throw "processing instruction unsupported"
      let opacity ← match attr attrs "opacity" with | none => pure 1 | some s => number s
      geometry.toList.mapM fun g => do
        let dashParts ← dashedParts g inherited authorLength
        pure {geometry:=g,style:=inherited,opacity:=if transform.det == 0 then 0 else max 0 (min 1 opacity),transform,dashParts}
private def readChildren (rules : List NativeSVGCSS.Rule) (lengths : LengthContext) (ids : List String) (parent : Transform) (depth : Nat) (style : Style) (nodes : List NamespaceNode) : Except String (List Primitive) := do
  let mut out : Array Primitive := #[]
  for node in nodes do
    let chunk ← readNode rules lengths ids parent depth style node
    if out.size+chunk.length > maxPrimitives then throw "painted primitive count exceeds 12288"
    out := out ++ chunk.toArray
  return out.toList
end

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
structure Scene where
  width : Nat
  height : Nat
  mapping : Mapping
  primitives : List Primitive
  deriving Repr
private def viewportMapping (w h : Float) (attrs : List NamespaceAttribute) : Except String Mapping := do
  let view ← match attr attrs "viewBox" with
    | none => pure [0,0,w,h] | some value => numbers value
  let [x,y,vw,vh] := view | throw "viewBox requires four numbers"
  if vw <= 0 || vh <= 0 then throw "viewBox dimensions must be positive"
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
          let parsed ← NativeSVGCSS.parseSheet cssProperties (String.join text.toList)
          if out.size+parsed.length > 256 then throw "document CSS rule count exceeds 256"
          out := out ++ parsed.toArray
        else if !(name.namespace_ == some svgURI && ["metadata","title","desc"].contains name.localPart) then
          pending := children ++ pending
  throw "stylesheet traversal exceeds input bound"

def parse (xml : String) (outputWidth outputHeight : Nat := 0) : Except String Scene := do
  if xml.length > maxInputChars then throw "SVG input exceeds 1048576 characters"
  let document ← (parseXML xml).mapError (fun e => s!"XML: {e.message} at {e.position}")
  if let some encoding := document.decl.bind (·.encoding) then
    if encoding.toLower != "utf-8" then throw "SVG host accepts UTF-8 input only"
  if document.doctype.isSome then throw "DOCTYPE/DTD unsupported in SVG profile"
  for node in document.prolog ++ document.epilog do
    match node with | .pi .. => throw "processing instruction unsupported" | _ => pure ()
  let root ← parseNamespaceView xml
  let .element name attrs children := root | throw "SVG root must be an element"
  if name.namespace_ != some svgURI || name.localPart != "svg" then throw "root must be svg in the SVG namespace"
  validateAttrs "svg" attrs ["width","height","viewBox","preserveAspectRatio","version","style"]
  if let some version := attr attrs "version" then
    if !["1.1","2.0"].contains version then throw "unsupported SVG version label"
  for key in ["width","height"] do
    if let some source := attr attrs key then
      let size ← if (trim source).endsWith "%" then
        if outputWidth == 0 || outputHeight == 0 then throw "percentage root dimensions require explicit host output viewport"
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
  let mapping ← viewportMapping w h attrs
  let lengths ← match attr attrs "viewBox" with
    | none => pure ({width:=w,height:=h} : LengthContext)
    | some source => do
      let [_,_,vw,vh] ← numbers source | throw "viewBox requires four numbers"
      pure {width:=vw,height:=vh}
  let ids ← nodeIds root
  let rules ← styleRules root
  let attrs ← applyCSS lengths ids rules "svg" attrs
  validateAttrs "svg" attrs ["width","height","viewBox","preserveAspectRatio","version"]
  let inherited ← readStyle lengths ids attrs {}
  let primitives ← readChildren rules lengths ids identityTransform 0 inherited children
  return {width:=w.ceil.toUInt32.toNat,height:=h.ceil.toUInt32.toNat,mapping,primitives}

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
private def fillCondition (g : Geometry) (base : Nat) : Test :=
  match g with
  | .rect .. => box (scalar base 0) (scalar base 1) (scalar base 2) (scalar base 3)
  | .circle .. => le (squared (.subV (.var .position) (point base 0))) (.mul (scalar base 2) (scalar base 2))
  | .ellipse .. =>
    let dx := Expr.divide (.sub px (scalar base 0)) (scalar base 2)
    let dy := Expr.divide (.sub py (scalar base 1)) (scalar base 3)
    le (.add (.mul dx dx) (.mul dy dy)) (.lit 1)
  | _ => le (.lit 1) (.lit 0)
private def strokeShapeCondition (g : Geometry) (base : Nat) (cap : LineCap) : Test :=
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
    if cap == .butt then butt else
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
private def strokeCondition (g : Geometry) (base : Nat) (cap : LineCap) : Test :=
  .both (.not (le (scalar base 16) (.lit 0))) (strokeShapeCondition g base cap)
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
private def pointBounds (points : List Point) : List Float :=
  match points with
  | [] => [0,0,0,0]
  | p::rest =>
    let bounds := rest.foldl (fun (b : Float × Float × Float × Float) p =>
      (min b.1 p.x,min b.2.1 p.y,max b.2.2.1 p.x,max b.2.2.2 p.y)) (p.x,p.y,p.x,p.y)
    [bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2]
private def geometryRows : Geometry → List Float
  | .rect x y w h | .ellipse x y w h => [x,y,w,h]
  | .circle x y r => [x,y,r,0]
  | .line x y u v => [x,y,u,v]
  | .polygon points => pointBounds points
  | .path contours => pointBounds (contours.flatMap (·.points))
private def Primitive.effectiveOpacity (p : Primitive) : Float :=
  if p.transform.det == 0 then 0 else p.opacity
private def Primitive.rows (p : Primitive) : List Float :=
  let (tag,count) : Nat × Nat := match p.geometry with
    | .rect .. => (1,0) | .circle .. => (2,0) | .ellipse .. => (3,0)
    | .line .. => (4,0) | .polygon points => (5,points.length)
    | .path contours => (6,(NativeSVGPath.edges contours).length)
  geometryRows p.geometry ++ [Float.ofNat tag,Float.ofNat count,
    if p.style.rule == .evenodd then 1 else 0,(if p.style.lineCap == .round then 1 else 0)+(if p.transform.identity then 0 else 2)] ++ resolved p.style.fill p.style p.style.fillOpacity ++
  resolved p.style.stroke p.style p.style.strokeOpacity ++ [p.style.strokeWidth,p.effectiveOpacity,Float.ofNat (p.dashParts.getD []).length,if p.dashParts.isSome then 1 else 0] ++
  (match p.geometry with
   | .polygon points => points.flatMap (fun q => [q.x,q.y]) ++ (if points.length%2 == 1 then [0,0] else [])
   | .path contours => (NativeSVGPath.edges contours).flatMap fun (a,b) => [a.x,a.y,b.x,b.y]
   | _ => []) ++
  ((p.dashParts.getD []).flatMap fun g => geometryRows g ++
    [match g with | .line .. => 4 | .circle .. => 2 | _ => 1,0,0,0] ++
    [0,0,0,0,0,0,0,0,p.style.strokeWidth,0,0,0]) ++
  (if p.transform.identity then [] else
    let t := p.transform.inverse
    (t.toPackedRows floatOps).toList)
private def Scene.data (s : Scene) : Array Float :=
  ([s.mapping.sx,s.mapping.sy,s.mapping.tx,s.mapping.ty,
    s.mapping.minX,s.mapping.minY,s.mapping.viewportWidth,s.mapping.viewportHeight] ++
    s.primitives.flatMap Primitive.rows).toArray
private def Primitive.wgsl (p : Primitive) (base : Nat) : String :=
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
private def shaderCase (tag : Nat) (g : Geometry) : String :=
  s!"case {tag}u: " ++ "{fillHit=" ++ relativeCondition (fillCondition g 0) ++
  ";strokeHit=" ++ relativeCondition (strokeCondition g 0 .butt) ++ ";}\n"
private def Scene.wgsl (_s : Scene) : String :=
  "struct Params {rows:array<vec4f>};\n" ++
  "@group(0) @binding(0) var<storage,read> params:Params;\n" ++
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
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {" ++
  "let vertices=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(vertices[i],0,1); }\n" ++
  "fn samplePixel(pixel:vec4f)->vec4f {" ++
  "var rgb=vec3f(1.0);if any(pixel.xy>=params.rows[1].zw){return vec4f(rgb,1.0);}" ++
  "let worldP=vec4f((pixel.xy-params.rows[0].zw)/params.rows[0].xy+params.rows[1].xy,0,1);" ++
  "var base=2u;\n" ++
  s!"for(var primitive=0u;primitive<{maxPrimitives}u&&base<arrayLength(&params.rows);primitive++)" ++ "{" ++
  "let header=vec4u(params.rows[base+1u]);let tag=header.x;let count=header.y;" ++
  "let shapeRows=select((count+1u)/2u,count,tag==6u);let dashCount=u32(params.rows[base+4u].z);let tailRows=shapeRows+5u*dashCount;var p=worldP;if(header.w>=2u){let tb=base+5u+tailRows;let x=params.rows[tb];let y=params.rows[tb+1u];" ++
  "p=vec4f(dot(x.xy,worldP.xy)+x.z,dot(y.xy,worldP.xy)+y.z,0,1);}" ++
  "var fillHit=false;var strokeHit=false;switch tag {\n" ++
  shaderCase 1 (.rect 0 0 0 0) ++ shaderCase 2 (.circle 0 0 0) ++ shaderCase 3 (.ellipse 0 0 0 0) ++
  "case 4u: {if((header.w%2u)==1u){strokeHit=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .round) ++
  ";}else{strokeHit=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .butt) ++ ";}}\n" ++
  "case 5u:{if(withinBounds(base,p.xy)){fillHit=windingContains(base,count,header.z,p.xy,2u);}}" ++
  "case 6u:{if(withinBounds(base,p.xy)){fillHit=windingContains(base,count,header.z,p.xy,4u);}} default:{} }\n" ++
  "if(params.rows[base+4u].w==1.0){strokeHit=false;let parentBase=base;for(var di=0u;di<dashCount;di++){base=parentBase+5u+shapeRows+di*5u;let dt=u32(params.rows[base+1u].x);var piece=false;" ++
  "if(dt==4u){piece=" ++ relativeCondition (strokeCondition (.line 0 0 0 0) 0 .butt) ++ ";}" ++
  "else if(dt==2u){piece=" ++ relativeCondition (fillCondition (.circle 0 0 0) 0) ++ ";}" ++
  "else{piece=" ++ relativeCondition (fillCondition (.rect 0 0 0 0) 0) ++ ";}strokeHit=strokeHit||piece;}base=parentBase;}" ++
  "let fill=params.rows[base+2u];let stroke=params.rows[base+3u];var element=vec4f(0.0);" ++
  "if fillHit {element=vec4f(fill.rgb*fill.a,fill.a);}" ++
  "if strokeHit {element=vec4f(stroke.rgb*stroke.a,stroke.a)+element*(1.0-stroke.a);}" ++
  "let opacity=params.rows[base+4u].y;rgb=element.rgb*opacity+rgb*(1.0-element.a*opacity);" ++
  "base+=5u+tailRows+select(0u,2u,header.w>=2u);}return vec4f(rgb,1.0); }\n" ++
  "@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {var total=vec4f(0.0);" ++
  String.join (pixelSampleOffsets.map fun (x,y) =>
    "total+=samplePixel(vec4f(pixel.xy+vec2f(" ++ toString (x-0.5) ++ "," ++ toString (y-0.5) ++ "),0.0,1.0));") ++
  "return total/" ++ toString pixelSampleOffsets.length ++ ".0;}\n"

private def Scene.sampleAt (s : Scene) (screenX screenY : Float) : Color := Id.run do
  if screenX >= s.mapping.viewportWidth || screenY >= s.mapping.viewportHeight then return rgb 255 255 255
  let position := ((screenX-s.mapping.tx)/s.mapping.sx+s.mapping.minX,
    (screenY-s.mapping.ty)/s.mapping.sy+s.mapping.minY)
  let data := s.data
  let mut result := rgb 255 255 255
  let mut base := 8
  for primitive in s.primitives do
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
        let mut offset := base+20
        for piece in pieces do
          let condition := match piece with
            | .line .. => strokeCondition piece offset .butt
            | _ => fillCondition piece offset
          hit := hit || condition.eval env
          offset := offset+20
        return hit
    let fill := resolved primitive.style.fill primitive.style primitive.style.fillOpacity
    let stroke := resolved primitive.style.stroke primitive.style primitive.style.strokeOpacity
    let fa : Float := if fillHit then fill[3]! else 0
    let sa : Float := if strokeHit then stroke[3]! else 0
    -- Compose this element's fill/stroke in premultiplied form, then apply its
    -- non-inherited opacity once to the whole element, including their overlap.
    let alpha := sa+fa*(1-sa)
    let premul : Color := ⟨stroke[0]!*sa+fill[0]!*fa*(1-sa),stroke[1]!*sa+fill[1]!*fa*(1-sa),stroke[2]!*sa+fill[2]!*fa*(1-sa)⟩
    let opacity := primitive.effectiveOpacity
    result := ⟨premul.r*opacity+result.r*(1-alpha*opacity),
      premul.g*opacity+result.g*(1-alpha*opacity),
      premul.b*opacity+result.b*(1-alpha*opacity)⟩
    base := base+primitive.rows.length
  return result
private def Scene.sample (s : Scene) (x y : Nat) : Color := Id.run do
  let mut total : Color := ⟨0,0,0⟩
  for (dx,dy) in pixelSampleOffsets do
    let c := s.sampleAt (Float.ofNat x+dx) (Float.ofNat y+dy)
    total := ⟨total.r+c.r,total.g+c.g,total.b+c.b⟩
  let n := Float.ofNat pixelSampleOffsets.length
  return ⟨total.r/n,total.g/n,total.b/n⟩

private def Color.json (c : Color) : String := jsonArray ([c.r,c.g,c.b].map fun f => toString ((max 0 (min 255 (f*255))).round.toUInt32.toNat))
private def floatJSON (x : Float) : String :=
  let integer := x.toInt64.toInt
  if Float.ofInt integer == x then toString integer
  else L4Factoidal.Tdb2.javaDoubleString x.toBits

private def Scene.json (s : Scene) : Except String String := do
  if s.data.size > maxDataFloats then throw "storage data exceeds 262144 floats"
  let rawProbes := [(1,1),(s.width/4,s.height/4),(s.width/2,s.height/2),
    (s.width*3/4,s.height/2),(s.width/2,s.height*3/4),(s.width-2,s.height-2)]
  let probes := (rawProbes.map fun (x,y) => (min (s.width-1) x,min (s.height-1) y)).eraseDups
  let checks := probes.map fun (x,y) => "{\"x\":" ++ toString x ++ ",\"y\":" ++ toString y ++ ",\"rgb\":" ++ (s.sample x y).json ++ "}"
  return "{\"abi\":\"lean-svg-v1\",\"profile\":\"painted-primitives-experiment\",\"binding\":\"read-only-storage\",\"width\":" ++ toString s.width ++
    ",\"height\":" ++ toString s.height ++ ",\"primitiveCount\":" ++ toString s.primitives.length ++
    ",\"data\":" ++ jsonArray (s.data.toList.map floatJSON) ++ ",\"wgsl\":" ++ quote s.wgsl ++ ",\"checks\":" ++ jsonArray checks ++ "}"
@[export svg_compile]
def compile (xml : String) (width height : UInt32) : String :=
  match parse xml width.toNat height.toNat >>= Scene.json with
  | .ok artifact => artifact | .error message => "{\"error\":" ++ quote message ++ "}"
@[export svg_sample]
def sample (xml : String) (width height x y : UInt32) : String :=
  match parse xml width.toNat height.toNat with
  | .error message => "{\"error\":" ++ quote message ++ "}"
  | .ok s => "{\"rgb\":" ++ (s.sample x.toNat y.toNat).json ++ "}"
end NativeSVG
