import SVGForgiving

/- SVG Tiny 1.2 §11.13 to §11.16: paint servers, through the CPU reference. The
   expected values are stated from the specification; the GPU run is checked
   against the same reference in svg_test.ts. -/
open NativeSVG

private def svg (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' viewBox='0 0 100 100'>" ++ body ++ "</svg>"
private def scene (body : String) := (parse (svg body) 100 100).toOption
private def pixel (body : String) (x y : Nat) : List Nat :=
  match scene body with
  | none => []
  | some s =>
    let c := s.samplePixel x y
    [c.r,c.g,c.b].map fun f => (f*255).round.toUInt32.toNat
private def close (a b : List Nat) (tolerance : Nat := 3) : Bool :=
  a.length == b.length && (a.zip b).all fun (x,y) => (if x < y then y-x else x-y) <= tolerance
private def full := "<rect width='100' height='100' fill='url(#g)'/>"
private def redBlue := "<stop stop-color='red'/><stop offset='1' stop-color='blue'/>"
private def redBlueGradient (attrs : String) := s!"<linearGradient id='g' {attrs}>{redBlue}</linearGradient>"

-- Linear, object bounding box by default: x runs from 0 to 1 across the box.
#guard close (pixel (redBlueGradient "" ++ full) 0 50) [254,0,1]
#guard close (pixel (redBlueGradient "" ++ full) 50 50) [127,0,128]
#guard close (pixel (redBlueGradient "" ++ full) 99 50) [1,0,254]
-- The box is that of the shape, wherever the shape is.
#guard close (pixel (redBlueGradient "" ++ "<rect x='50' width='50' height='10' fill='url(#g)'/>") 75 5) [127,0,128]
-- A percentage in bounding box units is of the box.
#guard close (pixel (redBlueGradient "x2='50%'" ++ full) 25 50) [127,0,128]
-- User space: pad spread after the last stop, and the element's own transform.
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='50'" ++ full) 75 50) [0,0,255]
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x1='50' x2='100'" ++ full) 25 50) [255,0,0]
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='50'" ++
  "<rect width='50' height='100' transform='translate(50 0)' fill='url(#g)'/>") 75 50) [127,0,128]
-- gradientTransform: a quarter turn makes the gradient run down the box.
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='100' gradientTransform='rotate(90)'" ++ full) 50 25) [191,0,64]
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='100' gradientTransform='rotate(90)'" ++ full) 90 25) [191,0,64]
-- A singular gradient transform paints nothing.
#guard pixel (redBlueGradient "gradientTransform='scale(0)'" ++ full) 50 50 == [255,255,255]

-- Radial, defaults: centre at 50%, radius 50% of the box; pad spread outside.
private def radial (attrs : String) := s!"<radialGradient id='g' {attrs}>{redBlue}</radialGradient>"
#guard close (pixel (radial "" ++ full) 50 50) [255,0,0] 6
#guard close (pixel (radial "" ++ full) 75 50) [127,0,128] 6
#guard close (pixel (radial "" ++ full) 1 1) [0,0,255]
#guard close (pixel (radial "gradientUnits='userSpaceOnUse' cx='0' cy='0' r='100'" ++ full) 50 0) [127,0,128] 6
-- r of zero paints the last stop; a negative r is refused.
#guard pixel (radial "r='0'" ++ full) 50 50 == [0,0,255]
#guard (scene (radial "r='-1'" ++ full)).isNone

-- xlink:href takes stops and common attributes; coordinates only from a like kind.
private def chain := "<linearGradient id='base'>" ++ redBlue ++ "</linearGradient>" ++
  "<linearGradient id='mid' xlink:href='#base' x2='50%'/>"
#guard close (pixel (chain ++ "<linearGradient id='g' xlink:href='#mid'/>" ++ full) 25 50) [127,0,128]
#guard close (pixel (chain ++ "<linearGradient id='g' xlink:href='#mid' x2='100%'/>" ++ full) 50 50) [127,0,128]
#guard close (pixel (chain ++ "<radialGradient id='g' xlink:href='#mid'/>" ++ full) 75 50) [127,0,128] 6
#guard close (pixel (chain ++ "<linearGradient id='g' xlink:href='#mid'><stop stop-color='lime'/></linearGradient>" ++ full) 25 50) [0,255,0]
-- A cycle is refused; a target that is not a gradient ends the chain.
#guard (scene ("<linearGradient id='g' xlink:href='#h'/><linearGradient id='h' xlink:href='#g'/>" ++ full)).isNone
#guard pixel ("<linearGradient id='g' xlink:href='#r'/><rect id='r' width='1' height='1'/>" ++ full) 50 50 == [255,255,255]

-- One stop is a solid colour, with its opacity; no stops are `none`, fallback or not.
#guard pixel ("<linearGradient id='g'><stop offset='1' stop-color='lime'/></linearGradient>" ++ full) 50 50 == [0,255,0]
#guard close (pixel ("<linearGradient id='g'><stop stop-color='lime' stop-opacity='.5'/></linearGradient>" ++ full) 50 50) [127,255,127]
#guard pixel ("<linearGradient id='g'/><rect width='100' height='100' fill='url(#g) red'/>") 50 50 == [255,255,255]
-- A box with no height disables a bounding box gradient: fallback, else nothing.
private def flat (stroke : String) := s!"<linearGradient id='g'>{redBlue}</linearGradient>" ++
  s!"<line x1='0' y1='50' x2='100' y2='50' stroke-width='9' stroke='{stroke}'/>"
#guard pixel (flat "url(#g) lime") 50 50 == [0,255,0]
#guard pixel (flat "url(#g)") 50 50 == [255,255,255]
-- A diagonal line has a box, and its stroke takes the gradient.
#guard close (pixel (s!"<linearGradient id='g'>{redBlue}</linearGradient>" ++
  "<line x1='0' y1='0' x2='100' y2='100' stroke-width='9' stroke='url(#g)'/>") 50 50) [127,0,128]
-- User space does not need a box.
#guard close (pixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='100'" ++
  "<line x1='0' y1='50' x2='100' y2='50' stroke-width='9' stroke='url(#g)'/>") 50 50) [127,0,128]

-- Offsets clamp to 0..1 and to no less than any earlier one; the last of equal offsets wins.
private def stops (body : String) := s!"<linearGradient id='g'>{body}</linearGradient>" ++ full
#guard pixel (stops "<stop stop-color='red'/><stop offset='.5' stop-color='lime'/><stop offset='.1' stop-color='blue'/>") 75 50 == [0,0,255]
#guard pixel (stops "<stop stop-color='red'/><stop offset='.5' stop-color='lime'/><stop offset='.1' stop-color='blue'/>") 49 50 != [0,0,255]
#guard pixel (stops "<stop offset='-3' stop-color='red'/><stop offset='300%' stop-color='blue'/>") 99 50 != [0,0,255]
#guard close (pixel (stops "<stop offset='-3' stop-color='red'/><stop offset='300%' stop-color='blue'/>") 50 50) [127,0,128]
-- Colour and opacity interpolate apart: halfway from opaque red to clear blue.
#guard close (pixel (stops "<stop stop-color='red'/><stop offset='1' stop-color='blue' stop-opacity='0'/>") 50 50) [191,127,191] 4
-- fill-opacity multiplies the stop opacity.
#guard close (pixel ("<linearGradient id='g'><stop stop-color='lime'/></linearGradient>" ++
  "<rect width='100' height='100' fill='url(#g)' fill-opacity='.5'/>") 50 50) [127,255,127]

-- stop-color: `inherit` and currentColor resolve where the stop stands, and
-- `style` and a type rule reach a stop.
#guard pixel ("<g stop-color='lime'><linearGradient id='g' stop-color='inherit'><stop stop-color='inherit'/></linearGradient></g>" ++ full) 50 50 == [0,255,0]
#guard pixel ("<g color='lime'><linearGradient id='g'><stop stop-color='currentColor'/></linearGradient></g><g color='red'>" ++ full ++ "</g>") 50 50 == [0,255,0]
#guard pixel ("<g stop-color='lime'><linearGradient id='g'><stop/></linearGradient></g>" ++ full) 50 50 == [0,0,0]
#guard pixel (stops "<stop style='stop-color:lime'/>") 50 50 == [0,255,0]
#guard pixel ("<style>stop {stop-color:lime}</style>" ++ stops "<stop/>") 50 50 == [0,255,0]

-- solidColor is a paint server with no bounding box rule.
#guard pixel ("<solidColor id='g' solid-color='lime'/>" ++ full) 50 50 == [0,255,0]
#guard close (pixel ("<solidColor id='g' solid-color='lime' solid-opacity='.5'/>" ++ full) 50 50) [127,255,127]
#guard pixel ("<g solid-color='lime'><solidColor id='g' solid-color='inherit'/></g>" ++
  "<line x1='0' y1='50' x2='100' y2='50' stroke-width='9' stroke='url(#g)'/>") 50 50 == [0,255,0]
-- An element that is no paint server gives the fallback.
#guard pixel ("<rect id='g' width='1' height='1'/><rect width='100' height='100' fill='url(#g) lime'/>") 50 50 == [0,255,0]
-- A stop or a server draws nothing where it stands.
#guard pixel ("<g><linearGradient id='g'/><solidColor id='s'/><stop/></g>") 50 50 == [255,255,255]

-- The stated limit: 64 stops are read; one more is a refusal that names the limit.
private def manyStops (n : Nat) := String.join (List.replicate n "<stop stop-color='lime'/>")
#guard (scene (stops (manyStops 64))).isSome
#guard (parse (svg (stops (manyStops 65))) 100 100) matches .error "gradient stop count exceeds 64"

-- Spread methods and focal points are outside the Tiny profile. The strict reader
-- refuses them; the forgiving pass draws without them and logs each one.
#guard (scene ("<radialGradient id='g' fx='0'>" ++ redBlue ++ "</radialGradient>" ++ full)).isNone
#guard (scene ("<linearGradient id='g' spreadMethod='reflect'>" ++ redBlue ++ "</linearGradient>" ++ full)).isNone
#guard (scene ("<linearGradient id='g' spreadMethod='pad'>" ++ redBlue ++ "</linearGradient>" ++ full)).isSome
private def forgiven (body : String) : List String :=
  match NativeSVGForgiving.parse (svg body) 100 100 with
  | .ok (_,log) => log | .error message => [message]
#guard (forgiven ("<radialGradient id='g' fx='0'>" ++ redBlue ++ "</radialGradient>" ++ full)).contains "attribute: radialGradient fx"
#guard (forgiven (redBlueGradient "" ++ full)).isEmpty

private def forgivenPixel (body : String) (x y : Nat) : List Nat :=
  match NativeSVGForgiving.parse (svg body) 100 100 with
  | .error _ => []
  | .ok (s,_) => let c := s.samplePixel x y; [c.r,c.g,c.b].map fun f => (f*255).round.toUInt32.toNat

-- A glyph paints in the user space of its text, with the box of its text.
private def font : NativeSVGForgiving.SVGFont :=
  match NativeSVGForgiving.SVGFont.parse "<svg xmlns='http://www.w3.org/2000/svg'><font horiz-adv-x='1000'><font-face font-family='T' units-per-em='1000' ascent='1000' descent='0'/><glyph unicode='a' d='M0 0H1000V1000H0Z'/></font></svg>" with
  | .ok f => f | .error _ => {}
private def textPixel (body : String) (x y : Nat) : List Nat :=
  match NativeSVGForgiving.parse (svg body) 100 100 (some font) with
  | .error _ => []
  | .ok (s,_) =>
    let c := s.samplePixel x y
    [c.r,c.g,c.b].map fun f => (f*255).round.toUInt32.toNat
#guard close (textPixel (redBlueGradient "" ++ "<text x='0' y='50' font-size='50' fill='url(#g)'>aa</text>") 50 25) [127,0,128]
#guard close (textPixel (redBlueGradient "" ++ "<text x='0' y='50' font-size='50' fill='url(#g)'>aa</text>") 1 25) [254,0,1] 4
#guard close (textPixel (redBlueGradient "gradientUnits='userSpaceOnUse' x2='100'" ++
  "<text x='0' y='50' font-size='50' fill='url(#g)'>aa</text>") 75 25) [64,0,191]
-- An instance of text takes its font from the `use` element.
#guard textPixel "<defs><text id='t' y='50'>a</text></defs><use xlink:href='#t' font-size='50'/>" 25 25 == [0,0,0]
#guard textPixel "<defs><text id='t' y='50'>a</text></defs><use xlink:href='#t' x='50' font-size='50'/>" 25 25 == [255,255,255]
#guard textPixel "<defs><g id='t'><text y='50'>a</text></g></defs><use xlink:href='#t' fill='lime' font-size='50'/>" 25 25 == [0,255,0]
-- A paint server in a branch of `switch` that is not drawn can still be used.
#guard textPixel "<switch><rect width='1' height='1'/><linearGradient id='g'><stop stop-color='lime'/></linearGradient></switch><rect width='100' height='100' fill='url(#g)'/>" 50 50 == [0,255,0]
#guard textPixel "<switch><rect width='1' height='1' fill='lime'/><rect width='100' height='100' fill='red'/></switch>" 50 50 == [255,255,255]

-- A stroke narrower than the samples: https://github.com/danbri/factoidal/issues/1253.
-- A stroke of width 0.3 on a pixel edge is about 15% in each pixel.
#guard close (pixel "<rect x='50' width='40' height='100' fill='none' stroke='black' stroke-width='0.3'/>" 50 50) [216,216,216] 6
#guard close (pixel "<rect x='50' width='40' height='100' fill='none' stroke='black' stroke-width='0.3'/>" 49 50) [216,216,216] 6
-- A stroke of width 0.25 in a pixel is about 25%, and the same on a transform.
#guard close (pixel "<line x1='50.5' y1='0' x2='50.5' y2='100' stroke='black' stroke-width='0.25'/>" 50 50) [191,191,191] 8
#guard close (pixel "<g transform='scale(0.25)'><line x1='202' y1='0' x2='202' y2='400' stroke='black'/></g>" 50 50) [191,191,191] 8
-- A dashed thin stroke keeps its dashes, and a diagonal thin stroke has no gap.
#guard pixel "<line x1='0' y1='50.5' x2='100' y2='50.5' stroke='black' stroke-width='0.25' stroke-dasharray='10'/>" 15 50 == [255,255,255]
#guard (List.range 40).all fun i => (pixel "<line x1='0' y1='3' x2='100' y2='97' stroke='black' stroke-width='0.2'/>" (30+i) ((600+94*(2*(30+i)+1))/200)).head! < 255
-- A thin filled rectangle: the area times the opacity stays the same.
#guard close (pixel "<rect x='50.4' y='0' width='0.25' height='100'/>" 50 50) [191,191,191] 8

#guard pixel "<rect width='100' height='100' fill='currentColor' color='lime'/>" 50 50 == [0,255,0]
-- A system colour has a value, in any case.
#guard pixel "<rect width='100' height='100' fill='ButtonText'/>" 50 50 == [0,0,0]
#guard pixel "<rect width='100' height='100' fill='WINDOW'/><rect width='9' height='9' fill='infoBackground'/>" 5 5 == [255,255,225]
-- A paint value in error is as if not specified (W3C styling-pres-01-t).
#guard forgivenPixel "<g fill='lime'><rect width='100' height='100' fill='red !important'/></g>" 50 50 == [0,255,0]

-- Expected failures. Each guard states the present wrong result, so the build
-- fails when the fault is repaired; then state the right result and close the issue.
-- https://github.com/danbri/factoidal/issues/1260: this thin path must draw 10% grey.
#guard pixel "<path d='M50.5 0h0.1v100h-0.1z'/>" 50 50 == [255,255,255]
-- https://github.com/danbri/factoidal/issues/1265: W3C paint-color-05-t wants the colour of the `g`; this is CSS Color 4.
#guard pixel "<g fill='currentColor' color='lime'><rect width='100' height='100' color='blue'/></g>" 50 50 == [0,0,255]
-- https://github.com/danbri/factoidal/issues/1254: animation of a paint must run.
#guard (forgiven ("<solidColor id='g' solid-color='red'><animate attributeName='solid-color' to='lime' dur='1s'/></solidColor>" ++ full)).contains "element: animate"
-- https://github.com/danbri/factoidal/issues/1255: a paint in another document must be fetched.
#guard (scene "<rect width='100' height='100' fill='url(other.svg#g) lime'/>").isNone
