import SVG

/- SVG Tiny 1.2 §5.1.2: `version` and `baseProfile` on the `svg` element name a language version
   and a profile; they do not change the drawing. Each check compiles one drawing with and without
   the labels and compares the whole compiled scene (the JSON artifact of `NativeSVG.compile`).
   The theorem `NativeSVG.profileLabelsRemoved_cons` states the same for the attribute list. -/
open NativeSVG

private def doc (labels body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' " ++ labels ++ " viewBox='0 0 480 360'>" ++ body ++ "</svg>"
private def same (labels body : String) : Bool :=
  let with_ := compile (doc labels body) 480 360
  let without := compile (doc "" body) 480 360
  with_ == without && !(with_.startsWith "{\"error\"")
private def body1 := "<rect x='10' y='20' width='100' height='50' fill='red'/><circle cx='200' cy='100' r='40' fill='blue' stroke='black'/>"
private def body2 := "<g transform='translate(30 40)'><path d='M0 0 L100 0 L50 80 z' fill='green'/></g>"

#guard same "version='1.2' baseProfile='tiny'" body1
#guard same "version='1.2' baseProfile='tiny'" body2
#guard same "baseProfile='tiny'" body1
#guard same "version='1.1' baseProfile='full'" body2
#guard same "version='1.0' baseProfile='basic'" body1
#guard same "baseProfile='none'" body2
-- Spaces around a label are removed before the check.
#guard same "version=' 1.2 '" body1
-- Unknown labels are refused with a named reason, not ignored.
#guard compile (doc "baseProfile='huge'" body1) 480 360 == "{\"error\":\"unsupported SVG baseProfile label\"}"
#guard compile (doc "version='3.0'" body1) 480 360 == "{\"error\":\"unsupported SVG version label\"}"
-- A nested svg element takes the labels too (SVG 1.1 §5.1.2 allows them there).
#guard same "" ("<svg version='1.2' baseProfile='tiny' x='10' y='10' width='100' height='100'>" ++ body1 ++ "</svg>") &&
  compile (doc "" ("<svg version='1.2' baseProfile='tiny' x='10' y='10' width='100' height='100'>" ++ body1 ++ "</svg>")) 480 360 ==
  compile (doc "" ("<svg x='10' y='10' width='100' height='100'>" ++ body1 ++ "</svg>")) 480 360

/- SVG Tiny 1.2 §5.10.2: `xml:id` gives the element its identifier, as `id` does. A reference to
   it (`use`, a paint server) draws the same as a reference to an `id`. -/
private def withId (key : String) : String :=
  "<defs><linearGradient " ++ key ++ "='g'><stop stop-color='red'/><stop offset='1' stop-color='blue'/></linearGradient>" ++
  "<rect " ++ key ++ "='r' width='50' height='40' fill='url(#g)'/></defs><use href='#r' x='20' y='30'/>"
#guard compile (doc "" (withId "xml:id")) 480 360 == compile (doc "" (withId "id")) 480 360
#guard !((compile (doc "" (withId "xml:id")) 480 360).startsWith "{\"error\"")
-- With two values, xml:id names the element and id is not used.
#guard compile (doc "" "<defs><rect id='a' xml:id='b' width='5' height='5'/></defs><use href='#b'/>") 480 360 ==
  compile (doc "" "<g><rect width='5' height='5'/></g>") 480 360
#guard compile (doc "" "<defs><rect id='a' xml:id='b' width='5' height='5'/></defs><use href='#a'/>") 480 360 ==
  compile (doc "" "") 480 360

/- SVG Tiny 1.2 §23.1: an element in an unknown namespace is private data, not rendered, with
   its subtree (the W3C suite's own `SVGTestCase` description, editor data). -/
private def privateData := "<p:note xmlns:p='urn:example:private'><p:x/><rect width='9' height='9' fill='red'/></p:note>"
#guard compile (doc "" (privateData ++ body1)) 480 360 == compile (doc "" body1) 480 360
-- Refused: no namespace, XML Events (behaviour) and XHTML outside the metadata it reads.
#guard (compile (doc "" "<rect xmlns='' width='1' height='1'/>") 480 360).startsWith "{\"error\":\"foreign/non-SVG element"
#guard (compile (doc "" "<ev:listener xmlns:ev='http://www.w3.org/2001/xml-events' event='click'/>") 480 360).startsWith "{\"error\":\"foreign/non-SVG element"
#guard (compile (doc "" "<h:p xmlns:h='http://www.w3.org/1999/xhtml'>x</h:p>") 480 360).startsWith "{\"error\":\"foreign/non-SVG element"

/- SVG Tiny 1.2 §10.10: font and text properties are read only by `text` and `textArea`. On a
   group of shapes they change nothing; `text` itself stays refused by this reader. -/
#guard compile (doc "" ("<g font-family='serif' font-size='18' text-anchor='middle' font-weight='bold'>" ++ body1 ++ "</g>")) 480 360 ==
  compile (doc "" ("<g>" ++ body1 ++ "</g>")) 480 360
#guard (compile (doc "" "<g font-family='serif'><text>x</text></g>") 480 360).startsWith "{\"error\""

/- SVG Tiny 1.2 §11.11: `viewport-fill` paints the whole viewport before the content, also
   outside the viewBox when the aspect ratio leaves a margin. -/
private def pixelOf (xml : String) (x y : Nat) : List Nat :=
  match parse xml 100 50 with
  | .error _ => []
  | .ok s => let c := s.samplePixel x y; [c.r,c.g,c.b].map fun f => (f*255).round.toUInt32.toNat
private def filled (attrs body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 50 50' " ++ attrs ++ ">" ++ body ++ "</svg>"
-- The viewBox is centred: x 25 to 75 of 100. The margin (x 5) is filled too.
#guard pixelOf (filled "viewport-fill='blue'" "") 5 25 == [0,0,255]
#guard pixelOf (filled "viewport-fill='blue'" "") 95 25 == [0,0,255]
-- The content is drawn over it.
#guard pixelOf (filled "viewport-fill='blue'" "<rect width='50' height='50' fill='lime'/>") 50 25 == [0,255,0]
-- Half opacity over the white page.
#guard pixelOf (filled "viewport-fill='blue' viewport-fill-opacity='0.5'" "") 5 25 == [128,128,255] ||
  pixelOf (filled "viewport-fill='blue' viewport-fill-opacity='0.5'" "") 5 25 == [127,127,255]
-- none and inherit paint nothing.
#guard pixelOf (filled "viewport-fill='none'" "") 5 25 == pixelOf (filled "" "") 5 25
#guard pixelOf (filled "viewport-fill='inherit'" "") 5 25 == pixelOf (filled "" "") 5 25

/- SVG Tiny 1.2 §9.6, §9.7: no `points`, empty `points` or an odd number of coordinates: the
   element is not drawn. -/
#guard compile (doc "" "<polygon fill='red'/>") 480 360 == compile (doc "" "") 480 360
#guard compile (doc "" "<polyline points='' fill='red'/>") 480 360 == compile (doc "" "") 480 360
#guard compile (doc "" "<polygon points='0,0 10,0 10,10 5' fill='red'/>") 480 360 == compile (doc "" "") 480 360

/- SVG Tiny 1.2 §5.1.2 `zoomAndPan`: magnify (the viewer zooms) is taken; disable is refused. -/
#guard compile (doc "zoomAndPan='magnify'" body1) 480 360 == compile (doc "" body1) 480 360
#guard (compile (doc "zoomAndPan='disable'" body1) 480 360).startsWith "{\"error\":\"zoomAndPan disable"
