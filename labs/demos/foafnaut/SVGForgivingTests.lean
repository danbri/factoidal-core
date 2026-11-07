import SVGForgiving

open NativeSVGForgiving

private def svg (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' version='1.2' baseProfile='tiny' viewBox='0 0 40 40'>" ++ body ++ "</svg>"
private def result (body : String) := (parse (svg body) 40 40).toOption
private def primitives (body : String) : Nat := ((result body).map (·.1.compiled.length)).getD 999
private def log (body : String) : List String := ((result body).map (·.2)).getD []

-- The strict reader refuses these documents; the forgiving pass draws the rest.
#guard (NativeSVG.parse (svg "<rect width='9' height='9'/>") 40 40).toOption.isNone
#guard primitives "<rect width='9' height='9'/>" == 1
#guard primitives "<text>label</text><rect width='9' height='9'/>" == 1
#guard (log "<text>label</text>").contains "element: text"
#guard (log "<foo xmlns='urn:x'/>").contains "foreign element: foo"
#guard (log "<g font-size='9'/>").contains "attribute: g font-size"
-- A value the reader refuses removes that element only, and is logged.
#guard primitives "<rect width='-1' height='9'/><rect width='9' height='9'/>" == 1
#guard (log "<rect width='-1' height='9'/>").any (·.startsWith "removed rect")
-- A colour the reader refuses goes alone, and the element stays (W3C styling-pres-01-t).
#guard primitives "<rect fill='nocolour' width='9' height='9'/><rect width='9' height='9'/>" == 2
#guard (log "<rect fill='nocolour' width='9' height='9'/>").contains "approximated: colour nocolour"

-- Text. `font` has the glyph shapes that these guards tell apart by position.
private def tfont : SVGFont :=
  match SVGFont.parse "<svg xmlns='http://www.w3.org/2000/svg'><font horiz-adv-x='1000'><font-face font-family='T' units-per-em='1000' ascent='1000' descent='0'/><glyph unicode=' ' horiz-adv-x='500'/><glyph unicode='a' glyph-name='a' d='M0 0H1000V1000H0Z'/><glyph unicode='ab' glyph-name='ab' horiz-adv-x='2000' d='M0 0H2000V500H0Z'/><glyph unicode='b' glyph-name='b' d='M0 0H1000V500H0Z'/><glyph unicode='c' lang='fr' d='M0 0H1000V1000H0Z'/><glyph unicode='&#x69A;' arabic-form='isolated' d='M0 0H1000V1000H0Z'/><glyph unicode='&#x69A;' arabic-form='initial' d='M0 0H1000V500H0Z'/><glyph unicode='&#x69A;' arabic-form='terminal' d='M0 500H1000V1000H0Z'/><hkern u1='U+0061' u2='a' k='500'/></font></svg>" with
  | .ok f => f | .error _ => {}
private def tpixel (body : String) (x y : Nat) : Float :=
  match parse (svg body) 40 40 (some tfont) with
  | .error _ => -1
  | .ok (s,_) => (s.samplePixel x y).r
private def inked (body : String) (x y : Nat) : Bool := tpixel body x y == 0
private def clear (body : String) (x y : Nat) : Bool := tpixel body x y == 1
-- xml:space: a newline goes by default, and is a space under preserve.
#guard inked "<text x='0' y='10' font-size='10'>a\na</text>" 12 5 && clear "<text x='0' y='10' font-size='10' xml:space='preserve'>a\n a</text>" 12 5
#guard inked "<text x='0' y='10' font-size='10' xml:space='preserve'> a</text>" 8 5 && clear "<text x='0' y='10' font-size='10' xml:space='preserve'> a</text>" 2 5
-- A no-break space with no glyph draws as a space, not as the missing glyph.
#guard inked "<text x='0' y='10' font-size='10'>&#160;a</text>" 8 5
-- rotate turns a glyph about its origin, and the last value holds.
#guard inked "<text x='20' y='20' font-size='10' rotate='90'>a</text>" 25 25 && clear "<text x='20' y='20' font-size='10' rotate='90'>a</text>" 25 15
-- A tspan with x starts a chunk, with its own anchor.
#guard inked "<text x='0' y='10' font-size='10'>a<tspan x='30' text-anchor='end'>a</tspan></text>" 25 5
-- A ligature wins where it stands first; `lang` selects, and a fragment suits a language.
#guard inked "<text x='0' y='10' font-size='10'>ab</text>" 15 8 && clear "<text x='0' y='10' font-size='10'>ab</text>" 15 2
#guard inked "<text x='0' y='10' font-size='10' xml:lang='fr-ca'>c</text>" 5 2
#guard clear "<text x='0' y='10' font-size='10' xml:lang='de'>c</text>" 5 2
-- hkern with u1 and u2, by a range and by a character.
#guard clear "<text x='0' y='10' font-size='10'>aa</text>" 16 5
-- arabic-form follows joins, and the order is right to left.
#guard inked "<text x='0' y='10' font-size='10'>&#x69A;&#x69A;</text>" 15 8 && clear "<text x='0' y='10' font-size='10'>&#x69A;&#x69A;</text>" 15 2

-- Conditions. Each list must hold in full; an SVG 1.1 feature string is unknown.
private def feature (name : String) := "http://www.w3.org/Graphics/SVG/feature/1.2/#" ++ name
#guard primitives s!"<rect width='9' height='9' requiredFeatures='{feature "Shape"} {feature "Text"}'/>" == 1
#guard primitives s!"<rect width='9' height='9' requiredFeatures='{feature "Shape"} {feature "Animation"}'/>" == 0
#guard primitives "<rect width='9' height='9' requiredFeatures='http://www.w3.org/TR/SVG11/feature#BasicText'/>" == 0
#guard primitives "<rect width='9' height='9' requiredFeatures=''/>" == 0
#guard primitives "<rect width='9' height='9' requiredFormats='image/png image/svg+xml'/>" == 1
#guard primitives "<rect width='9' height='9' requiredFormats='image/png foo/foo'/>" == 0
#guard ((parse (svg "<rect width='9' height='9' requiredFonts='T'/>") 40 40 (some tfont)).toOption.map (·.1.compiled.length)) == some 1
#guard primitives "<rect width='9' height='9' requiredFonts='T'/>" == 0

-- `use` of another document. Only bytes that the host supplies are read.
private def linked (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' width='40' height='40'>" ++ body ++ "</svg>"
private def otherRect := linked "<rect id='r' width='40' height='40' fill='lime'/>"
private def main_ := "http://h.invalid/a/main.svg"
private def otherKey := "http://h.invalid/a/b.svg"
private def useOther := linked "<use xlink:href='b.svg#r'/>"
private def green (xml : String) (supplied : List (String × ByteArray)) : Bool :=
  match NativeSVGForgiving.parse xml 40 40 none supplied (some main_) with
  | .ok (s,_) => let c := s.samplePixel 20 20; c.g == 1 && c.r == 0
  | .error _ => false
#guard green useOther [(otherKey,otherRect.toUTF8)]
#guard !green useOther []
-- Without its bytes the `use` goes alone, and is logged with the document.
#guard match NativeSVGForgiving.parse (linked "<g><use xlink:href='b.svg#r'/><rect width='9' height='9'/></g>") 40 40 none [] (some main_) with
  | .ok (s,log) => s.compiled.length == 1 && log.contains s!"removed use: document not supplied: {otherKey}"
  | .error _ => false
-- Ids of the other document do not meet ids of this one.
#guard green (linked "<rect id='r' width='1' height='1' fill='red'/><use xlink:href='b.svg#r'/>") [(otherKey,otherRect.toUTF8)]
-- The host asks for the document, then for what that document names.
#guard (NativeSVGForgiving.imageRequests useOther (some main_)).toOption == some [otherKey]
private def nested := linked "<use id='r' xlink:href='c.svg#s'/>"
#guard (NativeSVGForgiving.imageRequests useOther (some main_) [(otherKey,nested.toUTF8)]).toOption == some ["http://h.invalid/a/c.svg"]
#guard green useOther [(otherKey,nested.toUTF8),("http://h.invalid/a/c.svg",(linked "<rect id='s' width='40' height='40' fill='lime'/>").toUTF8)]
-- `font-face-uri` names a font in another document; the referring face gives the family.
private def fontDoc := "<svg xmlns='http://www.w3.org/2000/svg'><font id='f' horiz-adv-x='1000'><font-face font-family='Other' units-per-em='1000' ascent='1000' descent='0'/><glyph unicode='a' d='M0 0H1000V1000H0Z'/></font></svg>"
private def fontUse := linked "<font-face font-family='L'><font-face-src><font-face-uri xlink:href='b.svg#f'/></font-face-src></font-face><text font-family='L' font-size='40' y='40' fill='lime'>a</text>"
#guard green fontUse [(otherKey,fontDoc.toUTF8)]
#guard (NativeSVGForgiving.imageRequests fontUse (some main_)).toOption == some [otherKey]
-- A cycle of documents ends: each document is imported once.
#guard (NativeSVGForgiving.parse useOther 40 40 none [(otherKey,(linked "<use id='r' xlink:href='main.svg#x'/>").toUTF8)] (some main_)).toOption.isSome
#guard (NativeSVGForgiving.parse useOther 40 40 none [(otherKey,(linked "<use id='r' xlink:href='b.svg#r'/>").toUTF8)] (some main_)).toOption.isSome
-- Bytes that are not XML draw nothing and stop nothing.
#guard !green useOther [(otherKey,"<svg".toUTF8)]
-- Not well-formed XML stays an error.
#guard (parse "<svg" 40 40).toOption.isNone

-- Rounded rectangles draw as one path; a zero radius stays a rectangle.
private def strict (body : String) : Option NativeSVG.Scene :=
  (NativeSVG.parse ("<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 40 40'>" ++ body ++ "</svg>") 40 40).toOption
#guard (strict "<rect width='20' height='20' rx='5'/>").isSome
#guard (strict "<rect width='20' height='20' rx='0'/>").isSome
-- clip-path takes one rect; other shapes stay a named refusal.
#guard (strict "<defs><clipPath id='c'><rect width='9' height='9'/></clipPath></defs><g clip-path='url(#c)'><rect width='20' height='20'/></g>").isSome
#guard (strict "<defs><clipPath id='c'><circle r='9'/></clipPath></defs><g clip-path='url(#c)'><rect width='20' height='20'/></g>").isNone

-- Text lowers to glyph paths; x lists, anchors and missing fonts behave.
private def font : SVGFont := match SVGFont.parse "<svg xmlns='http://www.w3.org/2000/svg'><font horiz-adv-x='500'><font-face font-family='T' units-per-em='1000'/><glyph unicode='a' glyph-name='a' d='M0 0H100V100Z'/><glyph unicode=' ' glyph-name='space'/></font></svg>" with
  | .ok f => f | .error _ => {}
private def withFont (body : String) : Nat := match parse (svg body) 40 40 (some font) with
  | .ok (scene,_) => scene.compiled.length | .error _ => 999
#guard withFont "<text x='1' y='9' font-size='9'>aa a</text>" == 3
#guard withFont "<text x='1 5 9' y='9' font-size='9'><tspan fill='red'>aa</tspan>a</text>" == 3
#guard withFont "<text font-size='0'>aa</text>" == 0
#guard withFont "<switch><rect systemLanguage='fr' width='9' height='9'/><rect width='5' height='5'/><rect width='3' height='3'/></switch>" == 1
#guard withFont "<a><rect width='9' height='9'/></a>" == 1
#guard primitives "<rect stroke='black' stroke-linejoin='round' width='9' height='9'/>" == 1
-- The reader draws each join, cap and miter limit; only a value it refuses is logged.
#guard (log "<rect stroke='black' stroke-linejoin='round' stroke-linecap='square' stroke-miterlimit='9' width='9' height='9'/>").all (!·.startsWith "approximated")
#guard (log "<rect stroke='black' stroke-linejoin='arcs' width='9' height='9'/>").contains "approximated: stroke-linejoin"
#guard (log "<rect stroke='black' stroke-miterlimit='.5' width='9' height='9'/>").contains "approximated: stroke-miterlimit"
-- A value the reader refuses goes; the same property with a valid value stays.
private def offsetKept : Bool := match parse (svg "<g stroke-dashoffset='none'><line x2='30' stroke='black' stroke-dasharray='5' stroke-dashoffset='5'/></g>") 40 40 with
  | .ok (scene,log) => log.contains "approximated: stroke-dashoffset" &&
      scene.primitives.any (fun p => p.style.dashOffset.value == 5)
  | .error _ => false
#guard offsetKept

-- textArea (SVG Tiny 1.2 §10.11). The glyph `a` advances 5 at font size 10.
private def areaOrigins (body : String) : List (Float × Float) := match parse (svg body) 40 40 (some font) with
  | .ok (scene,_) => scene.primitives.map (fun p => (p.transform.e,p.transform.f))
  | .error _ => []
private def near (a b : Float) : Bool := (a-b).abs < 0.001
private def originsAre (body : String) (expected : List (Float × Float)) : Bool :=
  let found := areaOrigins body
  found.length == expected.length && (found.zip expected).all fun (a,b) => near a.1 b.1 && near a.2 b.2
private def area (attrs text : String) : String := "<textArea font-size='10' " ++ attrs ++ ">" ++ text ++ "</textArea>"
-- A word goes to the next line, and the space at the break is consumed. The size of
-- a line is 1.1 times the font size; the baseline is at 0.8 of it for this font's ascent.
private def line1 : Float := 8.8
private def line2 : Float := 19.8
#guard originsAre (area "x='1' y='0' width='12' height='30'" "aa aa") [(1,line1),(6,line1),(1,line2),(6,line2)]
-- No tbreak and no room: a word wider than the area breaks between characters.
#guard originsAre (area "width='10' height='30'" "aaa") [(0,line1),(5,line1),(0,line2)]
-- An area narrower than one character still moves forward: one character on each line.
#guard withFont (area "width='1' height='40'" "aaa") == 3
-- A line that does not fit completely is not rendered.
#guard withFont (area "width='30' height='10'" "aa") == 0
#guard withFont (area "width='30' height='11'" "aa") == 2
#guard withFont (area "width='12' height='12'" "aa aa") == 2
-- `auto` is infinite: only a tbreak ends a line.
#guard withFont (area "width='auto' height='auto'" "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa<tbreak/>a") == 45
-- A tbreak ends a line even when it is empty, so two of them leave one empty line.
#guard originsAre (area "width='30' height='40'" "a<tbreak/><tbreak/>a") [(0,line1),(0,19.8+11)]
-- line-increment is in user units, and the largest value on the line wins.
#guard originsAre (area "width='30' height='40' line-increment='20'" "a<tbreak/>a") [(0,16),(0,36)]
#guard originsAre (area "width='30' height='40'" "<tspan line-increment='20'>a</tspan><tspan line-increment='5'>a</tspan>") [(0,16),(5,16)]
-- text-align and display-align; `auto` is `before`.
#guard originsAre (area "width='20' height='40' text-align='end'" "a") [(15,line1)]
#guard originsAre (area "width='20' height='40' text-align='center'" "a") [(7.5,line1)]
#guard originsAre (area "width='20' height='41' display-align='after'" "a") [(0,30+line1)]
#guard originsAre (area "width='20' height='41' display-align='center'" "a") [(0,15+line1)]
#guard originsAre (area "width='20' height='41' display-align='auto'" "a") [(0,line1)]
-- Zero disables rendering, and the rest of the document stays.
#guard withFont (area "width='0' height='30'" "a" ++ "<rect width='9' height='9'/>") == 1
#guard withFont (area "width='30' height='0'" "a") == 0
-- White space: runs of spaces collapse over a change of run; xml:space='preserve' keeps them.
#guard originsAre (area "width='40' height='40'" " a <tspan> a</tspan>") [(0,line1),(10,line1)]
#guard originsAre (area "width='40' height='40' xml:space='preserve'" "a  a") [(0,line1),(15,line1)]
-- An instance of a textArea lowers as text does, with the font values of its `use`.
#guard withFont ("<defs>" ++ area "id='t' width='30' height='30'" "a" ++ "</defs><use xlink:href='#t' xmlns:xlink='http://www.w3.org/1999/xlink'/>") == 1
-- With no font the element goes and is logged, as `text` is.
#guard (log "<textArea width='9' height='9'>a</textArea>").contains "element: textArea"
-- Expected failure, https://github.com/danbri/factoidal/issues/1259: a soft hyphen is
-- not yet a break opportunity. When it is one, "a a-" fits on line 1 and this guard fails.
#guard originsAre (area "width='22' height='30'" "a a\u00ADaa") [(0,line1),(0,line2),(10,line2),(15,line2)]

-- Expected failures. Each guard states the present wrong result, so the build fails
-- when the fault is repaired; then state the right result and close the issue.
-- https://github.com/danbri/factoidal/issues/1261: the browser path must list `b.svg`.
#guard (match L4Factoidal.XML.parseNamespaceView useOther with
  | .ok tree => NativeSVG.imageKeys tree (some main_)
  | .error _ => ["not parsed"]) == []
-- https://github.com/danbri/factoidal/issues/1262: bold must differ from normal.
#guard (parse (svg "<text font-size='10' y='10'>a</text>") 40 40 (some tfont)).toOption.map (·.1.compiled.length) ==
  (parse (svg "<text font-size='10' y='10' font-weight='bold' font-style='italic'>a</text>") 40 40 (some tfont)).toOption.map (·.1.compiled.length)
#guard tpixel "<text font-size='10' y='10' font-weight='bold'>a</text>" 11 5 == 1
-- https://github.com/danbri/factoidal/issues/1263: a character outside the fonts must draw.
#guard clear "<text font-size='10' y='10'>&#x416;</text>" 5 5
-- https://github.com/danbri/factoidal/issues/1264: `direction` must put the start at the right.
#guard inked "<text x='20' y='10' font-size='10' direction='rtl'>a</text>" 25 5
-- https://github.com/danbri/factoidal/issues/1266: the shape must stand on the baseline.
private def baselineFont : SVGFont :=
  match SVGFont.parse "<svg xmlns='http://www.w3.org/2000/svg'><font horiz-adv-x='1000'><font-face font-family='B' units-per-em='1000' ascent='800' descent='200' alphabetic='200'/><glyph unicode='a' d='M0 200H1000V900H0Z'/></font></svg>" with
  | .ok f => f | .error _ => {}
#guard match parse (svg "<text y='30' font-size='10'>a</text>") 40 40 (some baselineFont) with
  | .ok (s,_) => (s.samplePixel 5 28).r == 1
  | .error _ => false
