import L4Factoidal.DOM.SvgTinyTraits
import L4Factoidal.DOM.OfXml

/-! Checks of the SVG Tiny 1.2 trait decisions (`DOM.SvgTinyTraits`) on small documents,
from the rules of the uDOM, Appendix A.8.13 and A.8.14. -/

namespace L4Factoidal.DOM.SvgTinyTraits.Tests
open L4Factoidal.DOM

private def doc : Dom :=
  (parseXmlDocument ("<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' width='100%' viewBox='0 0 480 360'>" ++
    "<g fill='blue' stroke-width='3' color='#00ff00'>" ++
    "<rect xml:id='r' x='10' width='5' transform='translate(5,6) scale(2)'/>" ++
    "<circle fill='inherit' stroke='currentColor' r='4'/>" ++
    "<path d='m 1 2 l 3 4 z'/>" ++
    "<text x='1 2 3' y='7'>Hi</text>" ++
    "<animate attributeName='x' fill='freeze'/>" ++
    "</g></svg>")).toOption.getD {}

/-- The node of the first element named `name`. -/
private def el (name : String) : NodeId :=
  ((doc.treeOrder 0).find? fun k => (doc.get k).lname == name).getD 0

private def ans : Except Int String → String
  | .ok v => v
  | .error e => s!"E{e}"

private def g (name : String) (trait : String) (k : Kind) : Except Int String := get doc (el name) "" trait k
private def s (name : String) (trait : String) (k : Kind) (v : String) : Except Int String := set doc (el name) "" trait k v

-- typed getters; an inherited property from the parent; the lacuna value
#guard ans (g "rect" "x" .float) == "10"
#guard ans (g "rect" "y" .float) == "0"
#guard ans (g "rect" "fill" .rgb) == "0 0 255"
#guard ans (g "rect" "stroke-width" .float) == "3"
#guard ans (g "rect" "stroke" .rgb) == nullText
#guard ans (g "circle" "fill" .rgb) == "0 0 255"
#guard ans (g "circle" "stroke" .rgb) == "0 255 0"
#guard ans (g "rect" "display" .string) == "inline"
#guard ans (g "rect" "transform" .matrix) == "translate 5 6\nscale 2"
#guard ans (g "path" "d" .path) == "M 1 2\nL 4 6\nZ"
#guard ans (g "svg" "viewBox" .rect) == "0 0 480 360"
#guard ans (g "rect" "#text" .string) == ""
#guard ans (g "text" "#text" .string) == "Hi"
-- A.8.14: a percentage width on `svg`, and `x` with several coordinates on `text`, are type mismatches
#guard ans (g "svg" "width" .float) == "E-17"
#guard ans (g "text" "x" .float) == "E-17"
#guard ans (g "text" "x" .floatList) == "1 2 3"
#guard ans (g "text" "y" .float) == "7"
-- the wrong accessor, and a trait the element does not have
#guard ans (g "rect" "x" .rgb) == "E-17"
#guard ans (g "rect" "r" .float) == "E-9"
#guard ans (g "rect" "foo" .string) == "E-9"
#guard ans (get doc (el "rect") xlinkNS "href" .string) == "E-9"
-- the animation element's `fill` is its own attribute
#guard ans (g "animate" "fill" .string) == "freeze"

-- setters: the attribute text, or the DOMException code
#guard ans (s "rect" "x" .float "12.5") == "12.5"
#guard ans (s "rect" "width" .float "-1") == "E-15"
#guard ans (s "rect" "fill-opacity" .float "2") == "E-15"
#guard ans (s "rect" "fill" .rgb "255 18 52") == "rgb(255,18,52)"
#guard ans (s "rect" "fill" .rgb typeMark) == "E-17"
#guard ans (s "rect" "fill" .rgb nullMark) == "E-15"
#guard ans (s "rect" "x" .rgb "1 2 3") == "E-17"
#guard ans (s "rect" "foo" .rgb "1 2 3") == "E-9"
#guard ans (s "rect" "stroke-linejoin" .string "foo") == "E-15"
#guard ans (s "rect" "stroke-linejoin" .string "round") == "round"
#guard ans (s "rect" "fill" .string "inherit") == "inherit"
#guard ans (s "rect" "transform" .matrix "1 0 0 1 5 5") == "matrix(1,0,0,1,5,5)"
#guard ans (s "path" "d" .path "M 1 2\nL 3 4\nZ") == "M 1 2 L 3 4 Z"
#guard ans (s "path" "d" .path "M 1\nZ") == "E-15"
-- an animation element in the tree takes no trait change (A.8.14)
#guard ans (s "animate" "attributeName" .string "y") == "E-9"

end L4Factoidal.DOM.SvgTinyTraits.Tests
