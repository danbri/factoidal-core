import SVGText
import SVGForgiving

open NativeSVGText

/-! Distance along a path, the point at a distance, `startOffset`, and the text
    passes that do not need a font file. The SFNT glyphs are tested by
    `svg_text_test.ts`, which loads Noto Sans into the engines. -/

private def pt (x y : Float) : Point := ⟨x,y⟩
private def near (a b : Float) : Bool := (a-b).abs < 1e-9

-- An L: 3 right, then 4 down. A move to a new subpath adds no length.
private def ell := vertices [(pt 0 0,true),(pt 3 0,false),(pt 3 4,false)]
#guard ell.map (·.length) == [0,3,7]
#guard (vertices [(pt 0 0,true),(pt 3 4,false),(pt 10 10,true),(pt 10 11,false)]).map (·.length) == [0,5,5,6]
-- Distances do not decrease (not proved over Float; checked here).
#guard (ell.zip ell.tail).all fun (a,b) => a.length ≤ b.length
#guard totalLength ell == 7

-- The point at a distance, and the tangent there.
#guard match placeAt ell 1.5 with
  | some p => near p.point.x 1.5 && near p.point.y 0 && near p.angle 0
  | none => false
#guard match placeAt ell 5 with
  | some p => near p.point.x 3 && near p.point.y 2 && near p.angle (3.141592653589793/2)
  | none => false
-- At a vertex the first segment that reaches it is used.
#guard match placeAt ell 3 with
  | some p => near p.point.x 3 && near p.point.y 0
  | none => false
-- Off the path: not drawn.
#guard (placeAt ell (-0.1)).isNone
#guard (placeAt ell 7.1).isNone
#guard (placeAt [] 0).isNone
-- A path of one point has no segment.
#guard (placeAt (vertices [(pt 1 1,true)]) 0).isNone
-- A subpath join of no length is skipped: the point is on the second subpath.
#guard match placeAt (vertices [(pt 0 0,true),(pt 3 4,false),(pt 10 10,true),(pt 10 11,false)]) 5.5 with
  | some p => near p.point.x 10 && near p.point.y 10.5
  | none => false

#guard startOffsetOf (some "50%") 200 == 100
#guard startOffsetOf (some "40") 200 == 40
#guard startOffsetOf (some " 12px ") 200 == 12
#guard startOffsetOf none 200 == 0

-- A path by reference, with its transform; `side="right"` reverses it.
private def lookup : String → Option L4Factoidal.XML.NamespaceNode
  | "p" => some (svgElement "path" [mkAttr "d" "M0 0H10", mkAttr "transform" "translate(5,7)"] [])
  | "r" => some (svgElement "rect" [] [])
  | _ => none
#guard match pathVertices lookup {href := some "#p"} with
  | .ok vs => vs.map (fun v => (v.point.x,v.point.y)) == [(5,7),(15,7)] && totalLength vs == 10
  | .error _ => false
#guard match pathVertices lookup {href := some "#p", side := "right"} with
  | .ok vs => vs.map (fun v => (v.point.x,v.point.y)) == [(15,7),(5,7)]
  | .error _ => false
#guard match pathVertices lookup {data := some "M0 0V5"} with
  | .ok vs => totalLength vs == 5
  | .error _ => false
-- A closed path goes back to its start.
#guard match pathVertices lookup {data := some "M0 0H4V3Z"} with
  | .ok vs => totalLength vs == 12
  | .error _ => false
#guard !(pathVertices lookup {href := some "#r"}).toOption.isSome
#guard !(pathVertices lookup {href := some "#missing"}).toOption.isSome
#guard !(pathVertices lookup {href := some "other.svg#p"}).toOption.isSome

-- Runs: a textPath gives runs on its path only when paths are read.
private def tp : L4Factoidal.XML.NamespaceNode :=
  svgElement "textPath" [mkAttr "href" "#p", mkAttr "startOffset" "50%"] [.other (.text "on path")]
#guard ((textRuns false true maxDepth {} [] tp).1.map (·.onPath.isSome)) == [true]
#guard ((textRuns false true maxDepth {} [] tp).1.map (·.onPath.map (·.startOffset))) == [some (some "50%")]
#guard (textRuns false false maxDepth {} [] tp).1.isEmpty
#guard (textRuns false false maxDepth {} [] tp).2 == ["element in text: textPath"]
-- A tspan keeps all its dx, dy and rotate values.
#guard match (textRuns false true maxDepth {} []
    (svgElement "tspan" [mkAttr "dx" "1 2", mkAttr "rotate" "5,6"] [.other (.text "ab")])).1 with
  | [r] => r.dxs == [1,2] && r.dx == 1 && r.rotates == [5,6]
  | _ => false
-- Text state: spacing, writing mode and the style attribute.
#guard ((({} : TextState).read (expandStyle [mkAttr "style" "font-size:30px; letter-spacing: 2"])).size) == 30
#guard ((({} : TextState).read (expandStyle [mkAttr "style" "font-size:30px; letter-spacing: 2"])).letterSpacing) == 2
#guard (({} : TextState).read [mkAttr "writing-mode" "vertical-rl"]).vertical
#guard (spaceRuns [{text := "  a  b ", size := 1, strokeWidth := 1, paint := []}]).map (·.text) == ["a b"]

-- Containers lose their text properties, also in `style`.
#guard (stripTextProperties [mkAttr "font-family" "x", mkAttr "fill" "red"]).map (·.value) == ["red"]
#guard (stripTextProperties [mkAttr "style" "font-size:9px;fill:red"]).map (·.value) == ["fill:red"]
#guard (stripTextProperties [mkAttr "style" "font-size:9px"]).isEmpty

-- With no font held, text in an HTML document draws nothing and keeps its place.
private def html : L4Factoidal.XML.NamespaceNode :=
  .element {namespace_ := some "http://www.w3.org/1999/xhtml", localPart := "body"} []
    [svgElement "svg" [mkAttr "font-family" "Noto Sans"]
      [svgElement "text" [mkAttr "id" "t", mkAttr "x" "1"] [.other (.text "hi")],
       svgElement "rect" [mkAttr "width" "1", mkAttr "height" "1"] []]]
#guard match lowerDocument #[] html with
  | (.element _ _ [.element _ svgAttrs [.element g gAttrs [], .element r _ _]],log) =>
    svgAttrs.isEmpty && g.localPart == "g" && gAttrs.map (·.value) == ["t"] && r.localPart == "rect" &&
      log == ["text: no font is held"]
  | _ => false

-- The forgiving pass with no SVG font and no SFNT font still drops and logs text.
#guard match NativeSVGForgiving.parse "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 9 9'><text>a</text></svg>" 9 9 with
  | .ok (_,log) => log.contains "element: text"
  | .error _ => false
