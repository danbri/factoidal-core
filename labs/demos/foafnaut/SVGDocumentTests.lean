import SVG

namespace NativeSVGDocumentTests
open NativeSVG L4Factoidal.XML
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def unwrap (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def attr (name value : String) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=name},value}
private def base (value : String) : NamespaceAttribute :=
  {name:={namespace_:=some "http://www.w3.org/XML/1998/namespace",localPart:="base"},value}
private def xlink (value : String) : NamespaceAttribute :=
  {name:={namespace_:=some "http://www.w3.org/1999/xlink",localPart:="href"},value}
private def svg (tag : String) (attrs : List NamespaceAttribute := [])
    (children : List NamespaceNode := []) : NamespaceNode :=
  .element {namespace_:=some "http://www.w3.org/2000/svg",localPart:=tag} attrs children
private def document (children : List NamespaceNode) (attrs : List NamespaceAttribute := []) : NamespaceNode :=
  .element {namespace_:=some "http://www.w3.org/1999/xhtml",localPart:="html"} attrs children
private def root (children : List NamespaceNode) (attrs : List NamespaceAttribute := []) : NamespaceNode :=
  svg "svg" ([attr "width" "300",attr "height" "300"] ++ attrs) children
private def rect (attrs : List NamespaceAttribute := []) : NamespaceNode :=
  svg "rect" ([attr "width" "100",attr "height" "100"] ++ attrs)
private def use (id : String) (attrs : List NamespaceAttribute := []) : NamespaceNode :=
  svg "use" (attr "href" id :: attrs)
private def color (scene : Scene) (x y : Nat) (r g b : Float) (message : String) : IO Unit := do
  let actual := scene.samplePixel x y
  check (actual.r == r && actual.g == g && actual.b == b) message
private def normalizeRoot (attrs : List NamespaceAttribute) : Except String (List NamespaceAttribute) :=
  .ok (attrs.filter fun a => a.name.localPart != "style" && a.name.localPart != "base")

def run : IO Unit := do
  -- Equivalent source nodes to the actual cross-root href fixture. Additional
  -- text/comment positions catch element-only path indexing and false cycles.
  let first := root [svg "g" [attr "id" "refRect",attr "style" "fill:red"] [rect []],
    svg "circle" [attr "id" "refCircle",attr "cx" "50",attr "cy" "50",attr "r" "50",attr "fill" "orange"]]
    [attr "style" "display:none"]
  let second := root [svg "title" [] [.other (.text "selected SVG")],
    svg "g" [] [use "#refRect" [xlink "#refCircle"]]] [attr "style" "width:300px"]
  let doc := document [.other (.text "before"),first,.other (.comment "between"),second]
  let context ← unwrap (ReferenceContext.create doc)
  check (!(parseRoot second).isOk) "HTML-owned root CSS unexpectedly admitted without its Lean normalizer"
  check (!(parseRootInContext context [3]).isOk) "context silently removed root CSS without the caller normalizer"
  let scene ← unwrap (parseRootInContext context [3] 300 300 {} normalizeRoot)
  check (scene.primitives.length == 1) "cross-root target disappeared or href/xlink both painted"
  color scene 50 50 1 0 0 "hidden first SVG target lost specified inline fill or href precedence"
  color scene 150 150 1 1 1 "cross-root rectangle escaped its actual geometry"
  let localRoot := root [use "#refRect"]
  let standalone ← unwrap (parseRoot localRoot)
  check standalone.primitives.isEmpty "standalone SVG unexpectedly acquired another document's IDs"
  check (!(parseRootInContext context [0]).isOk && !(parseRootInContext context [99]).isOk &&
    !(parseRootInContext context (List.replicate 33 0)).isOk) "source path type/range/depth checks were bypassed"
  IO.println "PASS original-order cross-root href, hidden definitions, text/comment source paths and root-only normalization"

  let duplicateDoc := document [root [rect [attr "id" "same",attr "fill" "blue"]] [attr "style" "display:none"],
    root [rect [attr "id" "same",attr "fill" "red"],use "#same" [attr "x" "120"]]]
  let duplicates ← unwrap (ReferenceContext.create duplicateDoc)
  let duplicateScene ← unwrap (parseRootInContext duplicates [1])
  check (duplicateScene.primitives.length == 2) "global duplicate ID suppressed unrelated paint"
  color duplicateScene 10 10 1 0 0 "duplicate source root paint changed"
  color duplicateScene 130 10 0 0 1 "global ID lookup did not choose the first original document element"

  let url := some "https://example.test/a/doc.html"
  let originalBases := document [
    root [svg "defs" [] [rect [attr "id" "r",attr "fill" "red"],
      svg "g" [attr "id" "t"] [use "../../doc.html#r"]]] [base "deep/sub/"],
    root [use "../doc.html#t"] [base "other/",attr "style" "width:300px"]]
  let bases ← unwrap (ReferenceContext.create originalBases url)
  let based ← unwrap (parseRootInContext bases [1] 300 300 {} normalizeRoot)
  color based 50 50 1 0 0 "normalizer or clone rebased an original source reference"
  let baseDoc := document [root [rect [attr "id" "r",attr "fill" "red"]] [attr "style" "display:none"],
    root [use "doc.html#r"]]
  let localBase ← unwrap (ReferenceContext.create baseDoc url)
  let localBased ← unwrap (parseRootInContext localBase [1])
  color localBased 50 50 1 0 0 "retrieval base default changed"
  let externalBase ← unwrap (ReferenceContext.create baseDoc url (some "https://example.test/resources/"))
  check (!(parseRootInContext externalBase [1]).isOk) "HTML effective base was confused with retrieval document identity"
  IO.println "PASS global first-ID lookup, original xml:base through cloning/normalization and separate effective/retrieval bases"

  let cycleDoc := document [root [svg "defs" [] [svg "g" [attr "id" "a"]
      [rect [attr "fill" "red"],use "#b"]]],
    root [svg "defs" [] [svg "g" [attr "id" "b"]
      [rect [attr "x" "120",attr "fill" "blue"],use "#a"]],use "#a",
      rect [attr "y" "120",attr "fill" "green"]]]
  let cycles ← unwrap (ReferenceContext.create cycleDoc)
  let cycled ← unwrap (parseRootInContext cycles [1])
  check (cycled.primitives.length == 3) "cross-root cycle did not cut only its recursive instance"
  color cycled 10 10 1 0 0 "cycle cut valid first paint"
  color cycled 130 10 0 0 1 "cycle cut valid second paint"
  color cycled 10 130 0 (128/255) 0 "cycle cut unrelated sibling paint"

  let styledDoc := document [root [svg "style" [] [.other (.text "rect { fill:red; }")],
      rect [attr "id" "r",attr "fill" "blue"]] [attr "style" "display:none"],
    root [use "#r"]]
  let styles ← unwrap (ReferenceContext.create styledDoc)
  let styled ← unwrap (parseRootInContext styles [1])
  color styled 50 50 1 0 0 "global SVG stylesheet was confined to its defining SVG root"
  let paintDoc := document [root [svg "defs" [] [svg "linearGradient" [attr "id" "paint"]]] [attr "style" "display:none"],
    root [rect [attr "fill" "url(#paint) red"]]]
  let paints ← unwrap (ReferenceContext.create paintDoc)
  check (!(parseRootInContext paints [1]).isOk) "existing global paint server was treated as missing fallback"
  IO.println "PASS cross-root cycle refusal, sibling survival, global SVG styles and explicit global paint-server refusal"

#eval run
end NativeSVGDocumentTests
