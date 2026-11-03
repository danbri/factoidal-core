import SVG

namespace NativeSVGRootTests
open NativeSVG L4Factoidal.XML

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def xmlAttr (key value : String) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=key},value}

private def element (tag : String) (attrs : List NamespaceAttribute)
    (children : List NamespaceNode := []) : NamespaceNode :=
  .element {namespace_:=some "http://www.w3.org/2000/svg",localPart:=tag} attrs children

def run : IO Unit := do
  let shape := element "rect" [xmlAttr "width" "8",xmlAttr "height" "8",
    xmlAttr "fill" "currentColor"]
  let root := element "svg" [xmlAttr "width" "64",xmlAttr "height" "64"] [shape]
  let red ← unwrap (parseRoot root 0 0 {currentColor:={r:=1,g:=0,b:=0}})
  let color := red.samplePixel 2 2
  check (color.r == 1 && color.g == 0 && color.b == 0) "DOM fragment inherited currentColor"
  let xml := "<svg xmlns='http://www.w3.org/2000/svg' width='64' height='64' color='red'><rect width='8' height='8' fill='currentColor'/></svg>"
  let standalone ← unwrap (parse xml)
  let redArtifact ← unwrap red.artifact
  let standaloneArtifact ← unwrap standalone.artifact
  check (redArtifact == standaloneArtifact) "DOM and XML complete artifact equality"
  let coordinates := [(2,2),(8,2),(63,63),(64,64)]
  for ((x,y),batched) in coordinates.zip (red.samplePixels coordinates) do
    let single := red.samplePixel x y
    check (batched.r == single.r && batched.g == single.g && batched.b == single.b)
      "batch CPU samples changed a color"
  let scaledRoot := element "svg" [xmlAttr "viewBox" "0 0 16 16"] [shape]
  let scaled ← unwrap (parseRoot scaledRoot 32 48)
  check (scaled.width == 32 && scaled.height == 48) "embedding viewport dimensions"
  check ((scaled.samplePixel 3 12).r == 0 && (scaled.samplePixel 25 40).r == 1)
    "DOM embedding viewBox geometry"
  let wrong := NamespaceNode.element {namespace_:=some "urn:wrong",localPart:="svg"} [] []
  check (!(parseRoot wrong 32 32).isOk) "foreign root admitted as SVG"
  check (!(parse "<!DOCTYPE svg><svg xmlns='http://www.w3.org/2000/svg' width='8' height='8'/>").isOk)
    "standalone DTD restriction lost"
  check (!(parse "<svg>").isOk) "standalone XML validation lost"
  for viewBox in ["0 0 0 16","0 0 16 0","0 0 0 0"] do
    let zeroRoot := element "svg" [xmlAttr "width" "64",xmlAttr "height" "64",xmlAttr "viewBox" viewBox] [shape]
    let zero ← unwrap (parseRoot zeroRoot)
    check (zero.width == 64 && zero.height == 64 && zero.primitives.isEmpty)
      "zero viewBox must retain the backing viewport but suppress all paint"
    check (zero.mapping.sx == 1 && zero.mapping.sy == 1)
      "zero viewBox reached a division in viewport mapping"
    for color in zero.samplePixels [(0,0),(31,31),(63,63)] do
      check (color.r == 1 && color.g == 1 && color.b == 1) "zero root viewBox painted"
  let percentages := element "rect" [xmlAttr "x" "50%",xmlAttr "width" "50%",xmlAttr "height" "100%"]
  for viewBox in ["0 0 -32 32","0 0 32 -32"] do
    let invalidRoot := element "svg" [xmlAttr "width" "64",xmlAttr "height" "64",xmlAttr "viewBox" viewBox] [percentages]
    let invalid ← unwrap (parseRoot invalidRoot)
    let [primitive] := invalid.primitives
      | throw (IO.userError "invalid viewBox disabled rendering instead of being ignored")
    let .rect x y w h := primitive.geometry
      | throw (IO.userError "invalid viewBox lost rectangle geometry")
    check (x == 32 && y == 0 && w == 32 && h == 64)
      "ignored invalid viewBox changed viewport percentage bases"
    check (invalid.mapping.sx == 1 && invalid.mapping.sy == 1 && (invalid.samplePixel 40 20).r == 0)
      "negative viewBox applied a transform"
  let nested ← unwrap (parse "<svg xmlns='http://www.w3.org/2000/svg' width='64' height='64'><svg x='8' y='8' width='16' height='16' viewBox='0 0 -8 8'><rect width='100%' height='100%'/></svg><rect x='40' width='8' height='8' fill='blue'/></svg>")
  check ((nested.samplePixel 16 16).r == 0 && (nested.samplePixel 32 16).r == 1 &&
    (nested.samplePixel 42 2).b == 1 && (nested.samplePixel 42 2).r == 0)
    "ignored nested viewBox changed its viewport clip, percentages or sibling paint"
  for radius in ["-40","-1%"] do
    let invalidCircle ← unwrap (parse ("<svg xmlns='http://www.w3.org/2000/svg' width='64' height='64'><rect width='8' height='8' fill='blue'/><circle cx='4' cy='4' r='" ++ radius ++ "' fill='red'/></svg>"))
    check (invalidCircle.primitives.length == 1 && (invalidCircle.samplePixel 4 4).b == 1 &&
      (invalidCircle.samplePixel 4 4).r == 0)
      "invalid negative radius painted or suppressed an unrelated sibling"
  IO.println "PASS zero root viewBox no paint, invalid-negative viewBox fallback/percentages/clips and invalid circle radius initial value"
  IO.println "PASS public namespace DOM root, inherited style, exact artifact, viewport sampling and standalone validation"

#eval run
end NativeSVGRootTests
