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
  IO.println "PASS public namespace DOM root, inherited style, exact artifact, viewport sampling and standalone validation"

#eval run
end NativeSVGRootTests
