import SceneSVG
import FoafNaut
import SVG

namespace NativeSVGCapacityTests
open NativeGraphics L4Factoidal.JSON
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def rgbJSON (c : RGB) : String :=
  "{\"rgb\":[" ++ toString c.r ++ "," ++ toString c.g ++ "," ++ toString c.b ++ "]}"
private def measure (name text : String) (expected : Nat) : IO Unit := do
  let .ok graph := FoafGraph.fromTurtle text none NativeFoafNaut.graphLimits | throw (IO.userError "RDF parse")
  let scene := (NativeFoafNaut.initial graph 1000 700).scene
  let .ok xml := NativeSceneSVG.serialize scene | throw (IO.userError "SVG serialization")
  let .ok parsed := NativeSVG.parse xml | throw (IO.userError "full generated SVG refused")
  check (parsed.primitives.length == expected) "generated primitive measurement changed"
  let .ok artifact := parseJson (NativeSVG.compile xml 0 0) | throw (IO.userError "artifact JSON")
  check (artifact.field? "error" == none) "generated SVG artifact refused"
  check (artifact.getString? "binding" == some "read-only-storage") "storage contract missing"
  let some data := artifact.getArray? "data" | throw (IO.userError "missing data")
  let some shader := artifact.getString? "wgsl" | throw (IO.userError "missing WGSL")
  check (data.length == 8+20*expected && data.length <= NativeSVG.maxDataFloats) "storage record count"
  check (shader.length < 32768 && (shader.splitOn "for(var primitive=").length == 2) "shader still expands per primitive"
  for (x,y) in [(0,100),(500,335),(494,311),(500,316),(427,358),(500,350),(100,100),(800,100)] do
    check (NativeSVG.sample xml 0 0 x y == rgbJSON (scene.sample x.toNat y.toNat)) "full-scene CPU sample disagreement"
  IO.println s!"PASS {name}: chars={xml.length} primitives={expected} floats={data.length} shaderChars={shader.length}"

def run : IO Unit := do
  measure "default8" (← IO.FS.readFile "../../labs/demos/foafnaut/foaf/fixtures/demo.ttl") 1880
  let people := (List.range 16).map fun i => s!"<https://example.org/p{i}> a f:Person; f:name \"WWWWWWWWWWWW\" ."
  let links := (List.range 48).map fun i => s!"<https://example.org/p{i/3}> f:knows <https://example.org/p{(i/3+i%3+1)%16}> ."
  measure "dense16" ("@prefix f: <http://xmlns.com/foaf/0.1/> . " ++ String.join (people++links)) 6748
  let root (children : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='16' height='16'>" ++ children ++ "</svg>"
  check ((NativeSVG.parse (root (String.join (List.replicate 12289 "<circle r='1'/>")))).isOk == false) "primitive budget ignored"
  check ((NativeSVG.parse (String.ofList (List.replicate 1048577 'x'))).isOk == false) "character budget ignored"
  IO.println "3 SVG storage-capacity native groups passed; no GPU result"

#eval run
end NativeSVGCapacityTests
