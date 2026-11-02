import SVG
import L4Factoidal.JSON.Parser

namespace NativeSVGClipTests
open NativeSVG L4Factoidal.JSON

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def identity : Transform := ⟨1,0,0,1,0,0⟩
private def red : Color := ⟨1,0,0⟩
private def scene (tree : List DisplayNode) : Scene :=
  {width:=64,height:=64,mapping:=⟨1,1,0,0,0,0,64,64⟩,tree,
   primitives:=DisplayNode.lowerFromRootList tree,loweringCorrect:=rfl}
private def paint (x y width height : Float) : DisplayNode :=
  .paint {geometry:=.rect x y width height,style:={fill:=.solid red}}
private def diamond : ClipRect := ⟨0,0,4,4,⟨1,1,-1,1,20,10⟩⟩

-- Independent exact half-plane description of the transformed local square.
-- It does not call ClipRect.contains, the packed decoder, or SVG coverage.
private def inDiamond (x y : Float) : Bool :=
  let dx := x-20; let dy := y-10
  0 <= dx+dy && dx+dy <= 8 && 0 <= dy-dx && dy-dx <= 8
private def expectedGreen (inside : Float → Float → Bool) (x y : Nat) : Float :=
  let offsets : List (Float × Float) := [(0.25,0.25),(0.75,0.25),(0.25,0.75),(0.75,0.75)]
  let covered := offsets.foldl (fun count (dx,dy) =>
    count + if inside (Float.ofNat x+dx) (Float.ofNat y+dy) then 1 else 0) 0
  Float.ofNat (4-covered)/4
private def compareGrid (s : Scene) (inside : Float → Float → Bool) : IO Unit := do
  let coordinates := (List.range 24).flatMap fun y => (List.range 36).map fun x => (x,y)
  for ((x,y),actual) in coordinates.zip (s.samplePixels coordinates) do
    let green := expectedGreen inside x y
    check (actual.r == 1 && actual.g == green && actual.b == green)
      s!"independent clipped coverage at {x},{y}"

/-- Analytic controls: each predicate is an independent half-plane oracle,
    separate from the packed clip decoder and rendered geometry. -/
def controls : List (String × Scene × (Float → Float → Bool)) :=
  [("rotated", scene [.clipped (some "clip") identity diamond [paint (-64) (-64) 128 128]], inDiamond),
   ("content-frame", scene [.clipped none ⟨1,0,0,1,18,10⟩ diamond [paint 0 0 8 8]],
     fun x y => inDiamond x y && 18 <= x && x <= 26 && 10 <= y && y <= 18),
   ("parent-frame", scene [.group (some "parent") ⟨1,0,0,1,3,5⟩
       [.clipped none identity diamond [paint (-64) (-64) 128 128]]],
     fun x y => inDiamond (x-3) (y-5)),
   ("intersection", scene [.clipped none identity ⟨20,12,2,2,identity⟩
       [.clipped none identity diamond [paint (-64) (-64) 128 128]]],
     fun x y => inDiamond x y && 20 <= x && x <= 22 && 12 <= y && y <= 14),
   ("singular", scene [.clipped none identity {diamond with transform:=⟨1,2,2,4,20,10⟩}
       [paint (-64) (-64) 128 128]], fun _ _ => false)]

/-- Write actual Lean artifacts and independently calculated full-size RGBA
    quarter-grid expectations. This is a backend diagnostic, not an SVG/WPT case. -/
def writeControls (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for (name,s,inside) in controls do
    let .ok artifact := s.artifact | throw (IO.userError s!"{name}: artifact refused")
    IO.FS.writeFile (directory / (name ++ ".json")) artifact
    let mut expected := ByteArray.empty
    for y in List.range 64 do
      for x in List.range 64 do
        let green := ((expectedGreen inside x y)*255).round.toUInt32.toUInt8
        expected := expected.push 255 |>.push green |>.push green |>.push 255
    IO.FS.writeBinFile (directory / (name ++ ".expected.rgba")) expected


def run : IO Unit := do
  for (_,s,inside) in controls do compareGrid s inside
  let clipped := scene [.clipped (some "clip") identity diamond [paint (-64) (-64) 128 128]]
  compareGrid clipped inDiamond
  check ((clipped.samplePixel 16 10).g == 1) "clip approximated by world bounding box"
  check ((clipped.samplePixel 20 14).g == 0) "clip interior lost"
  check ((clipped.hitTestAt 16.5 10.5).isNone && (clipped.hitTestAt 20.5 14.5).isSome)
    "picking and paint clip coverage differ"
  let placed := scene [.clipped none ⟨1,0,0,1,18,10⟩ diamond [paint 0 0 8 8]]
  compareGrid placed (fun x y => inDiamond x y && 18 <= x && x <= 26 && 10 <= y && y <= 18)
  let shifted := scene [.group (some "parent") ⟨1,0,0,1,3,5⟩
    [.clipped none identity diamond [paint (-64) (-64) 128 128]]]
  compareGrid shifted (fun x y => inDiamond (x-3) (y-5))
  let nested := scene [.clipped none identity ⟨20,12,2,2,identity⟩
    [.clipped none identity diamond [paint (-64) (-64) 128 128]]]
  compareGrid nested (fun x y => inDiamond x y && 20 <= x && x <= 22 && 12 <= y && y <= 14)
  for clip in [({diamond with width:=0}),({diamond with transform:=⟨1,2,2,4,20,10⟩})] do
    let empty := scene [.clipped none identity clip [paint (-64) (-64) 128 128]]
    check ((empty.samplePixel 20 14).g == 1 && (empty.hitTestAt 20.5 14.5).isNone)
      "zero or singular clip is not empty"
  let .ok artifact := clipped.artifact | throw (IO.userError "clipped artifact refused")
  let .ok object := parseJson artifact | throw (IO.userError "clipped artifact is not JSON")
  let some data := object.getArray? "data" | throw (IO.userError "clipped data missing")
  check (data.length == 40) "clip row/cursor encoding changed"
  IO.println "PASS rotated clip half-planes, independent content/clip frames, parent CTM, nested intersection, empty/singular coverage and picking"

#eval run
end NativeSVGClipTests
