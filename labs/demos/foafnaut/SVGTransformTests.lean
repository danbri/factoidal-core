import SVG
namespace NativeSVGTransformTests
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='100' height='100'>" ++ body ++ "</svg>"
private def black := "{\"rgb\":[0,0,0]}"
private def white := "{\"rgb\":[255,255,255]}"
def run : IO Unit := do
  let rect := "<rect width='8' height='6'/>"
  let sample (xml : String) (x y : UInt32) := NativeSVG.sample (wrap xml) 0 0 x y
  check (sample ("<g transform='translate(10,20) scale(2,3)'>"++rect++"</g>") 11 21 == black) "list application order"
  check (sample ("<g transform='scale(2,3) translate(10,20)'>"++rect++"</g>") 11 21 == white) "noncommutative order"
  check (sample ("<g transform='scale(2,3) translate(10,20)'>"++rect++"</g>") 21 61 == black) "scaled translation"
  check (sample "<rect x='10' y='10' width='6' height='3' transform='rotate(90,10,10)'/>" 8 12 == black) "centered rotation"
  check (sample "<rect width='4' height='4' transform='skewX(45)'/>" 5 2 == black) "skewX"
  check (sample "<rect x='-20' y='5' width='10' height='10' transform='scale(-1,1)'/>" 15 10 == black) "reflection"
  check (sample "<rect width='100' height='100' transform='matrix(1,2,2,4,0,0)'/>" 5 5 == white) "singular CTM painted"
  for bad in ["matrix(1,2)","translate(1)","scale(1e-12)","translate(1),",String.join (List.replicate 33 "translate(1)")] do
    let xml := if bad == "translate(1)" then "<svg xmlns='http://www.w3.org/2000/svg' width='32' height='32' transform='translate(1)'/>"
      else wrap ("<rect width='2' height='2' transform='"++bad++"'/>")
    check (!(NativeSVG.parse xml).isOk) ("profile refusal lost: "++bad)
  IO.println "PASS SVG affine order, centered rotation, shear, reflection, singular CTM and bounds"
end NativeSVGTransformTests
#eval NativeSVGTransformTests.run
