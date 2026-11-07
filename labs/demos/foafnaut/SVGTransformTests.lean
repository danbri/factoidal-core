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
  -- SVG Tiny 1.2 §7.7.5: ref(svg) leaves out the transforms of the ancestors.
  let box := "<rect x='10' y='10' width='4' height='4'/>"
  let plain := "<g transform='translate(5,5) scale(2)'><g>"++box++"</g></g>"
  let constrained := "<g transform='translate(5,5) scale(2)'><g transform='ref(svg)'>"++box++"</g></g>"
  check (sample plain 11 11 == white && sample plain 26 26 == black) "ancestors apply with no ref"
  check (sample constrained 11 11 == black && sample constrained 26 26 == white) "ref(svg) leaves out the ancestors"
  let offset := "<g transform='translate(20,20)'><rect width='4' height='4' transform='ref(svg, 3, 3)'/></g>"
  check (sample offset 4 4 == black && sample offset 21 21 == white) "ref(svg,x,y) puts the origin at x,y"
  let compact := "<g transform='translate(20,20)'><g transform=' ref ( svg , 3 3 ) '><rect width='4' height='4'/></g></g>"
  check (sample compact 4 4 == black) "ref grammar allows spaces"
  let inner := "<g transform='translate(20,20)'><g transform='ref(svg)'><g transform='translate(2,2)'><rect width='4' height='4'/></g></g></g>"
  check (sample inner 3 3 == black) "a child of ref(svg) composes as usual"
  let scaled := "<svg xmlns='http://www.w3.org/2000/svg' width='32' height='32' viewBox='0 0 16 16'><g transform='translate(4,4)'><g transform='ref(svg)'><rect x='2' y='2' width='2' height='2'/></g></g></svg>"
  check (NativeSVG.sample scaled 0 0 5 5 == black) "ref(svg) keeps the root viewBox mapping"
  for bad in ["ref(svg,1)","ref(svg,1,2,3)","ref(view)","ref","ref(svg"] do
    check (!(NativeSVG.parse (wrap ("<rect width='2' height='2' transform='"++bad++"'/>"))).isOk) ("invalid ref accepted: "++bad)
  -- Expected failure, https://github.com/danbri/factoidal/issues/1256: the
  -- specification draws this case. When it draws, this check fails the build:
  -- change it to a sample of the rectangle and close the issue.
  check (!(NativeSVG.parse (wrap "<g transform='scale(0)'><rect width='2' height='2' transform='ref(svg)'/></g>")).isOk)
    "issue 1256 now draws: replace this expected failure"
  IO.println "PASS SVG affine order, centered rotation, shear, reflection, singular CTM, ref(svg) and bounds"
end NativeSVGTransformTests
#eval NativeSVGTransformTests.run
