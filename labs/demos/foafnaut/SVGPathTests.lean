import SVG
namespace NativeSVGPathTests
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def wrap (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='32' height='32'>" ++ body ++ "</svg>"
private def path (d : String) (attrs : String := "") := wrap ("<path d='"++d++"' "++attrs++"/>")
private def black := "{\"rgb\":[0,0,0]}"
private def white := "{\"rgb\":[255,255,255]}"
private def sample (xml : String) (x y : UInt32) := NativeSVG.sample xml 0 0 x y

def run : IO Unit := do
  for d in ["M2 2H10V10H2Z","m2,2h8v8h-8z","M2 2 10 2 10 10 2 10"] do
    for y in List.range 16 do
      for x in List.range 16 do
        check (sample (path d) x.toUInt32 y.toUInt32 == (if x>=2 && x<10 && y>=2 && y<10 then black else white)) "linear path rectangle mismatch"
  let .ok parsed := NativeSVG.parse (path "M1e1-2L20.5-2 20.5.5 10 .5z") | throw (IO.userError "compact numeric grammar refused")
  let some primitive := parsed.primitives.head? | throw (IO.userError "missing path")
  let .path contours := primitive.geometry | throw (IO.userError "path was not retained")
  check ((contours.head?.map (·.closed)) == some true) "close flag lost"
  check ((contours.head?.map (·.points.length)) == some 4) "implicit coordinate pairs lost"
  let outer := "M2 2H26V26H2Z"
  let same := outer++"M8 8H20V20H8Z"
  check (sample (path same) 12 12 == black) "nonzero same-winding hole"
  check (sample (path same "fill-rule='evenodd'") 12 12 == white) "evenodd hole"
  check (sample (path (outer++"M8 8V20H20V8Z")) 12 12 == white) "opposite winding hole"
  let disjoint := path "M1 1L6 1 1 6M20 20L26 20 20 26"
  check (sample disjoint 2 2 == black && sample disjoint 21 21 == black && sample disjoint 12 12 == white) "subpaths connected or open fill not closed"
  check (sample (path "M2 2h4v4h-4z m10 0h4v4h-4z") 14 4 == black) "closepath did not restore current point"
  check (sample (path "none") 0 0 == white) "none path painted"
  check (sample (path "M0 0") 0 0 == white) "degenerate moveto painted"
  check (sample (path "M0 0L20 0L0 20" "transform='translate(5,5)'") 6 6 == black) "path CTM"
  for d in ["L0 0","M0","M,0 0","M0,,0","M0 0,","M0 0LZ","M0 0Z1 2","M0 0Q1 2 3 4","M1000000 0l1 0","M0 0L1. 2","M0 0L1.e2 2","M0 0p1 2"] do
    check (!(NativeSVG.parse (path d)).isOk) ("invalid/unsupported path accepted: "++d)
  check (!(NativeSVG.parse (path "M0 0L10 10" "stroke='black'")).isOk) "unsupported path stroke accepted"
  check (!(NativeSVG.parse (path (String.join (List.replicate 129 "M0 0")))).isOk) "subpath budget ignored"
  check (!(NativeSVG.parse (path ("M"++String.ofList (List.replicate 40000 '0')++" 0"))).isOk) "numeric scan budget ignored"
  let excessiveData := "M0 0" ++ String.join (List.replicate 512 "L1 1")
  let excessive := NativeSVG.parse (path excessiveData)
  check (!excessive.isOk) "point budget ignored"
  IO.println "PASS retained MLHVZ, compact numbers, implicit closure, compound winding, CTM and strict limits"
end NativeSVGPathTests
#eval NativeSVGPathTests.run
