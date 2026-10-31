import L4Factoidal.Math.Affine
import L4Factoidal.Math.Matrix

/- Executable cross-checks, not general matrix/algebra correctness proofs.
   Uses the existing TOAN/MathML exact-rational arithmetic and matrix product. -/
namespace L4Factoidal.Math.AffineTests
open L4Factoidal.MathML
private def exact : AffineScalarOps (Int × Int) :=
  ⟨(0,1),(1,1),addRat,subRat,mulRat,divRat⟩
private def r (n : Int) : Int × Int := (n,1)
private def rows (m : Affine2 (Int × Int)) := (m.toRows exact).map (List.map some)
private def check (b : Bool) (s : String) : IO Unit := unless b do throw (IO.userError s)
private def cases : List (Affine2 (Int × Int)) :=
  [.identity exact,⟨r 2,r 1,(-1,2),r 1,r 20,r 10⟩,
   ⟨r (-1),r 0,r 0,r 3,(2,3),(-5,7)⟩,⟨r 0,r 1,r (-1),r 0,r 10,r 10⟩]
private def floats (m : Affine2 (Int × Int)) : Affine2 Float :=
  let f (x : Int × Int) := Float.ofInt x.1 / Float.ofInt x.2
  ⟨f m.a,f m.b,f m.c,f m.d,f m.e,f m.f⟩
private def numberJSON (f : Float) := "\"" ++ toString f.toBits.toNat ++ "\""
private def json (m : Affine2 Float) : String :=
  "[" ++ String.intercalate "," ([m.a,m.b,m.c,m.d,m.e,m.f].map numberJSON) ++ "]"
private def pairJSON (p : Float × Float) := "[" ++ numberJSON p.1 ++ "," ++ numberJSON p.2 ++ "]"
private def fixtures : String :=
  "{\"encoding\":\"ieee754-binary64-bits-decimal\",\"cases\":[" ++ String.intercalate "," (cases.flatMap fun p => cases.map fun q =>
    let a := floats p; let b := floats q; let s := AffineScalarOps.float
    "{\"p\":" ++ json a ++ ",\"q\":" ++ json b ++ ",\"compose\":" ++ json (a.compose s b) ++
    ",\"inverse\":" ++ ((a.inverse? s).map json).getD "null" ++
    ",\"normal\":" ++ ((a.applyNormal? s 1 0).map pairJSON).getD "null" ++
    ",\"corners\":[" ++ String.intercalate "," ((a.boxCorners s (-2) (-1) 4 3).map pairJSON) ++ "]" ++
    ",\"point\":" ++ pairJSON (a.applyPoint s 3.25 (-2.5)) ++
    ",\"direction\":" ++ pairJSON (a.applyDirection s 3.25 (-2.5)) ++ "}") ++ "]}"

def run : IO Unit := do
  for p in cases do
    check (determinant 3 (rows p) == some (p.determinant exact)) "TOAN determinant disagreement"
    let some inverse := p.inverse? exact | throw (IO.userError "unexpected singular exact matrix")
    check (rows (p.compose exact inverse) == rows (.identity exact)) "exact right inverse"
    check (rows (inverse.compose exact p) == rows (.identity exact)) "exact left inverse"
    for q in cases do
      check (rows (p.compose exact q) == matMul 3 (rows p) (rows q)) "TOAN homogeneous composition disagreement"
    let some normal := p.applyNormal? exact (r 1) (r 0) | throw (IO.userError "normal inverse")
    let tangent := p.applyDirection exact (r 0) (r 1)
    check (addRat (mulRat normal.1 tangent.1) (mulRat normal.2 tangent.2) == r 0) "normal/tangent orthogonality"
    let corners := p.boxCorners exact (r (-2)) (r (-1)) (r 4) (r 3)
    check (corners.length == 4) "box corner count"
    let point := p.applyPoint exact (r 3) (r (-2))
    let direction := p.applyDirection exact (r 3) (r (-2))
    let pointMatrix := matMul 1 (rows p) [[some (r 3)],[some (r (-2))],[some (r 1)]]
    let directionMatrix := matMul 1 (rows p) [[some (r 3)],[some (r (-2))],[some (r 0)]]
    check (matElem pointMatrix 0 0 == some point.1 && matElem pointMatrix 1 0 == some point.2) "point homogeneous w=1"
    check (matElem directionMatrix 0 0 == some direction.1 && matElem directionMatrix 1 0 == some direction.2) "direction homogeneous w=0"
  check ((Affine2.mk (r 1) (r 2) (r 2) (r 4) (r 0) (r 0)).inverse? exact |>.isNone) "exact singular inverse accepted"
  IO.println "PASS shared affine: 16 TOAN matrix products, four determinants/two-sided inverses/points/directions, singular refusal"

def emit (path : System.FilePath) : IO Unit := IO.FS.writeFile path (fixtures ++ "\n")
end L4Factoidal.Math.AffineTests

def main (args : List String) : IO Unit := do
  L4Factoidal.Math.AffineTests.run
  match args with
  | [] => pure ()
  | ["--emit-json",path] => L4Factoidal.Math.AffineTests.emit path
  | _ => throw (IO.userError "usage: AffineTests [--emit-json PATH]")
