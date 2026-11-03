import SVG
namespace NativeSVGPercentageTests
private def check (b : Bool) (label : String) : IO Unit := unless b do throw (IO.userError label)
private def close (a b : Float) : Bool := Float.abs (a-b) < 0.00001
private def wrap (attrs body : String) := "<svg xmlns='http://www.w3.org/2000/svg' "++attrs++">"++body++"</svg>"
private def scene (attrs body : String) (w h : Nat := 0) : IO NativeSVG.Scene :=
  match NativeSVG.parse (wrap attrs body) w h with
  | .ok s => pure s | .error e => throw (IO.userError e)
def run : IO Unit := do
  let s ← scene "width='200' height='100'" "<rect x='10%' y='20%' width='50%' height='25%'/><ellipse cx='50%' cy='50%' rx='10%' ry='20%'/><line x1='10%' y1='20%' x2='90%' y2='80%'/><circle cx='50%' cy='50%' r='10%'/>"
  match s.primitives.map (fun (p : NativeSVG.Primitive) => p.geometry) with
  | [.rect x y w h, .ellipse cx cy rx ry, .line x1 y1 x2 y2, .circle _ _ r] =>
    check (x==20 && y==20 && w==100 && h==25) "rectangle percentage axes"
    check (cx==100 && cy==50 && rx==20 && ry==20) "ellipse percentage axes"
    check (x1==20 && y1==20 && x2==180 && y2==80) "line percentage axes"
    check (close r 15.8113883) "circle normalized diagonal"
  | _ => throw (IO.userError "unexpected primitive list")
  for preserve in ["none", "xMidYMid meet", "xMidYMid slice"] do
    let s ← scene ("width='400' height='100' viewBox='10 20 100 50' preserveAspectRatio='"++preserve++"'") "<g transform='scale(2)' stroke='black' stroke-width='10%'><rect x='10%' y='20%' width='50%' height='50%' stroke-width='inherit'/></g>"
    match s.primitives with
    | [p] =>
      match p.geometry with
      | .rect x y w h => check (x==10 && y==10 && w==50 && h==25) "viewBox basis or origin incorrectly included"
      | _ => throw (IO.userError "expected rectangle")
      check (close p.style.strokeWidth 7.90569415) "stroke normalized diagonal or inherited value"
      check (p.transform.a==2 && p.transform.d==2) "child transform changed percentage basis"
    | _ => throw (IO.userError "expected one primitive")
  let hosted ← scene "width='100%' height='100%'" "<rect width='50%' height='50%'/>" 200 100
  check (hosted.width==200 && hosted.height==100) "host viewport dimensions"
  for body in ["<rect width='-1%' height='50%'/>","<circle r='-1%'/>","<circle r='10%' stroke-width='-1%'/>","<rect width='1%%' height='1'/>"] do
    check (!(NativeSVG.parse (wrap "width='200' height='100'" body)).isOk) "invalid percentage admitted"
  check (!(NativeSVG.parse (wrap "width='100%' height='100%'" "")).isOk) "unresolved root percentage accepted"
  let negative ← scene "width='200' height='100'" "<rect x='-10%' y='120%' width='10px' height='10'/>"
  match negative.primitives.map (fun (p : NativeSVG.Primitive) => p.geometry) with
  | [.rect x y w h] => check (x == -20 && y==120 && w==10 && h==10) "signed or over-100 coordinate/absolute regression"
  | _ => throw (IO.userError "signed coordinate primitive")
  for relation in ["help", "match", "author"] do
    check ((NativeSVG.parse (wrap "width='100' height='100' xmlns:h='http://www.w3.org/1999/xhtml'" ("<h:link rel='"++relation++"' href='https://invalid.example/no-fetch'/><rect width='50%' height='50%'/>") )).isOk) "inert metadata refused"
  check (!(NativeSVG.parse (wrap "width='100' height='100' xmlns:h='http://www.w3.org/1999/xhtml'" "<h:link rel='stylesheet' href='https://invalid.example/no-fetch'/>")).isOk) "stylesheet silently accepted"
  IO.println "PASS SVG percentage axes, diagonal, viewBox meet/slice/none, transformed inheritance, host viewport and refusals"
end NativeSVGPercentageTests
#eval NativeSVGPercentageTests.run
