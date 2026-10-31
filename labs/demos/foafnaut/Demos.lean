import Graphics
namespace NativeDemos
open NativeGraphics
private def clamp (lo hi x : Int) : Int := max lo (min hi x)
private def bound (lo hi x : Nat) : Nat := max lo (min hi x)
private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n") ++ "\""
private def array (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def boolean (b : Bool) : Int := if b then 1 else 0

-- Deterministic fixed-point arithmetic: 1000 position/velocity units per pixel.
-- Integer square root via bounded binary search over validated coordinate ranges.
private def rootLoop : Nat → Nat → Nat → Nat → Nat
  | 0, _, lo, _ => lo
  | fuel+1, n, lo, hi =>
    if hi <= lo+1 then lo else
      let mid := (lo+hi)/2
      if mid*mid <= n then rootLoop fuel n mid hi else rootLoop fuel n lo mid
private def root (n : Nat) : Int := Int.ofNat (rootLoop 64 n 0 (n+1))
structure Node where
  x : Int
  y : Int
  vx : Int := 0
  vy : Int := 0
  deriving BEq, Repr, Inhabited
private def baseNodes : Array Node := #[
  ⟨72000,72000,0,0⟩,⟨192000,60000,0,0⟩,⟨312000,72000,0,0⟩,
  ⟨88000,184000,0,0⟩,⟨192000,196000,0,0⟩,⟨296000,184000,0,0⟩]
private def edges : List (Nat × Nat) := [(0,1),(1,2),(3,4),(4,5),(0,3),(1,4),(2,5),(0,4),(1,3),(1,5),(2,4)]
private def length (a b : Node) : Int :=
  root ((b.x-a.x)*(b.x-a.x)+(b.y-a.y)*(b.y-a.y)).toNat
private def initialNodes : Array Node := baseNodes.set! 1 {baseNodes[1]! with y:=84000}
structure Springs where
  width : Nat := 768
  height : Nat := 512
  nodes : Array Node := initialNodes
  selected : Nat := 0
  animating : Bool := true
  accumulator : Nat := 0
  simulated : Nat := 0
  dropped : Nat := 0
  closed : Bool := false
  revision : Nat := 0
  dragging : Bool := false
  deriving BEq, Repr

-- Hooke F=k(length-rest)*direction with unit masses and viscous damping c*v.
-- Semi-implicit Euler, fixed dt=10ms, k=12/s², c=4/s. The captured node is
-- kinematically constrained; forces still propagate to its neighbours.
def physicsStep (s : Springs) : Springs := Id.run do
  let mut forces : Array (Int × Int) := Array.replicate 6 (0,0)
  for (a,b) in edges do
    let p := s.nodes[a]!
    let q := s.nodes[b]!
    let dist := max 1 (length p q)
    let extension := dist - length baseNodes[a]! baseNodes[b]!
    let fx := 12*extension*(q.x-p.x)/dist
    let fy := 12*extension*(q.y-p.y)/dist
    let fa := forces[a]!
    let fb := forces[b]!
    forces := forces.set! a (fa.1+fx,fa.2+fy)
    forces := forces.set! b (fb.1-fx,fb.2-fy)
  let nodes := s.nodes.mapIdx fun i node =>
    if s.dragging && s.selected == i+1 then {node with vx:=0,vy:=0} else
      let f := forces[i]!
      let vx := clamp (-500000) 500000 (node.vx+(f.1-4*node.vx)/100)
      let vy := clamp (-500000) 500000 (node.vy+(f.2-4*node.vy)/100)
      let x := node.x+vx/100
      let y := node.y+vy/100
      {x:=clamp 18000 366000 x, y:=clamp 18000 238000 y,
       vx:=if x < 18000 || x > 366000 then -vx/3 else vx,
       vy:=if y < 18000 || y > 238000 then -vy/3 else vy}
  return {s with nodes, simulated:=s.simulated+10}

private def tick (s : Springs) (ms : Nat) : Springs := Id.run do
  if !s.animating then return s
  let total := s.accumulator+min 80 ms
  let mut next := {s with accumulator:=total%10, dropped:=s.dropped+(ms-min 80 ms)}
  for _ in List.range (min 8 (total/10)) do next := physicsStep next
  return next

private def pixelPoint (s : Springs) (n : Node) : Point :=
  ⟨n.x.toNat*s.width/384000,n.y.toNat*s.height/256000⟩
def Springs.scene (s : Springs) : Scene :=
  let scale := fun n => max 1 (min (n*s.width/384) (n*s.height/256))
  {width:=s.width,height:=s.height,background:=⟨18,24,39⟩,shapes:=
    (edges.map fun (a,b) => .segment (pixelPoint s s.nodes[a]!) (pixelPoint s s.nodes[b]!) (scale 2) ⟨86,116,155⟩) ++
    (s.nodes.toList.zipIdx.map fun (n,i) => .circle (pixelPoint s n) (scale 9)
      (if s.selected == i+1 then ⟨255,190,79⟩ else ⟨53,211,167⟩))}

private def selectedNode (s : Springs) (x y : Int) : Nat := Id.run do
  let radius := Int.ofNat (max 1 (min (12*s.width/384) (12*s.height/256)))
  for i in List.range 6 do
    let p := pixelPoint s s.nodes[i]!
    let dx := x-Int.ofNat p.x
    let dy := y-Int.ofNat p.y
    if dx*dx+dy*dy <= radius*radius then return i+1
  return 0

private def springsUpdate (s : Springs) (kind : Nat) (a b : Int) : Springs × List String := Id.run do
  if s.closed then return (s,[])
  let mut n := s
  let mut extra : List String := []
  if kind == 1 then n := {s with width:=bound 16 4096 a.toNat,height:=bound 16 4096 b.toNat}
  else if kind == 2 then
    let selected := selectedNode s a b
    n := {s with selected,dragging:=selected > 0}
  else if kind == 3 && s.selected > 0 && s.dragging then
    let x := clamp 18000 366000 (a*384000/Int.ofNat s.width)
    let y := clamp 18000 238000 (b*256000/Int.ofNat s.height)
    n := {s with nodes:=s.nodes.set! (s.selected-1) ⟨x,y,0,0⟩}
  else if kind == 4 then n := {s with dragging:=false}
  else if kind == 5 && a == 49 then
    n := {s with animating:=!s.animating}
    extra := [if n.animating then "startClock" else "stopClock"]
  else if kind == 5 && a == 15 then
    n := {width:=s.width,height:=s.height,revision:=s.revision}
    extra := ["startClock"]
  else if kind == 6 || (kind == 5 && a == 53) then
    return ({s with closed:=true,revision:=s.revision+1},["close"])
  else if kind == 7 then n := tick s a.toNat
  if n == s then return (s,[])
  let visible := n.nodes != s.nodes || n.selected != s.selected || n.width != s.width || n.height != s.height
  return ({n with revision:=s.revision+1}, (if visible then ["render"] else []) ++ extra)

structure Layout where
  width : Nat := 768
  height : Nat := 512
  selected : Nat := 0
  closed : Bool := false
  revision : Nat := 0
  deriving BEq, Repr
structure Card where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  deriving Repr
private def Layout.columns (s : Layout) : Nat :=
  if s.width < 600 then 2 else if s.width < 1000 then 3 else 4

def Layout.cards (s : Layout) : List Card :=
  let columns := s.columns
  let rows := (12+columns-1)/columns
  let gap := max 2 (min s.width s.height/40)
  let cellWidth := (s.width-gap*(columns+1))/columns
  let cellHeight := (s.height-gap*(rows+1))/rows
  (List.range 12).map fun i =>
    let height := cellHeight - (i%3)*(cellHeight/6)
    {x:=gap+(i%columns)*(cellWidth+gap), y:=gap+(i/columns)*(cellHeight+gap),
     width:=cellWidth,height}
private def palette (i : Nat) : RGB :=
  match i%4 with
  | 0 => ⟨53,161,151⟩ | 1 => ⟨78,115,195⟩ | 2 => ⟨187,95,150⟩ | _ => ⟨190,137,69⟩
def Layout.scene (s : Layout) : Scene :=
  {width:=s.width,height:=s.height,background:=⟨18,24,39⟩,shapes:=
    s.cards.zipIdx.flatMap fun (c,i) =>
      let inset := min 3 (min c.width c.height/4)
      [.rectangle ⟨c.x,c.y⟩ ⟨c.width,c.height⟩
        (if s.selected == i+1 then ⟨255,215,102⟩ else ⟨39,51,71⟩),
       .rectangle ⟨c.x+inset,c.y+inset⟩ ⟨c.width-2*inset,c.height-2*inset⟩ (palette i)]}
private def layoutUpdate (s : Layout) (kind : Nat) (a b : Int) : Layout × List String := Id.run do
  if s.closed then return (s,[])
  let mut n := s
  if kind == 1 then n := {s with width:=bound 192 4096 a.toNat,height:=bound 128 4096 b.toNat}
  else if kind == 2 then
    let mut selection := 0
    for (c,i) in s.cards.zipIdx do
      if a >= Int.ofNat c.x && a < Int.ofNat (c.x+c.width) &&
         b >= Int.ofNat c.y && b < Int.ofNat (c.y+c.height) then selection := i+1
    n := {s with selected:=selection}
  else if kind == 5 && a == 15 then n := {s with selected:=0}
  else if kind == 6 || (kind == 5 && a == 53) then
    return ({s with closed:=true,revision:=s.revision+1},["close"])
  if n == s then return (s,[])
  return ({n with revision:=s.revision+1},["render"])

inductive Demo where | springs (s : Springs) | layout (s : Layout)
private def Demo.encode : Demo → String
  | .springs s =>
    "s," ++ String.intercalate "," (([Int.ofNat s.width,Int.ofNat s.height,Int.ofNat s.selected,
      boolean s.animating,Int.ofNat s.accumulator,Int.ofNat s.simulated,Int.ofNat s.dropped,
      boolean s.closed,Int.ofNat s.revision] ++
      s.nodes.toList.flatMap (fun n => [n.x,n.y,n.vx,n.vy]) ++ [boolean s.dragging]).map toString)
  | .layout s => "l," ++ String.intercalate "," ([Int.ofNat s.width,Int.ofNat s.height,
      Int.ofNat s.selected,boolean s.closed,Int.ofNat s.revision].map toString)
private def validNode (n : Node) : Bool :=
  n.x >= 18000 && n.x <= 366000 && n.y >= 18000 && n.y <= 238000 &&
  n.vx >= -500000 && n.vx <= 500000 && n.vy >= -500000 && n.vy <= 500000
private def Demo.decode (wire : String) : Option Demo := do
  if wire.length > 1024 then none else do
    let parts := wire.splitOn ","
    let tag ← parts.head?
    let nums ← parts.tail.mapM String.toInt?
    let fields := nums.toArray
    if tag == "s" && fields.size == 34 then
      let nodes := ((List.range 6).map fun i => Node.mk fields[9+i*4]! fields[10+i*4]! fields[11+i*4]! fields[12+i*4]!).toArray
      if fields[0]! >= 16 && fields[0]! <= 4096 && fields[1]! >= 16 && fields[1]! <= 4096 &&
         fields[2]! >= 0 && fields[2]! <= 6 && fields[3]! >= 0 && fields[3]! <= 1 &&
         fields[4]! >= 0 && fields[4]! < 10 && fields[5]! >= 0 && fields[6]! >= 0 &&
         fields[7]! >= 0 && fields[7]! <= 1 && fields[8]! >= 0 && nodes.all validNode &&
         fields[33]! >= 0 && fields[33]! <= 1 && (fields[33]! == 0 || fields[2]! > 0) then
        some (.springs {
          width:=fields[0]!.toNat,height:=fields[1]!.toNat
          selected:=fields[2]!.toNat,animating:=fields[3]! == 1,accumulator:=fields[4]!.toNat,
          simulated:=fields[5]!.toNat,dropped:=fields[6]!.toNat,closed:=fields[7]! == 1,
          revision:=fields[8]!.toNat,nodes,dragging:=fields[33]! == 1})
      else none
    else if tag == "l" && fields.size == 5 then
      if fields[0]! >= 192 && fields[0]! <= 4096 && fields[1]! >= 128 && fields[1]! <= 4096 &&
         fields[2]! >= 0 && fields[2]! <= 12 && fields[3]! >= 0 && fields[3]! <= 1 && fields[4]! >= 0 then
        some (.layout {
          width:=fields[0]!.toNat,height:=fields[1]!.toNat,selected:=fields[2]!.toNat
          closed:=fields[3]! == 1,revision:=fields[4]!.toNat})
      else none
    else none

private def Demo.scene : Demo → Scene
  | .springs s => s.scene | .layout s => s.scene
private def Demo.metadata : Demo → Nat × Bool × Bool × Nat × String
  | .springs s => (s.selected,s.animating,s.closed,s.revision,
      "{\"simulatedMs\":" ++ toString s.simulated ++ ",\"remainderMs\":" ++ toString s.accumulator ++
      ",\"droppedMs\":" ++ toString s.dropped ++ "}")
  | .layout s => (s.selected,false,s.closed,s.revision,"{\"columns\":" ++ toString s.columns ++ "}")
private def response (demo : Demo) (commands : List String) (shader : Bool := false) : String :=
  let scene := demo.scene
  let (selection,animating,closed,revision,facts) := demo.metadata
  let name := match demo with | .springs _ => "springs" | .layout _ => "layout"
  let dragging := match demo with | .springs s => s.dragging | .layout _ => false
  "{\"abi\":\"lean-demos-v1\",\"demo\":" ++ quote name ++ ",\"model\":" ++ quote demo.encode ++
  ",\"width\":" ++ toString scene.width ++ ",\"height\":" ++ toString scene.height ++
  ",\"data\":" ++ array (scene.data.map toString) ++ ",\"commands\":" ++ array (commands.map quote) ++
  ",\"selection\":" ++ toString selection ++ ",\"animating\":" ++ toString animating ++
  ",\"closed\":" ++ toString closed ++ ",\"revision\":" ++ toString revision ++ ",\"facts\":" ++ facts ++
  ",\"dragging\":" ++ toString dragging ++
  (if shader then ",\"wgsl\":" ++ quote scene.wgsl else "") ++ "}"

@[export demos_initialize]
def initialResponse (width height kind : UInt32) : String :=
  if kind == 0 then response (.springs {width:=bound 16 4096 width.toNat,height:=bound 16 4096 height.toNat}) ["render","startClock"] true
  else response (.layout {width:=bound 192 4096 width.toNat,height:=bound 128 4096 height.toNat}) ["render"] true
@[export demos_transition]
def transition (wire : String) (kind : UInt32) (a b : Int32) : String :=
  match Demo.decode wire with
  | none => "{\"error\":\"invalid demo model\"}"
  | some (.springs s) => let (n,commands) := springsUpdate s kind.toNat a.toInt b.toInt
                         response (.springs n) commands
  | some (.layout s) => let (n,commands) := layoutUpdate s kind.toNat a.toInt b.toInt
                        response (.layout n) commands

example : edges.length = 11 := rfl
example : ({} : Layout).scene.shapes.length = 24 := rfl
end NativeDemos
