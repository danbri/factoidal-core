import Init

namespace NativeGraphics

inductive Ty where | scalar | vec2 | boolean

abbrev Ty.Value : Ty → Type
  | .scalar => Float
  | .vec2 => Float × Float
  | .boolean => Bool

inductive Var : Ty → Type where
  | position : Var .vec2
  | t : Var .scalar
  | previous : Var .vec2
  | q : Var .vec2
  | d : Var .vec2
  | h : Var .scalar

inductive Expr : Ty → Type where
  | lit (n : Nat) : Expr .scalar
  | param (offset : Nat) : Expr .scalar
  | var : Var t → Expr t
  | vec : Expr .scalar → Expr .scalar → Expr .vec2
  | add : Expr .scalar → Expr .scalar → Expr .scalar
  | sub : Expr .scalar → Expr .scalar → Expr .scalar
  | mul : Expr .scalar → Expr .scalar → Expr .scalar
  | divide : Expr .scalar → Expr .scalar → Expr .scalar
  | maximum : Expr .scalar → Expr .scalar → Expr .scalar
  | clamp01 : Expr .scalar → Expr .scalar
  | addV : Expr .vec2 → Expr .vec2 → Expr .vec2
  | subV : Expr .vec2 → Expr .vec2 → Expr .vec2
  | scale : Expr .scalar → Expr .vec2 → Expr .vec2
  | dot : Expr .vec2 → Expr .vec2 → Expr .scalar
  | le : Expr .scalar → Expr .scalar → Expr .boolean
  | and : Expr .boolean → Expr .boolean → Expr .boolean

structure Env where
  data : Array Float
  position : Float × Float := (0, 0)
  t : Float := 0
  previous : Float × Float := (0, 0)
  q : Float × Float := (0, 0)
  d : Float × Float := (0, 0)
  h : Float := 0

def Var.eval {ty : Ty} (env : Env) : Var ty → ty.Value
  | .position => env.position
  | .t => env.t
  | .previous => env.previous
  | .q => env.q
  | .d => env.d
  | .h => env.h

def Expr.eval {ty : Ty} (env : Env) : Expr ty → ty.Value
  | .lit n => Float.ofNat n
  | .param i => env.data[i]!
  | .var v => v.eval env
  | .vec x y => (x.eval env, y.eval env)
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .divide a b => a.eval env / b.eval env
  | .maximum a b => max (a.eval env) (b.eval env)
  | .clamp01 a => max 0 (min 1 (a.eval env))
  | .addV a b => let x := a.eval env; let y := b.eval env; (x.1+y.1, x.2+y.2)
  | .subV a b => let x := a.eval env; let y := b.eval env; (x.1-y.1, x.2-y.2)
  | .scale a b => let x := a.eval env; let y := b.eval env; (x*y.1, x*y.2)
  | .dot a b => let x := a.eval env; let y := b.eval env; x.1*y.1+x.2*y.2
  | .le a b => a.eval env <= b.eval env
  | .and a b => a.eval env && b.eval env

def Var.wgsl {ty : Ty} : Var ty → String
  | .position => "p.xy"
  | .t => "t"
  | .previous => "previous"
  | .q => "q"
  | .d => "d"
  | .h => "h"

def Expr.wgsl {ty : Ty} : Expr ty → String
  | .lit n => toString n ++ ".0"
  | .param i => s!"params.rows[{i / 4}][{i % 4}]"
  | .var v => v.wgsl
  | .vec x y => "vec2f(" ++ x.wgsl ++ "," ++ y.wgsl ++ ")"
  | .add a b => "(" ++ a.wgsl ++ "+" ++ b.wgsl ++ ")"
  | .sub a b => "(" ++ a.wgsl ++ "-" ++ b.wgsl ++ ")"
  | .mul a b => "(" ++ a.wgsl ++ "*" ++ b.wgsl ++ ")"
  | .divide a b => "(" ++ a.wgsl ++ "/" ++ b.wgsl ++ ")"
  | .maximum a b => "max(" ++ a.wgsl ++ "," ++ b.wgsl ++ ")"
  | .clamp01 a => "clamp(" ++ a.wgsl ++ ",0.0,1.0)"
  | .addV a b => "(" ++ a.wgsl ++ "+" ++ b.wgsl ++ ")"
  | .subV a b => "(" ++ a.wgsl ++ "-" ++ b.wgsl ++ ")"
  | .scale a b => "(" ++ a.wgsl ++ "*" ++ b.wgsl ++ ")"
  | .dot a b => "dot(" ++ a.wgsl ++ "," ++ b.wgsl ++ ")"
  | .le a b => "(" ++ a.wgsl ++ "<=" ++ b.wgsl ++ ")"
  | .and a b => "(" ++ a.wgsl ++ "&&" ++ b.wgsl ++ ")"

structure Point where
  x : Nat
  y : Nat
  deriving Repr
structure RGB where
  r : Nat
  g : Nat
  b : Nat
  deriving Repr, BEq
inductive Shape where
  | circle (center : Point) (radius : Nat) (color : RGB)
  | rectangle (origin size : Point) (color : RGB)
  | quadratic (a b c : Point) (stroke : Nat) (color : RGB)
  | cubic (a b c d : Point) (stroke : Nat) (color : RGB)
  | segment (a b : Point) (stroke : Nat) (color : RGB)
  deriving Repr

-- Each command uses exactly four vec4 rows. Layout is specified here in Lean.
def Shape.rows : Shape → List Nat
  | .circle p r color => [p.x,p.y,r,0, 0,0,0,0, 0,0,0,0, color.r,color.g,color.b,255]
  | .rectangle p size color => [p.x,p.y,size.x,size.y, 0,0,0,0, 0,0,0,0, color.r,color.g,color.b,255]
  | .quadratic a b c stroke color => [a.x,a.y,b.x,b.y, c.x,c.y,0,0, stroke,64,0,0, color.r,color.g,color.b,255]
  | .cubic a b c d stroke color => [a.x,a.y,b.x,b.y, c.x,c.y,d.x,d.y, stroke,96,0,0, color.r,color.g,color.b,255]
  | .segment a b stroke color => [a.x,a.y,b.x,b.y, 0,0,0,0, stroke,0,0,0, color.r,color.g,color.b,255]

theorem Shape.rows_length (s : Shape) : s.rows.length = 16 := by
  cases s <;> rfl

private def point (base offset : Nat) : Expr .vec2 := .vec (.param (base+offset)) (.param (base+offset+1))
private def square (x : Expr .scalar) : Expr .scalar := .mul x x
private def squared (x : Expr .vec2) : Expr .scalar := .dot x x
private def t : Expr .scalar := .var .t
private def u : Expr .scalar := .sub (.lit 1) t

-- These are typed polynomial expressions, interpreted on CPU and lowered to WGSL.
def quadratic (base : Nat) : Expr .vec2 :=
  .addV (.addV (.scale (square u) (point base 0))
    (.scale (.mul (.mul (.lit 2) u) t) (point base 2)))
    (.scale (square t) (point base 4))

def cubic (base : Nat) : Expr .vec2 :=
  .addV (.addV (.scale (.mul (square u) u) (point base 0))
    (.scale (.mul (.mul (.lit 3) (square u)) t) (point base 2)))
    (.addV (.scale (.mul (.mul (.lit 3) u) (square t)) (point base 4))
      (.scale (.mul (square t) t) (point base 6)))

def segmentFraction : Expr .scalar :=
  .clamp01 (.divide (.dot (.subV (.var .position) (.var .previous)) (.var .d))
    (.maximum (.dot (.var .d) (.var .d)) (.divide (.lit 1) (.lit 1000000))))

def segmentHit (base : Nat) : Expr .boolean :=
  .le (squared (.subV (.var .position) (.addV (.var .previous) (.scale (.var .h) (.var .d)))))
    (square (.divide (.param (base+8)) (.lit 2)))

def circleHit (base : Nat) : Expr .boolean :=
  .le (squared (.subV (.var .position) (point base 0))) (square (.param (base+2)))

def rectangleHit (base : Nat) : Expr .boolean :=
  let x : Expr .scalar := .param base
  let y : Expr .scalar := .param (base+1)
  -- Position components are expressed by dot products with unit vectors.
  let px := Expr.dot (.var .position) (.vec (.lit 1) (.lit 0))
  let py := Expr.dot (.var .position) (.vec (.lit 0) (.lit 1))
  .and (.and (.le x px) (.le px (.add x (.param (base+2)))))
    (.and (.le y py) (.le py (.add y (.param (base+3)))))

def Shape.color : Shape → RGB
  | .circle _ _ c | .rectangle _ _ c | .quadratic _ _ _ _ c | .cubic _ _ _ _ _ c | .segment _ _ _ c => c

def Shape.curve : Shape → Option (Nat × (Nat → Expr .vec2))
  | .quadratic .. => some (64, NativeGraphics.quadratic)
  | .cubic .. => some (96, NativeGraphics.cubic)
  | _ => none

def Shape.hit (s : Shape) (base : Nat) (env : Env) : Bool := Id.run do
  match s with
  | .circle .. => return (circleHit base).eval env
  | .rectangle .. => return (rectangleHit base).eval env
  | .segment .. =>
    let previous := (point base 0).eval env
    let q := (point base 2).eval env
    let current := {env with previous, q, d:=(q.1-previous.1,q.2-previous.2)}
    return (segmentHit base).eval {current with h:=segmentFraction.eval current}
  | _ =>
    let some (steps, polynomial) := s.curve | return false
    let mut previous := (point base 0).eval env
    for i in List.range steps do
      let current := { env with t := Float.ofNat (i+1) / Float.ofNat steps, previous }
      let q := (polynomial base).eval current
      let d := (q.1-previous.1, q.2-previous.2)
      let current := { current with q, d }
      let current := { current with h := segmentFraction.eval current }
      if (segmentHit base).eval current then return true
      previous := q
    return false

private def paint (base : Nat) : String := s!"color=params.rows[{base/4+3}].xyz;"

def Shape.wgsl (s : Shape) (base : Nat) : String :=
  match s with
  | .circle .. => "if " ++ (circleHit base).wgsl ++ " {" ++ paint base ++ "}\n"
  | .rectangle .. => "if " ++ (rectangleHit base).wgsl ++ " {" ++ paint base ++ "}\n"
  | .segment .. =>
    "{let previous=" ++ (point base 0).wgsl ++ ";let d=" ++ (point base 2).wgsl ++
    "-previous;let h=" ++ segmentFraction.wgsl ++ ";if " ++ (segmentHit base).wgsl ++
    " {" ++ paint base ++ "}}\n"
  | _ =>
    match s.curve with
    | none => ""
    | some (steps, polynomial) =>
      "{ var previous=" ++ (point base 0).wgsl ++ ";\n" ++
      s!"for(var i=1u;i<={steps}u;i++)" ++ "{\n" ++
      s!"let t=f32(i)/{steps}.0;\n" ++
      "let q=" ++ (polynomial base).wgsl ++ ";\nlet d=q-previous;\nlet h=" ++
      segmentFraction.wgsl ++ ";\nif " ++ (segmentHit base).wgsl ++ " {" ++
      paint base ++ "}\nprevious=q;\n}\n}\n"

structure Scene where
  width : Nat
  height : Nat
  background : RGB
  shapes : List Shape

def Scene.data (s : Scene) : List Nat := s.shapes.flatMap Shape.rows

def Scene.sample (s : Scene) (x y : Nat) : RGB := Id.run do
  let env : Env := {
    data := s.data.toArray.map Float.ofNat
    position := (Float.ofNat x + 0.5, Float.ofNat y + 0.5) }
  let mut color := s.background
  let mut base := 0
  for shape in s.shapes do
    if shape.hit base env then color := shape.color
    base := base + 16
  return color

def Scene.wgsl (s : Scene) : String :=
  s!"struct Params " ++ "{ rows:array<vec4f," ++ toString (s.shapes.length*4) ++ "> };\n" ++
  "@group(0) @binding(0) var<uniform> params:Params;\n" ++
  "@vertex fn vertex(@builtin(vertex_index) i:u32)->@builtin(position) vec4f {\n" ++
  "let points=array<vec2f,3>(vec2f(-1,-1),vec2f(3,-1),vec2f(-1,3));return vec4f(points[i],0,1);}\n" ++
  "@fragment fn fragment(@builtin(position) p:vec4f)->@location(0) vec4f {\n" ++
  s!"var color=vec3f({s.background.r},{s.background.g},{s.background.b});\n" ++
  String.join (s.shapes.zipIdx.map fun (shape, i) => shape.wgsl (i*16)) ++
  "return vec4f(color/255.0,1.0);}\n"

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n") ++ "\""
private def array (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def RGB.json (c : RGB) : String := array [toString c.r,toString c.g,toString c.b]

def Scene.json (s : Scene) : String :=
  let points := [(8*s.width/384,8*s.height/256),(104*s.width/384,104*s.height/256),
    (250*s.width/384,100*s.height/256),(36*s.width/384,213*s.height/256),
    (184*s.width/384,173*s.height/256),(347*s.width/384,217*s.height/256),
    (28*s.width/384,57*s.height/256)]
  let checks := points.map fun (x,y) =>
    "{\"x\":" ++ toString x ++ ",\"y\":" ++ toString y ++ ",\"rgb\":" ++ (s.sample x y).json ++ "}"
  "{\"abi\":\"lean-graphics-v1\",\"width\":" ++ toString s.width ++
  ",\"height\":" ++ toString s.height ++ ",\"shapeCount\":" ++ toString s.shapes.length ++
  ",\"data\":" ++ array (s.data.map toString) ++ ",\"wgsl\":" ++ quote s.wgsl ++
  ",\"checks\":" ++ array checks ++ "}"

-- Dynamic viewport and variant are inputs to the Lean computation, not host geometry.
def demo (width height variant : Nat) : Scene :=
  let p := fun x y => Point.mk (x*width/384) (y*height/256)
  let scale := fun n => max 1 (min (n*width/384) (n*height/256))
  { width, height, background := ⟨18,24,39⟩, shapes := [
    .circle (p 104 104) (scale 55) ⟨53,211,167⟩,
    .rectangle (p 209 49) (p 110 110) ⟨92,141,250⟩,
    .quadratic (p 36 213) (p 184 122) (p 348 217) (scale 5) ⟨255,190,79⟩,
    .cubic (p 28 57) (p 94 (if variant % 2 == 0 then 8 else 113))
      (p 260 12) (p 355 30) (scale 4) ⟨239,110,184⟩] }

@[export graphics_generate]
def generate (width height variant : UInt32) : String :=
  if width.toNat < 16 || height.toNat < 16 || width.toNat > 4096 || height.toNat > 4096 then
    "{\"error\":\"viewport must be between 16 and 4096\"}"
  else (demo width.toNat height.toNat variant.toNat).json

-- Small definitional checks complement CPU/WASM cross-runtime tests.
example : Expr.wgsl (.add (.lit 2) (.lit 3)) = "(2.0+3.0)" := rfl
example : (demo 384 256 0).shapes.length = 4 := rfl

end NativeGraphics

def main (args : List String) : IO Unit := do
  let width := (args[0]?.getD "384").toNat!.toUInt32
  let height := (args[1]?.getD "256").toNat!.toUInt32
  let variant := (args[2]?.getD "0").toNat!.toUInt32
  IO.println (NativeGraphics.generate width height variant)
