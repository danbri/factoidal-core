import L4Factoidal.Rendering.BoxAlign
import L4Factoidal.Math.Affine

/-! CSS `transform` on boxes (CSS Transforms 1 §6, §12): the 2D functions as affine
transforms, and the transform of a box about its `transform-origin`.

A transform does not take part in layout: the box is laid out where it would be, and
what is drawn of it (and the boxes that answer where it is) is moved. `steps` reads a
`transform` value into `TransformStep`s: a translation keeps its percentages, which are of
the box's own size, known when it is laid out; any other function is its matrix. The 3D
functions are read as what they do in the plane: `translateZ` and `perspective` nothing,
`rotateX` and `rotateY` a squeeze of the other axis by the cosine of the angle,
`matrix3d` its 2D part.

`about` is generic in the scalar (`Math.Affine2`), so what is proved of it is proved on
whole numbers (`aboutInt_origin`, `aboutInt_translation`); the layout uses the same
function on `Float`.

Bound: a `transform` value has at most `maxSteps` functions (`steps_length_le`); a longer
list is not a value. -/
namespace L4Factoidal.Rendering.CSS

/-- One function of a `transform` list as the layout applies it. -/
inductive TransformStep where
  /-- A translation: in each axis a length and a fraction of the box's own size. -/
  | translate (x ofWidth y ofHeight : Float)
  /-- Any other function, as `matrix(a, b, c, d, e, f)`. -/
  | matrix (a b c d e f : Float)
  deriving Repr

/-- The same function with the same numbers. -/
def TransformStep.same : TransformStep → TransformStep → Bool
  | .translate x xw y yh, .translate x' xw' y' yh' => x == x' && xw == xw' && y == y' && yh == yh'
  | .matrix a b c d e f, .matrix a' b' c' d' e' f' => a == a' && b == b' && c == c' && d == d' && e == e' && f == f'
  | _, _ => false

/-- Two lists of functions that transform the same. -/
def sameSteps : List TransformStep → List TransformStep → Bool
  | [], [] => true
  | a :: as, b :: bs => a.same b && sameSteps as bs
  | _, _ => false

namespace BoxTransform

/-- The most functions a `transform` value may have. -/
def maxSteps : Nat := 64

/-- An argument of a transform function. -/
inductive Arg where
  | number (v : Float)
  /-- a length: px and a fraction of the box's size -/
  | length (px ofBox : Float)
  | angle (degrees : Float)

private def term : CssValues.CV → Option Arg
  | .tok (.num v _) => some (.number (ratToFloat v))
  | .tok (.pct v) => some (.length 0 (ratToFloat v/100))
  | .tok (.dim v _ unit) =>
    let x := ratToFloat v
    match unit with
    | "px" => some (.length x 0)
    | "deg" => some (.angle x)
    | "rad" => some (.angle (x*180/3.141592653589793))
    | "grad" => some (.angle (x*0.9))
    | "turn" => some (.angle (x*360))
    | _ => none
  | _ => none

/-- A sum of px and percentage terms, as the computed value of a `calc()` has it. -/
private def calcSum (body : List CssValues.CV) : Option Arg :=
  let r := (CssValues.stripWs body).foldl (fun (acc : Option (Float × Float × Float)) cv =>
    acc.bind fun (sign,px,pct) =>
      match cv with
      | .tok (.delim '+') => some (1,px,pct)
      | .tok (.delim '-') => some (-1,px,pct)
      | other => match term other with
        | some (.length x p) => some (1,px+sign*x,pct+sign*p)
        | _ => none) (some (1,0,0))
  r.map fun (_,px,pct) => .length px pct

private def arg : CssValues.CV → Option Arg
  | .fn name body => if CssValues.lower name == "calc" then calcSum body else none
  | cv => term cv

private def isComma : CssValues.CV → Bool
  | .tok .comma => true
  | _ => false

private def lengthOf : Arg → Option (Float × Float)
  | .length x p => some (x,p)
  | .number v => if v == 0 then some (0,0) else none
  | _ => none

private def numberOf : Arg → Option Float
  | .number v => some v
  | .length x p => if x == 0 then some p else none
  | _ => none

private def radiansOf : Arg → Option Float
  | .angle d => some (d*3.141592653589793/180)
  | .number v => if v == 0 then some 0 else none
  | _ => none

/-- The step of one function, by its name in lower case; `none` when it is not one. -/
def step (name : String) (args : List Arg) : Option TransformStep :=
  let identity : TransformStep := .matrix 1 0 0 1 0 0
  match name,args with
  | "translate",[x] => (lengthOf x).map fun (x,xw) => .translate x xw 0 0
  | "translate",[x,y] | "translate3d",[x,y,_] => do
    let (x,xw) ← lengthOf x
    let (y,yh) ← lengthOf y
    pure (.translate x xw y yh)
  | "translatex",[x] => (lengthOf x).map fun (x,xw) => .translate x xw 0 0
  | "translatey",[y] => (lengthOf y).map fun (y,yh) => .translate 0 0 y yh
  | "translatez",[_] | "perspective",[_] | "scalez",[_] => some identity
  | "scale",[s] => (numberOf s).map fun s => .matrix s 0 0 s 0 0
  | "scale",[sx,sy] | "scale3d",[sx,sy,_] => do
    let sx ← numberOf sx
    let sy ← numberOf sy
    pure (.matrix sx 0 0 sy 0 0)
  | "scalex",[s] => (numberOf s).map fun s => .matrix s 0 0 1 0 0
  | "scaley",[s] => (numberOf s).map fun s => .matrix 1 0 0 s 0 0
  | "rotate",[a] | "rotatez",[a] => (radiansOf a).map fun r => .matrix r.cos r.sin (-r.sin) r.cos 0 0
  -- a turn about an axis of the plane, seen from the front: the other axis is squeezed
  | "rotatex",[a] => (radiansOf a).map fun r => .matrix 1 0 0 r.cos 0 0
  | "rotatey",[a] => (radiansOf a).map fun r => .matrix r.cos 0 0 1 0 0
  | "rotate3d",[_,_,_,a] => (radiansOf a).map fun _ => identity
  | "skew",[ax] | "skewx",[ax] => (radiansOf ax).map fun x => .matrix 1 0 x.tan 1 0 0
  | "skew",[ax,ay] => do
    let x ← radiansOf ax
    let y ← radiansOf ay
    pure (.matrix 1 y.tan x.tan 1 0 0)
  | "skewy",[ay] => (radiansOf ay).map fun y => .matrix 1 y.tan 0 1 0 0
  | "matrix",[a,b,c,d,e,f] => do
    pure (.matrix (← numberOf a) (← numberOf b) (← numberOf c) (← numberOf d) (← numberOf e) (← numberOf f))
  | "matrix3d",[a,b,_,_,c,d,_,_,_,_,_,_,e,f,_,_] => do
    pure (.matrix (← numberOf a) (← numberOf b) (← numberOf c) (← numberOf d) (← numberOf e) (← numberOf f))
  | _,_ => none

/-- The steps of a `transform` value from its components: `none` (the value `none`) is no
step; `Option.none` when the components are not a transform list. -/
def steps (cvs : List CssValues.CV) : Option (List TransformStep) :=
  let cvs := CssValues.stripWs cvs
  match cvs with
  | [.tok (.ident k)] => if CssValues.lower k == "none" then some [] else none
  | _ =>
    if cvs.isEmpty || cvs.length > maxSteps then none else
    cvs.mapM fun
      | .fn name body => (((CssValues.stripWs body).filter (!isComma ·)).mapM arg).bind (step (CssValues.lower name))
      | _ => none

/-- The steps of a `transform` value as the property table computes it. -/
def read (computed : String) : Option (List TransformStep) := steps (CssValues.CV.parse computed)

/-- One part of a `transform-origin`: a length and a fraction of the box, or a keyword
that names a side (`horizontal`: it is `left` or `right`; `vertical`: `top` or `bottom`). -/
private def originPart : CssValues.CV → Option (Float × Float × Bool × Bool)
  | .tok (.ident k) => match CssValues.lower k with
    | "left" => some (0,0,true,false)
    | "right" => some (0,1,true,false)
    | "top" => some (0,0,false,true)
    | "bottom" => some (0,1,false,true)
    | "center" => some (0,0.5,false,false)
    | _ => none
  | cv => match arg cv with
    | some (.length x p) => some (x,p,false,false)
    | some (.number v) => if v == 0 then some (0,0,false,false) else none
    | _ => none

/-- A `transform-origin` (CSS Transforms 1 §8) as `(x, ofWidth, y, ofHeight)`: one or two
parts (a third, the depth, is not read); a keyword of the other axis may come first. -/
def origin (computed : String) : Option (Float × Float × Float × Float) :=
  match (CssValues.stripWs (CssValues.CV.parse computed)).mapM originPart with
  | some [(x,p,_,vertical)] => if vertical then some (0,0.5,x,p) else some (x,p,0,0.5)
  | some [(x,p,h1,v1),(y,q,h2,v2)] | some [(x,p,h1,v1),(y,q,h2,v2),_] =>
    if v1 || h2 then (if h1 || v2 then none else some (y,q,x,p)) else some (x,p,y,q)
  | _ => none

/-- A translation. -/
def translation {α : Type} (ops : Math.AffineScalarOps α) (dx dy : α) : Math.Affine2 α :=
  ⟨ops.one,ops.zero,ops.zero,ops.one,dx,dy⟩

/-- The transform `m` about the point `(ox, oy)`: that point is the origin of `m`. -/
def about {α : Type} (ops : Math.AffineScalarOps α) (m : Math.Affine2 α) (ox oy : α) : Math.Affine2 α :=
  Math.Affine2.compose ops (translation ops ox oy)
    (Math.Affine2.compose ops m (translation ops (ops.sub ops.zero ox) (ops.sub ops.zero oy)))

/-- The matrix of a list of steps for a box `width` by `height`: the product of the
steps in order, so the last function is applied to the box first (§12). -/
def matrixOf (steps : List TransformStep) (width height : Float) : Math.Affine2 Float :=
  steps.foldl (fun m s => Math.Affine2.compose .float m (match s with
    | .translate x xw y yh => translation .float (x+xw*width) (y+yh*height)
    | .matrix a b c d e f => ⟨a,b,c,d,e,f⟩)) (Math.Affine2.identity .float)

/-- The bounding box of the rectangle `(x, y, w, h)` under `m`. -/
def bounds (m : Math.Affine2 Float) (x y w h : Float) : Float × Float × Float × Float :=
  let p := Math.Affine2.applyPoint .float m
  let (x0,y0) := p x y
  let (x1,y1) := p (x+w) y
  let (x2,y2) := p (x+w) (y+h)
  let (x3,y3) := p x (y+h)
  let left := min (min x0 x1) (min x2 x3)
  let top := min (min y0 y1) (min y2 y3)
  (left,top,max (max x0 x1) (max x2 x3)-left,max (max y0 y1) (max y2 y3)-top)

/-- Whole-number scalars, for the theorems. -/
def intOps : Math.AffineScalarOps Int :=
  ⟨0,1,(·+·),(·-·),(·*·),fun a b => if b == 0 then none else some (a/b)⟩

/-- Says: the origin of a transform about a point moves only by the transform's own
translation: a rotation or a scale about a point leaves that point where it is. -/
theorem aboutInt_origin (m : Math.Affine2 Int) (ox oy : Int) :
    Math.Affine2.applyPoint intOps (about intOps m ox oy) ox oy = (ox+m.e,oy+m.f) := by
  simp only [about, translation, Math.Affine2.compose, Math.Affine2.applyPoint, intOps]
  simp only [Int.one_mul, Int.zero_mul, Int.mul_zero, Int.mul_one, Int.add_zero, Int.zero_add, Int.zero_sub]
  have hx : m.a * -ox + m.c * -oy + m.e + ox = ox + m.e - m.a * ox - m.c * oy := by
    rw [Int.mul_neg, Int.mul_neg]; omega
  have hy : m.b * -ox + m.d * -oy + m.f + oy = oy + m.f - m.b * ox - m.d * oy := by
    rw [Int.mul_neg, Int.mul_neg]; omega
  rw [hx, hy]
  ext <;> simp only <;> omega

/-- Says: a translation does not depend on the origin: about any point it moves every
point by its own offset. -/
theorem aboutInt_translation (dx dy ox oy x y : Int) :
    Math.Affine2.applyPoint intOps (about intOps (translation intOps dx dy) ox oy) x y = (x+dx,y+dy) := by
  simp only [about, translation, Math.Affine2.compose, Math.Affine2.applyPoint, intOps]
  simp only [Int.one_mul, Int.zero_mul, Int.mul_zero, Int.mul_one, Int.add_zero, Int.zero_add, Int.zero_sub]
  ext <;> simp only <;> omega

/-- Says: no function, no transform. -/
theorem matrixOf_nil (width height : Float) : matrixOf [] width height = Math.Affine2.identity .float := rfl

private theorem mapM_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp at h
    subst h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases fa : f a with
    | none => simp [fa] at h
    | some b =>
      cases fl : l.mapM f with
      | none => simp [fa, fl] at h
      | some bs =>
        simp [fa, fl] at h
        subst h
        simp [mapM_length f l bs fl]

/-- **A `transform` value has at most `maxSteps` functions.** -/
theorem steps_length_le (cvs : List CssValues.CV) (out : List TransformStep) (h : steps cvs = some out) :
    out.length ≤ maxSteps := by
  unfold steps at h
  simp only [] at h
  split at h
  · split at h
    · cases h; simp [maxSteps]
    · cases h
  · split at h
    · cases h
    · rename_i fits
      have same := mapM_length _ _ _ h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at fits
      omega

#guard (read "none").map (·.length) == some 0
#guard (read "translate(-50%, 10px)").map (·.length) == some 1
#guard match read "translate(-50%, 10px)" with | some [.translate x xw y yh] => x == 0 && xw == -0.5 && y == 10 && yh == 0 | _ => false
#guard match read "translateX(32px)" with | some [.translate x xw y yh] => x == 32 && xw == 0 && y == 0 && yh == 0 | _ => false
#guard match read "translate(calc(5% + 10px), 0)" with | some [.translate x xw y yh] => x == 10 && xw == 0.05 && y == 0 && yh == 0 | _ => false
#guard match read "scale(2, 3)" with | some [.matrix a b c d e f] => a == 2 && b == 0 && c == 0 && d == 3 && e == 0 && f == 0 | _ => false
#guard match read "matrix(1, 2, 3, 4, 5, 6)" with | some [.matrix a b c d e f] => a == 1 && b == 2 && c == 3 && d == 4 && e == 5 && f == 6 | _ => false
#guard match read "rotate(90deg)" with | some [.matrix a b c d _ _] => a.abs < 1e-9 && (b-1).abs < 1e-9 && (c+1).abs < 1e-9 && d.abs < 1e-9 | _ => false
#guard (read "translate(1px) rotate(10deg) scale(2)").map (·.length) == some 3
#guard (read "bogus(1px)").isNone
#guard (read "translate(1px, 2px, 3px)").isNone
#guard (read "10px").isNone
#guard origin "center" == some (0,0.5,0,0.5)
#guard origin "left" == some (0,0,0,0.5)
#guard origin "bottom" == some (0,0.5,0,1)
#guard origin "right top" == some (0,1,0,0)
#guard origin "top right" == some (0,1,0,0)
#guard origin "16px 25%" == some (16,0,0,0.25)
#guard origin "10px 20px 5px" == some (10,0,20,0)
#guard origin "top bottom" == none
-- a rotation by a quarter turn about the centre of a 100 by 50 box at (10, 20) turns it
-- on the spot: its bounding box is 50 by 100 around the same centre
#guard (let m := about .float (matrixOf (((read "rotate(90deg)").getD [])) 100 50) 60 45
        let (x,y,w,h) := bounds m 10 20 100 50
        (x-35).abs < 1e-6 && (y+5).abs < 1e-6 && (w-50).abs < 1e-6 && (h-100).abs < 1e-6)
-- translate(-50%, -50%) moves a box by half its own size
#guard (let m := about .float (matrixOf (((read "translate(-50%, -50%)").getD [])) 100 50) 60 45
        bounds m 10 20 100 50 == (-40,-5,100,50))

end BoxTransform
end L4Factoidal.Rendering.CSS
