/-
# Matrices of CSS transforms: products, decomposition, interpolation

CSS Transforms 1 §12 and §13, CSS Transforms 2 §8 and §9: a transform list is a product of
4×4 matrices; two lists that do not pair up function by function interpolate as matrices,
which means: decompose each into a translation, a scale, a skew, a rotation and a
perspective, interpolate those, and compose the result.

This module is the arithmetic alone, over `Float` (square roots, sines, arc tangents): it
reads no CSS text and knows no property. `Value` reads transform functions into matrices
and writes matrices back as `matrix()` or `matrix3d()`.

What is proved here is about shape (sizes, the identity cases that reduce by `rfl`); the
numeric results are tested (`#guard` with a tolerance) against the expected values of the
Web Platform Tests. `Float` arithmetic is IEEE 754 and is not reasoned about.
-/

namespace L4Factoidal.Rendering.Animation.Matrix

/-- A 4×4 matrix in the order of `matrix3d()`: 16 numbers, column by column. -/
abbrev M := Array Float

/-- The entry of column `c` and row `r` (both from 0); 0 outside the matrix. -/
def M.at (m : M) (c r : Nat) : Float := m.getD (c * 4 + r) 0

/-- The matrix whose entry of column `c`, row `r` is `f c r`. -/
def build (f : Nat → Nat → Float) : M := (Array.range 16).map fun i => f (i / 4) (i % 4)

def identity : M := build fun c r => if c == r then 1 else 0

/-- The product `a · b`: a point goes through `b` first, as the transform list `a b`. -/
def mul (a b : M) : M :=
  build fun c r => a.at 0 r * b.at c 0 + a.at 1 r * b.at c 1 + a.at 2 r * b.at c 2 + a.at 3 r * b.at c 3

/-- Kind: shape. Says: a built matrix has 16 entries. Does not say: anything of their
values. -/
theorem build_size (f : Nat → Nat → Float) : (build f).size = 16 := by
  simp [build]

theorem mul_size (a b : M) : (mul a b).size = 16 := build_size _

/-! ## The transform functions (CSS Transforms 1 §13, CSS Transforms 2 §8) -/

def translate (x y z : Float) : M :=
  build fun c r => if c == r then 1 else if c == 3 then (if r == 0 then x else if r == 1 then y else if r == 2 then z else 0) else 0

def scale (x y z : Float) : M :=
  build fun c r => if c != r then 0 else if c == 0 then x else if c == 1 then y else if c == 2 then z else 1

def pi : Float := 3.14159265358979323846

def radians (deg : Float) : Float := deg * pi / 180
def degrees (rad : Float) : Float := rad * 180 / pi

/-- A rotation by `deg` degrees about the axis `(x, y, z)` (CSS Transforms 2 §8
`rotate3d()`); the identity for a zero axis. -/
def rotate (x y z deg : Float) : M :=
  let len := Float.sqrt (x * x + y * y + z * z)
  if len == 0 then identity else
  let (x, y, z) := (x / len, y / len, z / len)
  let h := radians deg / 2
  let sc := Float.sin h * Float.cos h
  let sq := Float.sin h * Float.sin h
  #[1 - 2 * (y * y + z * z) * sq, 2 * (x * y * sq + z * sc), 2 * (x * z * sq - y * sc), 0,
    2 * (x * y * sq - z * sc), 1 - 2 * (x * x + z * z) * sq, 2 * (y * z * sq + x * sc), 0,
    2 * (x * z * sq + y * sc), 2 * (y * z * sq - x * sc), 1 - 2 * (x * x + y * y) * sq, 0,
    0, 0, 0, 1]

/-- `skew(ax, ay)` in degrees: `matrix(1, tan(ay), tan(ax), 1, 0, 0)`. -/
def skew (ax ay : Float) : M :=
  build fun c r => if c == r then 1 else if c == 1 && r == 0 then Float.tan (radians ax)
    else if c == 0 && r == 1 then Float.tan (radians ay) else 0

/-- `perspective(d)`: the entry of column 3, row 4 is -1/d; `d` of 0 or less is the
identity here (the caller clamps a length to at least 1px, CSS Transforms 2 §8). -/
def perspective (d : Float) : M :=
  build fun c r => if c == r then 1 else if c == 2 && r == 3 && d > 0 then -1 / d else 0

/-- `matrix(a, b, c, d, e, f)`. -/
def ofAffine (a b c d e f : Float) : M :=
  #[a, b, 0, 0, c, d, 0, 0, 0, 0, 1, 0, e, f, 0, 1]

/-- The matrix is one of two dimensions: it can be written `matrix(a, b, c, d, e, f)`
(CSS Transforms 2 §8). -/
def is2D (m : M) : Bool :=
  m.at 0 2 == 0 && m.at 0 3 == 0 && m.at 1 2 == 0 && m.at 1 3 == 0 &&
  m.at 2 0 == 0 && m.at 2 1 == 0 && m.at 2 2 == 1 && m.at 2 3 == 0 &&
  m.at 3 2 == 0 && m.at 3 3 == 1

/-! ## Inverse (for the perspective part of a decomposition) -/

/-- The inverse by Gauss–Jordan elimination with row pivoting; none for a matrix whose
pivot vanishes (a singular matrix). Rows of the working table are the matrix's rows
beside the identity's. -/
def inverse (m : M) : Option M := Id.run do
  -- t[r][k]: row r, columns 0..3 the matrix, 4..7 the identity
  let mut t : Array (Array Float) := (Array.range 4).map fun r =>
    (Array.range 8).map fun k => if k < 4 then m.at k r else if k - 4 == r then 1 else 0
  for col in [0:4] do
    -- the row at or below `col` with the largest entry in this column
    let mut best := col
    for r in [col + 1:4] do
      if (t[r]!)[col]!.abs > (t[best]!)[col]!.abs then best := r
    let pivot := (t[best]!)[col]!
    if pivot == 0 || !pivot.isFinite then return none
    let rowBest := t[best]!
    let rowCol := t[col]!
    t := (t.set! best rowCol).set! col (rowBest.map (· / pivot))
    let p := t[col]!
    for r in [0:4] do
      if r != col then
        let f := (t[r]!)[col]!
        if f != 0 then t := t.set! r ((Array.range 8).map fun k => (t[r]!)[k]! - f * p[k]!)
  return some (build fun c r => (t[r]!)[c + 4]!)

/-! ## The 3D decomposition (CSS Transforms 2 §9.2, "unmatrix") -/

/-- A matrix as perspective · translation · rotation · skews · scale. -/
structure D3 where
  px : Float := 0
  py : Float := 0
  pz : Float := 0
  pw : Float := 1
  tx : Float := 0
  ty : Float := 0
  tz : Float := 0
  sx : Float := 1
  sy : Float := 1
  sz : Float := 1
  /-- The skews: xy, xz, yz. -/
  kxy : Float := 0
  kxz : Float := 0
  kyz : Float := 0
  /-- The rotation as a quaternion (x, y, z, w). -/
  qx : Float := 0
  qy : Float := 0
  qz : Float := 0
  qw : Float := 1
  deriving Inhabited

abbrev V3 := Float × Float × Float

def dot (a b : V3) : Float := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def norm (a : V3) : Float := Float.sqrt (dot a a)
def scaled (a : V3) (k : Float) : V3 := (a.1 * k, a.2.1 * k, a.2.2 * k)
/-- `a · ka + b · kb`. -/
def combine (a b : V3) (ka kb : Float) : V3 := (a.1 * ka + b.1 * kb, a.2.1 * ka + b.2.1 * kb, a.2.2 * ka + b.2.2 * kb)
def cross (a b : V3) : V3 := (a.2.1 * b.2.2 - a.2.2 * b.2.1, a.2.2 * b.1 - a.1 * b.2.2, a.1 * b.2.1 - a.2.1 * b.1)
def unit (a : V3) : V3 := let n := norm a; if n == 0 then a else scaled a (1 / n)

/-- CSS Transforms 2 §9.2 "decomposing a 3D matrix": none for a matrix with no inverse. -/
def decompose3 (m0 : M) : Option D3 :=
  let w := m0.at 3 3
  if w == 0 || m0.size != 16 then none else
  let m : M := m0.map (· / w)
  -- the matrix without its perspective row: also the test of singularity
  let pm := build fun c r => if r == 3 then (if c == 3 then 1 else 0) else m.at c r
  match inverse pm with
  | none => none
  | some inv =>
    let (px, py, pz, pw) :=
      if m.at 0 3 != 0 || m.at 1 3 != 0 || m.at 2 3 != 0 then
        let rhs := fun (i : Nat) => m.at i 3
        let solve := fun (j : Nat) => rhs 0 * inv.at j 0 + rhs 1 * inv.at j 1 + rhs 2 * inv.at j 2 + rhs 3 * inv.at j 3
        (solve 0, solve 1, solve 2, solve 3)
      else (0, 0, 0, 1)
    let row := fun (i : Nat) => ((m.at i 0, m.at i 1, m.at i 2) : V3)
    -- the x scale; the first row to length 1
    let sx := norm (row 0)
    let r0 := unit (row 0)
    -- the xy shear; the second row made orthogonal to the first
    let kxy := dot r0 (row 1)
    let r1 := combine (row 1) r0 1 (-kxy)
    let sy := norm r1
    let r1 := unit r1
    let kxy := if sy == 0 then kxy else kxy / sy
    -- the xz and yz shears; the third row made orthogonal to both
    let kxz := dot r0 (row 2)
    let r2 := combine (row 2) r0 1 (-kxz)
    let kyz := dot r1 r2
    let r2 := combine r2 r1 1 (-kyz)
    let sz := norm r2
    let r2 := unit r2
    let kxz := if sz == 0 then kxz else kxz / sz
    let kyz := if sz == 0 then kyz else kyz / sz
    -- a flip of the coordinate system: the scales and the rows negated
    let flip := dot r0 (cross r1 r2) < 0
    let (sx, sy, sz) := if flip then (-sx, -sy, -sz) else (sx, sy, sz)
    let (r0, r1, r2) := if flip then (scaled r0 (-1), scaled r1 (-1), scaled r2 (-1)) else (r0, r1, r2)
    -- the rotation
    let half := fun (x : Float) => 0.5 * Float.sqrt (if x > 0 then x else 0)
    let qx := half (1 + r0.1 - r1.2.1 - r2.2.2)
    let qy := half (1 - r0.1 + r1.2.1 - r2.2.2)
    let qz := half (1 - r0.1 - r1.2.1 + r2.2.2)
    let qw := half (1 + r0.1 + r1.2.1 + r2.2.2)
    let qx := if r2.2.1 > r1.2.2 then -qx else qx
    let qy := if r0.2.2 > r2.1 then -qy else qy
    let qz := if r1.1 > r0.2.1 then -qz else qz
    some { px, py, pz, pw, tx := m.at 3 0, ty := m.at 3 1, tz := m.at 3 2, sx, sy, sz, kxy, kxz, kyz, qx, qy, qz, qw }

/-- CSS Transforms 2 §9.4 "recomposing to a 3D matrix": perspective, translation, the
rotation of the quaternion, the three skews, the scale. -/
def compose3 (d : D3) : M :=
  -- perspective and translation (the translation goes through the perspective row)
  let pt : M := build fun c r =>
    if r == 3 then
      (if c == 0 then d.px else if c == 1 then d.py else if c == 2 then d.pz
       else d.tx * d.px + d.ty * d.py + d.tz * d.pz + d.pw)
    else if c == 3 then (if r == 0 then d.tx else if r == 1 then d.ty else d.tz)
    else if c == r then 1 else 0
  let (x, y, z, w) := (d.qx, d.qy, d.qz, d.qw)
  -- the rotation matrix of a unit quaternion, written by rows
  let rot : M := #[
    1 - 2 * (y * y + z * z), 2 * (x * y + z * w), 2 * (x * z - y * w), 0,
    2 * (x * y - z * w), 1 - 2 * (x * x + z * z), 2 * (y * z + x * w), 0,
    2 * (x * z + y * w), 2 * (y * z - x * w), 1 - 2 * (x * x + y * y), 0,
    0, 0, 0, 1]
  let shear := fun (c r : Nat) (k : Float) => build fun c' r' => if c' == r' then 1 else if c' == c && r' == r then k else 0
  let m := mul pt rot
  let m := if d.kyz != 0 then mul m (shear 2 1 d.kyz) else m
  let m := if d.kxz != 0 then mul m (shear 2 0 d.kxz) else m
  let m := if d.kxy != 0 then mul m (shear 1 0 d.kxy) else m
  mul m (scale d.sx d.sy d.sz)

def lerp (a b t : Float) : Float := a + (b - a) * t

/-- Two unit quaternions at `t` along the shorter arc between them (spherical linear
interpolation); the first when they are one rotation. -/
def slerp (a b : Float × Float × Float × Float) (t : Float) : Float × Float × Float × Float :=
  let (ax, ay, az, aw) := a
  let (bx, by_, bz, bw) := b
  let c := ax * bx + ay * by_ + az * bz + aw * bw
  -- (x, y, z, w) and its negation are one rotation: take the one on the near side
  let (ax, ay, az, aw, c) := if c < 0 then (-ax, -ay, -az, -aw, -c) else (ax, ay, az, aw, c)
  let c := if c > 1 then 1 else c
  let s := Float.sqrt (1 - c * c)
  if s < 0.00001 then (ax, ay, az, aw)
  else
    let h := Float.acos c
    let ka := Float.sin ((1 - t) * h) / s
    let kb := Float.sin (t * h) / s
    (ka * ax + kb * bx, ka * ay + kb * by_, ka * az + kb * bz, ka * aw + kb * bw)

/-- CSS Transforms 2 §9.3 "interpolation of decomposed 3D matrix values". -/
def blend3 (a b : D3) (t : Float) : D3 :=
  let (qx, qy, qz, qw) := slerp (a.qx, a.qy, a.qz, a.qw) (b.qx, b.qy, b.qz, b.qw) t
  { px := lerp a.px b.px t, py := lerp a.py b.py t, pz := lerp a.pz b.pz t, pw := lerp a.pw b.pw t,
    tx := lerp a.tx b.tx t, ty := lerp a.ty b.ty t, tz := lerp a.tz b.tz t,
    sx := lerp a.sx b.sx t, sy := lerp a.sy b.sy t, sz := lerp a.sz b.sz t,
    kxy := lerp a.kxy b.kxy t, kxz := lerp a.kxz b.kxz t, kyz := lerp a.kyz b.kyz t,
    qx, qy, qz, qw }

/-! ## The 2D decomposition (CSS Transforms 1 §12.2) -/

/-- A 2D matrix as translation · rotation · skew · scale. -/
structure D2 where
  tx : Float := 0
  ty : Float := 0
  sx : Float := 1
  sy : Float := 1
  /-- The shear of x by y. -/
  k : Float := 0
  /-- The rotation in radians. -/
  angle : Float := 0
  deriving Inhabited

/-- CSS Transforms 1 §12.2.1 "decomposing a 2D matrix", with the shear as one number:
the first column gives the x scale and the angle; the second, turned back by the angle,
the shear and the y scale. A negative determinant flips the axis whose unit vector is
further from its own direction. -/
def decompose2 (m : M) : D2 :=
  let (a, b, c, d) := (m.at 0 0, m.at 0 1, m.at 1 0, m.at 1 1)
  let sx := Float.sqrt (a * a + b * b)
  let sy := Float.sqrt (c * c + d * d)
  let det := a * d - b * c
  let (sx, sy) := if det < 0 then (if a < d then (-sx, sy) else (sx, -sy)) else (sx, sy)
  let (a, b) := if sx != 0 then (a / sx, b / sx) else (a, b)
  let (c, d) := if sy != 0 then (c / sy, d / sy) else (c, d)
  let angle := Float.atan2 b a
  -- the second column turned back by the angle
  let (c, d) := if angle != 0 then (a * c + b * d, -b * c + a * d) else (c, d)
  -- (c, d) is now (k, 1) scaled: the shear, and the rest of the y scale
  let (k, sy) := if d != 0 then (c / d, sy * d) else (c, sy)
  { tx := m.at 3 0, ty := m.at 3 1, sx, sy, k, angle }

/-- Translation · rotation · skew · scale as a matrix. -/
def compose2 (d : D2) : M :=
  let (cs, sn) := (Float.cos d.angle, Float.sin d.angle)
  -- rotation · [1 k; 0 1] · scale
  ofAffine (cs * d.sx) (sn * d.sx) ((cs * d.k - sn) * d.sy) ((sn * d.k + cs) * d.sy) d.tx d.ty

/-- CSS Transforms 1 §12.2.2 "interpolation of decomposed 2D matrix values": a flip of x
in one and of y in the other is a half turn; the rotation goes the short way round. -/
def blend2 (a b : D2) (t : Float) : D2 :=
  let a := if (a.sx < 0 && b.sy < 0) || (a.sy < 0 && b.sx < 0) then
      { a with sx := -a.sx, sy := -a.sy, angle := a.angle + (if a.angle < 0 then pi else -pi) }
    else a
  let (aa, ba) := (if a.angle == 0 then 2 * pi else a.angle, if b.angle == 0 then 2 * pi else b.angle)
  let (aa, ba) := if (aa - ba).abs > pi then (if aa > ba then (aa - 2 * pi, ba) else (aa, ba - 2 * pi)) else (aa, ba)
  { tx := lerp a.tx b.tx t, ty := lerp a.ty b.ty t, sx := lerp a.sx b.sx t, sy := lerp a.sy b.sy t,
    k := lerp a.k b.k t, angle := lerp aa ba t }

/-- Two matrices at `t` (CSS Transforms 2 §9 "interpolation of matrices"): as 2D
matrices when both are; none when one of them has no decomposition (the caller's values
then do not interpolate). -/
def blend (a b : M) (t : Float) : Option M :=
  if is2D a && is2D b then
    -- a 2D matrix with no inverse does not interpolate (CSS Transforms 1 §12)
    let det := fun (m : M) => m.at 0 0 * m.at 1 1 - m.at 0 1 * m.at 1 0
    if det a == 0 || det b == 0 then none
    else some (compose2 (blend2 (decompose2 a) (decompose2 b) t))
  else
    match decompose3 a, decompose3 b with
    | some x, some y => some (compose3 (blend3 x y t))
    | _, _ => none

/-- The product of two quaternions: the rotation of `b`, then that of `a`. -/
def qmul (a b : Float × Float × Float × Float) : Float × Float × Float × Float :=
  let (ax, ay, az, aw) := a
  let (bx, by_, bz, bw) := b
  (aw * bx + ax * bw + ay * bz - az * by_, aw * by_ - ax * bz + ay * bw + az * bx,
   aw * bz + ax * by_ - ay * bx + az * bw, aw * bw - ax * bx - ay * by_ - az * bz)

/-- `b` accumulated onto `a` (Web Animations 1 §5.2 with CSS Transforms 2 §9: matrices
accumulate by their decomposed values): translations, skews and perspectives add, scales
add about 1, rotations follow one another. None when one has no decomposition. -/
def accumulate (a b : M) : Option M :=
  if is2D a && is2D b then
    let det := fun (m : M) => m.at 0 0 * m.at 1 1 - m.at 0 1 * m.at 1 0
    if det a == 0 || det b == 0 then none
    else
      let (x, y) := (decompose2 a, decompose2 b)
      some (compose2 { tx := x.tx + y.tx, ty := x.ty + y.ty, sx := x.sx + y.sx - 1, sy := x.sy + y.sy - 1,
                       k := x.k + y.k, angle := x.angle + y.angle })
  else
    match decompose3 a, decompose3 b with
    | some x, some y =>
      let (qx, qy, qz, qw) := qmul (x.qx, x.qy, x.qz, x.qw) (y.qx, y.qy, y.qz, y.qw)
      some (compose3 {
        px := x.px + y.px, py := x.py + y.py, pz := x.pz + y.pz, pw := x.pw + y.pw - 1,
        tx := x.tx + y.tx, ty := x.ty + y.ty, tz := x.tz + y.tz,
        sx := x.sx + y.sx - 1, sy := x.sy + y.sy - 1, sz := x.sz + y.sz - 1,
        kxy := x.kxy + y.kxy, kxz := x.kxz + y.kxz, kyz := x.kyz + y.kyz, qx, qy, qz, qw })
    | _, _ => none

/-! ## Tests -/

/-- Entry by entry within 10⁻⁶. -/
def near (a b : M) : Bool :=
  a.size == 16 && b.size == 16 && (List.range 16).all fun i => (a.getD i 0 - b.getD i 0).abs < 0.000001

#guard near (mul identity (translate 1 2 3)) (translate 1 2 3)
#guard near (mul (translate 1 2 3) (translate 10 20 30)) (translate 11 22 33)
#guard near (mul (scale 2 3 4) (translate 1 1 1)) #[2, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4, 0, 2, 3, 4, 1]
#guard near (rotate 0 0 1 90) (ofAffine 0 1 (-1) 0 0 0)
#guard near (rotate 0 0 2 90) (rotate 0 0 1 90)
#guard near (rotate 1 0 0 90) #[1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 1]
#guard near (skew 45 0) (ofAffine 1 0 1 1 0 0)
#guard near (perspective 10) #[1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -0.1, 0, 0, 0, 1]
#guard is2D (ofAffine 1 2 3 4 5 6) && !is2D (perspective 10) && !is2D (rotate 1 0 0 30) && is2D (rotate 0 0 1 30)
-- inverse
#guard (inverse (mul (translate 5 6 7) (scale 2 4 8))).map (fun i => near (mul i (mul (translate 5 6 7) (scale 2 4 8))) identity) == some true
#guard (inverse (scale 0 1 1)).isNone
-- a decomposition composes back
private def sample3 : M := mul (mul (mul (translate 8 (-4) 12) (rotate 1 2 3 40)) (mul (skew 20 0) (scale 2 3 0.5))) (perspective 400)
-- a matrix whose last entry is not 1 composes back divided by it (one projective transform)
private def sample3w : M := mul (perspective 400) sample3
#guard (decompose3 sample3w).map (fun d => near (compose3 d) (sample3w.map (· / sample3w.at 3 3))) == some true
#guard (decompose3 sample3).map (fun d => near (compose3 d) sample3) == some true
#guard (decompose3 (rotate 0 0 1 200)).map (fun d => near (compose3 d) (rotate 0 0 1 200)) == some true
#guard (decompose3 (scale 0 1 1)).isNone
private def sample2 : M := ofAffine 1 0.36 0.2 (-1.5) 200 100
#guard near (compose2 (decompose2 sample2)) sample2
#guard near (compose2 (decompose2 (ofAffine 0 7 (-1) 0 6 0))) (ofAffine 0 7 (-1) 0 6 0)
-- the ends
#guard (blend sample3 (rotate 1 0 0 50) 0).map (near sample3) == some true
#guard (blend sample3 (rotate 1 0 0 50) 1).map (near (rotate 1 0 0 50)) == some true
#guard (blend sample2 (ofAffine 2 0 0 2 0 0) 0).map (near sample2) == some true
#guard (blend sample2 (ofAffine 2 0 0 2 0 0) 1).map (near (ofAffine 2 0 0 2 0 0)) == some true
-- css/css-transforms/animation/transform-interpolation-005.html
#guard (blend (ofAffine 1 0 0 1 0 (-6)) (ofAffine 0 7 (-1) 0 6 0) (-1)).map (near (ofAffine 0 5 1 0 (-6) (-12))) == some true
#guard (blend (ofAffine 1 0 0 1 0 (-6)) (ofAffine 0 7 (-1) 0 6 0) 0.5).map
  (near (ofAffine (4 * Float.cos (pi / 4)) (4 * Float.sin (pi / 4)) (-(Float.sin (pi / 4))) (Float.cos (pi / 4)) 3 (-3))) == some true
-- accumulation: the identity changes nothing; two rotations follow one another
#guard (accumulate sample3 identity).map (near sample3) == some true
#guard (accumulate (rotate 0 0 1 30) (rotate 0 0 1 40)).map (near (rotate 0 0 1 70)) == some true
#guard (accumulate (rotate 1 0 0 30) (rotate 1 0 0 40)).map (near (rotate 1 0 0 70)) == some true
#guard (accumulate (mul (translate 100 0 0) (scale 2 2 1)) (mul (translate 50 0 0) (scale 3 3 1))).map
  (near (mul (translate 150 0 0) (scale 4 4 1))) == some true
-- a matrix with no inverse does not interpolate
#guard (blend (ofAffine 1 1 0 0 0 0) identity 0.5).isNone

end L4Factoidal.Rendering.Animation.Matrix
