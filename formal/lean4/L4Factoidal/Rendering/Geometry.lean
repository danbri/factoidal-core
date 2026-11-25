import L4Factoidal.Rendering.CssValues.Numeric
import L4Factoidal.Rendering.Animation.Matrix

/-!
# Geometry Interfaces 1: the matrices of `DOMMatrix`

The arithmetic behind `DOMMatrixReadOnly` and `DOMMatrix` (Geometry Interfaces 1 §6): a
matrix from a string (§6.2 "parse a string into an abstract matrix"), from a dictionary
(§6.1 "validate and fixup"), from a sequence of 6 or 16 numbers, and the operations that
change one (§6.5): products, translations, scales, rotations, skews, the inverse, and the
transform of a point (§3). The page's bindings (`prelude.js`) keep the 16 numbers and the
"is 2D" flag of each object and ask here for every new matrix (`DomOps` query op 167).

The numbers travel exactly: each is the 16 hexadecimal digits of its IEEE 754 bits
(`Float.toBits`), so a value a script gave comes back the same value. The products,
rotations and the inverse are those of `Animation.Matrix`, the arithmetic of CSS transforms.

A matrix is `Animation.Matrix.M`: 16 numbers column by column, as `matrix3d()` and as the
attributes `m11, m12, m13, m14, m21, …, m44` in that order.
-/

namespace L4Factoidal.Rendering.Geometry

open L4Factoidal.Rendering.CssValues
open L4Factoidal.Rendering.Animation

abbrev M := Matrix.M

/-! ## Exact numbers -/

/-- The nearest `Float` to the rational `q`, ties to even: the quotient is taken to at least
66 bits with a sticky bit for any remainder, then rounded once (`UInt64.toFloat`) and
scaled. A CSS number is a decimal, so `0.1` here is the double nearest 1/10. -/
def ratToFloat (q : Rat) : Float :=
  if q.num == 0 then 0 else
  let n := q.num.natAbs
  let d := q.den
  -- a quotient of about 70 bits: (n · 2^k) / d
  let k : Int := 70 + (d.log2 : Int) - (n.log2 : Int)
  let (num, den) := if k ≥ 0 then (n <<< k.toNat, d) else (n, d <<< (-k).toNat)
  let m := num / den
  let inexact := num % den != 0
  -- down to 64 bits, the bits shifted out and the remainder kept in the last bit
  let s := m.log2 - 63
  let top := m >>> s
  let sticky := inexact || m % (2 ^ s) != 0
  let m64 := (if sticky then top ||| 1 else top).toUInt64
  let x := Float.scaleB m64.toFloat ((s : Int) - k)
  if q.num < 0 then -x else x

/-- The 16 lower-case hexadecimal digits of a number's bits. -/
def hex (x : Float) : String :=
  let b := x.toBits.toNat
  String.ofList ((List.range 16).reverse.map fun i => Nat.toDigits 16 ((b >>> (4 * i)) % 16) |>.headD '0')

/-- The number of 16 hexadecimal digits of its bits; none for anything else. -/
def ofHex (s : String) : Option Float :=
  if s.length != 16 then none else
  s.toList.foldlM (fun acc c => (CssValues.hexVal c).map (acc * 16 + ·)) 0 |>.map
    fun n => Float.ofBits n.toUInt64

#guard ofHex (hex 0.1) == some 0.1 && hex 1 == "3ff0000000000000"
#guard ratToFloat ((1 : Rat) / 10) == 0.1 && ratToFloat ((-5 : Rat) / 2) == -2.5
#guard ratToFloat ((9600 : Rat) / 254) == 9600 / 254

/-- A matrix and its "is 2D" flag, as the bindings keep them: `2` or `3`, then 16 numbers. -/
def write (m : M) (two : Bool) : String :=
  (if two then "2" else "3") ++ String.join ((List.range 16).map fun i => hex (m.getD i 0))

def read (s : String) : Option (M × Bool) :=
  let two := s.startsWith "2"
  if !(two || s.startsWith "3") || s.length != 257 then none else
  let body := s.drop 1
  ((List.range 16).mapM fun i => ofHex ((body.drop (16 * i)).take 16).toString).map
    fun xs => (xs.toArray, two)

#guard (read (write Matrix.identity true)).map (·.2) == some true

/-! ## A string as a matrix (§6.2) -/

/-- A value of a transform function's argument, exact: a number, a length in px, or an angle
in degrees (`"px"`, `"deg"`, `""`; a percentage as `"%"`). Calculations are simplified first
and must come to one value; a length or angle that is not absolute (`em`, `vw`, `%` of a box)
is none. -/
def argValue (cvs : List CV) : Option (Rat × String) :=
  let canon := fun (v : Rat) (u : String) =>
    if u == "" then some (v, "") else (absFactor (lower u)).map fun (f, cu) => (v * f, cu)
  match stripWs cvs with
  | [.tok (.num v _)] => some (v, "")
  | [.tok (.pct v)] => some (v, "%")
  | [.tok (.dim v _ u)] => canon v u
  | [cv@(.fn _ _)] =>
    match (Calc.parse cv).map (Calc.simp none 64) with
    | some (.val v u) => canon v u
    | some (.sum [.val v u]) => canon v u
    | _ => none
  | _ => none

def numArg (a : Rat × String) : Option Float :=
  if a.2 == "" then some (ratToFloat a.1) else none
def scaleArg (a : Rat × String) : Option Float :=
  if a.2 == "" then some (ratToFloat a.1) else if a.2 == "%" then some (ratToFloat (a.1 / 100)) else none
def lengthArg (a : Rat × String) : Option Float :=
  if a.2 == "px" || (a.2 == "" && a.1 == 0) then some (ratToFloat a.1) else none
def angleArg (a : Rat × String) : Option Float :=
  if a.2 == "deg" || (a.2 == "" && a.1 == 0) then some (ratToFloat a.1) else none

/-- One transform function (CSS Transforms 1 §13, 2 §8): its matrix and whether it is a 2D
function. Names are matched without regard to case. -/
def fnMatrix (name : String) (args : List CV) : Option (M × Bool) := do
  let parts := if (stripWs args).isEmpty then [] else splitCommas args
  let vs ← parts.mapM argValue
  let all := fun (f : Rat × String → Option Float) => vs.mapM f
  match lower name, vs.length with
  | "matrix", 6 => let a ← all numArg; return (Matrix.ofAffine a[0]! a[1]! a[2]! a[3]! a[4]! a[5]!, true)
  | "matrix3d", 16 => let a ← all numArg; return (a.toArray, false)
  | "translate", 1 => let a ← all lengthArg; return (Matrix.translate a[0]! 0 0, true)
  | "translate", 2 => let a ← all lengthArg; return (Matrix.translate a[0]! a[1]! 0, true)
  | "translatex", 1 => let a ← all lengthArg; return (Matrix.translate a[0]! 0 0, true)
  | "translatey", 1 => let a ← all lengthArg; return (Matrix.translate 0 a[0]! 0, true)
  | "translatez", 1 => let a ← all lengthArg; return (Matrix.translate 0 0 a[0]!, false)
  | "translate3d", 3 => let a ← all lengthArg; return (Matrix.translate a[0]! a[1]! a[2]!, false)
  | "scale", 1 => let a ← all scaleArg; return (Matrix.scale a[0]! a[0]! 1, true)
  | "scale", 2 => let a ← all scaleArg; return (Matrix.scale a[0]! a[1]! 1, true)
  | "scalex", 1 => let a ← all scaleArg; return (Matrix.scale a[0]! 1 1, true)
  | "scaley", 1 => let a ← all scaleArg; return (Matrix.scale 1 a[0]! 1, true)
  | "scalez", 1 => let a ← all scaleArg; return (Matrix.scale 1 1 a[0]!, false)
  | "scale3d", 3 => let a ← all scaleArg; return (Matrix.scale a[0]! a[1]! a[2]!, false)
  | "rotate", 1 => let a ← all angleArg; return (Matrix.rotate 0 0 1 a[0]!, true)
  | "rotatez", 1 => let a ← all angleArg; return (Matrix.rotate 0 0 1 a[0]!, false)
  | "rotatex", 1 => let a ← all angleArg; return (Matrix.rotate 1 0 0 a[0]!, false)
  | "rotatey", 1 => let a ← all angleArg; return (Matrix.rotate 0 1 0 a[0]!, false)
  | "rotate3d", 4 =>
    let x ← numArg vs[0]!; let y ← numArg vs[1]!; let z ← numArg vs[2]!; let d ← angleArg vs[3]!
    return (Matrix.rotate x y z d, false)
  | "skew", 1 => let a ← all angleArg; return (Matrix.skew a[0]! 0, true)
  | "skew", 2 => let a ← all angleArg; return (Matrix.skew a[0]! a[1]!, true)
  | "skewx", 1 => let a ← all angleArg; return (Matrix.skew a[0]! 0, true)
  | "skewy", 1 => let a ← all angleArg; return (Matrix.skew 0 a[0]!, true)
  | "perspective", 1 =>
    match stripWs args with
    | [.tok (.ident k)] => if lower k == "none" then return (Matrix.identity, false) else none
    | _ => let d ← lengthArg vs[0]!; if d < 0 then none else return (Matrix.perspective (max d 1), false)
  | _, _ => none

/-- §6.2: the matrix of a `<transform-list>` (or `none`), and whether every function in it is
a 2D one; none for a string that is not one, or that uses a length or angle that is not
absolute. The empty string is the identity. -/
def parse (s : String) : Option (M × Bool) :=
  if s.isEmpty then some (Matrix.identity, true) else
  match stripWs (CV.parse s) with
  | [.tok (.ident k)] => if lower k == "none" then some (Matrix.identity, true) else none
  | [] => none
  | items =>
    items.foldlM (fun (acc : M × Bool) cv => match cv with
      | .fn name args => (fnMatrix name args).map fun (m, two) => (Matrix.mul acc.1 m, acc.2 && two)
      | _ => none) (Matrix.identity, true)

#guard (parse "scale(2) translateX(5px) translateY(5px)").map (fun p => (p.1.getD 12 0, p.2)) == some (10, true)
#guard (parse "scale(2)translateX(calc(2 * 2.5px))").map (·.1.getD 12 0) == some 10
#guard (parse "translateX(5em)").isNone && (parse " ").isNone && (parse "/**/").isNone && (parse "none;").isNone
#guard (parse "translateX    (5px)").isNone && (parse "scale(2, 2), translateX(5px)").isNone
#guard (parse "NONE").isSome && (parse "none/**/").isSome && (parse "").isSome && (parse "rotate(5)").isNone
#guard (parse "translate3d(1px, 2px, 0)").map (·.2) == some false
#guard (parse "matrix(1, 2, 3, 4, 5, 6)").map (·.1) == some (Matrix.ofAffine 1 2 3 4 5 6)

/-! ## A dictionary as a matrix (§6.1) -/

/-- SameValueZero of two numbers: NaN is NaN, 0 is -0. -/
def sameValueZero (a b : Float) : Bool := a == b || (a.isNaN && b.isNaN)

/-- §6.1 "validate and fixup" of a `DOMMatrix2DInit` (`threeD` false) or a `DOMMatrixInit`,
then "create a DOMMatrix from the dictionary": `members` are, in this order,
a b c d e f m11 m12 m13 m14 m21 m22 m23 m24 m31 m32 m33 m34 m41 m42 m43 m44 as given (none
when not present), and `is2D` likewise. None is a TypeError: a member and its alias that
differ, or a 3D member that is not its identity value in a dictionary that says it is 2D. -/
def fromInit (threeD : Bool) (members : Array (Option Float)) (is2D : Option Bool) : Option (M × Bool) := do
  let g := fun (i : Nat) => members.getD i none
  -- the six pairs of a 2D matrix: a/m11, b/m12, c/m21, d/m22, e/m41, f/m42
  let pair := fun (i j : Nat) (dflt : Float) =>
    match g i, g j with
    | some x, some y => if sameValueZero x y then some y else none
    | some x, none => some x
    | none, some y => some y
    | none, none => some dflt
  let m11 ← pair 0 6 1
  let m12 ← pair 1 7 0
  let m21 ← pair 2 10 0
  let m22 ← pair 3 11 1
  let m41 ← pair 4 18 0
  let m42 ← pair 5 19 0
  if !threeD then return (Matrix.ofAffine m11 m12 m21 m22 m41 m42, true)
  -- the 3D members: m13 m14 m23 m24 m31 m32 m34 m43 (0 when 2D), m33 m44 (1)
  let zeros := [8, 9, 12, 13, 14, 15, 17, 20]
  let ones := [16, 21]
  let flat := zeros.all (fun i => (g i).all (· == 0)) && ones.all (fun i => (g i).all (· == 1))
  if is2D == some true && !flat then none
  let two := is2D.getD flat
  if two then return (Matrix.ofAffine m11 m12 m21 m22 m41 m42, true)
  let v := fun (i : Nat) (dflt : Float) => (g i).getD dflt
  return (#[m11, m12, v 8 0, v 9 0, m21, m22, v 12 0, v 13 0, v 14 0, v 15 0, v 16 1, v 17 0,
    m41, m42, v 20 0, v 21 1], false)

#guard (fromInit true ((List.replicate 22 none).toArray.set! 0 (some 2)) none).map (·.2) == some true
#guard (fromInit true (((List.replicate 22 none).toArray.set! 0 (some 2)).set! 6 (some 3)) none).isNone
#guard (fromInit true ((List.replicate 22 none).toArray.set! 8 (some 1)) (some true)).isNone
#guard (fromInit true ((List.replicate 22 none).toArray.set! 8 (some 1)) none).map (·.2) == some false

/-! ## The operations (§6.5) -/

/-- The inverse of a matrix (§6.5 `invertSelf()`): that of a 2D matrix by its determinant,
that of another by `Matrix.inverse`; none when it is not invertible. -/
def inverse (m : M) (two : Bool) : Option M :=
  if two then
    let (a, b, c, d, e, f) := (m.getD 0 0, m.getD 1 0, m.getD 4 0, m.getD 5 0, m.getD 12 0, m.getD 13 0)
    let det := a * d - b * c
    if det == 0 || !det.isFinite then none else
    some (Matrix.ofAffine (d / det) (-b / det) (-c / det) (a / det) ((c * f - d * e) / det) ((b * e - a * f) / det))
  else Matrix.inverse m

/-- A matrix of 16 NaN: what `invertSelf()` makes of one that has no inverse. -/
def nanMatrix : M := (Array.range 16).map fun _ => (0 : Float) / 0

/-- The transform of the point `(x, y, z, w)` by the matrix (§3 "transform a point with a
matrix"). -/
def point (m : M) (x y z w : Float) : Float × Float × Float × Float :=
  let r := fun (i : Nat) => m.getD i 0 * x + m.getD (i + 4) 0 * y + m.getD (i + 8) 0 * z + m.getD (i + 12) 0 * w
  (r 0, r 1, r 2, r 3)

def degOfRad (r : Float) : Float := r * 180 / Matrix.pi

/-- One operation on the matrix `m` with "is 2D" `two`: the new matrix and flag; none for
arguments that do not fit the operation. Arguments are the bindings' (defaults filled). -/
def operate (verb : String) (m : M) (two : Bool) (xs : List Float) : Option (M × Bool) :=
  let post := fun (n : M) => Matrix.mul m n
  match verb, xs with
  | "translate", [tx, ty, tz] => some (post (Matrix.translate tx ty tz), two && tz == 0)
  | "scale", [sx, sy, sz, ox, oy, oz] =>
    let n := Matrix.mul (Matrix.translate ox oy oz) (Matrix.mul (Matrix.scale sx sy sz) (Matrix.translate (-ox) (-oy) (-oz)))
    some (post n, two && sz == 1 && oz == 0)
  | "rotate", [rx, ry, rz] =>
    let n := Matrix.mul (Matrix.rotate 0 0 1 rz) (Matrix.mul (Matrix.rotate 0 1 0 ry) (Matrix.rotate 1 0 0 rx))
    some (post n, two && rx == 0 && ry == 0)
  | "vector", [x, y] =>
    let deg := if x == 0 && y == 0 then 0 else degOfRad (Float.atan2 y x)
    some (post (Matrix.rotate 0 0 1 deg), two)
  | "axis", [x, y, z, angle] => some (post (Matrix.rotate x y z angle), two && x == 0 && y == 0)
  | "skewx", [s] => some (post (Matrix.skew s 0), two)
  | "skewy", [s] => some (post (Matrix.skew 0 s), two)
  | "invert", [] =>
    match inverse m two with
    | some n => some (n, two)
    | none => some (nanMatrix, false)
  | _, _ => none

/-- The query of the bindings (`DomOps` op 167): fields separated by U+0000, numbers as
`hex`, matrices as `write`. Answers a matrix as `write`, a point as four `hex`, `"S"` for a
SyntaxError, `"T"` for a TypeError. -/
def answer (q : String) : String :=
  let num := fun (s : String) => ofHex s
  match q.splitOn "\x00" with
  | ["parse", text] => match parse text with | some (m, two) => write m two | none => "S"
  | ["seq", body] =>
    let n := body.length / 16
    match (List.range n).mapM (fun i => num ((body.drop (16 * i)).take 16).toString) with
    | some [a, b, c, d, e, f] => write (Matrix.ofAffine a b c d e f) true
    | some xs => if xs.length == 16 && body.length == 256 then write xs.toArray false else "T"
    | none => "T"
  | ["init", mode, members, is2D] =>
    let ms := (List.range 22).map fun i => num ((members.drop (16 * i)).take 16).toString
    let flag := if is2D == "1" then some true else if is2D == "0" then some false else none
    match fromInit (mode == "3") ms.toArray flag with
    | some (m, two) => write m two
    | none => "T"
  | ["mul", a, b] =>
    match read a, read b with
    | some (x, tx), some (y, ty) => write (Matrix.mul x y) (tx && ty)
    | _, _ => "T"
  | ["point", a, x, y, z, w] =>
    match read a, num x, num y, num z, num w with
    | some (m, _), some x, some y, some z, some w =>
      let (p, q, r, s) := point m x y z w
      hex p ++ hex q ++ hex r ++ hex s
    | _, _, _, _, _ => "T"
  | verb :: a :: args =>
    match read a, args.mapM num with
    | some (m, two), some xs => match operate verb m two xs with | some (n, t) => write n t | none => "T"
    | _, _ => "T"
  | _ => "T"

#guard answer ("parse\x00none") == write Matrix.identity true
#guard answer ("translate\x00" ++ write Matrix.identity true ++ "\x00" ++ hex 1 ++ "\x00" ++ hex 2 ++ "\x00" ++ hex 0) ==
  write (Matrix.translate 1 2 0) true
#guard (read (answer ("invert\x00" ++ write (Matrix.ofAffine 2 0 0 2 10 10) true))) == some (Matrix.ofAffine 0.5 0 0 0.5 (-5) (-5), true)
#guard answer ("invert\x00" ++ write (Matrix.ofAffine 0 0 0 0 0 0) true) == write nanMatrix false
#guard answer ("point\x00" ++ write (Matrix.translate 1 2 3) false ++ "\x00" ++ hex 1 ++ "\x00" ++ hex 1 ++ "\x00" ++ hex 1 ++ "\x00" ++ hex 1) ==
  hex 2 ++ hex 3 ++ hex 4 ++ hex 1

/-- Kind: invariant. Says: the inverse of a 2D matrix that has one is a 2D matrix written by
`Matrix.ofAffine` (its 3D entries are those of the identity). Does not say: anything of the
values. -/
theorem inverse_two_affine (m : M) (n : M) (h : inverse m true = some n) :
    ∃ a b c d e f, n = Matrix.ofAffine a b c d e f := by
  unfold inverse at h
  simp only [↓reduceIte] at h
  split at h
  · simp at h
  · injection h with h
    exact ⟨_, _, _, _, _, _, h.symm⟩

/-- Kind: invariant. Says: a translation keeps a 3D matrix 3D: the flag only ever turns from
2D to 3D (§6.5 `translateSelf`). -/
theorem translate_keeps_3d (m : M) (tx ty tz : Float) :
    (operate "translate" m false [tx, ty, tz]).map (·.2) = some false := by
  simp [operate]

/-- Kind: invariant. Says: a matrix with no inverse becomes the NaN matrix, and 3D
(§6.5 `invertSelf` step 2). -/
theorem invert_none (m : M) (two : Bool) (h : inverse m two = none) :
    operate "invert" m two [] = some (nanMatrix, false) := by
  simp [operate, h]

end L4Factoidal.Rendering.Geometry
