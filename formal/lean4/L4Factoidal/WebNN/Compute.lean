/-
L4Factoidal.WebNN.Compute: the arithmetic of the Web Neural Network operators on the CPU: the
reference backend. Element-wise functions, broadcasting binary operators, reductions, matrix
products, convolutions, pooling, normalisations, resampling, quantisation and the recurrent
cells.

Numerics (see `Tensor.lean`): elements of float tensors are binary64 values exactly
representable in the tensor's type; every operator computes in binary64 (`Float`, with the
platform's `exp`, `log`, `tanh`, … as BubblePopJS's `Math` uses) and rounds each output
element once to the type. Sums of many products (matmul, conv2d, reductions) are therefore
accumulated in binary64 and are at least as accurate as a binary32 accumulation; they are
not bit-identical to one, which the WPT tolerances allow for. Integer tensors are exact and
wrap. Nothing here is proved about floating point: the kernels are tested against the WPT
vectors (`Tests.lean` and the conformance tests).

Buffers are flat; loops index them with multiplications, with no object per element.
-/
import L4Factoidal.WebNN.Move
import L4Factoidal.WebNN.Approx

namespace L4Factoidal.WebNN
open Shape

/-! ## Scalar functions -/

def sqrt2 : Float := Float.sqrt 2.0
def sqrtPi : Float := Float.sqrt (4.0 * Float.atan 1.0)

/-! The transcendental functions are `WebNN.Approx`'s, evaluated in binary64: one definition
shared with the GPU kernels (record, section 2.9). -/

def expF (x : Float) : Float := Id.run (Approx.exp x)
def logF (x : Float) : Float := Id.run (Approx.log x)
def tanhF (x : Float) : Float := Id.run (Approx.tanh x)
def erf (x : Float) : Float := Id.run (Approx.erf x)
/-- `erfc x`, with `erfc(−a) = 2 − erfc(a)`. -/
def erfc (x : Float) : Float := if x < 0.0 then 2.0 - Id.run (Approx.erfcPos (-x)) else Id.run (Approx.erfcPos x)
def expm1 (x : Float) : Float := Id.run (Approx.expm1 x)
def softplus (x : Float) : Float := Id.run (Approx.softplus x)
def sigmoid (x : Float) : Float := Id.run (Approx.sigmoid x)
def gelu (x : Float) : Float := Id.run (Approx.gelu x)
def powF (x y : Float) : Float := Id.run (Approx.pow x y)

def signF (x : Float) : Float := if x > 0.0 then 1.0 else if x < 0.0 then -1.0 else x

/-- The element-wise unary operators and activations on floats. `alpha` and `beta` are the
operator's attributes, already cast to the tensor's type. -/
def unaryF (name : String) (alpha beta : Float) : Float → Float :=
  match name with
  | "abs" => Float.abs
  | "ceil" => Float.ceil
  | "cos" => Float.cos
  | "erf" => erf
  | "exp" => expF
  | "floor" => Float.floor
  | "log" => logF
  | "neg" => fun x => -x
  | "reciprocal" => fun x => 1.0 / x
  | "roundEven" => roundEvenF
  | "sin" => Float.sin
  | "sign" => signF
  | "sqrt" => Float.sqrt
  | "tan" => Float.tan
  | "relu" => fun x => if x > 0.0 then x else if x.isNaN then x else 0.0
  | "sigmoid" => sigmoid
  | "softplus" => softplus
  | "softsign" => fun x => x / (1.0 + x.abs)
  | "tanh" => tanhF
  | "gelu" => gelu
  | "elu" => fun x => Id.run (Approx.elu alpha x)
  | "hardSigmoid" => fun x => let y := alpha * x + beta; if y < 0.0 then 0.0 else if y > 1.0 then 1.0 else y
  | "hardSwish" => fun x => let y := x + 3.0; x * (if y < 0.0 then 0.0 else if y > 6.0 then 6.0 else y) / 6.0
  | "leakyRelu" => fun x => if x ≥ 0.0 then x else alpha * x
  | "linear" => fun x => alpha * x + beta
  | _ => id

def unaryI (name : String) : Int → Int :=
  match name with
  | "abs" => fun v => if v < 0 then -v else v
  | "neg" => fun v => -v
  | "sign" => fun v => if v > 0 then 1 else if v < 0 then -1 else 0
  | "relu" => fun v => if v > 0 then v else 0
  | _ => id

def binaryF (name : String) : Float → Float → Float :=
  match name with
  | "add" => (· + ·)
  | "sub" => (· - ·)
  | "mul" => (· * ·)
  | "div" => (· / ·)
  | "max" => fun a b => if a.isNaN || b.isNaN then a + b else if a > b then a else b
  | "min" => fun a b => if a.isNaN || b.isNaN then a + b else if a < b then a else b
  | "pow" => powF
  | "prelu" => fun x s => if x ≥ 0.0 then x else s * x
  | _ => fun a _ => a

def powI (a : Int) (b : Int) : Int :=
  if b ≥ 0 then a ^ (if b > 64 then (if a == 0 || a == 1 then 1 else if a == -1 then (b % 2).toNat + 64 else 64) else b.toNat)
  else if a == 1 then 1 else if a == -1 then (if b % 2 == 0 then 1 else -1) else 0

def binaryI (name : String) : Int → Int → Int :=
  match name with
  | "add" => (· + ·)
  | "sub" => (· - ·)
  | "mul" => (· * ·)
  | "div" => fun a b => if b == 0 then 0 else a.tdiv b
  | "max" => fun a b => if a > b then a else b
  | "min" => fun a b => if a < b then a else b
  | "pow" => powI
  | "prelu" => fun x s => if x ≥ 0 then x else s * x
  | _ => fun a _ => a

def compareF (name : String) : Float → Float → Bool :=
  match name with
  | "equal" => (· == ·)
  | "notEqual" => (· != ·)
  | "greater" => (· > ·)
  | "greaterOrEqual" => (· ≥ ·)
  | "lesser" => (· < ·)
  | _ => (· ≤ ·)

def compareI (name : String) : Int → Int → Bool :=
  match name with
  | "equal" => (· == ·)
  | "notEqual" => (· != ·)
  | "greater" => (· > ·)
  | "greaterOrEqual" => (· ≥ ·)
  | "lesser" => (· < ·)
  | _ => (· ≤ ·)

def logicalI (name : String) : Int → Int → Int :=
  match name with
  | "logicalAnd" => fun a b => if a != 0 && b != 0 then 1 else 0
  | "logicalOr" => fun a b => if a != 0 || b != 0 then 1 else 0
  | _ => fun a b => if (a != 0) != (b != 0) then 1 else 0

def activation (name : String) : Float → Float :=
  match name with
  | "relu" => fun x => if x > 0.0 then x else 0.0
  | "sigmoid" => sigmoid
  | _ => tanhF

/-! ## Buffers -/

@[specialize] def mapFA (a : FloatArray) (f : Float → Float) : FloatArray :=
  a.foldl (fun acc x => acc.push (f x)) (FloatArray.emptyWithCapacity a.size)

@[specialize] def zipFA (a b : FloatArray) (f : Float → Float → Float) : FloatArray :=
  Nat.fold a.size (fun k _ acc => acc.push (f (a.get! k) (b.get! k))) (FloatArray.emptyWithCapacity a.size)

def floats (n : Nat) (x : Float) : FloatArray :=
  Nat.fold n (fun _ _ acc => acc.push x) (FloatArray.emptyWithCapacity n)

namespace Tensor

/-- Apply a function to every element (rounded or wrapped to the tensor's type). -/
@[specialize] def map (t : Tensor) (ff : Float → Float) (fi : Int → Int) : Tensor :=
  match t.buf with
  | .f a => let ty := t.dtype; { t with buf := .f (mapFA a fun x => ty.normF (ff x)) }
  | .i a => let r := t.dtype.range; { t with buf := .i (a.map fun v => r.wrap (fi v)) }

/-- A broadcasting binary operator: both operands read through index maps to `out`. -/
@[specialize] def zip (a b : Tensor) (out : Shape) (ff : Float → Float → Float) (fi : Int → Int → Int) : Tensor :=
  let a := a.expand out
  let b := b.expand out
  match a.buf, b.buf with
  | .f x, .f y => let ty := a.dtype; ⟨ty, out, .f (zipFA x y fun p q => ty.normF (ff p q))⟩
  | x, y =>
    let r := a.dtype.range
    let xs := x.toInts; let ys := y.toInts
    ⟨a.dtype, out, .i (Array.ofFn (n := xs.size) fun k => r.wrap (fi xs[k] (ys[k.val]!)))⟩

/-- A broadcasting comparison: a uint8 tensor of 0 and 1. -/
@[specialize] def compare (a b : Tensor) (out : Shape) (ff : Float → Float → Bool) (fi : Int → Int → Bool) : Tensor :=
  let a := a.expand out
  let b := b.expand out
  let n := Shape.size out
  match a.buf, b.buf with
  | .f x, .f y => ⟨.uint8, out, .i (Array.ofFn (n := n) fun k => if ff (x.get! k.val) (y.get! k.val) then 1 else 0)⟩
  | x, y =>
    let xs := x.toInts; let ys := y.toInts
    ⟨.uint8, out, .i (Array.ofFn (n := n) fun k => if fi (xs[k.val]!) (ys[k.val]!) then 1 else 0)⟩

/-- cast: float to integer truncates toward zero and saturates (NaN is 0); integer to
integer keeps the low bits; to a float type rounds to nearest. -/
def cast (t : Tensor) (to : DType) : Tensor :=
  if to.isFloat then ⟨to, t.shape, .f (mapFA t.buf.toFloats to.normF)⟩
  else
    let r := to.range
    match t.buf with
    | .i a => ⟨to, t.shape, .i (a.map r.wrap)⟩
    | .f a =>
      let lo := Float.ofInt r.lo; let hi := Float.ofInt r.hi
      ⟨to, t.shape, .i (Array.ofFn (n := a.size) fun k =>
        let x := a.get! k.val
        if x.isNaN then 0 else if x ≤ lo then r.lo else if x ≥ hi then r.hi
        else if x ≥ 9.2e18 then Int.ofNat x.toUInt64.toNat else x.toInt64.toInt)⟩

def clamp (t : Tensor) (lo hi : Option Arg) : Tensor :=
  match t.buf with
  | .f a =>
    let l := match lo with | some (.number b i x) => numberToFloat t.dtype b i x | _ => -(1.0 / 0.0)
    let h := match hi with | some (.number b i x) => numberToFloat t.dtype b i x | _ => 1.0 / 0.0
    { t with buf := .f (mapFA a fun x => if x < l then l else if x > h then h else x) }
  | .i a =>
    let l := match lo with | some (.number b i x) => numberToInt t.dtype b i x | _ => t.dtype.minInt
    let h := match hi with | some (.number b i x) => numberToInt t.dtype b i x | _ => t.dtype.maxInt
    { t with buf := .i (a.map fun v => if v < l then l else if v > h then h else v) }

/-! ## Reductions -/

/-- For each element of a tensor of shape `s`, the flat number of the group it reduces into
(the shape with `axes` removed). -/
def groupMap (s : Shape) (axes : List Nat) : Array Nat :=
  let rank := s.length
  let keep := (List.range rank).filter fun a => !axes.contains a
  let gs := keep.map fun a => s.getD a 1
  Array.ofFn (n := Shape.size s) fun k =>
    let o := unravel s k.val
    ravel gs (keep.map fun a => o.getD a 0)

@[specialize] def foldGroupsF (a : FloatArray) (groups : Array Nat) (n : Nat) (init : Float)
    (step : Float → Float → Float) : FloatArray :=
  Nat.fold a.size (fun k _ (acc : FloatArray) =>
    let g := groups[k]!
    acc.set! g (step (acc.get! g) (a.get! k))) (floats n init)

@[specialize] def foldGroupsI (a : Array Int) (groups : Array Nat) (n : Nat) (init : Int)
    (step : Int → Int → Int) : Array Int :=
  Nat.fold a.size (fun k _ (acc : Array Int) =>
    let g := groups[k]!
    acc.set! g (step (acc[g]!) (a[k]!))) (Array.replicate n init)

theorem foldGroupsI_aux (a : Array Int) (init : Int) (step : Int → Int → Int) :
    ∀ k, k ≤ a.size →
    Nat.fold k (fun i _ (acc : Array Int) =>
      let g := (Array.replicate a.size 0)[i]!
      acc.set! g (step (acc[g]!) (a[i]!))) #[init] = #[(a.toList.take k).foldl step init] := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k < a.size := hk
    rw [Nat.fold_succ, ih (Nat.le_of_lt hk')]
    have hz : (Array.replicate a.size (0 : Nat))[k]! = 0 := by simp [hk']
    simp only [hz]
    rw [List.take_add_one]
    simp [hk']

/-- Kind: kernel equals specification (integer tensors). Says: the reduction kernel, run
over all axes (every element in the one group), computes exactly the left fold of the
elements in order: the kernel's loop, group table and in-place updates add nothing and lose
nothing. Does not say: the same for float tensors (`FloatArray` has no lemmas in core Lean;
the float kernel is the same code shape and is tested against the WPT vectors). -/
theorem foldGroupsI_all (a : Array Int) (init : Int) (step : Int → Int → Int) :
    foldGroupsI a (Array.replicate a.size 0) 1 init step = #[a.foldl step init] := by
  unfold foldGroupsI
  have h := foldGroupsI_aux a init step a.size (Nat.le_refl _)
  rw [show Array.replicate 1 init = #[init] from rfl, h, List.take_of_length_le (by simp), Array.foldl_toList]

theorem foldl_add_replicate (n : Nat) (c x : Int) : (List.replicate n c).foldl (· + ·) x = x + n * c := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.foldl_cons, ih, Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

/-- Kind: value (reductions over all axes of a constant tensor). Says: reduceSum over all
axes of an integer tensor of `n` elements that all equal `c` is `n · c` (before the final
wrap to the data type), computed by the kernel itself. -/
theorem reduceSum_const (n : Nat) (c : Int) :
    foldGroupsI (Array.replicate n c) (Array.replicate n 0) 1 0 (· + ·) = #[n * c] := by
  have h := foldGroupsI_all (Array.replicate n c) 0 (· + ·)
  conv at h => lhs; rw [Array.size_replicate]
  rw [h, ← Array.foldl_toList, Array.toList_replicate, foldl_add_replicate]
  simp

theorem foldl_max_replicate (n : Nat) (c x : Int) (h : x ≤ c) :
    (List.replicate (n + 1) c).foldl (fun acc v => if v > acc then v else acc) x = c := by
  induction n generalizing x with
  | zero => simp only [List.replicate_succ, List.replicate_zero, List.foldl_cons, List.foldl_nil]; split <;> omega
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons]
    apply ih
    split <;> omega

/-- Kind: value. Says: reduceMax over all axes of a non-empty integer tensor whose elements
all equal `c` is `c`, whatever the starting value below `c` (the kernel starts from the
least value of the data type). -/
theorem reduceMax_const (n : Nat) (c lo : Int) (h : lo ≤ c) :
    foldGroupsI (Array.replicate (n + 1) c) (Array.replicate (n + 1) 0) 1 lo (fun acc v => if v > acc then v else acc) = #[c] := by
  have hh := foldGroupsI_all (Array.replicate (n + 1) c) lo (fun acc v => if v > acc then v else acc)
  conv at hh => lhs; rw [Array.size_replicate]
  rw [hh, ← Array.foldl_toList, Array.toList_replicate, foldl_max_replicate n c lo h]

/-- The reduction operators over `axes`; `out` is the output shape. -/
def reduce (t : Tensor) (name : String) (axes : List Nat) (out : Shape) : Tensor :=
  let groups := groupMap t.shape axes
  let n := Shape.size out
  let count := Float.ofNat (t.shape.size / (if n == 0 then 1 else n))
  let inf : Float := 1.0 / 0.0
  match t.buf with
  | .f a =>
    let ty := t.dtype
    let r : FloatArray := match name with
      | "reduceL1" => foldGroupsF a groups n 0.0 fun acc x => acc + x.abs
      | "reduceL2" => mapFA (foldGroupsF a groups n 0.0 fun acc x => acc + x * x) Float.sqrt
      | "reduceLogSum" => mapFA (foldGroupsF a groups n 0.0 (· + ·)) logF
      -- `max + log(Σ e^(x − max))`: no overflow (as the GPU kernel, one definition)
      | "reduceLogSumExp" =>
        let mx := foldGroupsF a groups n (-inf) fun acc x => if x > acc || x.isNaN then x else acc
        let e := Nat.fold a.size (fun k _ (acc : FloatArray) => acc.push (expF (a.get! k - mx.get! (groups[k]!))))
          (FloatArray.emptyWithCapacity a.size)
        let sums := foldGroupsF e groups n 0.0 (· + ·)
        Nat.fold n (fun k _ (acc : FloatArray) => acc.push (logF (sums.get! k) + mx.get! k)) (FloatArray.emptyWithCapacity n)
      | "reduceMax" => foldGroupsF a groups n (-inf) fun acc x => if x > acc || x.isNaN then x else acc
      | "reduceMean" => mapFA (foldGroupsF a groups n 0.0 (· + ·)) (· / count)
      | "reduceMin" => foldGroupsF a groups n inf fun acc x => if x < acc || x.isNaN then x else acc
      | "reduceProduct" => foldGroupsF a groups n 1.0 (· * ·)
      | "reduceSumSquare" => foldGroupsF a groups n 0.0 fun acc x => acc + x * x
      | _ => foldGroupsF a groups n 0.0 (· + ·)
    ⟨ty, out, .f (mapFA r ty.normF)⟩
  | .i a =>
    let rg := t.dtype.range
    let r : Array Int := match name with
      | "reduceL1" => foldGroupsI a groups n 0 fun acc x => acc + (if x < 0 then -x else x)
      | "reduceMax" => foldGroupsI a groups n rg.lo fun acc x => if x > acc then x else acc
      | "reduceMin" => foldGroupsI a groups n rg.hi fun acc x => if x < acc then x else acc
      | "reduceProduct" => foldGroupsI a groups n 1 fun acc x => rg.wrap (acc * x)
      | "reduceSumSquare" => foldGroupsI a groups n 0 fun acc x => acc + x * x
      | _ => foldGroupsI a groups n 0 (· + ·)
    ⟨t.dtype, out, .i (r.map rg.wrap)⟩

/-- argMin / argMax along one axis: the first index of the least (greatest) element. -/
def argMinMax (t : Tensor) (isMax : Bool) (axis : Nat) (out : Desc) : Tensor :=
  let groups := groupMap t.shape [axis]
  let n := Shape.size out.shape
  let stride := Shape.size (t.shape.drop (axis + 1))
  let dim := t.shape.getD axis 1
  let better (x best : Float) : Bool := if isMax then x > best else x < best
  let xs := t.buf.toFloats
  let init : Float := if isMax then -(1.0 / 0.0) else 1.0 / 0.0
  let (_, idx) := Nat.fold xs.size (fun k _ (acc : FloatArray × Array Int) =>
    let g := groups[k]!
    let pos := (k / stride) % dim
    let x := xs.get! k
    if pos == 0 || better x (acc.1.get! g) then (acc.1.set! g x, acc.2.set! g (Int.ofNat pos)) else acc)
    (floats n init, Array.replicate n 0)
  ⟨out.dtype, out.shape, .i idx⟩

/-- softmax along `axis`. -/
def softmax (t : Tensor) (axis : Nat) : Tensor :=
  let groups := groupMap t.shape [axis]
  let n := t.shape.size / t.shape.getD axis 1
  let a := t.buf.toFloats
  let mx := foldGroupsF a groups n (-(1.0 / 0.0)) fun acc x => if x > acc then x else acc
  let e := Nat.fold a.size (fun k _ (acc : FloatArray) => acc.push (expF (a.get! k - mx.get! (groups[k]!))))
    (FloatArray.emptyWithCapacity a.size)
  let sums := foldGroupsF e groups n 0.0 (· + ·)
  let ty := t.dtype
  { t with buf := .f (Nat.fold a.size (fun k _ (acc : FloatArray) =>
      acc.push (ty.normF (e.get! k / sums.get! (groups[k]!)))) (FloatArray.emptyWithCapacity a.size)) }

/-- cumulativeSum along `axis` (each partial sum rounded or wrapped to the type). -/
def cumulativeSum (t : Tensor) (axis : Nat) (exclusive reversed : Bool) : Tensor :=
  let t := if reversed then t.reverse [axis] else t
  let stride := Shape.size (t.shape.drop (axis + 1))
  let dim := t.shape.getD axis 1
  let r : Tensor := match t.buf with
    | .f a =>
      let ty := t.dtype
      { t with buf := .f (Nat.fold a.size (fun k _ (acc : FloatArray) =>
          let first := (k / stride) % dim == 0
          acc.push (if exclusive then (if first then 0.0 else ty.normF (acc.get! (k - stride) + a.get! (k - stride)))
            else if first then a.get! k else ty.normF (acc.get! (k - stride) + a.get! k)))
          (FloatArray.emptyWithCapacity a.size)) }
    | .i a =>
      let rg := t.dtype.range
      { t with buf := .i (Nat.fold a.size (fun k _ (acc : Array Int) =>
          let first := (k / stride) % dim == 0
          acc.push (if exclusive then (if first then 0 else rg.wrap (acc[k - stride]! + a[k - stride]!))
            else if first then a[k]! else rg.wrap (acc[k - stride]! + a[k]!)))
          (Array.emptyWithCapacity a.size)) }
  if reversed then r.reverse [axis] else r

/-! ## Matrix products -/

/-- matmul: the last two axes are matrices, the leading axes broadcast. -/
def matmul (a b : Tensor) (out : Shape) : Tensor :=
  let ra := a.shape.length; let rb := b.shape.length
  let m := a.shape.getD (ra - 2) 1; let kk := a.shape.getD (ra - 1) 1; let n := b.shape.getD (rb - 1) 1
  let batch := out.take (out.length - 2)
  let am := broadcastMap (a.shape.take (ra - 2)) batch
  let bm := broadcastMap (b.shape.take (rb - 2)) batch
  let x := a.buf.toFloats; let y := b.buf.toFloats
  let ty := a.dtype
  let r := Id.run do
    let mut acc := FloatArray.emptyWithCapacity (Shape.size out)
    for bi in [0:Shape.size batch] do
      let ao := am[bi]! * m * kk
      let bo := bm[bi]! * kk * n
      for i in [0:m] do
        for j in [0:n] do
          let mut s := 0.0
          for k in [0:kk] do
            s := s + x.get! (ao + i * kk + k) * y.get! (bo + k * n + j)
          acc := acc.push (ty.normF s)
    pure acc
  ⟨ty, out, .f r⟩

/-- gemm: `alpha · A · B + beta · C` on matrices, with optional transposes. -/
def gemm (a b : Tensor) (c : Option Tensor) (alpha beta : Float) (aT bT : Bool) (out : Shape) : Tensor :=
  let a := if aT then a.transpose [1, 0] else a
  let b := if bT then b.transpose [1, 0] else b
  let m := out.getD 0 1; let n := out.getD 1 1; let kk := a.shape.getD 1 1
  let x := a.buf.toFloats; let y := b.buf.toFloats
  let cc := c.map fun c => (c.expand out).buf.toFloats
  let ty := a.dtype
  let r := Id.run do
    let mut acc := FloatArray.emptyWithCapacity (m * n)
    for i in [0:m] do
      for j in [0:n] do
        let mut s := 0.0
        for k in [0:kk] do
          s := s + x.get! (i * kk + k) * y.get! (k * n + j)
        let v := alpha * s + (match cc with | some z => beta * z.get! (i * n + j) | none => 0.0)
        acc := acc.push (ty.normF v)
    pure acc
  ⟨ty, out, .f r⟩

/-! ## Convolution and pooling (computed in NCHW; other layouts are transposed in and out) -/

def toNchw (t : Tensor) (layout : String) : Tensor := if layout == "nhwc" then t.transpose [0, 3, 1, 2] else t
def fromNchw (t : Tensor) (layout : String) : Tensor := if layout == "nhwc" then t.transpose [0, 2, 3, 1] else t

/-- conv2d on an NCHW input and an OIHW filter. -/
def conv2dNchw (input filter : Tensor) (bias : Option Tensor) (w : Window) (groups : Nat) (out : Shape) : Tensor :=
  let g := fun (l : List Nat) i => l.getD i 0
  let c := g input.shape 1; let h := g input.shape 2; let wd := g input.shape 3
  let oc := g filter.shape 0; let icg := g filter.shape 1; let kh := g filter.shape 2; let kw := g filter.shape 3
  let n := g out 0; let oh := g out 2; let ow := g out 3
  let ocg := oc / groups
  let sh := g w.strides 0; let sw := g w.strides 1; let dh := g w.dilations 0; let dw := g w.dilations 1
  let pt := g w.padding 0; let pl := g w.padding 2
  let x := input.buf.toFloats; let f := filter.buf.toFloats
  let bs := bias.map (·.buf.toFloats)
  let ty := input.dtype
  let r := Id.run do
    let mut acc := FloatArray.emptyWithCapacity (Shape.size out)
    for ni in [0:n] do
      for o in [0:oc] do
        let grp := o / ocg
        let b0 := match bs with | some b => b.get! o | none => 0.0
        for y in [0:oh] do
          for xx in [0:ow] do
            let mut s := 0.0
            for ic in [0:icg] do
              let cin := grp * icg + ic
              for ky in [0:kh] do
                let iy := y * sh + ky * dh
                if iy ≥ pt && iy - pt < h then
                  for kx in [0:kw] do
                    let ix := xx * sw + kx * dw
                    if ix ≥ pl && ix - pl < wd then
                      s := s + x.get! (((ni * c + cin) * h + (iy - pt)) * wd + (ix - pl)) *
                        f.get! (((o * icg + ic) * kh + ky) * kw + kx)
            acc := acc.push (ty.normF (s + b0))
    pure acc
  ⟨ty, out, .f r⟩

/-- convTranspose2d on an NCHW input and an IOHW filter: each input element adds its
multiples of the filter to the output. -/
def convTranspose2dNchw (input filter : Tensor) (bias : Option Tensor) (w : Window) (groups : Nat) (out : Shape) : Tensor :=
  let g := fun (l : List Nat) i => l.getD i 0
  let n := g input.shape 0; let c := g input.shape 1; let h := g input.shape 2; let wd := g input.shape 3
  let ocg := g filter.shape 1; let kh := g filter.shape 2; let kw := g filter.shape 3
  let oc := g out 1; let oh := g out 2; let ow := g out 3
  let icg := c / groups
  let sh := g w.strides 0; let sw := g w.strides 1; let dh := g w.dilations 0; let dw := g w.dilations 1
  let pt := g w.padding 0; let pl := g w.padding 2
  let x := input.buf.toFloats; let f := filter.buf.toFloats
  let ty := input.dtype
  let sums := Id.run do
    let mut acc := floats (Shape.size out) 0.0
    for ni in [0:n] do
      for ic in [0:c] do
        let grp := ic / icg
        for iy in [0:h] do
          for ix in [0:wd] do
            let v := x.get! (((ni * c + ic) * h + iy) * wd + ix)
            for o in [0:ocg] do
              let co := grp * ocg + o
              for ky in [0:kh] do
                let oy := iy * sh + ky * dh
                if oy ≥ pt && oy - pt < oh then
                  for kx in [0:kw] do
                    let ox := ix * sw + kx * dw
                    if ox ≥ pl && ox - pl < ow then
                      let p := ((ni * oc + co) * oh + (oy - pt)) * ow + (ox - pl)
                      acc := acc.set! p (acc.get! p + v * f.get! (((ic * ocg + o) * kh + ky) * kw + kx))
    pure acc
  let plane := oh * ow
  let r := match bias with
    | some b =>
      let bs := b.buf.toFloats
      Nat.fold sums.size (fun k _ (acc : FloatArray) => acc.push (ty.normF (sums.get! k + bs.get! ((k / plane) % oc))))
        (FloatArray.emptyWithCapacity sums.size)
    | none => mapFA sums ty.normF
  ⟨ty, out, .f r⟩

/-- Pooling on an NCHW input. Padding cells are not part of a window: the average divides by
the number of input cells in the window. -/
def pool2dNchw (input : Tensor) (name : String) (win : List Nat) (w : Window) (out : Shape) : Tensor :=
  let g := fun (l : List Nat) i => l.getD i 0
  let c := g input.shape 1; let h := g input.shape 2; let wd := g input.shape 3
  let n := g out 0; let oh := g out 2; let ow := g out 3
  let kh := g win 0; let kw := g win 1
  let sh := g w.strides 0; let sw := g w.strides 1; let dh := g w.dilations 0; let dw := g w.dilations 1
  let pt := g w.padding 0; let pl := g w.padding 2
  let x := input.buf.toFloats
  let ty := input.dtype
  let isMax := name == "maxPool2d"; let isL2 := name == "l2Pool2d"
  let r := Id.run do
    let mut acc := FloatArray.emptyWithCapacity (Shape.size out)
    for ni in [0:n] do
      for ch in [0:c] do
        for y in [0:oh] do
          for xx in [0:ow] do
            let mut s := if isMax then -(1.0 / 0.0) else 0.0
            let mut cnt := 0
            for ky in [0:kh] do
              let iy := y * sh + ky * dh
              if iy ≥ pt && iy - pt < h then
                for kx in [0:kw] do
                  let ix := xx * sw + kx * dw
                  if ix ≥ pl && ix - pl < wd then
                    let v := x.get! (((ni * c + ch) * h + (iy - pt)) * wd + (ix - pl))
                    cnt := cnt + 1
                    s := if isMax then (if v > s then v else s) else if isL2 then s + v * v else s + v
            -- a window that lies wholly in the padding (ceil rounding) has no cell: 0
            let v := if cnt == 0 then 0.0 else if isMax then s else if isL2 then Float.sqrt s else s / Float.ofNat cnt
            acc := acc.push (ty.normF v)
    pure acc
  let t : Tensor := ⟨ty, out, .f r⟩
  if input.dtype.isFloat then t else t.cast input.dtype

/-! ## Normalisations -/

/-- batchNormalization along `axis`. -/
def batchNorm (t mean variance : Tensor) (scale bias : Option Tensor) (axis : Nat) (eps : Float) : Tensor :=
  let stride := Shape.size (t.shape.drop (axis + 1))
  let dim := t.shape.getD axis 1
  let a := t.buf.toFloats
  let m := mean.buf.toFloats; let v := variance.buf.toFloats
  let s := scale.map (·.buf.toFloats); let b := bias.map (·.buf.toFloats)
  let ty := t.dtype
  { t with buf := .f (Nat.fold a.size (fun k _ (acc : FloatArray) =>
      let c := (k / stride) % dim
      let y := (a.get! k - m.get! c) / Float.sqrt (v.get! c + eps)
      let y := match s with | some s => y * s.get! c | none => y
      let y := match b with | some b => y + b.get! c | none => y
      acc.push (ty.normF y)) (FloatArray.emptyWithCapacity a.size)) }

/-- Normalise over `axes` (mean and variance of each group of elements that share the other
indices), then scale and shift by tensors whose shape is `sShape`, indexed through `sIdx`. -/
def normOver (t : Tensor) (axes : List Nat) (eps : Float) (scale bias : Option Tensor) (sIdx : Array Nat) : Tensor :=
  let groups := groupMap t.shape axes
  let cnt := Shape.size (axes.map fun a => t.shape.getD a 1)
  let n := t.shape.size / (if cnt == 0 then 1 else cnt)
  let a := t.buf.toFloats
  let count := Float.ofNat cnt
  let means := mapFA (foldGroupsF a groups n 0.0 (· + ·)) (· / count)
  let sq := Nat.fold a.size (fun k _ (acc : FloatArray) =>
    let g := groups[k]!
    let d := a.get! k - means.get! g
    acc.set! g (acc.get! g + d * d)) (floats n 0.0)
  let vars := mapFA sq (· / count)
  let s := scale.map (·.buf.toFloats); let b := bias.map (·.buf.toFloats)
  let ty := t.dtype
  { t with buf := .f (Nat.fold a.size (fun k _ (acc : FloatArray) =>
      let g := groups[k]!
      let y := (a.get! k - means.get! g) / Float.sqrt (vars.get! g + eps)
      let y := match s with | some s => y * s.get! (sIdx[k]!) | none => y
      let y := match b with | some b => y + b.get! (sIdx[k]!) | none => y
      acc.push (ty.normF y)) (FloatArray.emptyWithCapacity a.size)) }

/-- instanceNormalization: over the two spatial axes of each (batch, channel). -/
def instanceNorm (t : Tensor) (scale bias : Option Tensor) (eps : Float) (layout : String) : Tensor :=
  let (spatial, chAxis) := if layout == "nhwc" then ([1, 2], 3) else ([2, 3], 1)
  let sIdx := Array.ofFn (n := t.shape.size) fun k => (unravel t.shape k.val).getD chAxis 0
  t.normOver spatial eps scale bias sIdx

/-- layerNormalization over `axes`; scale and bias have the dimensions of `axes`, in order. -/
def layerNorm (t : Tensor) (scale bias : Option Tensor) (axes : List Nat) (eps : Float) : Tensor :=
  let sShape := axes.map fun a => t.shape.getD a 1
  let sIdx := Array.ofFn (n := t.shape.size) fun k =>
    let o := unravel t.shape k.val
    ravel sShape (axes.map fun a => o.getD a 0)
  t.normOver axes eps scale bias sIdx

/-! ## Resampling -/

/-- The source coordinate of an output coordinate (specification: half-pixel centres, clamped). -/
def resampleCoord (o outSize inSize : Nat) : Float :=
  let scale := Float.ofNat outSize / Float.ofNat inSize
  let u := (Float.ofNat o + 0.5) / scale - 0.5
  let hi := Float.ofNat (inSize - 1)
  if u < 0.0 then 0.0 else if u > hi then hi else u

def resample2d (t : Tensor) (linear : Bool) (axes : List Nat) (out : Shape) : Tensor :=
  let a0 := axes.getD 0 2; let a1 := axes.getD 1 3
  let in0 := t.shape.getD a0 1; let in1 := t.shape.getD a1 1
  let out0 := out.getD a0 1; let out1 := out.getD a1 1
  let n := Shape.size out
  if !linear then
    let pickI (c : Float) (inSize : Nat) : Nat :=
      let v := (c - 0.5).ceil
      let i := if v < 0.0 then 0 else v.toUInt64.toNat
      if i ≥ inSize then inSize - 1 else i
    let idx := Array.ofFn (n := n) fun k =>
      let o := unravel out k.val
      let y := pickI (resampleCoord (o.getD a0 0) out0 in0) in0
      let x := pickI (resampleCoord (o.getD a1 0) out1 in1) in1
      ravel t.shape ((o.set a0 y).set a1 x)
    ⟨t.dtype, out, t.buf.select idx⟩
  else
    let a := t.buf.toFloats
    let ty := t.dtype
    let r := Nat.fold n (fun k _ (acc : FloatArray) =>
      let o := unravel out k
      let cy := resampleCoord (o.getD a0 0) out0 in0
      let cx := resampleCoord (o.getD a1 0) out1 in1
      let y0 := cy.floor.toUInt64.toNat; let y1 := cy.ceil.toUInt64.toNat
      let x0 := cx.floor.toUInt64.toNat; let x1 := cx.ceil.toUInt64.toNat
      let tap := fun (y x : Nat) => a.get! (ravel t.shape ((o.set a0 y).set a1 x))
      let tx := cx - cx.floor; let tyy := cy - cy.floor
      let vy0 := tap y0 x0 * (1.0 - tx) + tap y0 x1 * tx
      let vy1 := tap y1 x0 * (1.0 - tx) + tap y1 x1 * tx
      acc.push (ty.normF (vy0 * (1.0 - tyy) + vy1 * tyy))) (FloatArray.emptyWithCapacity n)
    let r : Tensor := ⟨ty, out, .f r⟩
    if t.dtype.isFloat then r else
      -- integer types: rounded to nearest
      let rg := t.dtype.range
      ⟨t.dtype, out, .i (Array.ofFn (n := n) fun k => rg.sat (roundEvenF (r.buf.getF k.val)).toInt64.toInt)⟩

/-! ## Quantisation -/

/-- The index map of a blockwise broadcast: each element of `s` covers a block of `to`. -/
def blockMap (s to : Shape) : Array Nat :=
  remap s to fun o => (List.range o.length).map fun a => o.getD a 0 / (to.getD a 1 / (let d := s.getD a 1; if d == 0 then 1 else d))

/-- quantizeLinear: `sat(roundEven(input / scale) + zeroPoint)`. -/
def quantize (t scale zp : Tensor) : Tensor :=
  let sm := blockMap scale.shape t.shape
  let a := t.buf.toFloats; let s := scale.buf.toFloats; let z := zp.buf.toInts
  let rg := zp.dtype.range
  let lo := Float.ofInt rg.lo; let hi := Float.ofInt rg.hi
  ⟨zp.dtype, t.shape, .i (Array.ofFn (n := a.size) fun k =>
    let j := sm[k.val]!
    let q := roundEvenF (a.get! k.val / s.get! j) + Float.ofInt (z[j]!)
    if q.isNaN then 0 else if q ≤ lo then rg.lo else if q ≥ hi then rg.hi else q.toInt64.toInt)⟩

/-- dequantizeLinear: `(input - zeroPoint) · scale`. -/
def dequantize (t scale zp : Tensor) : Tensor :=
  let sm := blockMap scale.shape t.shape
  let a := t.buf.toInts; let s := scale.buf.toFloats; let z := zp.buf.toInts
  let ty := scale.dtype
  ⟨ty, t.shape, .f (Nat.fold a.size (fun k _ (acc : FloatArray) =>
    let j := sm[k]!
    acc.push (ty.normF (Float.ofInt (a[k]! - z[j]!) * s.get! j))) (FloatArray.emptyWithCapacity a.size))⟩

end Tensor

/-! ## Recurrent cells

Flat matrices: `w` is `[rows, cols]`; `x` is one batch row of `cols` values. -/

/-- `(W x)[r]` for the rows `r0 … r0+h-1` of `w`, added to `acc`. -/
def addMatVec (acc : FloatArray) (w : FloatArray) (cols r0 h : Nat) (x : FloatArray) (xo : Nat) : FloatArray :=
  Id.run do
    let mut acc := acc
    for r in [0:h] do
      let mut s := 0.0
      for c in [0:cols] do
        s := s + w.get! ((r0 + r) * cols + c) * x.get! (xo + c)
      acc := acc.set! r (acc.get! r + s)
    pure acc

def addVec (acc : FloatArray) (b : Option FloatArray) (o h : Nat) : FloatArray :=
  match b with
  | some b => Nat.fold h (fun r _ (acc : FloatArray) => acc.set! r (acc.get! r + b.get! (o + r))) acc
  | none => acc

/-- The weights of one direction of a recurrent network, as flat arrays. -/
structure RnnWeights where
  w : FloatArray
  r : FloatArray
  b : Option FloatArray
  rb : Option FloatArray
  p : Option FloatArray
  inSize : Nat
  hidden : Nat

/-- One GRU step for one batch row: the new hidden state. `order` is the positions of the
update, reset and new gates in the weights. -/
def gruStep (ws : RnnWeights) (order : Nat × Nat × Nat) (resetAfter : Bool) (f g : Float → Float)
    (x : FloatArray) (xo : Nat) (hs : FloatArray) : FloatArray :=
  let h := ws.hidden
  let (zi, ri, ni) := order
  let gate (gi : Nat) : FloatArray :=
    let acc := floats h 0.0
    let acc := addVec (addVec acc ws.b (gi * h) h) ws.rb (gi * h) h
    let acc := addMatVec acc ws.w ws.inSize (gi * h) h x xo
    addMatVec acc ws.r h (gi * h) h hs 0
  let z := mapFA (gate zi) f
  let r := mapFA (gate ri) f
  let n :=
    if resetAfter then
      let inner := addMatVec (addVec (floats h 0.0) ws.rb (ni * h) h) ws.r h (ni * h) h hs 0
      let acc := addVec (floats h 0.0) ws.b (ni * h) h
      let acc := addMatVec acc ws.w ws.inSize (ni * h) h x xo
      mapFA (Nat.fold h (fun k _ (acc : FloatArray) => acc.set! k (acc.get! k + r.get! k * inner.get! k)) acc) g
    else
      let rh := zipFA r hs (· * ·)
      let acc := addVec (addVec (floats h 0.0) ws.b (ni * h) h) ws.rb (ni * h) h
      let acc := addMatVec acc ws.w ws.inSize (ni * h) h x xo
      mapFA (addMatVec acc ws.r h (ni * h) h rh 0) g
  Nat.fold h (fun k _ (acc : FloatArray) => acc.push (z.get! k * hs.get! k + n.get! k * (1.0 - z.get! k)))
    (FloatArray.emptyWithCapacity h)

/-- One LSTM step for one batch row: the new hidden and cell states. `order` is the positions
of the input, output, forget and cell gates; the peephole weights are input, output, forget. -/
def lstmStep (ws : RnnWeights) (order : Nat × Nat × Nat × Nat) (f g hAct : Float → Float)
    (x : FloatArray) (xo : Nat) (hs cs : FloatArray) : FloatArray × FloatArray :=
  let h := ws.hidden
  let (ii, oi, fi, gi) := order
  let gate (k : Nat) (peep : Option Nat) : FloatArray :=
    let acc := floats h 0.0
    let acc := match peep, ws.p with
      | some pi, some p => Nat.fold h (fun r _ (acc : FloatArray) => acc.set! r (cs.get! r * p.get! (pi * h + r))) acc
      | _, _ => acc
    let acc := addVec (addVec acc ws.b (k * h) h) ws.rb (k * h) h
    let acc := addMatVec acc ws.w ws.inSize (k * h) h x xo
    addMatVec acc ws.r h (k * h) h hs 0
  let i := mapFA (gate ii (some 0)) f
  let fg := mapFA (gate fi (some 2)) f
  let gg := mapFA (gate gi none) g
  let o := mapFA (gate oi (some 1)) f
  let ct := Nat.fold h (fun k _ (acc : FloatArray) => acc.push (fg.get! k * cs.get! k + i.get! k * gg.get! k))
    (FloatArray.emptyWithCapacity h)
  let ht := Nat.fold h (fun k _ (acc : FloatArray) => acc.push (o.get! k * hAct (ct.get! k)))
    (FloatArray.emptyWithCapacity h)
  (ht, ct)

def sliceFA (a : FloatArray) (o n : Nat) : FloatArray :=
  Nat.fold n (fun k _ (acc : FloatArray) => acc.push (a.get! (o + k))) (FloatArray.emptyWithCapacity n)

def appendFA (a b : FloatArray) : FloatArray := b.foldl (fun acc x => acc.push x) a

end L4Factoidal.WebNN
