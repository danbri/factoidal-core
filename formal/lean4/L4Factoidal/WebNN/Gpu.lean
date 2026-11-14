/-
L4Factoidal.WebNN.Gpu: WGSL compute kernels for WebNN operators, generated in Lean from the
same operator names and index maps as the CPU reference
(record: docs/designissues/2026-11-14-gpu-compute-and-webnn.md, part 2).

A kernel is a `PageGpu.Wgsl.Module` value, not text: one invocation per output element
(`global_invocation_id.x` is the flat output number), the output multi-index by division
and remainder with the output shape's literal strides, each input's flat index from its
`Idx` map (`WebNN.Idx`, proved equal to `Move`'s maps) and the input's literal strides, and
the operator's scalar expression from `binaryExpr` / `unaryExpr`, keyed by the names the CPU
reference uses (`Compute.binaryF`, `Compute.unaryF`). The module then goes through
`Wgsl.finish` like any page shader, so the page GPU theorems (subset, clamped indices, cost,
dispatch bounds) hold for every kernel with no new proof.

Proved here: `emitC_eval`: the printed `u32` arithmetic of a coordinate computes
`Coord.eval` whenever its values fit in 32 bits. Not proved: that the device's `f32`
arithmetic equals the CPU reference's binary64-then-round (it does not, in general); that is
a differential test per operator against the WebNN tolerances.

This first group: element-wise binary operators with broadcasting and element-wise unary
operators, for `float32`.
-/
import L4Factoidal.WebNN.Idx
import L4Factoidal.PageGpu.Wgsl

namespace L4Factoidal.WebNN.Gpu
open L4Factoidal.PageGpu

/-- A `u32` literal. -/
def u (n : Nat) : Wgsl.Expr := .lit (.int n "u")

/-- The WGSL name of output coordinate `a`. -/
def coordName (a : Nat) : String := s!"o{a}"

/-- A coordinate as WGSL `u32` arithmetic over the names `nm a` of the output coordinates. -/
def emitC (nm : Nat → String) : Coord → Wgsl.Expr
  | .out a => .name (nm a)
  | .lit n => u n
  | .add x y => .binary "+" (emitC nm x) (emitC nm y)
  | .mulLit x k => .binary "*" (emitC nm x) (u k)
  | .modLit x k => .binary "%" (emitC nm x) (u k)
  | .subFrom k x => .binary "-" (u k) (emitC nm x)

/-! ## `u32` arithmetic, as WGSL computes it -/

def two32 : Nat := 4294967296

/-- The value of an integer expression of the subset's `u32` arithmetic (`+ - * / %` wrap
or truncate as WGSL's `u32` does; `/` and `%` by 0 give the left operand, as WGSL defines
them for integers), with the values of names from `env`; `none` for anything else. -/
def evalU (env : String → Option Nat) : Wgsl.Expr → Option Nat
  | .lit (.int n "u") => if n < two32 then some n else none
  | .name s => env s
  | .binary op a b =>
    match evalU env a, evalU env b with
    | some x, some y =>
      if op == "+" then some ((x + y) % two32)
      else if op == "-" then some ((x + two32 - y) % two32)
      else if op == "*" then some ((x * y) % two32)
      else if op == "/" then some (if y == 0 then x else x / y)
      else if op == "%" then some (if y == 0 then x else x % y)
      else none
    | _, _ => none
  | _ => none

/-- Every value a coordinate's arithmetic takes at `o` is below 2^32, and no subtraction goes
below 0. -/
def _root_.L4Factoidal.WebNN.Coord.Fits (o : List Nat) : Coord → Prop
  | .out a => o.getD a 0 < two32
  | .lit n => n < two32
  | .add x y => x.Fits o ∧ y.Fits o ∧ x.eval o + y.eval o < two32
  | .mulLit x k => x.Fits o ∧ k < two32 ∧ x.eval o * k < two32
  | .modLit x k => x.Fits o ∧ k < two32
  | .subFrom k x => x.Fits o ∧ k < two32 ∧ x.eval o ≤ k

theorem _root_.L4Factoidal.WebNN.Coord.eval_lt {o : List Nat} : ∀ {c : Coord}, c.Fits o → c.eval o < two32
  | .out _, h => h
  | .lit _, h => h
  | .add _ _, h => h.2.2
  | .mulLit _ _, h => h.2.2
  | .modLit x k, h => by
    simp only [Coord.eval]
    have := Coord.eval_lt h.1
    by_cases hk : k = 0
    · subst hk; simpa using this
    · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this
  | .subFrom _ _, h => by simp only [Coord.eval]; have := h.2.1; omega

/-- Kind: equality (generated code against its reference). Says: when the names of the
output coordinates hold `o` (`henv`) and the coordinate's values fit in 32 bits (`Fits`),
the WGSL `u32` arithmetic `emitC` prints computes exactly `Coord.eval o`: the GPU kernel
reads the source element the CPU reference reads. Does not say: anything about `f32`
values, or that the host's compiler implements `u32` as WGSL defines it. -/
theorem emitC_eval (nm : Nat → String) (env : String → Option Nat) (o : List Nat)
    (henv : ∀ a, env (nm a) = some (o.getD a 0)) :
    ∀ (c : Coord), c.Fits o → evalU env (emitC nm c) = some (c.eval o)
  | .out a, _ => by simp [emitC, evalU, henv, Coord.eval]
  | .lit n, h => by simp [emitC, u, evalU, Coord.eval, Coord.Fits] at *; exact h
  | .add x y, h => by
    obtain ⟨hx, hy, hs⟩ := h
    simp only [emitC, evalU, emitC_eval nm env o henv x hx, emitC_eval nm env o henv y hy, Coord.eval]
    simp [Nat.mod_eq_of_lt hs]
  | .mulLit x k, h => by
    obtain ⟨hx, hk, hs⟩ := h
    simp only [emitC, evalU, emitC_eval nm env o henv x hx, u, Coord.eval]
    simp [hk, Nat.mod_eq_of_lt hs]
  | .modLit x k, h => by
    obtain ⟨hx, hk⟩ := h
    simp only [emitC, evalU, emitC_eval nm env o henv x hx, u, Coord.eval]
    by_cases h0 : k = 0
    · subst h0; simp [two32]
    · simp [hk, h0]
  | .subFrom k x, h => by
    obtain ⟨hx, hk, hle⟩ := h
    simp only [emitC, evalU, emitC_eval nm env o henv x hx, u, Coord.eval]
    have : k + two32 - x.eval o = (k - x.eval o) + two32 := by omega
    simp [hk, this, Nat.add_mod_right, Nat.mod_eq_of_lt (show k - x.eval o < two32 by omega)]

/-! ## Scalar expressions: one row per operator name of the CPU reference -/

def f (t : String) : Wgsl.Expr := .lit (.float t)
def call1 (fn : String) (x : Wgsl.Expr) : Wgsl.Expr := .call (.fn fn) (.cons x .nil)
def call2 (fn : String) (x y : Wgsl.Expr) : Wgsl.Expr := .call (.fn fn) (.cons x (.cons y .nil))

/-- The element-wise binary operators (`Compute.binaryF`'s names) with a WGSL form. -/
def binaryExpr (name : String) (a b : Wgsl.Expr) : Option Wgsl.Expr :=
  match name with
  | "add" => some (.binary "+" a b)
  | "sub" => some (.binary "-" a b)
  | "mul" => some (.binary "*" a b)
  | "div" => some (.binary "/" a b)
  | "max" => some (call2 "max" a b)
  | "min" => some (call2 "min" a b)
  | "pow" => some (call2 "pow" a b)
  | _ => none

/-- The element-wise unary operators (`Compute.unaryF`'s names) with a WGSL form. `log`,
`sqrt` and `tanh` are left out: on a real GPU (Apple M-series, Metal through Deno's WebGPU,
2026-11-14) their WGSL builtins differed from the CPU reference by 75, 2 and 44 ULP where the
WebNN conformance tests allow 8, 1 and 16 (WGSL's own precision for them is looser than the
tests'); they run on the CPU reference until a WGSL form within the tolerance is measured. -/
def unaryExpr (name : String) (x : Wgsl.Expr) : Option Wgsl.Expr :=
  match name with
  | "abs" | "ceil" | "cos" | "exp" | "floor" | "sin" | "tan" => some (call1 name x)
  | "neg" => some (.unary "-" x)
  | "reciprocal" => some (.binary "/" (f "1.0") x)
  | "relu" => some (call2 "max" x (f "0.0"))
  | "sigmoid" => some (.binary "/" (f "1.0") (.binary "+" (f "1.0") (call1 "exp" (.unary "-" x))))
  | "softsign" => some (.binary "/" x (.binary "+" (f "1.0") (call1 "abs" x)))
  | _ => none

/-! ## Kernels -/

/-- Workgroup size of every kernel; outputs up to `maxElements` (one dimension of dispatch). -/
def wg : Nat := 64
def maxElements : Nat := 65535 * 64

/-- Row-major strides of a shape: `strides [2,3,4] = [12,4,1]`. -/
def strides (s : Shape) : List Nat := (List.range s.length).map fun a => Shape.size (s.drop (a + 1))

/-- The flat index of a source with shape `inShape` read through map `m`, as WGSL. -/
def flatIndex (m : Idx) (inShape : Shape) : Wgsl.Expr :=
  let terms := (m.zip (strides inShape)).map fun (c, st) => Wgsl.Expr.binary "*" (emitC coordName c) (u st)
  terms.foldl (fun acc t => .binary "+" acc t) (u 0)

/-- `let oA = (k / strideA) % dimA;` for each output axis. -/
def coordLets (outShape : Shape) : List Wgsl.Stmt :=
  ((outShape.zip (strides outShape)).zip (List.range outShape.length)).map fun ((d, st), a) =>
    .letS (coordName a) none (.binary "%" (.binary "/" (.name "k") (u st)) (u d))

def stmts : List Wgsl.Stmt → Wgsl.Stmts
  | [] => .nil
  | s :: ss => .cons s (stmts ss)

def rt : Wgsl.Ty := .array (.scalar .f32) 0

/-- A module with read-only inputs `ins` at bindings 0.., the output `y` after them, and one
compute entry point `main` whose body for output element `k` is `body`. -/
def kernel (ins : List String) (outShape : Shape) (value : Wgsl.Expr) : Wgsl.Module :=
  let n := Shape.size outShape
  let storage := (ins.zip (List.range ins.length)).map (fun (nm, b) => ({ binding := b, name := nm, write := false, ty := rt } : Wgsl.StorageVar)) ++
    [{ binding := ins.length, name := "y", write := true, ty := rt }]
  let inner := stmts (coordLets outShape ++ [.assign (.index (.name "y") (.name "k")) "" value])
  let body := stmts [.letS "k" none (.member (.name "gid") "x"), .ifS (.binary "<" (.name "k") (u n)) inner .nil]
  let gid : Wgsl.Member := { name := "gid", ty := .vec 3 .u32, attrs := [.builtin "global_invocation_id"] }
  let main : Wgsl.Fn := { stage := .compute, name := "main", workgroup := (wg, 1, 1), params := [gid], ret := none, body := body }
  { storage := storage, fns := [main] }

/-- The kernel of an element-wise binary operator with broadcasting (`a` of shape `sa`, `b`
of `sb`, output `out`), validated and hardened by `Wgsl.finish`. -/
def binaryKernel (name : String) (sa sb out : Shape) : Except String Wgsl.Module := do
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  let ia := Wgsl.Expr.index (.name "a") (flatIndex (expandMap sa out.length) sa)
  let ib := Wgsl.Expr.index (.name "b") (flatIndex (expandMap sb out.length) sb)
  let some v := binaryExpr name ia ib | throw s!"webnn gpu: no kernel for {name}"
  Wgsl.finish (kernel ["a", "b"] out v)

/-- The kernel of an element-wise unary operator. -/
def unaryKernel (name : String) (s : Shape) : Except String Wgsl.Module := do
  if Shape.size s > maxElements then throw "webnn gpu: output too large for one dispatch"
  let some v := unaryExpr name (.index (.name "x") (.name "k")) | throw s!"webnn gpu: no kernel for {name}"
  Wgsl.finish (kernel ["x"] s v)

/-- The kernel of transpose: the output element `k` copies the source element `transposeMap`
reads. -/
def transposeKernel (perm : List Nat) (inShape : Shape) : Except String Wgsl.Module := do
  let out := permute perm inShape
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  Wgsl.finish (kernel ["x"] out (.index (.name "x") (flatIndex (transposeMap perm) inShape)))

/-- Workgroups to dispatch for `n` output elements. -/
def groups (n : Nat) : Nat := (n + wg - 1) / wg

/-! ## Tests: every kernel passes the page subset's check; the printed index arithmetic -/

def printed : Except String Wgsl.Module → String
  | .ok m => m.print
  | .error e => "error: " ++ e

-- add with broadcasting: [2,3] + [3] reads b at o1 (the size-1 axis is absent, the other aligned right)
#guard ((printed (binaryKernel "add" [2, 3] [3] [2, 3])).splitOn "let o1 = ((k / 1u) % 3u);").length == 2
#guard ((printed (binaryKernel "add" [2, 3] [3] [2, 3])).splitOn "b[min(u32((0u + (o1 * 1u))), (arrayLength(&b) - 1u))]").length == 2
#guard (printed (binaryKernel "mul" [2, 1, 4] [3, 1] [2, 3, 4])).startsWith "@group(0) @binding(0) var<storage, read> a: array<f32>;"
#guard !(printed (binaryKernel "mul" [2, 1, 4] [3, 1] [2, 3, 4])).startsWith "error"
#guard (printed (unaryKernel "tanh" [4])).startsWith "error"
#guard (["abs", "ceil", "cos", "exp", "floor", "neg", "reciprocal", "relu", "sigmoid", "sin", "softsign", "tan"].all
  fun n => !(printed (unaryKernel n [4, 5])).startsWith "error")
#guard (["add", "sub", "mul", "div", "max", "min", "pow"].all fun n => !(printed (binaryKernel n [4, 5] [5] [4, 5])).startsWith "error")
#guard (printed (unaryKernel "gelu" [4])).startsWith "error"
#guard (printed (unaryKernel "relu" [65536, 65])).startsWith "error"
-- transpose [2,3,4] by [2,0,1]: the output [4,2,3]; source index from transposeMap
#guard !(printed (transposeKernel [2, 0, 1] [2, 3, 4])).startsWith "error"
#guard (transposeMap [2, 0, 1]).eval [3, 1, 2] == transposeIdx [2, 0, 1] [3, 1, 2]
-- the u32 evaluator on the printed coordinate of a slice
#guard evalU (fun s => if s == "o0" then some 5 else none) (emitC coordName (.add (.lit 2) (.mulLit (.out 0) 3))) == some 17

end L4Factoidal.WebNN.Gpu
