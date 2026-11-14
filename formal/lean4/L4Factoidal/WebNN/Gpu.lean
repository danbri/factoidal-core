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

/-- A kernel whose output element `k` comes from variables `decls` updated by `steps` over
`count` iterations of a loop counter `t` (a `forCap` loop, cost bound `count`). -/
def loopKernel (ins : List String) (outShape : Shape) (count lo : Nat) (decls : List Wgsl.Stmt)
    (steps : Wgsl.Stmts) (fin : Wgsl.Expr) : Wgsl.Module :=
  let loop := Wgsl.Stmt.forCap "t" .u32 lo (u count) count steps
  let m := kernel ins outShape fin
  let body := match m.fns with
    | [f] => match f.body with
      | .cons k (.cons (.ifS c inner e) .nil) =>
        let rec splice : Wgsl.Stmts → Wgsl.Stmts
          | .cons (.assign l op v) .nil => stmts (decls ++ [loop, .assign l op v])
          | .cons st rest => .cons st (splice rest)
          | .nil => .nil
        Wgsl.Stmts.cons k (.cons (.ifS c (splice inner) e) .nil)
      | b => b
    | _ => .nil
  { m with fns := m.fns.map fun f => { f with body := body } }

/-- A kernel whose output element `k` is accumulated over `count` steps of a loop counter
`t` (`for (var t = lo; t < min(count, count); t++)`, a `forCap` loop: its cost bound is
`count`): `acc` starts at `init`, each step does `acc = step`, the output is `fin`. -/
def foldKernel (ins : List String) (outShape : Shape) (count lo : Nat) (init : Wgsl.Expr)
    (step : Wgsl.Expr) (fin : Wgsl.Expr) : Wgsl.Module :=
  loopKernel ins outShape count lo [.varS "acc" none (some init)] (stmts [.assign (.name "acc") "" step]) fin

/-- matmul (`Compute.matmul`): `a` of shape `[..., M, K]`, `b` of `[..., K, N]`, output
`[..., M, N]`, the batch dimensions broadcast by `expandMap` (as the CPU's `broadcastMap`);
the sum over K accumulates in `f32`. -/
def matmulKernel (sa sb out : Shape) : Except String Wgsl.Module := do
  let ra := sa.length; let rb := sb.length; let ro := out.length
  if ra < 2 || rb < 2 || ro < 2 then throw "webnn gpu: matmul needs matrices"
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  let m := sa.getD (ra - 2) 1; let kk := sa.getD (ra - 1) 1; let n := sb.getD (rb - 1) 1
  if kk == 0 || kk > Wgsl.maxCapLoop then throw "webnn gpu: matmul inner dimension out of range"
  let nb := ro - 2
  let aBatch := sa.take (ra - 2); let bBatch := sb.take (rb - 2)
  let ab := flatIndex (expandMap aBatch nb) aBatch
  let bb := flatIndex (expandMap bBatch nb) bBatch
  let i := Wgsl.Expr.name (coordName nb); let j := Wgsl.Expr.name (coordName (nb + 1)); let t := Wgsl.Expr.name "t"
  let ai := Wgsl.Expr.binary "+" (.binary "+" (.binary "*" ab (u (m * kk))) (.binary "*" i (u kk))) t
  let bi := Wgsl.Expr.binary "+" (.binary "+" (.binary "*" bb (u (kk * n))) (.binary "*" t (u n))) j
  let step := Wgsl.Expr.binary "+" (.name "acc") (.binary "*" (.index (.name "a") ai) (.index (.name "b") bi))
  Wgsl.finish (foldKernel ["a", "b"] out kk 0 (f "0.0") step (.name "acc"))

/-- The reductions of `Compute.reduce` with a WGSL form: (start from the first element?,
step from `acc` and `x`, final value from `acc` and the count). -/
def reduceForm (name : String) (count : Nat) : Option (Bool × (Wgsl.Expr → Wgsl.Expr → Wgsl.Expr) × (Wgsl.Expr → Wgsl.Expr)) :=
  let id := fun (a : Wgsl.Expr) => a
  match name with
  | "reduceSum" => some (false, fun a x => .binary "+" a x, id)
  | "reduceMean" => some (false, fun a x => .binary "+" a x, fun a => .binary "/" a (f s!"{count}.0"))
  | "reduceL1" => some (false, fun a x => .binary "+" a (call1 "abs" x), id)
  | "reduceSumSquare" => some (false, fun a x => .binary "+" a (.binary "*" x x), id)
  | "reduceProduct" => some (true, fun a x => .binary "*" a x, id)
  | "reduceMax" => some (true, fun a x => call2 "max" a x, id)
  | "reduceMin" => some (true, fun a x => call2 "min" a x, id)
  | _ => none

/-- A reduction of `x` (shape `s`) over `axes`; the output's elements are the kept axes in
order (with or without `keepDimensions`, the same elements). -/
def reduceKernel (name : String) (s : Shape) (axes : List Nat) : Except String Wgsl.Module := do
  if axes.any (· ≥ s.length) then throw "webnn gpu: reduction axis out of range"
  let kept := (List.range s.length).filter (!axes.contains ·)
  let red := (List.range s.length).filter (axes.contains ·)
  let keptShape := kept.map (s.getD · 1)
  let redShape := red.map (s.getD · 1)
  let count := Shape.size redShape
  if count == 0 || count > Wgsl.maxCapLoop then throw "webnn gpu: reduction size out of range"
  if Shape.size keptShape > maxElements then throw "webnn gpu: output too large for one dispatch"
  let some (fromFirst, stepF, finF) := reduceForm name count | throw s!"webnn gpu: no kernel for {name}"
  let st := strides s
  let base := (kept.zip (List.range kept.length)).foldl (fun acc (ax, j) =>
    Wgsl.Expr.binary "+" acc (.binary "*" (.name (coordName j)) (u (st.getD ax 0)))) (u 0)
  let rst := strides redShape
  let off := fun (t : Wgsl.Expr) => (red.zip (List.range red.length)).foldl (fun acc (ax, i) =>
    Wgsl.Expr.binary "+" acc (.binary "*" (.binary "%" (.binary "/" t (u (rst.getD i 1))) (u (redShape.getD i 1))) (u (st.getD ax 0)))) (u 0)
  let x := fun (t : Wgsl.Expr) => Wgsl.Expr.index (.name "x") (.binary "+" base (off t))
  let init := if fromFirst then x (u 0) else f (if name == "reduceProduct" then "1.0" else "0.0")
  Wgsl.finish (foldKernel ["x"] keptShape count (if fromFirst then 1 else 0) init (stepF (.name "acc") (x (.name "t"))) (finF (.name "acc")))

def nm (s : String) : Wgsl.Expr := .name s
def add (a b : Wgsl.Expr) : Wgsl.Expr := .binary "+" a b
def mulE (a b : Wgsl.Expr) : Wgsl.Expr := .binary "*" a b
def andE (a b : Wgsl.Expr) : Wgsl.Expr := .binary "&&" a b

/-- The window loop of conv2d and pooling, as `Compute.conv2dNchw` / `pool2dNchw` index it:
for loop step `t` over (`ic`,) `ky`, `kx`: `iy = y·sh + ky·dh`, `ix = x·sw + kx·dw`, and the
cell is inside when `iy ≥ pt ∧ iy - pt < h ∧ ix ≥ pl ∧ ix - pl < w` (the same `Nat` tests). -/
def windowLets (kh kw sh sw dh dw : Nat) : List Wgsl.Stmt :=
  [.letS "ky" none (.binary "%" (.binary "/" (nm "t") (u kw)) (u kh)),
   .letS "kx" none (.binary "%" (nm "t") (u kw)),
   .letS "iy" none (add (mulE (nm (coordName 2)) (u sh)) (mulE (nm "ky") (u dh))),
   .letS "ix" none (add (mulE (nm (coordName 3)) (u sw)) (mulE (nm "kx") (u dw)))]

def inside (h w pt pl : Nat) : Wgsl.Expr :=
  andE (andE (.binary ">=" (nm "iy") (u pt)) (.binary "<" (.binary "-" (nm "iy") (u pt)) (u h)))
       (andE (.binary ">=" (nm "ix") (u pl)) (.binary "<" (.binary "-" (nm "ix") (u pl)) (u w)))

/-- conv2d on an NCHW input and an OIHW filter (`Compute.conv2dNchw`): output `[n, oc, oh, ow]`,
`groups` groups, optional bias; padding `[top, bottom, left, right]`. -/
def conv2dKernel (inShape filterShape out : Shape) (strides dilations padding : List Nat) (groups : Nat)
    (bias : Bool) : Except String Wgsl.Module := do
  let g := fun (l : List Nat) (i : Nat) => l.getD i 0
  let c := g inShape 1; let h := g inShape 2; let wd := g inShape 3
  let oc := g filterShape 0; let icg := g filterShape 1; let kh := g filterShape 2; let kw := g filterShape 3
  if inShape.length != 4 || filterShape.length != 4 || out.length != 4 || groups == 0 || oc % groups != 0 then
    throw "webnn gpu: conv2d shapes"
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  let count := icg * kh * kw
  if count == 0 || count > Wgsl.maxCapLoop then throw "webnn gpu: conv2d window out of range"
  let ocg := oc / groups
  let pt := g padding 0; let pl := g padding 2
  let lets := [Wgsl.Stmt.letS "ic" none (.binary "/" (nm "t") (u (kh * kw)))] ++
    windowLets kh kw (g strides 0) (g strides 1) (g dilations 0) (g dilations 1) ++
    [.letS "cin" none (add (mulE (.binary "/" (nm (coordName 1)) (u ocg)) (u icg)) (nm "ic"))]
  let xi := add (mulE (add (mulE (add (mulE (nm (coordName 0)) (u c)) (nm "cin")) (u h)) (.binary "-" (nm "iy") (u pt))) (u wd))
    (.binary "-" (nm "ix") (u pl))
  let wi := add (mulE (add (mulE (add (mulE (nm (coordName 1)) (u icg)) (nm "ic")) (u kh)) (nm "ky")) (u kw)) (nm "kx")
  let step := Wgsl.Stmt.ifS (inside h wd pt pl)
    (stmts [.assign (nm "acc") "" (add (nm "acc") (mulE (.index (nm "x") xi) (.index (nm "w") wi)))]) .nil
  let fin := if bias then add (nm "acc") (.index (nm "bias") (nm (coordName 1))) else nm "acc"
  Wgsl.finish (loopKernel (if bias then ["x", "w", "bias"] else ["x", "w"]) out count 0
    [.varS "acc" none (some (f "0.0"))] (stmts (lets ++ [step])) fin)

/-- averagePool2d and maxPool2d on an NCHW input (`Compute.pool2dNchw`): padding cells are not
part of a window; a window with no cell gives 0. -/
def poolKernel (name : String) (inShape out : Shape) (window strides dilations padding : List Nat) :
    Except String Wgsl.Module := do
  let g := fun (l : List Nat) (i : Nat) => l.getD i 0
  let c := g inShape 1; let h := g inShape 2; let wd := g inShape 3
  let kh := g window 0; let kw := g window 1
  if inShape.length != 4 || out.length != 4 then throw "webnn gpu: pool shapes"
  if name != "averagePool2d" && name != "maxPool2d" then throw s!"webnn gpu: no kernel for {name}"
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  let count := kh * kw
  if count == 0 || count > Wgsl.maxCapLoop then throw "webnn gpu: pool window out of range"
  let pt := g padding 0; let pl := g padding 2
  let v := Wgsl.Expr.index (nm "x") (add (mulE (add (mulE (add (mulE (nm (coordName 0)) (u c)) (nm (coordName 1))) (u h))
    (.binary "-" (nm "iy") (u pt))) (u wd)) (.binary "-" (nm "ix") (u pl)))
  let upd := if name == "maxPool2d"
    then Wgsl.Stmt.ifS (.binary "==" (nm "cnt") (u 0)) (stmts [.assign (nm "acc") "" v]) (stmts [.assign (nm "acc") "" (call2 "max" (nm "acc") v)])
    else .assign (nm "acc") "" (add (nm "acc") v)
  let step := Wgsl.Stmt.ifS (inside h wd pt pl) (stmts [upd, .assign (nm "cnt") "" (add (nm "cnt") (u 1))]) .nil
  let value := if name == "maxPool2d" then nm "acc" else .binary "/" (nm "acc") (.call (.ty (.scalar .f32)) (.cons (nm "cnt") .nil))
  let fin := Wgsl.Expr.call (.fn "select") (.cons value (.cons (f "0.0") (.cons (.binary "==" (nm "cnt") (u 0)) .nil)))
  Wgsl.finish (loopKernel ["x"] out count 0 [.varS "acc" none (some (f "0.0")), .varS "cnt" none (some (u 0))]
    (stmts (windowLets kh kw (g strides 0) (g strides 1) (g dilations 0) (g dilations 1) ++ [step])) fin)

/-- A finite `Float` as a WGSL `f32` literal (its decimal text; a minus sign as negation);
`none` for NaN, an infinity or a text the subset does not take. -/
def floatLit (x : Float) : Option Wgsl.Expr :=
  if x.isNaN || x.isInf then none else
  let t := (if x < 0.0 then -x else x).toString
  if Wgsl.Lit.ok (.float t) then some (if x < 0.0 then .unary "-" (f t) else f t) else none

/-- gemm (`Compute.gemm`): `alpha · A · B + beta · C` on matrices, `A` `[M, K]` (`[K, M]` when
`aT`), `B` `[K, N]` (`[N, K]` when `bT`), `C` broadcast to `[M, N]` by `expandMap`. -/
def gemmKernel (sa sb : Shape) (sc : Option Shape) (alpha beta : Float) (aT bT : Bool) (out : Shape) :
    Except String Wgsl.Module := do
  if sa.length != 2 || sb.length != 2 || out.length != 2 then throw "webnn gpu: gemm shapes"
  if Shape.size out > maxElements then throw "webnn gpu: output too large for one dispatch"
  let m := out.getD 0 1; let n := out.getD 1 1
  let kk := if aT then sa.getD 0 1 else sa.getD 1 1
  if kk == 0 || kk > Wgsl.maxCapLoop then throw "webnn gpu: gemm inner dimension out of range"
  let some al := floatLit alpha | throw "webnn gpu: gemm alpha"
  let some be := floatLit beta | throw "webnn gpu: gemm beta"
  let i := nm (coordName 0); let j := nm (coordName 1); let t := nm "t"
  let ai := if aT then add (mulE t (u m)) i else add (mulE i (u kk)) t
  let bi := if bT then add (mulE j (u kk)) t else add (mulE t (u n)) j
  let step := add (nm "acc") (mulE (.index (nm "a") ai) (.index (nm "b") bi))
  let fin := match sc with
    | some c => add (mulE al (nm "acc")) (mulE be (.index (nm "c") (flatIndex (expandMap c 2) c)))
    | none => mulE al (nm "acc")
  Wgsl.finish (foldKernel (if sc.isSome then ["a", "b", "c"] else ["a", "b"]) out kk 0 (f "0.0") step fin)

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
-- matmul with batch broadcasting, reductions over chosen axes
#guard !(printed (matmulKernel [2, 3, 4] [4, 5] [2, 3, 5])).startsWith "error"
#guard ((printed (matmulKernel [3, 4] [4, 5] [3, 5])).splitOn "for (var t: u32 = 0u; t < min(u32(4u), 4u); t++)").length == 2
#guard (["reduceSum", "reduceMean", "reduceL1", "reduceSumSquare", "reduceProduct", "reduceMax", "reduceMin"].all
  fun n => !(printed (reduceKernel n [2, 3, 4] [1])).startsWith "error")
#guard (printed (reduceKernel "reduceLogSum" [2, 3] [1])).startsWith "error"
#guard !(printed (conv2dKernel [1, 4, 8, 8] [6, 2, 3, 3] [1, 6, 8, 8] [1, 1] [1, 1] [1, 1, 1, 1] 2 true)).startsWith "error"
#guard !(printed (poolKernel "averagePool2d" [1, 2, 8, 8] [1, 2, 4, 4] [3, 3] [2, 2] [1, 1] [1, 1, 1, 1])).startsWith "error"
#guard !(printed (poolKernel "maxPool2d" [1, 2, 8, 8] [1, 2, 4, 4] [3, 3] [2, 2] [1, 1] [1, 1, 1, 1])).startsWith "error"
#guard (printed (matmulKernel [2, 70000] [70000, 2] [2, 2])).startsWith "error"
#guard !(printed (gemmKernel [4, 3] [5, 4] (some [5]) 1.5 (-0.25) true true [3, 5])).startsWith "error"
#guard (printed (gemmKernel [3, 4] [4, 5] none (0.0 / 0.0) 1.0 false false [3, 5])).startsWith "error"
-- the u32 evaluator on the printed coordinate of a slice
#guard evalU (fun s => if s == "o0" then some 5 else none) (emitC coordName (.add (.lit 2) (.mulLit (.out 0) 3))) == some 17

end L4Factoidal.WebNN.Gpu
