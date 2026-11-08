import Graphics
import Init.Data.Array.Lemmas

/-! Partial evaluation of the existing typed coverage interpreter. Arithmetic
operations retain their exact order; no real/Float algebra laws are used.
Out-of-range parameters remain delayed so preparation does not move a panic
from an unvisited short-circuit branch into scene construction. -/
namespace NativeGraphics

inductive Prepared (α : Type) where
  | constant (value : α)
  | dynamic (run : Env → α)

def Prepared.eval (env : Env) : Prepared α → α
  | .constant value => value
  | .dynamic run => run env

def Prepared.map (f : α → β) : Prepared α → Prepared β
  | .constant value => .constant (f value)
  | .dynamic run => .dynamic (fun env => f (run env))

def Prepared.combine (f : α → β → γ) : Prepared α → Prepared β → Prepared γ
  | .constant a,.constant b => .constant (f a b)
  | a,b => .dynamic (fun env => f (a.eval env) (b.eval env))

/-- A known left operand decides or removes the test, as `&&` itself does. An unstroked
    primitive has a constant-false stroke test, which then costs nothing per sample. -/
def Prepared.and : Prepared Bool → Prepared Bool → Prepared Bool
  | .constant false,_ => .constant false
  | .constant true,b => b
  | a,.constant true => a
  | a,b => .dynamic (fun env => a.eval env && b.eval env)

def Prepared.or : Prepared Bool → Prepared Bool → Prepared Bool
  | .constant true,_ => .constant true
  | .constant false,b => b
  | a,.constant false => a
  | a,b => .dynamic (fun env => a.eval env || b.eval env)

/-- Same value as `and`; the right side is not prepared when the left side decides. -/
def Prepared.andThen (a : Prepared Bool) (b : Unit → Prepared Bool) : Prepared Bool :=
  match a with
  | .constant false => .constant false
  | _ => a.and (b ())

@[simp] theorem Prepared.eval_map (env : Env) (f : α → β) (a : Prepared α) :
    (a.map f).eval env = f (a.eval env) := by cases a <;> rfl
@[simp] theorem Prepared.eval_combine (env : Env) (f : α → β → γ)
    (a : Prepared α) (b : Prepared β) :
    (Prepared.combine f a b).eval env = f (a.eval env) (b.eval env) := by
  cases a <;> cases b <;> rfl
@[simp] theorem Prepared.eval_and (env : Env) (a b : Prepared Bool) :
    (a.and b).eval env = (a.eval env && b.eval env) := by
  unfold Prepared.and
  split <;> simp [Prepared.eval]
@[simp] theorem Prepared.eval_or (env : Env) (a b : Prepared Bool) :
    (a.or b).eval env = (a.eval env || b.eval env) := by
  unfold Prepared.or
  split <;> simp [Prepared.eval]
@[simp] theorem Prepared.eval_andThen (env : Env) (a : Prepared Bool) (b : Unit → Prepared Bool) :
    (a.andThen b).eval env = (a.eval env && (b ()).eval env) := by
  cases a with
  | constant v =>
    cases v
    · rfl
    · simp only [Prepared.andThen]
      exact Prepared.eval_and env _ _
  | dynamic f =>
    simp only [Prepared.andThen]
    exact Prepared.eval_and env _ _

theorem Var.eval_with_data (v : Var ty) (env : Env) (data : Array Float) :
    v.eval {env with data := data} = v.eval env := by cases v <;> rfl

/-- Every scene condition uses these literals, and `Float.ofNat` goes through bignum
    scientific conversion at each call. The closed values are computed once. -/
def literalFloat : Nat → Float
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | n => Float.ofNat n

theorem literalFloat_eq (n : Nat) : literalFloat n = Float.ofNat n := by
  unfold literalFloat
  split <;> rfl

def Expr.prepare (data : Array Float) {ty : Ty} : Expr ty → Prepared ty.Value
  | .lit n => .constant (literalFloat n)
  | .param i => match data[i]? with
    | some value => .constant value
    | none => .dynamic (fun _ => data[i]!)
  | .var v => .dynamic (fun env => v.eval env)
  | .vec a b => Prepared.combine Prod.mk (a.prepare data) (b.prepare data)
  | .add a b => Prepared.combine (·+·) (a.prepare data) (b.prepare data)
  | .sub a b => Prepared.combine (·-·) (a.prepare data) (b.prepare data)
  | .mul a b => Prepared.combine (·*·) (a.prepare data) (b.prepare data)
  | .divide a b => Prepared.combine (·/·) (a.prepare data) (b.prepare data)
  | .maximum a b => Prepared.combine max (a.prepare data) (b.prepare data)
  | .clamp01 a => (a.prepare data).map (fun x => max 0 (min 1 x))
  | .addV a b => Prepared.combine (fun x y => (x.1+y.1,x.2+y.2)) (a.prepare data) (b.prepare data)
  | .subV a b => Prepared.combine (fun x y => (x.1-y.1,x.2-y.2)) (a.prepare data) (b.prepare data)
  | .scale a b => Prepared.combine (fun x y => (x*y.1,x*y.2)) (a.prepare data) (b.prepare data)
  | .dot a b => Prepared.combine (fun x y => x.1*y.1+x.2*y.2) (a.prepare data) (b.prepare data)
  | .le a b => Prepared.combine (·<=·) (a.prepare data) (b.prepare data)
  | .and a b => (a.prepare data).and (b.prepare data)

theorem Expr.prepare_correct (data : Array Float) {ty : Ty} (expr : Expr ty) (env : Env) :
    (expr.prepare data).eval env = expr.eval {env with data := data} := by
  induction expr with
  | lit n => simp [Expr.prepare,Prepared.eval,Expr.eval,literalFloat_eq]
  | param i =>
    cases found : data[i]? with
    | none => simp [Expr.prepare,Prepared.eval,found,Expr.eval]
    | some value =>
      have atIndex : data[i]! = value := by
        simp [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,found]
      simp [Expr.prepare,Prepared.eval,found,Expr.eval,atIndex]
  | var v => simp [Expr.prepare,Prepared.eval,Expr.eval,Var.eval_with_data]
  | _ => simp_all only [Expr.prepare,Expr.eval,Prepared.eval_map,
      Prepared.eval_combine,Prepared.eval_and]

#guard ((Expr.add (.param 0) (.lit 2)).prepare #[3]).eval {data := #[]} == 5
#guard ((Expr.dot (.var .position) (.vec (.lit 1) (.lit 0))).prepare #[]).eval
  {data := #[],position := (7,9)} == 7
-- An unreachable invalid parameter must remain unreachable after preparation.
#guard !((Expr.and (.le (.lit 1) (.lit 0)) (.le (.param 99) (.lit 0))).prepare #[]).eval {data := #[]}
#guard ((Prepared.constant true).or (.dynamic (fun _ => panic! "unreachable"))).eval {data := #[]}
#guard !((Prepared.constant false).and (.dynamic (fun _ => panic! "unreachable"))).eval {data := #[]}
#print axioms Expr.prepare_correct

/-- `Expr.eval` with each literal from `literalFloat`: the same values (`literalFloat_eq`)
    with no bignum conversion at each call. Polygon fills, dashed strokes and clipped
    primitives evaluate expressions at every sample of the CPU raster (`SVGRaster`). -/
def Expr.evalFast {ty : Ty} (env : Env) : Expr ty → ty.Value
  | .lit n => literalFloat n
  | .param i => env.data[i]!
  | .var v => v.eval env
  | .vec x y => (x.evalFast env, y.evalFast env)
  | .add a b => a.evalFast env + b.evalFast env
  | .sub a b => a.evalFast env - b.evalFast env
  | .mul a b => a.evalFast env * b.evalFast env
  | .divide a b => a.evalFast env / b.evalFast env
  | .maximum a b => max (a.evalFast env) (b.evalFast env)
  | .clamp01 a => max 0 (min 1 (a.evalFast env))
  | .addV a b => let x := a.evalFast env; let y := b.evalFast env; (x.1+y.1, x.2+y.2)
  | .subV a b => let x := a.evalFast env; let y := b.evalFast env; (x.1-y.1, x.2-y.2)
  | .scale a b => let x := a.evalFast env; let y := b.evalFast env; (x*y.1, x*y.2)
  | .dot a b => let x := a.evalFast env; let y := b.evalFast env; x.1*y.1+x.2*y.2
  | .le a b => a.evalFast env <= b.evalFast env
  | .and a b => a.evalFast env && b.evalFast env

@[csimp] theorem Expr.eval_eq_evalFast : @Expr.eval = @Expr.evalFast := by
  funext ty env e
  induction e with
  | lit n => simp [Expr.eval,Expr.evalFast,literalFloat_eq]
  | _ => simp_all [Expr.eval,Expr.evalFast]
#print axioms Expr.eval_eq_evalFast
end NativeGraphics
