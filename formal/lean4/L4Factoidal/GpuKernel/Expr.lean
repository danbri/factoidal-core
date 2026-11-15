/-
L4Factoidal.GpuKernel.Expr — a small IR for the `u32` arithmetic of GPU compute kernels,
with its meaning in Lean (`E.eval`, natural numbers), the meaning the GPU gives it
(`E.eval32`, every operation modulo 2^32, as WGSL `u32`), and the WGSL text it prints as
(`E.wgsl`). Core issue 398.

What an expression can read: the invocation's index (`inv`), the counter of the kernel's
one loop (`k`), four uniform parameters (`param 0 .. 3`, printed as `params.x .. params.w`)
and the read-only input buffer (`load idx`). There is no way to read the output buffer, so
`Race.lean`'s model (writes depend only on read-only data) holds for every kernel built
from this IR.

- `E.eval32_eq`: when every value along the way is below 2^32 (`E.Fits`) and the input
  holds `u32` values, the GPU's wrapped arithmetic equals the Lean meaning. Each kernel
  proves `Fits` for the inputs within its stated limits, so on those inputs the GPU can not
  overflow into a different answer.
- Division and remainder are by `max b 1` in both meanings and in the printed text, so
  they are total and a zero divisor is not undefined behaviour.

Not proved: that `E.wgsl` prints text whose WGSL meaning is `E.eval32` (the printer is
small and checked by differential tests against the GPU), and the shader compiler.
-/
namespace L4Factoidal.GpuKernel

/-- `u32` expressions. -/
inductive E where
  | lit (n : Nat)
  | inv
  | k
  | param (i : Fin 4)
  | load (idx : E)
  | add (a b : E)
  | mul (a b : E)
  | div (a b : E)
  | mod (a b : E)
  deriving Repr, Inhabited

/-- Conditions. -/
inductive P where
  | lt (a b : E)
  | and (p q : P)
  deriving Repr, Inhabited

/-- What one invocation sees: its index, the loop counter, the parameters, the input. -/
structure Env where
  inv : Nat
  k : Nat
  params : Fin 4 → Nat
  input : Nat → Nat

def U32 : Nat := 4294967296

/-- The Lean meaning: natural numbers. -/
def E.eval (env : Env) : E → Nat
  | .lit n => n
  | .inv => env.inv
  | .k => env.k
  | .param i => env.params i
  | .load idx => env.input (idx.eval env)
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .div a b => a.eval env / max (b.eval env) 1
  | .mod a b => a.eval env % max (b.eval env) 1

/-- The GPU's meaning: every operation modulo 2^32. -/
def E.eval32 (env : Env) : E → Nat
  | .lit n => n % U32
  | .inv => env.inv % U32
  | .k => env.k % U32
  | .param i => env.params i % U32
  | .load idx => env.input (idx.eval32 env)
  | .add a b => (a.eval32 env + b.eval32 env) % U32
  | .mul a b => (a.eval32 env * b.eval32 env) % U32
  | .div a b => a.eval32 env / max (b.eval32 env) 1
  | .mod a b => a.eval32 env % max (b.eval32 env) 1

/-- Every value along the way is a `u32`. -/
def E.Fits (env : Env) : E → Prop
  | .lit n => n < U32
  | .inv => env.inv < U32
  | .k => env.k < U32
  | .param i => env.params i < U32
  | .load idx => idx.Fits env
  | .add a b => a.Fits env ∧ b.Fits env ∧ a.eval env + b.eval env < U32
  | .mul a b => a.Fits env ∧ b.Fits env ∧ a.eval env * b.eval env < U32
  | .div a b => a.Fits env ∧ b.Fits env
  | .mod a b => a.Fits env ∧ b.Fits env

theorem E.eval_lt_of_fits (env : Env) (hin : ∀ i, env.input i < U32) :
    ∀ (e : E), e.Fits env → e.eval env < U32
  | .lit _, h => h
  | .inv, h => h
  | .k, h => h
  | .param _, h => h
  | .load _, _ => hin _
  | .add _ _, h => h.2.2
  | .mul _ _, h => h.2.2
  | .div a _, h => Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (E.eval_lt_of_fits env hin a h.1)
  | .mod a _, h => Nat.lt_of_le_of_lt (Nat.mod_le _ _) (E.eval_lt_of_fits env hin a h.1)

/-- On values that fit, the GPU's `u32` arithmetic is the Lean meaning. -/
theorem E.eval32_eq (env : Env) (hin : ∀ i, env.input i < U32) :
    ∀ (e : E), e.Fits env → e.eval32 env = e.eval env
  | .lit _, h => Nat.mod_eq_of_lt h
  | .inv, h => Nat.mod_eq_of_lt h
  | .k, h => Nat.mod_eq_of_lt h
  | .param _, h => Nat.mod_eq_of_lt h
  | .load idx, h => by simp only [E.eval32, E.eval, E.eval32_eq env hin idx h]
  | .add a b, h => by
    simp only [E.eval32, E.eval, E.eval32_eq env hin a h.1, E.eval32_eq env hin b h.2.1]
    exact Nat.mod_eq_of_lt h.2.2
  | .mul a b, h => by
    simp only [E.eval32, E.eval, E.eval32_eq env hin a h.1, E.eval32_eq env hin b h.2.1]
    exact Nat.mod_eq_of_lt h.2.2
  | .div a b, h => by simp only [E.eval32, E.eval, E.eval32_eq env hin a h.1, E.eval32_eq env hin b h.2]
  | .mod a b, h => by simp only [E.eval32, E.eval, E.eval32_eq env hin a h.1, E.eval32_eq env hin b h.2]

def P.eval (env : Env) : P → Bool
  | .lt a b => decide (a.eval env < b.eval env)
  | .and p q => p.eval env && q.eval env

def P.eval32 (env : Env) : P → Bool
  | .lt a b => decide (a.eval32 env < b.eval32 env)
  | .and p q => p.eval32 env && q.eval32 env

def P.Fits (env : Env) : P → Prop
  | .lt a b => a.Fits env ∧ b.Fits env
  | .and p q => p.Fits env ∧ q.Fits env

theorem P.eval32_eq (env : Env) (hin : ∀ i, env.input i < U32) :
    ∀ (p : P), p.Fits env → p.eval32 env = p.eval env
  | .lt a b, h => by simp only [P.eval32, P.eval, E.eval32_eq env hin a h.1, E.eval32_eq env hin b h.2]
  | .and p q, h => by simp only [P.eval32, P.eval, P.eval32_eq env hin p h.1, P.eval32_eq env hin q h.2]

/-- The input indices an expression reads (as expressions). -/
def E.loads : E → List E
  | .load idx => idx :: idx.loads
  | .add a b | .mul a b | .div a b | .mod a b => a.loads ++ b.loads
  | _ => []

def P.loads : P → List E
  | .lt a b => a.loads ++ b.loads
  | .and p q => p.loads ++ q.loads

/-! ## WGSL text -/

def paramField : Fin 4 → String
  | 0 => "x" | 1 => "y" | 2 => "z" | 3 => "w"

/-- The input buffer is `inp`; a read is clamped to the buffer as a second line of defence
(the kernels prove their reads are in bounds without it). -/
def E.wgsl : E → String
  | .lit n => s!"{n}u"
  | .inv => "t"
  | .k => "k"
  | .param i => s!"params.{paramField i}"
  | .load idx => s!"inp[min({idx.wgsl}, arrayLength(&inp) - 1u)]"
  | .add a b => s!"({a.wgsl} + {b.wgsl})"
  | .mul a b => s!"({a.wgsl} * {b.wgsl})"
  | .div a b => s!"({a.wgsl} / max({b.wgsl}, 1u))"
  | .mod a b => s!"({a.wgsl} % max({b.wgsl}, 1u))"

def P.wgsl : P → String
  | .lt a b => s!"({a.wgsl} < {b.wgsl})"
  | .and p q => s!"({p.wgsl} && {q.wgsl})"

end L4Factoidal.GpuKernel
