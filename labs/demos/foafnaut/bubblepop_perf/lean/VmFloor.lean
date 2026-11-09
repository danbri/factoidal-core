/-!
# What the execution model costs: three ways to run one JavaScript loop in compiled Lean

    var s = 0; for (var i = 0; i < n; i++) s = s + i;

Record: docs/designissues/2026-11-09-foafnaut-perf-exploration.md, section 8. Run it with
`labs/demos/foafnaut/bubblepop_perf/lean/run.sh` (it needs only `lean` and `leanc`; this file is
not part of the Lake project).

- `A`: a tree walk in `EStateM` over boxed values, with fuel and a step budget: the shape of
  `L4Factoidal/JS/Interp.lean`, with locals already in slots.
- `B`: the same tree walk as pure functions that pass the slots and return a boxed value and
  the slots (no monad).
- `C`: a register bytecode loop: instructions in an `Array UInt32`, numbers unboxed in a
  `FloatArray`, the machine state as the arguments of one tail-recursive function. No type
  test and no property access: it is a floor for a number loop, not an engine.
-/

namespace A
inductive Val where
  | undef | bool (b : Bool) | num (x : Float)
  deriving Inhabited
inductive Expr where
  | num (x : Float) | loc (i : Nat) | add (a b : Expr) | lt (a b : Expr) | assign (i : Nat) (e : Expr)
inductive Stmt where
  | expr (e : Expr) | forS (test update : Expr) (body : List Stmt)
structure Heap where
  vals : Array Val
  steps : UInt64
abbrev M := EStateM String Heap

def tick : M Unit := do
  let h ← get
  if h.steps == 0 then throw "budget"
  set { h with steps := h.steps - 1 }

mutual
def evalExpr : Nat → Expr → M Val
  | 0, _ => throw "fuel"
  | n + 1, e => do
    match e with
    | .num x => pure (.num x)
    | .loc i => do pure ((← get).vals.getD i .undef)
    | .add a b =>
      let x ← evalExpr n a
      let y ← evalExpr n b
      match x, y with
      | .num p, .num q => pure (.num (p + q))
      | _, _ => throw "type"
    | .lt a b =>
      let x ← evalExpr n a
      let y ← evalExpr n b
      match x, y with
      | .num p, .num q => if p < q then pure (.bool true) else pure (.bool false)
      | _, _ => throw "type"
    | .assign i e =>
      let v ← evalExpr n e
      modify fun h => { h with vals := h.vals.set! i v }
      pure v
termination_by structural n _ => n
def evalStmts : Nat → List Stmt → M Unit
  | 0, _ => throw "fuel"
  | _ + 1, [] => pure ()
  | n + 1, s :: ss => do evalStmt n s; evalStmts n ss
termination_by structural n _ => n
def evalStmt : Nat → Stmt → M Unit
  | 0, _ => throw "fuel"
  | n + 1, s => do
    match s with
    | .expr e => let _ ← evalExpr n e; pure ()
    | .forS test update body => forLoop n test update body
termination_by structural n _ => n
def forLoop : Nat → Expr → Expr → List Stmt → M Unit
  | 0, _, _, _ => throw "fuel"
  | n + 1, test, update, body => do
    tick
    match ← evalExpr n test with
    | .bool true =>
      evalStmts n body
      let _ ← evalExpr n update
      forLoop n test update body
    | _ => pure ()
termination_by structural n _ _ _ => n
end

/-- slots: 0 = s, 1 = i, 2 = n -/
def program : Stmt :=
  .forS (.lt (.loc 1) (.loc 2)) (.assign 1 (.add (.loc 1) (.num 1)))
    [.expr (.assign 0 (.add (.loc 0) (.loc 1)))]

def run (n : Nat) : String :=
  let h : Heap := { vals := #[.num 0, .num 0, .num n.toUInt64.toFloat], steps := 1000000000000 }
  match (evalStmt 2147483647 program).run h with
  | .ok _ h => match h.vals.getD 0 .undef with | .num x => toString x | _ => "?"
  | .error e _ => e
end A

namespace B
open A (Val Expr Stmt)
mutual
def evalExpr : Nat → Expr → Array Val → Val × Array Val
  | 0, _, vs => (.undef, vs)
  | n + 1, e, vs =>
    match e with
    | .num x => (.num x, vs)
    | .loc i => (vs.getD i .undef, vs)
    | .add a b =>
      let (x, vs) := evalExpr n a vs
      let (y, vs) := evalExpr n b vs
      match x, y with
      | .num p, .num q => (.num (p + q), vs)
      | _, _ => (.undef, vs)
    | .lt a b =>
      let (x, vs) := evalExpr n a vs
      let (y, vs) := evalExpr n b vs
      match x, y with
      | .num p, .num q => (if p < q then .bool true else .bool false, vs)
      | _, _ => (.undef, vs)
    | .assign i e =>
      let (v, vs) := evalExpr n e vs
      (v, vs.set! i v)
termination_by structural n _ _ => n
def evalStmts : Nat → List Stmt → Array Val → Array Val
  | 0, _, vs => vs
  | _ + 1, [], vs => vs
  | n + 1, s :: ss, vs => evalStmts n ss (evalStmt n s vs)
termination_by structural n _ _ => n
def evalStmt : Nat → Stmt → Array Val → Array Val
  | 0, _, vs => vs
  | n + 1, s, vs =>
    match s with
    | .expr e => (evalExpr n e vs).2
    | .forS test update body => forLoop n test update body vs
termination_by structural n _ _ => n
def forLoop : Nat → Expr → Expr → List Stmt → Array Val → Array Val
  | 0, _, _, _, vs => vs
  | n + 1, test, update, body, vs =>
    match evalExpr n test vs with
    | (.bool true, vs) =>
      let vs := evalStmts n body vs
      let (_, vs) := evalExpr n update vs
      forLoop n test update body vs
    | (_, vs) => vs
termination_by structural n _ _ _ _ => n
end
def run (n : Nat) : String :=
  match (evalStmt 2147483647 A.program #[.num 0, .num 0, .num n.toUInt64.toFloat]).getD 0 .undef with
  | .num x => toString x | _ => "?"
end B

namespace C
/-- An instruction: `op | a << 8 | b << 16 | c << 24`. Registers hold unboxed doubles.
1 ADD a b c: r[a] = r[b] + r[c].  2 LT a b c: r[a] = (r[b] < r[c]) as 1 or 0.
3 JMPF a t: if r[a] == 0 then pc = t (t = b + 256 c).  4 JMP t.  0 HALT. -/
def ins (op a b c : UInt32) : UInt32 := op ||| (a <<< 8) ||| (b <<< 16) ||| (c <<< 24)

def exec (code : Array UInt32) (pc : Nat) (regs : FloatArray) (steps : UInt64) : FloatArray :=
  if hs : steps = 0 then regs else
  let w := code.getD pc 0
  let op := w &&& 0xFF
  let a := ((w >>> 8) &&& 0xFF).toNat
  let b := ((w >>> 16) &&& 0xFF).toNat
  let c := ((w >>> 24) &&& 0xFF).toNat
  if op == 1 then exec code (pc + 1) (regs.set! a (regs.get! b + regs.get! c)) (steps - 1)
  else if op == 2 then exec code (pc + 1) (regs.set! a (if regs.get! b < regs.get! c then 1 else 0)) (steps - 1)
  else if op == 3 then
    if regs.get! a == 0 then exec code (b + 256 * c) regs (steps - 1) else exec code (pc + 1) regs (steps - 1)
  else if op == 4 then exec code (b + 256 * c) regs (steps - 1)
  else regs
termination_by steps.toNat
decreasing_by
  all_goals
    have h1 : steps.toNat ≠ 0 := fun h => hs (UInt64.toNat_inj.mp (by simpa using h))
    have h2 : (steps - 1).toNat = steps.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le]
      · rfl
      · exact UInt64.le_iff_toNat_le.mpr (by simp; omega)
    omega

/-- registers: 0 = s, 1 = i, 2 = n, 3 = one, 4 = t.
0: LT 4 1 2;  1: JMPF 4 -> 5;  2: ADD 0 0 1;  3: ADD 1 1 3;  4: JMP 0;  5: HALT -/
def program : Array UInt32 :=
  #[ins 2 4 1 2, ins 3 4 5 0, ins 1 0 0 1, ins 1 1 1 3, ins 4 0 0 0, ins 0 0 0 0]

def run (n : Nat) : String :=
  let regs : FloatArray := ⟨#[0, 0, n.toUInt64.toFloat, 1, 0]⟩
  toString ((exec program 0 regs 1000000000000).get! 0)
end C

def time (name : String) (n : Nat) (act : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := act ()
  let t1 ← (if r.length == 12345678 then pure 0 else IO.monoNanosNow)
  let ps := (t1 - t0) * 10 / n
  IO.println s!"{name}: {ps / 10}.{ps % 10} ns per loop iteration   (result {r})"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  time "A  tree walk, EStateM, boxed values, fuel, step budget" n fun _ => A.run n
  time "B  tree walk, pure, boxed values, fuel" n fun _ => B.run n
  time "C  register bytecode, unboxed doubles, one tail-recursive loop" n fun _ => C.run n
