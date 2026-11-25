import L4Factoidal.Paralliverse.CountTarget

/-! # Finite storage instructions with bounded loops

One invocation has private word locals, two immutable input bindings and one
writable binding. A loop uses the evaluated u32 bound and a u32 index. The
independent static limit is checked before entering the loop. -/

namespace L4Factoidal.Paralliverse.LoopTarget

inductive Binding where
  | packet | auxiliary
  deriving Repr

structure Inputs where
  packet : Array UInt32
  auxiliary : Array UInt32

def Inputs.get (inputs : Inputs) : Binding → Array UInt32
  | .packet => inputs.packet
  | .auxiliary => inputs.auxiliary

inductive Fault where
  | storage (fault : CountTarget.Fault)
  | loopLimit (actual maximum : Nat)
  deriving Repr, DecidableEq

structure State where
  locals : Nat → UInt32
  dst : Array UInt32

def State.assign (s : State) (slot : Nat) (v : UInt32) : State :=
  {s with locals := fun j => if j = slot then v else s.locals j}

def read (inputs : Inputs) (binding : Binding) (i : UInt32) : Except Fault UInt32 :=
  (CountTarget.loadWord (inputs.get binding) i).mapError Fault.storage

def store (s : State) (i v : UInt32) : Except Fault State :=
  match CountTarget.storeWord s.dst i v with
  | .error e => .error (.storage e)
  | .ok dst => .ok {s with dst}

inductive Expr where
  | literal (v : UInt32)
  | globalId
  | index
  | localWord (slot : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)
  | load (binding : Binding) (address : Expr)
  deriving Repr

def Expr.eval (inputs : Inputs) (gid index : UInt32) (s : State) : Expr → Except Fault UInt32
  | .literal v => .ok v
  | .globalId => .ok gid
  | .index => .ok index
  | .localWord slot => .ok (s.locals slot)
  | .add a b => do return (← a.eval inputs gid index s) + (← b.eval inputs gid index s)
  | .mul a b => do return (← a.eval inputs gid index s) * (← b.eval inputs gid index s)
  | .load b i => do read inputs b (← i.eval inputs gid index s)

private inductive Bin where
  | plus | times

private def Bin.apply : Bin → UInt32 → UInt32 → UInt32
  | .plus => (· + ·)
  | .times => (· * ·)

private inductive ExprKont where
  | done
  | right (op : Bin) (operand : Expr) (outer : ExprKont)
  | combine (op : Bin) (left : UInt32) (outer : ExprKont)
  | loadAt (binding : Binding) (outer : ExprKont)

private inductive ExprControl where
  | evaluate (expr : Expr) (k : ExprKont)
  | resume (word : UInt32) (k : ExprKont)

-- These weights are used only to prove termination.
@[simp] private noncomputable def Expr.work : Expr → Nat
  | .literal _ | .globalId | .index | .localWord _ => 1
  | .add a b | .mul a b => a.work + b.work + 3
  | .load _ i => i.work + 2

@[simp] private noncomputable def ExprKont.work : ExprKont → Nat
  | .done => 0
  | .right _ b k => b.work + 2 + k.work
  | .combine _ _ k | .loadAt _ k => 1 + k.work

@[simp] private noncomputable def ExprControl.work : ExprControl → Nat
  | .evaluate e k => e.work + k.work
  | .resume _ k => k.work

private def executeExpr (inputs : Inputs) (gid index : UInt32) (s : State) :
    ExprControl → Except Fault UInt32
  | .evaluate (.literal v) k => executeExpr inputs gid index s (.resume v k)
  | .evaluate .globalId k => executeExpr inputs gid index s (.resume gid k)
  | .evaluate .index k => executeExpr inputs gid index s (.resume index k)
  | .evaluate (.localWord slot) k => executeExpr inputs gid index s (.resume (s.locals slot) k)
  | .evaluate (.add a b) k => executeExpr inputs gid index s (.evaluate a (.right .plus b k))
  | .evaluate (.mul a b) k => executeExpr inputs gid index s (.evaluate a (.right .times b k))
  | .evaluate (.load binding i) k => executeExpr inputs gid index s (.evaluate i (.loadAt binding k))
  | .resume v .done => .ok v
  | .resume a (.right op b k) => executeExpr inputs gid index s (.evaluate b (.combine op a k))
  | .resume b (.combine op a k) => executeExpr inputs gid index s (.resume (op.apply a b) k)
  | .resume i (.loadAt binding k) =>
    match read inputs binding i with
    | .error fault => .error fault
    | .ok v => executeExpr inputs gid index s (.resume v k)
termination_by control => control.work
decreasing_by all_goals simp <;> omega

/-- Evaluate an expression with an explicit stack of pending operands and selected bindings. -/
def Expr.evalTR (inputs : Inputs) (gid index : UInt32) (s : State) (e : Expr) : Except Fault UInt32 :=
  executeExpr inputs gid index s (.evaluate e .done)

/-- Kind: expression simulation.
Says: the continuation for a binary operation evaluates its operands in order and
combines the resulting words, propagating the first fault.
Does not say: that the operands always evaluate successfully. -/
private theorem binary_cont (inputs : Inputs) (gid index : UInt32) (s : State)
    (op : Bin) (a b : Expr) (k : ExprKont)
    (ha : ∀ q, executeExpr inputs gid index s (.evaluate a q) =
      (a.eval inputs gid index s).bind (fun x => executeExpr inputs gid index s (.resume x q)))
    (hb : ∀ q, executeExpr inputs gid index s (.evaluate b q) =
      (b.eval inputs gid index s).bind (fun x => executeExpr inputs gid index s (.resume x q))) :
    executeExpr inputs gid index s (.evaluate a (.right op b k)) =
      ((do return op.apply (← a.eval inputs gid index s) (← b.eval inputs gid index s)) :
        Except Fault UInt32).bind (fun x => executeExpr inputs gid index s (.resume x k)) := by
  rw [ha]
  cases a.eval inputs gid index s with
  | error fault => rfl
  | ok left =>
    change executeExpr inputs gid index s (.resume left (.right op b k)) = _
    rw [executeExpr, hb]
    cases b.eval inputs gid index s with
    | error fault => rfl
    | ok right =>
      change executeExpr inputs gid index s (.resume right (.combine op left k)) =
        executeExpr inputs gid index s (.resume (op.apply left right) k)
      rw [executeExpr]

/-- Kind: expression simulation.
Says: starting an expression in any pending continuation reads the selected
binding and preserves the structural result, including a failing word address.
Does not say: that arbitrary syntax has a fixed heap bound. -/
private theorem execute_cont (inputs : Inputs) (gid index : UInt32) (s : State) (e : Expr) (k : ExprKont) :
    executeExpr inputs gid index s (.evaluate e k) =
      (e.eval inputs gid index s).bind (fun v => executeExpr inputs gid index s (.resume v k)) := by
  induction e generalizing k with
  | literal v => rw [executeExpr] <;> rfl
  | globalId => rw [executeExpr] <;> rfl
  | index => rw [executeExpr] <;> rfl
  | localWord slot => rw [executeExpr] <;> rfl
  | add a b ha hb =>
    rw [executeExpr]
    exact binary_cont inputs gid index s .plus a b k ha hb
  | mul a b ha hb =>
    rw [executeExpr]
    exact binary_cont inputs gid index s .times a b k ha hb
  | load binding i ih =>
    change executeExpr inputs gid index s (.evaluate (.load binding i) k) =
      ((i.eval inputs gid index s).bind (fun j => read inputs binding j)).bind
        (fun v => executeExpr inputs gid index s (.resume v k))
    rw [executeExpr, ih]
    cases i.eval inputs gid index s with
    | error fault => rfl
    | ok addr =>
      change executeExpr inputs gid index s (.resume addr (.loadAt binding k)) =
        (read inputs binding addr).bind (fun v => executeExpr inputs gid index s (.resume v k))
      rw [executeExpr]
      cases read inputs binding addr <;> rfl

/-- Kind: executable equivalence.
Says: the continuation machine returns the same word or first storage fault for every
expression, input pair, invocation ID, loop index and local state.
Does not say: that emitted code uses a particular native stack or heap limit. -/
@[csimp] theorem Expr.eval_eq_evalTR : @Expr.eval = @Expr.evalTR := by
  funext inputs gid index s e
  unfold Expr.evalTR
  rw [execute_cont]
  cases e.eval inputs gid index s with
  | error fault => rfl
  | ok v =>
    change Except.ok v = executeExpr inputs gid index s (.resume v .done)
    rw [executeExpr]

#print axioms Expr.eval_eq_evalTR

inductive Stmt where
  | assign (slot : Nat) (value : Expr)
  | storeWord (address value : Expr)
  | seq (first second : Stmt)
  | whenLt (a b : Expr) (body : Stmt)
  | forRange (maximum : Nat) (bound : Expr) (body : Stmt)
  deriving Repr

/-- Execute the same body with successive u32 indices. The first fault stops execution. -/
def iterate (body : UInt32 → State → Except Fault State) : Nat → UInt32 → State → Except Fault State
  | 0, _, s => .ok s
  | k + 1, i, s => do
    let next ← body i s
    iterate body k (i + 1) next

def Stmt.exec (inputs : Inputs) (gid index : UInt32) (s : State) : Stmt → Except Fault State
  | .assign slot value => do return s.assign slot (← value.eval inputs gid index s)
  | .storeWord i v => do store s (← i.eval inputs gid index s) (← v.eval inputs gid index s)
  | .seq a b => do
    let next ← a.exec inputs gid index s
    b.exec inputs gid index next
  | .whenLt a b body => do
    if (← a.eval inputs gid index s) < (← b.eval inputs gid index s) then
      body.exec inputs gid index s
    else return s
  | .forRange maximum bound body => do
    let n ← bound.eval inputs gid index s
    if n.toNat ≤ maximum then
      iterate (fun i st => body.exec inputs gid i st) n.toNat 0 s
    else throw (.loopLimit n.toNat maximum)

private inductive Pending where
  | done
  | run (index : UInt32) (stmt : Stmt) (rest : Pending)
  | iterations (remaining : Nat) (next : UInt32) (body : Stmt) (rest : Pending)

-- These upper bounds are used in the termination proof. The worker schedules
-- one iteration at a time and carries the actual remaining count.
@[simp] private noncomputable def Stmt.work : Stmt → Nat
  | .assign .. | .storeWord .. => 1
  | .seq a b => a.work + b.work + 1
  | .whenLt _ _ body => body.work + 1
  | .forRange maximum _ body => maximum * (body.work + 1) + 2

@[simp] private noncomputable def Pending.work : Pending → Nat
  | .done => 0
  | .run _ stmt rest => stmt.work + rest.work
  | .iterations remaining _ body rest => remaining * (body.work + 1) + 1 + rest.work

/-- Kind: termination.
Says: scheduling an admitted number of iterations decreases the loop's work bound.
Does not say: that the bound is computed during execution. -/
private theorem enter_loop_lt (actual maximum unit tail : Nat) (h : actual ≤ maximum) :
    actual * unit + 1 + tail < maximum * unit + 2 + tail := by
  have hm := Nat.mul_le_mul_right unit h
  omega

private def executeStmt (inputs : Inputs) (gid : UInt32) : Pending → State → Except Fault State
  | .done, s => .ok s
  | .run index (.assign slot value) rest, s =>
    match value.eval inputs gid index s with
    | .error fault => .error fault
    | .ok v => executeStmt inputs gid rest (s.assign slot v)
  | .run index (.storeWord address value) rest, s =>
    match (do store s (← address.eval inputs gid index s) (← value.eval inputs gid index s)) with
    | .error fault => .error fault
    | .ok next => executeStmt inputs gid rest next
  | .run index (.seq a b) rest, s =>
    executeStmt inputs gid (.run index a (.run index b rest)) s
  | .run index (.whenLt a b body) rest, s =>
    match a.eval inputs gid index s with
    | .error fault => .error fault
    | .ok x =>
      match b.eval inputs gid index s with
      | .error fault => .error fault
      | .ok y =>
        if x < y then executeStmt inputs gid (.run index body rest) s
        else executeStmt inputs gid rest s
  | .run index (.forRange maximum bound body) rest, s =>
    match bound.eval inputs gid index s with
    | .error fault => .error fault
    | .ok n =>
      if _h : n.toNat ≤ maximum then executeStmt inputs gid (.iterations n.toNat 0 body rest) s
      else .error (.loopLimit n.toNat maximum)
  | .iterations 0 _ _ rest, s => executeStmt inputs gid rest s
  | .iterations (remaining + 1) next body rest, s =>
    executeStmt inputs gid (.run next body (.iterations remaining (next + 1) body rest)) s
termination_by pending _ => pending.work
decreasing_by
  all_goals first
    | exact enter_loop_lt _ _ _ _ (by assumption)
    | (simp <;> omega)
    | (simp [Nat.succ_mul] <;> omega)

/-- Execute a statement with a private stack of pending statements and loop iterations. -/
def Stmt.execTR (inputs : Inputs) (gid index : UInt32) (s : State) (stmt : Stmt) : Except Fault State :=
  executeStmt inputs gid (.run index stmt .done) s

/-- Kind: iteration simulation.
Says: consecutive scheduled iterations pass their resulting states and successive
word indices to the body in the same order as the source iterator.
Does not say: that a loop with a failing body completes all iterations. -/
private theorem iterations_cont (inputs : Inputs) (gid : UInt32) (body : Stmt)
    (hbody : ∀ index s rest, executeStmt inputs gid (.run index body rest) s =
      (body.exec inputs gid index s).bind (executeStmt inputs gid rest))
    (remaining : Nat) (next : UInt32) (s : State) (rest : Pending) :
    executeStmt inputs gid (.iterations remaining next body rest) s =
      (iterate (fun i st => body.exec inputs gid i st) remaining next s).bind (executeStmt inputs gid rest) := by
  induction remaining generalizing next s with
  | zero => rw [executeStmt] <;> rfl
  | succ remaining ih =>
    rw [executeStmt, hbody]
    change (body.exec inputs gid next s).bind
        (executeStmt inputs gid (.iterations remaining (next + 1) body rest)) =
      ((body.exec inputs gid next s).bind (fun st =>
        iterate (fun i st => body.exec inputs gid i st) remaining (next + 1) st)).bind
          (executeStmt inputs gid rest)
    cases body.exec inputs gid next s with
    | error fault => rfl
    | ok st => exact ih (next + 1) st

/-- Kind: statement simulation.
Says: starting a statement with any pending work passes the same resulting state
to that work or returns the source statement's first fault.
Does not say: that a caller supplied a bounded program or a particular initial state. -/
private theorem stmt_cont (inputs : Inputs) (gid : UInt32) (stmt : Stmt) (index : UInt32)
    (s : State) (rest : Pending) : executeStmt inputs gid (.run index stmt rest) s =
      (stmt.exec inputs gid index s).bind (executeStmt inputs gid rest) := by
  induction stmt generalizing index s rest with
  | assign slot value =>
    rw [executeStmt, Stmt.exec]
    cases value.eval inputs gid index s <;> rfl
  | storeWord address value =>
    rw [executeStmt, Stmt.exec] <;> cases address.eval inputs gid index s with
    | error fault => rfl
    | ok i =>
      cases value.eval inputs gid index s with
      | error fault => rfl
      | ok v =>
        change (match store s i v with
          | .error fault => .error fault
          | .ok next => executeStmt inputs gid rest next) =
            (store s i v).bind (executeStmt inputs gid rest)
        cases store s i v <;> rfl
  | seq a b ha hb =>
    rw [executeStmt, ha]
    change (a.exec inputs gid index s).bind (executeStmt inputs gid (.run index b rest)) =
      ((a.exec inputs gid index s).bind (fun st => b.exec inputs gid index st)).bind (executeStmt inputs gid rest)
    cases a.exec inputs gid index s with
    | error fault => rfl
    | ok st => exact hb index st rest
  | whenLt a b body ih =>
    rw [executeStmt, Stmt.exec]
    cases a.eval inputs gid index s with
    | error fault => rfl
    | ok x =>
      cases b.eval inputs gid index s with
      | error fault => rfl
      | ok y =>
        change (if x < y then executeStmt inputs gid (.run index body rest) s else executeStmt inputs gid rest s) =
          (if x < y then body.exec inputs gid index s else .ok s).bind (executeStmt inputs gid rest)
        by_cases h : x < y
        · simp only [if_pos h]
          exact ih index s rest
        · simp only [if_neg h] <;> rfl
  | forRange maximum bound body ih =>
    rw [executeStmt, Stmt.exec]
    cases bound.eval inputs gid index s with
    | error fault => rfl
    | ok n =>
      change (if n.toNat ≤ maximum then executeStmt inputs gid (.iterations n.toNat 0 body rest) s
        else .error (.loopLimit n.toNat maximum)) =
          (if n.toNat ≤ maximum then iterate (fun i st => body.exec inputs gid i st) n.toNat 0 s
            else .error (.loopLimit n.toNat maximum)).bind (executeStmt inputs gid rest)
      by_cases h : n.toNat ≤ maximum
      · simp only [if_pos h]
        exact iterations_cont inputs gid body ih n.toNat 0 s rest
      · simp only [if_neg h] <;> rfl

/-- Kind: executable equivalence.
Says: every statement produces the same locals and destination or the same first
fault, including loop-limit refusals, for arbitrary inputs, indices and state.
Does not say: that native code or a device implements the machine with a fixed resource bound. -/
@[csimp] theorem Stmt.exec_eq_execTR : @Stmt.exec = @Stmt.execTR := by
  funext inputs gid index s stmt
  unfold Stmt.execTR
  rw [stmt_cont]
  cases stmt.exec inputs gid index s with
  | error fault => rfl
  | ok next =>
    change Except.ok next = executeStmt inputs gid .done next
    rw [executeStmt]

#print axioms Stmt.exec_eq_execTR

/-- Kind: storage semantics.
Says: a present word at the addressed slot is the value of the checked input read.
Does not say: that an external binding contains the intended packet. -/
theorem read_ok (inputs : Inputs) (b : Binding) (i v : UInt32)
    (h : (inputs.get b)[i.toNat]? = some v) : read inputs b i = .ok v := by
  unfold read CountTarget.loadWord
  rw [h] <;> rfl

/-- Kind: storage semantics.
Says: an in-bounds target store updates the addressed array slot and preserves the locals.
Does not say: that another dispatch observes this write. -/
theorem store_ok (s : State) (i v : UInt32) (h : i.toNat < s.dst.size) :
    store s i v = .ok {s with dst := s.dst.set i.toNat v h} := by
  simp [store, CountTarget.storeWord, h]

/-- Kind: finite buffer representation.
Says: observing any encoded word array after an in-bounds store changes only that
address, also when the observation is extended with a default outside the array.
Does not say: that a store outside the extent succeeds. -/
theorem observe_set {α β : Type} (encode : α → β) (outside : α) (a : Array α)
    (i : Nat) (v : α) (hi : i < a.size) :
    (fun j => encode ((a.set i v hi)[j]?.getD outside)) =
      GpuKernel.Mem.write (fun j => encode (a[j]?.getD outside)) i (encode v) := by
  funext j
  unfold GpuKernel.Mem.write
  by_cases hj : j = i
  · subst j
    rw [Array.getElem?_set_self hi, if_pos rfl] <;> rfl
  · rw [Array.getElem?_set_ne hi (Ne.symm hj), if_neg hj]

#print axioms read_ok
#print axioms store_ok
#print axioms observe_set

end L4Factoidal.Paralliverse.LoopTarget
