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
