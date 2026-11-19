import L4Factoidal.Paralliverse.DSL
import L4Factoidal.Paralliverse.PackWire

/-! # Finite-buffer count kernel

This target fragment has unsigned word instructions, a read-only input packet and a
separate writable binding. Loads and stores can fail. Programs inspect no logical rows.
WGSL text, binding creation and device execution are outside this interpreter. -/

namespace L4Factoidal.Paralliverse.CountTarget

open L4Factoidal.GpuKernel

inductive Fault where
  | readPastEnd (address : Nat)
  | writePastEnd (address : Nat)
  deriving Repr, DecidableEq

inductive Expr where
  | literal (word : UInt32)
  | globalId
  | add (a b : Expr)
  | mul (a b : Expr)
  | load (index : Expr)
  deriving Repr

inductive Stmt where
  | store (index value : Expr)
  | whenLt (a b : Expr) (body : Stmt)
  deriving Repr

def loadWord (packet : Array UInt32) (index : UInt32) : Except Fault UInt32 :=
  match packet[index.toNat]? with
  | some word => .ok word
  | none => .error (.readPastEnd index.toNat)

def storeWord (dst : Array UInt32) (index word : UInt32) : Except Fault (Array UInt32) :=
  if h : index.toNat < dst.size then .ok (dst.set index.toNat word h)
  else .error (.writePastEnd index.toNat)

def Expr.eval (packet : Array UInt32) (gid : UInt32) : Expr → Except Fault UInt32
  | .literal x => .ok x
  | .globalId => .ok gid
  | .add a b => do return (← a.eval packet gid) + (← b.eval packet gid)
  | .mul a b => do return (← a.eval packet gid) * (← b.eval packet gid)
  | .load idx => do loadWord packet (← idx.eval packet gid)

private inductive Bin where
  | plus | times

private def Bin.apply : Bin → UInt32 → UInt32 → UInt32
  | .plus => (· + ·)
  | .times => (· * ·)

/-- Private evaluation context. The first operand is evaluated before the saved right operand. -/
private inductive Kont where
  | done
  | right (op : Bin) (operand : Expr) (outer : Kont)
  | combine (op : Bin) (left : UInt32) (outer : Kont)
  | loadAt (outer : Kont)

private inductive Control where
  | evaluate (expr : Expr) (k : Kont)
  | resume (word : UInt32) (k : Kont)

-- Only the termination proof uses these weights. The interpreter never traverses
-- a supplied expression to compute fuel before beginning its first instruction.
@[simp] private noncomputable def Expr.work : Expr → Nat
  | .literal _ | .globalId => 1
  | .add a b | .mul a b => a.work + b.work + 3
  | .load i => i.work + 2

@[simp] private noncomputable def Kont.work : Kont → Nat
  | .done => 0
  | .right _ b k => b.work + 2 + k.work
  | .combine _ _ k | .loadAt k => 1 + k.work

@[simp] private noncomputable def Control.work : Control → Nat
  | .evaluate e k => e.work + k.work
  | .resume _ k => k.work

private def executeExpr (packet : Array UInt32) (gid : UInt32) : Control → Except Fault UInt32
  | .evaluate (.literal x) k => executeExpr packet gid (.resume x k)
  | .evaluate .globalId k => executeExpr packet gid (.resume gid k)
  | .evaluate (.add a b) k => executeExpr packet gid (.evaluate a (.right .plus b k))
  | .evaluate (.mul a b) k => executeExpr packet gid (.evaluate a (.right .times b k))
  | .evaluate (.load i) k => executeExpr packet gid (.evaluate i (.loadAt k))
  | .resume v .done => .ok v
  | .resume a (.right op b k) => executeExpr packet gid (.evaluate b (.combine op a k))
  | .resume b (.combine op a k) => executeExpr packet gid (.resume (op.apply a b) k)
  | .resume i (.loadAt k) =>
    match loadWord packet i with
    | .error fault => .error fault
    | .ok v => executeExpr packet gid (.resume v k)
termination_by state => state.work
decreasing_by all_goals simp <;> omega

/-- Evaluate any count-fragment expression with an explicit continuation stack. -/
def Expr.evalTR (packet : Array UInt32) (gid : UInt32) (e : Expr) : Except Fault UInt32 :=
  executeExpr packet gid (.evaluate e .done)

/-- Kind: expression simulation.
Says: binary continuations apply the same unsigned operation to the same
left and right results, preserving the order of any faults.
Does not say: that either operand must be in bounds. -/
private theorem binary_cont (packet : Array UInt32) (gid : UInt32) (op : Bin) (a b : Expr) (k : Kont)
    (ha : ∀ q, executeExpr packet gid (.evaluate a q) =
      (a.eval packet gid).bind (fun x => executeExpr packet gid (.resume x q)))
    (hb : ∀ q, executeExpr packet gid (.evaluate b q) =
      (b.eval packet gid).bind (fun x => executeExpr packet gid (.resume x q))) :
    executeExpr packet gid (.evaluate a (.right op b k)) =
      ((do return op.apply (← a.eval packet gid) (← b.eval packet gid)) : Except Fault UInt32).bind
        (fun x => executeExpr packet gid (.resume x k)) := by
  rw [ha]
  cases a.eval packet gid with
  | error fault => rfl
  | ok left =>
    change executeExpr packet gid (.resume left (.right op b k)) = _
    rw [executeExpr, hb]
    cases b.eval packet gid with
    | error fault => rfl
    | ok right =>
      change executeExpr packet gid (.resume right (.combine op left k)) =
        executeExpr packet gid (.resume (op.apply left right) k)
      rw [executeExpr]

/-- Kind: expression simulation.
Says: evaluating any expression with any pending continuation produces exactly the
structural result passed to that continuation, including the original read fault.
Does not say: that interpreting an arbitrary expression uses bounded heap space. -/
private theorem execute_cont (packet : Array UInt32) (gid : UInt32) (e : Expr) (k : Kont) :
    executeExpr packet gid (.evaluate e k) =
      (e.eval packet gid).bind (fun v => executeExpr packet gid (.resume v k)) := by
  induction e generalizing k with
  | literal x => rw [executeExpr] <;> rfl
  | globalId => rw [executeExpr] <;> rfl
  | add a b ha hb =>
    rw [executeExpr]
    exact binary_cont packet gid .plus a b k ha hb
  | mul a b ha hb =>
    rw [executeExpr]
    exact binary_cont packet gid .times a b k ha hb
  | load i ih =>
    change executeExpr packet gid (.evaluate (.load i) k) =
      ((i.eval packet gid).bind (fun j => loadWord packet j)).bind
        (fun v => executeExpr packet gid (.resume v k))
    rw [executeExpr, ih]
    cases i.eval packet gid with
    | error fault => rfl
    | ok index =>
      change executeExpr packet gid (.resume index (.loadAt k)) =
        (loadWord packet index).bind (fun v => executeExpr packet gid (.resume v k))
      rw [executeExpr]
      cases loadWord packet index <;> rfl

/-- Kind: executable equivalence.
Says: the continuation machine and structural evaluator return the same word or
the same fault for every packet, global ID and expression.
Does not say: that a compiler produces a native jump or a particular stack limit. -/
@[csimp] theorem Expr.eval_eq_evalTR : @Expr.eval = @Expr.evalTR := by
  funext packet gid e
  unfold Expr.evalTR
  rw [execute_cont]
  cases e.eval packet gid with
  | error fault => rfl
  | ok v =>
    change Except.ok v = executeExpr packet gid (.resume v .done)
    rw [executeExpr]

#print axioms Expr.eval_eq_evalTR

def Stmt.exec (packet : Array UInt32) (gid : UInt32) (dst : Array UInt32) :
    Stmt → Except Fault (Array UInt32)
  | .store idx value => do storeWord dst (← idx.eval packet gid) (← value.eval packet gid)
  | .whenLt a b body => do
    if (← a.eval packet gid) < (← b.eval packet gid) then body.exec packet gid dst
    else return dst

/-- The version 1 packet puts the row count in word 1 and the length of descriptor i
in word 4 + 2*i. Only active invocations read descriptors or touch the destination. -/
def lowerCount : DSL.Stage .input .counted → Stmt
  | .count =>
    .whenLt .globalId (.load (.literal 1))
      (.store .globalId (.load (.add (.literal 4) (.mul (.literal 2) .globalId))))

/-- Interpretation of source descriptor words. These facts refer only to the input
packet and logical rows; the initial and final count buffers do not occur here. -/
structure SourceRows (packet : Array UInt32) (rows : StaticPack.Rows) : Prop where
  limit : rows.length ≤ PackWire.maxRows
  header : (packet[1]?).map UInt32.toNat = some rows.length
  lengths : ∀ i, i < rows.length →
    (packet[4 + 2*i]?).map UInt32.toNat = some (rows.getD i []).length

/-- Observe the finite destination as natural-valued words. Zero extends the memory
outside its finite extent only for the logical comparison. Target accesses use checks. -/
def memory (a : Array UInt32) : Mem Nat := fun i => (a[i]?.getD 0).toNat

/-- Kind: arithmetic refinement.
Says: for active packet lanes the target's multiplication and addition give the
descriptor length's natural word address.
Does not say: that a particular packet contains the addressed word. -/
theorem descriptor_word_address (gid : UInt32) (h : gid.toNat < PackWire.maxRows) :
    (4 + 2 * gid : UInt32).toNat = 4 + 2 * gid.toNat := by
  change gid.toNat < 128 at h
  have hm : 2 * gid.toNat < 4294967296 := by omega
  have ha : 4 + 2 * gid.toNat < 4294967296 := by omega
  rw [UInt32.toNat_add, UInt32.toNat_mul]
  change (4 + ((2 * gid.toNat) % 4294967296)) % 4294967296 = _
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt ha]

/-- Kind: representation lemma.
Says: one checked finite-array store changes precisely the corresponding logical word.
Does not say: the destination fits a physical device. -/
private theorem memory_set (a : Array UInt32) (i : Nat) (word : UInt32) (hi : i < a.size) :
    memory (a.set i word hi) = (memory a).write i word.toNat := by
  funext j
  change ((a.set i word hi)[j]?.getD 0).toNat =
    if j = i then word.toNat else (a[j]?.getD 0).toNat
  by_cases hj : j = i
  · subst j
    rw [Array.getElem?_set_self hi, if_pos rfl] <;> rfl
  · rw [Array.getElem?_set_ne hi (Ne.symm hj), if_neg hj]

/-- Kind: target evaluation.
Says: when its header load succeeds, the lowered instruction tree branches on the
header and executes the guarded descriptor load and store.
Does not say: that an active invocation's read and write are in bounds. -/
private theorem exec_header (packet dst : Array UInt32) (gid n : UInt32)
    (hn : loadWord packet 1 = .ok n) :
    (lowerCount .count).exec packet gid dst =
      if gid < n then (loadWord packet (4 + 2 * gid)).bind (fun word => storeWord dst gid word)
      else .ok dst := by
  change (loadWord packet 1).bind (fun word =>
    if gid < word then (loadWord packet (4 + 2 * gid)).bind (fun v => storeWord dst gid v)
    else .ok dst) = _
  simp only [hn, Except.bind]

/-- Kind: instruction-level refinement.
Says: every physical u32 lane executes without a fault given valid source words
and count capacity. It writes its own descriptor length if active and otherwise
preserves the entire destination.
Does not say: that active lanes have all run or that device bindings are separate. -/
theorem count_lane (packet prior : Array UInt32) (rows : StaticPack.Rows)
    (src : SourceRows packet rows) (cap : rows.length ≤ prior.size) (gid : UInt32) :
    ∃ out, (lowerCount .count).exec packet gid prior = .ok out ∧
      out.size = prior.size ∧ memory out =
        if gid.toNat < rows.length then (memory prior).write gid.toNat (rows.getD gid.toNat []).length
        else memory prior := by
  obtain ⟨n, hn, hnVal⟩ := Option.map_eq_some_iff.mp src.header
  have header : loadWord packet 1 = .ok n := by
    change (match packet[1]? with
      | some v => Except.ok v
      | none => Except.error (Fault.readPastEnd 1)) = _
    rw [hn]
  have branch : (gid < n) ↔ gid.toNat < rows.length := by rw [UInt32.lt_iff_toNat_lt, hnVal]
  by_cases active : gid.toNat < rows.length
  · obtain ⟨w, hw, hwVal⟩ := Option.map_eq_some_iff.mp (src.lengths _ active)
    have addr := descriptor_word_address gid (Nat.lt_of_lt_of_le active src.limit)
    have loaded : loadWord packet (4 + 2 * gid) = .ok w := by
      unfold loadWord
      rw [addr, hw]
    have dest := Nat.lt_of_lt_of_le active cap
    refine ⟨prior.set gid.toNat w dest, ?_, by simp, ?_⟩
    · rw [exec_header packet prior gid n header, if_pos (branch.mpr active), loaded]
      change storeWord prior gid w = _
      exact dif_pos dest
    · rw [if_pos active, memory_set, hwVal]
  · refine ⟨prior, ?_, rfl, ?_⟩
    · rw [exec_header packet prior gid n header, if_neg (fun h => active (branch.mp h))]
    · rw [if_neg active]

/-- Execute the same target code for the supplied sequence of physical invocations.
Every instruction tree reads the immutable packet and receives the current finite
destination. An instruction fault stops the dispatch. -/
def dispatch (code : Stmt) (packet : Array UInt32) :
    List UInt32 → Array UInt32 → Except Fault (Array UInt32)
  | [], dst => .ok dst
  | gid :: rest, dst => do
    let next ← code.exec packet gid dst
    dispatch code packet rest next

def activeOrder (n : Nat) (lanes : List UInt32) : List Nat :=
  (lanes.map UInt32.toNat).filter (fun i => decide (i < n))

/-- Kind: dispatch simulation.
Says: even a partial or repeated sequence of target invocations terminates without
fault and agrees at every output address with the DSL count dispatch on its active IDs.
Does not say: that a partial sequence has counted every row. -/
theorem dispatch_count (packet prior : Array UInt32) (rows : StaticPack.Rows)
    (src : SourceRows packet rows) (cap : rows.length ≤ prior.size) (lanes : List UInt32) :
    ∃ out, dispatch (lowerCount .count) packet lanes prior = .ok out ∧
      out.size = prior.size ∧
      memory out = (DSL.countDispatch rows).runOrder (memory prior) (activeOrder rows.length lanes) := by
  induction lanes generalizing prior with
  | nil => exact ⟨prior, rfl, rfl, rfl⟩
  | cons gid rest ih =>
    obtain ⟨next, step, size, effect⟩ := count_lane packet prior rows src cap gid
    have nextCap : rows.length ≤ next.size := by rw [size]; exact cap
    obtain ⟨out, remaining, finalSize, finalMem⟩ := ih next nextCap
    refine ⟨out, ?_, finalSize.trans size, ?_⟩
    · rw [dispatch, step]
      exact remaining
    · by_cases active : gid.toNat < rows.length
      · have order : activeOrder rows.length (gid :: rest) =
            gid.toNat :: activeOrder rows.length rest := by simp [activeOrder, active]
        rw [finalMem, effect, if_pos active, order]
        simp [Dispatch.runOrder, DSL.countDispatch, applyWrites]
      · have order : activeOrder rows.length (gid :: rest) =
            activeOrder rows.length rest := by simp [activeOrder, active]
        rw [finalMem, effect, if_neg active, order]

/-- One-dimensional launch at a static workgroup size of 64. Zero rows need no groups. -/
def grid (n : Nat) : Nat := ((n + 63) / 64) * 64

def ValidGrid (n : Nat) (lanes : List UInt32) : Prop :=
  (lanes.map UInt32.toNat).Perm (List.range (grid n))

def canonicalLanes (n : Nat) : List UInt32 := (List.range (grid n)).map UInt32.ofNat

/-- Kind: physical launch bound.
Says: the rounded launch covers every row and has at most 128 lanes on an admitted packet.
Does not say: that a host submitted this geometry. -/
theorem grid_bounds (n : Nat) (h : n ≤ PackWire.maxRows) : n ≤ grid n ∧ grid n ≤ 128 := by
  change n ≤ 128 at h
  unfold grid
  omega

/-- Kind: schedule existence.
Says: the increasing order of physical word IDs satisfies the scheduling premise
on every admitted row count, including zero.
Does not say: that target invocations execute in this order. -/
theorem canonical_valid (n : Nat) (h : n ≤ PackWire.maxRows) : ValidGrid n (canonicalLanes n) := by
  apply List.Perm.of_eq
  apply List.ext_getElem
  · simp [canonicalLanes]
  · intro i _ hi
    have good : i < grid n := by simpa using hi
    have bound := (grid_bounds n h).2
    simp only [canonicalLanes, List.getElem_map, List.getElem_range]
    apply UInt32.toNat_ofNat_of_lt'
    change i < 4294967296
    omega

/-- Kind: index arithmetic.
Says: removing padded IDs from a covering increasing range yields exactly the active IDs.
Does not say: that physical lanes run in increasing order. -/
private theorem active_range (n m : Nat) (h : n ≤ m) :
    (List.range m).filter (fun i => decide (i < n)) = List.range n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero =>
    apply List.filter_eq_self.mpr
    intro i hi
    exact decide_eq_true (List.mem_range.mp hi)
  | succ k ih =>
    have inactive : ¬ n + k < n := by omega
    rw [Nat.add_succ, List.range_succ, List.filter_append, ih (by omega)]
    simp [inactive]

/-- Kind: launch schedule refinement.
Says: removing padded lanes from a valid finite launch leaves exactly one copy
of every active row ID, in some order.
Does not say: which order a device uses or when its writes become visible. -/
theorem activeOrder_perm {n : Nat} {lanes : List UInt32}
    (bound : n ≤ PackWire.maxRows) (order : ValidGrid n lanes) :
    (activeOrder n lanes).Perm (List.range n) := by
  have active := List.Perm.filter (fun i => decide (i < n)) order
  rw [active_range _ _ (grid_bounds _ bound).1] at active
  exact active

/-- Kind: finite target refinement.
Says: on every permitted ordering of the padded physical launch, count finishes
without a buffer fault. The entire resulting finite destination, including any
allocated tail, agrees word for word with the DSL's complete count dispatch.
Does not say: that byte decoding, shader text, physical binding separation, device
scheduling or a shader compiler implements this instruction interpreter. -/
theorem count_grid_eq_dsl (packet prior : Array UInt32) (rows : StaticPack.Rows)
    (src : SourceRows packet rows) (cap : rows.length ≤ prior.size) (lanes : List UInt32)
    (order : ValidGrid rows.length lanes) :
    ∃ out, dispatch (lowerCount .count) packet lanes prior = .ok out ∧
      out.size = prior.size ∧ memory out = (DSL.countDispatch rows).runSeq (memory prior) := by
  obtain ⟨out, run, size, effect⟩ := dispatch_count packet prior rows src cap lanes
  have active := List.Perm.filter (fun i => decide (i < rows.length)) order
  rw [active_range _ _ (grid_bounds _ src.limit).1] at active
  exact ⟨out, run, size, effect.trans
    ((DSL.countDispatch rows).runOrder_perm (DSL.count_raceFree rows) _ active (memory prior))⟩

#print axioms descriptor_word_address
#print axioms count_lane
#print axioms dispatch_count
#print axioms grid_bounds
#print axioms canonical_valid
#print axioms activeOrder_perm
#print axioms count_grid_eq_dsl

end L4Factoidal.Paralliverse.CountTarget
