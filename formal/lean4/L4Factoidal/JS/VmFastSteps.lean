import L4Factoidal.JS.VmFastProofs

/-!
# Steps of `vmLoop` that the inner loop takes

Each theorem: for an instruction that `vmFastGo` (`JS/VmFast.lean`) runs, when its operands pass
the inner loop's test, one step of `vmLoop` at fuel `m + 1` is `vmLoop` at fuel `m` from the
state that the inner loop's step makes (the same next instruction, registers and heap). These
are the steps that the inner loop strings together; with them, a run of the inner loop is that
many steps of `vmLoop` with the inner loop off (`vmLoop_tickF_off`), up to fuel.

Proof method: `vmLoop.eq_def` and the instruction at `pc`, then the operand tests; no
induction. The generated equation of `vmLoop` takes a few seconds.
-/

namespace L4Factoidal.JS.VmFastSteps
open L4Factoidal.JS

variable {H : Type}

/-- Kind: step equality. Says: `jmp t` goes to `t` and changes nothing else. -/
theorem vmLoop_jmp (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (t : Nat)
    (hi : code.instrs[pc]! = .jmp t) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs = vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]

/-- Kind: step equality. Says: `add` of two number registers is the float sum in `dst`. -/
theorem vmLoop_add (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .add d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl)
        (fregs.set! (bp + d) (fregs.get! (bp + a) + fregs.get! (bp + b))) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `jnltK a k t` on a number register goes on when `a < k`, else to
`t`. -/
theorem vmLoop_jnltK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a : Nat) (k : Float) (t : Nat)
    (hi : code.instrs[pc]! = .jnltK a k t) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) < k then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: with the inner loop off, the head of a marked loop (`tickF`) is
the step of the budget, as `tick` is. -/
theorem vmLoop_tickF_off (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H)
    (hi : code.instrs[pc]! = .tickF) (hoff : h.vmFastOn = false) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs h =
      (do tick; vmLoop m cx subs code (pc + 1) bp env fr regs fregs) h := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]
  simp only [bind, EStateM.bind, VmFastProofs.vmFast_off _ _ _ _ _ _ _ _ hoff, beq_self_eq_true, ite_true]

/-- Kind: step equality. Says: `tick` with budget left and no full-heap stop takes one step of
the budget. -/
theorem vmLoop_tick (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H)
    (hi : code.instrs[pc]! = .tick) (h0 : (h.steps == 0) = false)
    (hf : (h.steps % 1024 == 0 && h.full) = false) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs h =
      vmLoop m cx subs code (pc + 1) bp env fr regs fregs { h with steps := h.steps - 1 } := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]
  simp only [bind, EStateM.bind, tick, get, getThe, MonadStateOf.get, EStateM.get, set,
    MonadStateOf.set, EStateM.set, h0, hf, Bool.false_eq_true, ite_false]

/-- Kind: step equality. Says: `getUp` of a slot that holds the name and a number puts the
number in a number register, and changes nothing else. -/
theorem vmLoop_getUp_num (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H)
    (dst hops idx : Nat) (x : String) (y : String) (v : Float)
    (hi : code.instrs[pc]! = .getUp dst hops idx x)
    (hy : (h.envs.getD (h.envUp hops env) default).names[idx]? = some y)
    (hv : (h.envs.getD (h.envUp hops env) default).vals[idx]? = some (.num v)) (hyx : (y == x) = true) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs h =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) v) h := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hy, hv, hyx, ite_true]

/-- Kind: step equality. Says: `sub` of two number registers is the float result in `dst`. -/
theorem vmLoop_sub (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .sub d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl)
        (fregs.set! (bp + d) (fregs.get! (bp + a) - fregs.get! (bp + b))) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `mul` of two number registers is the float result in `dst`. -/
theorem vmLoop_mul (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .mul d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl)
        (fregs.set! (bp + d) (fregs.get! (bp + a) * fregs.get! (bp + b))) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `div` of two number registers is the float result in `dst`. -/
theorem vmLoop_div (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .div d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl)
        (fregs.set! (bp + d) (fregs.get! (bp + a) / fregs.get! (bp + b))) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `lt` of two number registers is the boolean in `dst`. -/
theorem vmLoop_lt (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .lt d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) < fregs.get! (bp + b) then
        vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool true)) fregs
      else vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool false)) fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `gt` of two number registers is the boolean in `dst`. -/
theorem vmLoop_gt (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .gt d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) > fregs.get! (bp + b) then
        vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool true)) fregs
      else vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool false)) fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `le` of two number registers is the boolean in `dst`. -/
theorem vmLoop_le (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .le d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then
        vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool true)) fregs
      else vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool false)) fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `ge` of two number registers is the boolean in `dst`. -/
theorem vmLoop_ge (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a b : Nat)
    (hi : code.instrs[pc]! = .ge d a b) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then
        vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool true)) fregs
      else vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) (.bool false)) fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `addK` of a number register and a constant. -/
theorem vmLoop_addK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a : Nat) (k : Float)
    (hi : code.instrs[pc]! = .addK d a k) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl) (fregs.set! (bp + d) (fregs.get! (bp + a) + k)) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `subK` of a number register and a constant. -/
theorem vmLoop_subK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a : Nat) (k : Float)
    (hi : code.instrs[pc]! = .subK d a k) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl) (fregs.set! (bp + d) (fregs.get! (bp + a) - k)) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `mulK` of a number register and a constant. -/
theorem vmLoop_mulK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d a : Nat) (k : Float)
    (hi : code.instrs[pc]! = .mulK d a k) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl) (fregs.set! (bp + d) (fregs.get! (bp + a) * k)) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `jngtK a k t` on a number register. -/
theorem vmLoop_jngtK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a : Nat) (k : Float) (t : Nat)
    (hi : code.instrs[pc]! = .jngtK a k t) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) > k then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `jnleK a k t` on a number register. -/
theorem vmLoop_jnleK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a : Nat) (k : Float) (t : Nat)
    (hi : code.instrs[pc]! = .jnleK a k t) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≤ k then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `jngeK a k t` on a number register. -/
theorem vmLoop_jngeK (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a : Nat) (k : Float) (t : Nat)
    (hi : code.instrs[pc]! = .jngeK a k t) (ha : regs[bp + a]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≥ k then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha]

/-- Kind: step equality. Says: `jnlt a b t` on two number registers. -/
theorem vmLoop_jnlt (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a b t : Nat)
    (hi : code.instrs[pc]! = .jnlt a b t) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) < fregs.get! (bp + b) then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `jngt a b t` on two number registers. -/
theorem vmLoop_jngt (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a b t : Nat)
    (hi : code.instrs[pc]! = .jngt a b t) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) > fregs.get! (bp + b) then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `jnle a b t` on two number registers. -/
theorem vmLoop_jnle (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a b t : Nat)
    (hi : code.instrs[pc]! = .jnle a b t) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `jnge a b t` on two number registers. -/
theorem vmLoop_jnge (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (a b t : Nat)
    (hi : code.instrs[pc]! = .jnge a b t) (ha : regs[bp + a]! = .fl) (hb : regs[bp + b]! = .fl) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then vmLoop m cx subs code (pc + 1) bp env fr regs fregs
      else vmLoop m cx subs code t bp env fr regs fregs := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]; dsimp only; rw [ha, hb]

/-- Kind: step equality. Says: `loadF` puts the constant in a number register. -/
theorem vmLoop_loadF (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (d : Nat) (x : Float) (hi : code.instrs[pc]! = .loadF d x) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl) (fregs.set! (bp + d) x) := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]

/-- Kind: step equality. Says: `getMember` that the heap's fast read answers with a number puts
the number in a number register, and changes nothing else. -/
theorem vmLoop_getMember_num (m : Nat) (cx : Ctx) (subs : Array Stmt) (code : Code) (pc bp env : Nat)
    (fr : List VFrame) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H) (d o : Nat) (k : String) (x : Float)
    (hi : code.instrs[pc]! = .getMember d o k) (hg : h.fastGetV (vmRd regs fregs (bp + o)) k = .num x) :
    vmLoop (H := H) (m + 1) cx subs code pc bp env fr regs fregs h =
      vmLoop m cx subs code (pc + 1) bp env fr (regs.set! (bp + d) .fl) (fregs.set! (bp + d) x) h := by
  rw [vmLoop.eq_def]; dsimp only; rw [hi]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hg]

end L4Factoidal.JS.VmFastSteps
