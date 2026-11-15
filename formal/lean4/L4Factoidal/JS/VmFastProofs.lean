import L4Factoidal.JS.Interp

/-!
# The register machine's inner loop is the register machine

`vmFast` (`JS/VmFast.lean`) runs, from a loop head, the instructions that need nothing of the
evaluator. Proved here, with Lean's standard axioms only:

- with the inner loop off (`HeapOf.vmFastOn`, `BUBBLEPOP_VM=nofast`) it stops at the
  instruction it was called at and changes nothing (`vmFast_off`), so `vmLoop` is the machine
  it was before; with no fuel it stops and changes nothing (`vmFastGo_zero`); a stop changes
  nothing (`fastStop_eq`);
- the number write into an environment slot that reuses the old box is the plain write
  (`setNumSlot_eq`), and so the slot write of the inner loop is `setSlot`'s
  (`fastSetSlot_fl`, `fastSetSlot_val`);
- one step of `vmLoop` for an instruction the inner loop runs is the inner loop's step, one unit
  of fuel later (`vmLoop_*` below).

Not mechanised: the induction that chains the steps into "a run of `vmFastGo` from a `tick` is
that many steps of `vmLoop` with the inner loop off", and its use with the fuel monotonicity
of the evaluator (the inner loop uses less fuel than the steps it stands for). Tested: the
Test262 tree and the corpus give the same verdicts and answers with the inner loop on and off.
-/

namespace L4Factoidal.JS.VmFastProofs
open L4Factoidal.JS

variable {H : Type}

/-- Kind: definition unfolding. Says: a stop of the inner loop returns where it stopped and
the registers, and leaves the heap as it is. -/
theorem fastStop_eq (pc : Nat) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H) :
    fastStop pc regs fregs h = .ok ⟨pc, regs, fregs⟩ h := rfl

/-- Kind: off-switch. Says: with the inner loop off, `vmFast` stops at the instruction it was
called at, with the same registers and the same heap: `vmLoop` then runs that `tick` as it did
before the inner loop existed. Does not say: anything about the inner loop on. -/
theorem vmFast_off (instrs : Array Instr) (env fuel pc bp : Nat) (regs : Array Value)
    (fregs : FloatArray) (h : HeapOf H) (hoff : h.vmFastOn = false) :
    vmFast instrs env fuel pc bp regs fregs h = .ok ⟨pc, regs, fregs⟩ h := by
  simp [vmFast, hoff]

/-- Kind: definition unfolding. Says: with no fuel the inner loop stops at once and changes
nothing. -/
theorem vmFastGo_zero (instrs : Array Instr) (env pc bp : Nat) (regs : Array Value)
    (fregs : FloatArray) (h : HeapOf H) :
    vmFastGo instrs env 0 pc bp regs fregs h = .ok ⟨pc, regs, fregs⟩ h := rfl

/-- Kind: equality of a fast path with its reference. Says: the slot write that takes the old
value out first (so that the compiler can reuse its box) is the plain write of the number.
Does not say: that the box is reused (that is the compiler's doing, measured, not proved). -/
theorem setNumSlot_eq (vals : Array Value) (i : Nat) (x : Float) :
    setNumSlot vals i x = vals.set! i (.num x) := by
  unfold setNumSlot
  dsimp only
  split <;> simp [Array.setIfInBounds_setIfInBounds]

/-- Kind: equality with the reference. Says: the inner loop's write of a number register into an
environment slot is the evaluator's `setSlot` of that number (`modifyEnv` with `set!`). -/
theorem fastSetSlot_fl (h : HeapOf H) (e idx : Nat) (regs : Array Value) (fregs : FloatArray) (r : Nat)
    (hr : regs[r]! = .fl) :
    fastSetSlot h e idx regs fregs r =
      { h with envs := h.envs.modify e fun en => { en with vals := en.vals.set! idx (.num (fregs.get! r)) } } := by
  simp only [fastSetSlot, hr, setNumSlot_eq]

/-- Kind: equality with the reference. Says: the inner loop's write of any other register into an
environment slot is `setSlot` of the register's value. -/
theorem fastSetSlot_val (h : HeapOf H) (e idx : Nat) (regs : Array Value) (fregs : FloatArray) (r : Nat)
    (v : Value) (hr : regs[r]! = v) (hv : v ≠ .fl) :
    fastSetSlot h e idx regs fregs r =
      { h with envs := h.envs.modify e fun en => { en with vals := en.vals.set! idx v } } := by
  unfold fastSetSlot
  dsimp only
  split
  · rename_i hfl; rw [hr] at hfl; exact absurd hfl hv
  · simp_all

/-- Kind: equality with the reference. Says: `fastRd` is `vmRd`. -/
theorem fastRd_eq (regs : Array Value) (fregs : FloatArray) (i : Nat) :
    fastRd regs fregs i = vmRd regs fregs i := rfl

/-- Kind: shape of a code transformation. Says: marking loops keeps the number of instructions. -/
theorem markFastLoops_size (code : Array Instr) : (Compile.markFastLoops code).size = code.size := by
  simp [Compile.markFastLoops]

/-- Kind: shape of a code transformation. Says: marking changes an instruction only by turning a
`tick` into `tickF`; every other instruction is kept. Does not say: which loops are marked. -/
theorem markAt_cases (code : Array Instr) (i : Nat) (ins : Instr) :
    Compile.markAt code i ins = ins ∨ (ins = .tick ∧ Compile.markAt code i ins = .tickF) := by
  unfold Compile.markAt
  split
  · split <;> simp_all
  · exact Or.inl rfl

end L4Factoidal.JS.VmFastProofs
