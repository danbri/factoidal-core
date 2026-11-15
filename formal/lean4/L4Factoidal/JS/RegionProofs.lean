import L4Factoidal.JS.Interp

/-!
# Region code: what is proved

Region code (`Code.region`, `Compile.compileRegion`) is a function body run by the register
machine with its variables in the evaluator's environments. The resolver puts the body in one
statement, `Stmt.compiled c (.block body) subs`. These theorems are about that wrapper and
about the environment instructions; the instructions' agreement with the evaluator as a whole
(`compile_correct`) is not proved here, it is tested (Test262 and the corpus with the machine
on and off, verdict by verdict).

- `compiled_off`, `compiled_noregion`: with the machine off for the run (`HeapOf.useVm`), or
  with region code off (`HeapOf.vmRegions`), the wrapper is the statement it stands for, one
  unit of fuel later: the reference run with the machine off is the evaluator on the body.
- `block_is_body`: the wrapped body as a block is `evalBody`, the function body the evaluator
  would run without the wrapper, at the same fuel.
- `enterBlock_plain`: a list with no lexical declaration (the one-statement list of the
  wrapper) makes no environment, so the evaluator's own `evalBody` of the wrapper costs only
  fuel.
- `pushEnv_get`, `pushEnv_parent`: the environment that `newEnv`, `copyEnv` and `enterBlock`
  push is at the number they answer, with the parent they gave it, when the free list is in
  bounds. So `popEnv` (the parent becomes the running environment) after `newEnv p` returns to
  `p`: the step on which region code's block and loop environments rely.
-/

namespace L4Factoidal.JS.RegionProofs
open L4Factoidal.JS

variable {H : Type}

theorem compiled_off (k : Nat) (ctx : Ctx) (labels : List String) (c : Code) (s : Stmt)
    (subs : Array Stmt) (h : HeapOf H) (hoff : h.useVm = false) :
    evalStmt (H := H) (k + 1) ctx labels (.compiled c s subs) h = evalStmt k ctx labels s h := by
  show (do
      if (← get).useVm then
        if c.region then
          if (← get).vmRegions then vmRegion k c ctx subs else evalStmt k ctx labels s
        else
          let _ ← vmEnter k c ctx.env ctx.thisV ctx.thisV #[]
          pure .normal
      else evalStmt k ctx labels s : JSM H Compl) h = _
  simp [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hoff]

theorem compiled_noregion (k : Nat) (ctx : Ctx) (labels : List String) (c : Code) (s : Stmt)
    (subs : Array Stmt) (h : HeapOf H) (hreg : c.region = true) (hoff : h.vmRegions = false) :
    evalStmt (H := H) (k + 1) ctx labels (.compiled c s subs) h = evalStmt k ctx labels s h := by
  show (do
      if (← get).useVm then
        if c.region then
          if (← get).vmRegions then vmRegion k c ctx subs else evalStmt k ctx labels s
        else
          let _ ← vmEnter k c ctx.env ctx.thisV ctx.thisV #[]
          pure .normal
      else evalStmt k ctx labels s : JSM H Compl) h = _
  cases hv : h.useVm <;>
    simp [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hv, hreg, hoff]

theorem block_is_body (m : Nat) (ctx : Ctx) (labels : List String) (ss : List Stmt) :
    evalStmt (H := H) (m + 1) ctx labels (.block ss) = evalBody m ctx ss := by
  match m with
  | 0 => rfl
  | _ + 1 => rfl

theorem enterBlock_plain (m : Nat) (ctx : Ctx) (ss : List Stmt)
    (hl : ss.any Stmt.isLexical = false) :
    enterBlock (H := H) (m + 1) ctx ss = pure ctx := by
  show (do
      let needs := ss.any Stmt.isLexical
      if !needs then return ctx
      let env ← newEnv ctx.env
      let ctx' := { ctx with env }
      declareLexical m ctx' ss
      return ctx' : JSM H Ctx) = _
  simp [hl]

/-- The free list holds slots of the environment array (an invariant of the heap that
`releaseEnv` keeps when it releases a slot in bounds). -/
def freeInBounds (h : HeapOf H) : Prop := ∀ e, h.envFree.back? = some e → e < h.envs.size

theorem pushEnv_get (en : Env) (h : HeapOf H) (hf : freeInBounds h) :
    ∃ r h', (pushEnv en : JSM H Nat) h = .ok r h' ∧ h'.envs.getD r default = en := by
  unfold pushEnv
  simp only [modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  cases hb : h.envFree.back? with
  | none => exact ⟨_, _, rfl, by simp [Array.getD]⟩
  | some e =>
    have he := hf e hb
    refine ⟨_, _, rfl, ?_⟩
    simp [Array.getD, Array.set!, he]

theorem pushEnv_parent (p : Nat) (h : HeapOf H) (hf : freeInBounds h) :
    ∃ r h', (newEnv p : JSM H Nat) h = .ok r h' ∧ (h'.envs.getD r default).parent = p := by
  obtain ⟨r, h', hr, hg⟩ := pushEnv_get (H := H) { parent := p } h hf
  exact ⟨r, h', hr, by rw [hg]⟩

#print axioms compiled_off
#print axioms compiled_noregion
#print axioms block_is_body
#print axioms enterBlock_plain
#print axioms pushEnv_get
#print axioms pushEnv_parent

end L4Factoidal.JS.RegionProofs
