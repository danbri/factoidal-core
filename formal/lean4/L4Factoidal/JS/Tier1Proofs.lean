import L4Factoidal.JS.Interp

/-!
# Tier 1 of the BubblePopJS JIT is equal to the interpreter

The reference is the evaluator of `JS/Interp.lean`. For each node that `JS/Tier1.lean` makes:

- `incLocal_eq`: `evalExpr n ctx (incLocal pre inc x hops idx)` equals
  `evalExpr n ctx (update pre inc (local x hops idx))`;
- `setLocal_eq`: `evalExpr n ctx (setLocal x hops idx rhs)` equals
  `evalExpr n ctx (assign none (local x hops idx) rhs)`, for `rhs` not a function expression;
- `blockN_eq`: `evalStmt n ctx labels (blockN ss)` equals `evalStmt n ctx labels (block ss)`,
  for `ss` that declares nothing lexical.

Each is an equality of functions of the heap in `EStateM Abrupt Heap`, for every fuel `n`: the
same value or abrupt completion (a thrown value, a halt for fuel, steps or a full heap) and the
same heap. The fuel is mirrored, so a run that ends for fuel ends at the same point.

`tE_incLocal`, `tE_setLocal`, `tS_blockN`: the pass makes each node only from the node its
theorem names, under that theorem's side condition.

What is not mechanised: the step from these local equalities to "a whole run with tier 1 equals
a whole run without it". Each node's equality holds with the same evaluator for its children,
and the evaluator is the unique function of its structural recursion on fuel, so the step is an
induction on fuel over the whole mutual block (`docs/bubblepopjs-jit.md`, "From local lemmas to
the whole run"). It is tested: Test262 with and without tier 1, verdict by verdict.
-/

namespace L4Factoidal.JS.Tier1Proofs
open L4Factoidal.JS

variable {H : Type}

theorem evalBlock_succ (m : Nat) (ctx : Ctx) (ss : List Stmt) :
    evalBlock (H := H) (m + 1) ctx ss = (do let ctx ← enterBlock m ctx ss; evalStmts m ctx ss) := rfl

theorem enterBlock_succ (m : Nat) (ctx : Ctx) (ss : List Stmt) :
    enterBlock (H := H) (m + 1) ctx ss = (do
      let needs := ss.any Stmt.isLexical
      if !needs then return ctx
      let env ← newEnv ctx.env
      let ctx' := { ctx with env }
      declareLexical m ctx' ss
      return ctx') := rfl

theorem blockN_eq (n : Nat) (ctx : Ctx) (labels : List String) (ss : List Stmt)
    (h : Tier1.lexical ss = false) :
    evalStmt (H := H) n ctx labels (.blockN ss) = evalStmt n ctx labels (.block ss) := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => funext hp; rfl
  | m + 3 =>
    show evalStmts (H := H) (m + 1) ctx ss = evalBlock (m + 2) ctx ss
    rw [evalBlock_succ, enterBlock_succ]
    simp only [Tier1.lexical] at h
    simp only [h, Bool.not_false]
    rfl

theorem lookupLocal_succ (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) :
    lookupLocal (H := H) (m + 1) ctx x hops idx = (do
      let h ← get
      let env := h.envs.getD (h.envUp hops ctx.env) default
      match env.names[idx]?, env.vals[idx]? with
      | some y, some v =>
        if y == x then
          match v with
          | .hole => throwErr .reference s!"Cannot access '{x}' before initialization"
          | _ =>
            if verifyLocals then
              let w ← lookup m ctx x
              if !sameValue v w then throw (.halt s!"verifyLocals: {x} {hops} {idx}")
            pure v
        else lookup m ctx x
      | _, _ => lookup m ctx x) := rfl

theorem assignLocal_succ (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (v : Value) :
    assignLocal (H := H) (m + 1) ctx x hops idx v = (do
      let h ← get
      let e := h.envUp hops ctx.env
      let env := h.envs.getD e default
      match env.names[idx]?, env.vals[idx]? with
      | some y, some old =>
        if y == x then
          if let .hole := old then throwErr .reference s!"Cannot access '{x}' before initialization"
          if !env.mutableAt idx then
            if !ctx.strict && fnNameScope h e x then return
            throwErr .type "Assignment to constant variable."
          if verifyLocals then
            if (h.findEnv x 100000 ctx.env) != some e then throw (.halt s!"verifyLocals: {x} {hops} {idx}")
          setSlot e idx v
        else assignName m ctx x v
      | _, _ => assignName m ctx x v) := rfl

/-- The fast read of `incLocal` is the read of `lookupLocal`, with no change to the heap. -/
theorem lookupLocal_of_slotNum (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat)
    (hp : HeapOf H) (e : Nat) (old : Float) (hs : slotNum? hp ctx x hops idx = some (e, old)) :
    lookupLocal (H := H) (m + 1) ctx x hops idx hp = .ok (.num old) hp := by
  rw [lookupLocal_succ]
  unfold slotNum? at hs
  dsimp only at hs
  split at hs
  · rename_i y o hn hv
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases hs
      obtain ⟨rfl, -⟩ := hc
      simp_all [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, verifyLocals, pure]
      rfl
    · cases hs
  · cases hs

/-- The fast write of `incLocal` and `setLocal` is the write of `assignLocal`. -/
theorem assignLocal_of_slotSet (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (v : Value)
    (hp : HeapOf H) (e : Nat) (hs : slotSet? hp ctx x hops idx = some e) :
    assignLocal (H := H) (m + 1) ctx x hops idx v hp = setSlot e idx v hp := by
  rw [assignLocal_succ]
  unfold slotSet? at hs
  dsimp only at hs
  split at hs
  · cases hs
  · rename_i y o hn hv hnh
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases hs
      cases o <;> simp_all [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, verifyLocals]
    · cases hs
  · cases hs

theorem slotSet_of_slotNum (hp : HeapOf H) (ctx : Ctx) (x : String) (hops idx e : Nat) (old : Float)
    (hs : slotNum? hp ctx x hops idx = some (e, old)) : slotSet? hp ctx x hops idx = some e := by
  unfold slotNum? at hs
  unfold slotSet?
  dsimp only at hs ⊢
  split at hs
  · rename_i y o hn hv
    split at hs
    · rename_i hc
      cases hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, hm⟩ := hc
      simp_all
    · cases hs
  · cases hs

/-- The plain evaluation of `update pre inc (local x hops idx)`, one step unfolded. -/
theorem update_local_succ (n : Nat) (ctx : Ctx) (pre inc : Bool) (x : String) (hops idx : Nat) :
    evalExpr (H := H) (n + 1) ctx (.update pre inc (.local x hops idx)) = (do
      match ← lookupLocal n ctx x hops idx with
      | .num old =>
        let nv := if inc then old + 1 else old - 1
        assignLocal n ctx x hops idx (.num nv)
        pure (.num (if pre then nv else old))
      | p =>
        match ← toPrim n p "number" with
        | .big big =>
          let nv := if inc then big + 1 else big - 1
          assignLocal n ctx x hops idx (.big nv)
          pure (.big (if pre then nv else big))
        | p =>
          let old ← toNum n p
          let nv := if inc then old + 1 else old - 1
          assignLocal n ctx x hops idx (.num nv)
          pure (.num (if pre then nv else old))) := rfl

/-- `incLocal`, one step unfolded: the fast path, else the plain evaluation of the node it
stands for. -/
theorem incLocal_succ (n : Nat) (ctx : Ctx) (pre inc : Bool) (x : String) (hops idx : Nat) :
    evalExpr (H := H) (n + 1) ctx (.incLocal pre inc x hops idx) = (do
      match n, slotNum? (← get) ctx x hops idx with
      | _ + 1, some (e, old) =>
        let nv := if inc then old + 1 else old - 1
        setSlot e idx (.num nv)
        pure (.num (if pre then nv else old))
      | _, _ => evalExpr (n + 1) ctx (.update pre inc (.local x hops idx))) := rfl

/-- **Tier 1, `incLocal`.** For every fuel, context and heap, the evaluator on `incLocal` gives
what it gives on `update pre inc (local x hops idx)`: the same value or abrupt completion and
the same heap. -/
theorem incLocal_eq (n : Nat) (ctx : Ctx) (pre inc : Bool) (x : String) (hops idx : Nat) :
    evalExpr (H := H) n ctx (.incLocal pre inc x hops idx) =
      evalExpr n ctx (.update pre inc (.local x hops idx)) := by
  match n with
  | 0 => rfl
  | n + 1 =>
    rw [incLocal_succ]
    funext hp
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    rcases n with _ | m
    · rfl
    · rcases hs : slotNum? hp ctx x hops idx with _ | ⟨e, old⟩
      · rfl
      · dsimp only
        rw [update_local_succ]
        simp only [bind, EStateM.bind]
        rw [lookupLocal_of_slotNum m ctx x hops idx hp e old hs]
        dsimp only
        simp only [EStateM.bind]
        rw [assignLocal_of_slotSet m ctx x hops idx _ hp e (slotSet_of_slotNum hp ctx x hops idx e old hs)]

/-- The plain evaluation of `assign none (local x hops idx) rhs`, two steps unfolded, when `rhs`
is not a function expression (which the assignment would name). -/
theorem assign_local_succ (j : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (rhs : Expr)
    (hr : ∀ f, rhs ≠ .func f) :
    evalExpr (H := H) (j + 2) ctx (.assign none (.local x hops idx) rhs) = (do
      let v ← evalExpr (j + 1) ctx rhs
      assignLocal j ctx x hops idx v
      pure v) := by
  cases rhs <;> first | exact absurd rfl (hr _) | rfl

theorem setLocal_succ (j : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (rhs : Expr) :
    evalExpr (H := H) (j + 2) ctx (.setLocal x hops idx rhs) = (do
      let v ← evalExpr (j + 1) ctx rhs
      match j, slotSet? (← get) ctx x hops idx with
      | _ + 1, some e => setSlot e idx v; pure v
      | _, _ => assignLocal j ctx x hops idx v; pure v) := rfl

/-- **Tier 1, `setLocal`.** For every fuel, context and heap, the evaluator on `setLocal` gives
what it gives on `assign none (local x hops idx) rhs`, for `rhs` not a function expression. -/
theorem setLocal_eq (n : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (rhs : Expr)
    (hr : ∀ f, rhs ≠ .func f) :
    evalExpr (H := H) n ctx (.setLocal x hops idx rhs) =
      evalExpr n ctx (.assign none (.local x hops idx) rhs) := by
  match n with
  | 0 => rfl
  | 1 => funext hp; rfl
  | j + 2 =>
    rw [setLocal_succ, assign_local_succ j ctx x hops idx rhs hr]
    funext hp
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get]
    rcases evalExpr (H := H) (j + 1) ctx rhs hp with ⟨v, hp'⟩ | ⟨err, hp'⟩
    · dsimp only
      rcases j with _ | m
      · rfl
      · rcases hs : slotSet? hp' ctx x hops idx with _ | e
        · rfl
        · dsimp only
          simp only [EStateM.bind]
          rw [assignLocal_of_slotSet m ctx x hops idx v hp' e hs]
    · rfl

/-! ## The pass makes each node only where its theorem applies -/

/-- An `incLocal` that the pass makes stands for `update pre inc (local x hops idx)`. -/
theorem tE_incLocal {n : Nat} {e : Expr} {pre inc : Bool} {x : String} {hops idx : Nat}
    (hT : Tier1.tE (n + 1) e = .incLocal pre inc x hops idx) :
    e = .update pre inc (.local x hops idx) ∨ e = .incLocal pre inc x hops idx := by
  unfold Tier1.tE at hT
  split at hT <;> first | (cases hT; simp) | (split at hT <;> simp_all) | simp_all

/-- A `setLocal` that the pass makes stands for `assign none (local x hops idx) v`, with `v`
not a function expression, and its value is `v` rewritten. -/
theorem tE_setLocal {n : Nat} {e : Expr} {x : String} {hops idx : Nat} {v' : Expr}
    (hT : Tier1.tE (n + 1) e = .setLocal x hops idx v') :
    (∃ v, e = .assign none (.local x hops idx) v ∧ (∀ f, v ≠ .func f) ∧ v' = Tier1.tE n v) ∨
      e = .setLocal x hops idx v' := by
  unfold Tier1.tE at hT
  split at hT <;> first
    | (cases hT; simp)
    | (split at hT <;> first | (cases hT; left; exact ⟨_, rfl, by intro f h; simp_all, rfl⟩) | simp_all)
    | simp_all

/-- A `blockN` that the pass makes stands for a `block` that declares nothing lexical. -/
theorem tS_blockN {n : Nat} {s : Stmt} {ss' : List Stmt}
    (hT : Tier1.tS (n + 1) s = .blockN ss') :
    (∃ ss, s = .block ss ∧ Tier1.lexical ss = false ∧ ss' = Tier1.tSs n ss) ∨ s = .blockN ss' := by
  unfold Tier1.tS at hT
  split at hT <;> first
    | (cases hT; simp)
    | (split at hT <;> first | (cases hT; left; exact ⟨_, rfl, by simp_all, rfl⟩) | simp_all)
    | simp_all

#print axioms incLocal_eq
#print axioms setLocal_eq
#print axioms blockN_eq
#print axioms tE_incLocal
#print axioms tE_setLocal
#print axioms tS_blockN

end L4Factoidal.JS.Tier1Proofs
