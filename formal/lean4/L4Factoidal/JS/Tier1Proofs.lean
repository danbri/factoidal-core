import L4Factoidal.JS.FuelMono

/-!
# Tier 1 of BubblePopJS: each fast path against the evaluator's own code

Tier 1 is four guarded fast paths inside the evaluator's arms (`Tier1` in `JS/Interp.lean`),
on when the run's `Mode` has `tier1`. The reference is the evaluator in `Mode.ref`, where each
site runs only the arm's own code.

Proved here, one lemma per site, in the form the walk of `JS/FuelMono.lean` leaves at a site
(`Le.withFast`): in a mode with tier 1 off, the arm's own code `g` is `Le` the fast path
followed by `g` (`Tier1.attempt fast c g`). In words: from every heap, either `g` runs out of
fuel, or trying the fast path first ends exactly as `g` does, the same value or completion and
the same heap.

- `update_site`: `x++`, `x--`, `++x`, `--x` on a resolved name (`Tier1.incLocal?`);
- `setLocal_site`: the write of a plain assignment to a resolved name (`Tier1.setLocal?`);
- `binary_site`: `a op b` for `+ - * /` on operands known as numbers (`Tier1.arith?`);
- `block_site`: a block that declares nothing lexical (`Tier1.plainBlock?`).

`JS/FuelMonoAll.lean` composes them over the whole mutual block (`IH_all`,
`tier1_evalStmts_refines`): a run with tier 1 on ends as the reference run does, whenever the
reference does not run out of fuel.

What these do not say: anything about speed, or about the register machine (`vmLoop`), which
is the same code in both modes.
-/

namespace L4Factoidal.JS.Tier1Proofs
open L4Factoidal.JS FuelMono

variable {H : Type}

/-- A fast path is sound against `g` when, from every heap where `g` does not run out of fuel:
a `some b` of the fast path, continued by `c`, is what `g` gives; a `none` leaves the heap as it
was; and the fast path does not end abruptly. -/
theorem le_attempt {α β : Type} {fast : JSM H (Option β)} {c : β → JSM H α} {g : JSM H α}
    (h : ∀ s, Out (g s) ∨
      ((∀ b s', fast s = .ok (some b) s' → g s = c b s') ∧
       (∀ s', fast s = .ok none s' → s' = s) ∧ (∀ e s', fast s ≠ .error e s'))) :
    Le g (Tier1.attempt fast c g) := by
  unfold Le
  intro s
  rcases h s with ho | ⟨h1, h2, h3⟩
  · exact Or.inl ho
  · right
    show g s = EStateM.bind fast (fun o => match o with | some b => c b | none => g) s
    unfold EStateM.bind
    cases hf : fast s with
    | ok o s' =>
      cases o with
      | some b => exact h1 b s' hf
      | none => rw [h2 s' hf]
    | error e s' => exact absurd hf (h3 e s')

/-! ## A block that declares nothing lexical -/

theorem evalBlock_succ (t : Mode) (m : Nat) (ctx : Ctx) (ss : List Stmt) :
    evalBlock (H := H) (md := t) (m + 1) ctx ss =
      (do let ctx ← enterBlock (md := t) m ctx ss; evalStmts (md := t) m ctx ss) := rfl

theorem enterBlock_succ (t : Mode) (m : Nat) (ctx : Ctx) (ss : List Stmt) :
    enterBlock (H := H) (md := t) (m + 1) ctx ss = (do
      let needs := ss.any Tier1.isLexical
      if !needs then return ctx
      let env ← newEnv ctx.env
      let ctx' := { ctx with env }
      declareLexical (md := t) m ctx' ss
      return ctx') := rfl

/-- **Tier 1, a plain block.** The reference's `evalBlock` at fuel `n` is `Le` the tier's run of
the block: its statements at the tier's fuel `m`, when nothing lexical is declared. `hst` is
the induction hypothesis for the statements at every fuel up to `n`. -/
theorem block_site (t1 t2 : Mode) (n m : Nat) (ctx : Ctx) (ss : List Stmt)
    (hst : ∀ j, j ≤ n → Le (evalStmts (H := H) (md := t1) j ctx ss) (evalStmts (md := t2) m ctx ss)) :
    t1.tier1 = false → Le (evalBlock (H := H) (md := t1) n ctx ss)
      (Tier1.attempt (Tier1.plainBlock? ss) (fun _ => evalStmts (md := t2) m ctx ss)
        (evalBlock (md := t1) n ctx ss)) := by
  intro _
  cases hl : ss.any Tier1.isLexical with
  | true =>
    have h : Tier1.attempt (Tier1.plainBlock? (H := H) ss) (fun _ => evalStmts (md := t2) m ctx ss)
        (evalBlock (md := t1) n ctx ss) = evalBlock (md := t1) n ctx ss := by
      simp only [Tier1.attempt, Tier1.plainBlock?, hl, ↓reduceIte]; rfl
    rw [h]; exact Le.refl _
  | false =>
    have h : Tier1.attempt (Tier1.plainBlock? (H := H) ss) (fun _ => evalStmts (md := t2) m ctx ss)
        (evalBlock (md := t1) n ctx ss) = evalStmts (md := t2) m ctx ss := by
      simp only [Tier1.attempt, Tier1.plainBlock?, hl, Bool.false_eq_true, ↓reduceIte]; rfl
    rw [h]
    rcases n with _ | _ | i
    · exact Le.of_out fun s => ⟨s, rfl⟩
    · exact Le.of_out fun s => ⟨s, rfl⟩
    · have he : evalBlock (H := H) (md := t1) (i + 2) ctx ss = evalStmts (md := t1) (i + 1) ctx ss := by
        rw [evalBlock_succ, enterBlock_succ]
        simp only [hl, Bool.not_false]
        rfl
      rw [he]; exact hst (i + 1) (by omega)

/-! ## Resolved names: the slot read and the slot write -/

theorem lookupLocal_succ (t : Mode) (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) :
    lookupLocal (H := H) (md := t) (m + 1) ctx x hops idx = (do
      let h ← get
      let env := h.envs.getD (h.envUp hops ctx.env) default
      match env.names[idx]?, env.vals[idx]? with
      | some y, some v =>
        if y == x then
          match v with
          | .hole => throwErr .reference s!"Cannot access '{x}' before initialization"
          | _ =>
            if verifyLocals then
              let w ← lookup (md := t) m ctx x
              if !sameValue v w then throw (.halt s!"verifyLocals: {x} {hops} {idx}")
            pure v
        else lookup (md := t) m ctx x
      | _, _ => lookup (md := t) m ctx x) := rfl

theorem assignLocal_succ (t : Mode) (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (v : Value) :
    assignLocal (H := H) (md := t) (m + 1) ctx x hops idx v = (do
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
        else assignName (md := t) m ctx x v
      | _, _ => assignName (md := t) m ctx x v) := rfl

/-- The fast read of `incLocal?` is the read of `lookupLocal`, with no change to the heap. -/
theorem lookupLocal_of_slotNum (t : Mode) (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat)
    (hp : HeapOf H) (e : Nat) (old : Float) (hs : Tier1.slotNum? hp ctx x hops idx = some (e, old)) :
    lookupLocal (H := H) (md := t) (m + 1) ctx x hops idx hp = .ok (.num old) hp := by
  rw [lookupLocal_succ]
  unfold Tier1.slotNum? at hs
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

/-- The fast write of `incLocal?` and `setLocal?` is the write of `assignLocal`. -/
theorem assignLocal_of_slotSet (t : Mode) (m : Nat) (ctx : Ctx) (x : String) (hops idx : Nat) (v : Value)
    (hp : HeapOf H) (e : Nat) (hs : Tier1.slotSet? hp ctx x hops idx = some e) :
    assignLocal (H := H) (md := t) (m + 1) ctx x hops idx v hp = setSlot e idx v hp := by
  rw [assignLocal_succ]
  unfold Tier1.slotSet? at hs
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
    (hs : Tier1.slotNum? hp ctx x hops idx = some (e, old)) : Tier1.slotSet? hp ctx x hops idx = some e := by
  unfold Tier1.slotNum? at hs
  unfold Tier1.slotSet?
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

/-- A slot write ends normally. -/
theorem setSlot_ok (e i : Nat) (v : Value) (s : HeapOf H) : ∃ s', setSlot e i v s = .ok () s' :=
  ⟨_, rfl⟩

/-! ## `x++` on a resolved name -/

/-- What `incLocal?` does: nothing and `none`, or the slot's number replaced and the answer. -/
theorem incLocal?_spec (pre inc : Bool) (x : String) (hops idx : Nat) (ctx : Ctx) (s : HeapOf H) :
    (Tier1.slotNum? s ctx x hops idx = none ∧ Tier1.incLocal? pre inc x hops idx ctx s = .ok none s) ∨
    (∃ e old s', Tier1.slotNum? s ctx x hops idx = some (e, old) ∧
      setSlot e idx (.num (if inc then old + 1 else old - 1)) s = .ok () s' ∧
      Tier1.incLocal? pre inc x hops idx ctx s =
        .ok (some (.num (if pre then (if inc then old + 1 else old - 1) else old))) s') := by
  rcases hs : Tier1.slotNum? s ctx x hops idx with _ | ⟨e, old⟩
  · left
    refine ⟨rfl, ?_⟩
    simp only [Tier1.incLocal?, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hs]
    rfl
  · right
    obtain ⟨s', hw⟩ := setSlot_ok e idx (.num (if inc then old + 1 else old - 1)) s
    refine ⟨e, old, s', rfl, hw, ?_⟩
    simp only [Tier1.incLocal?, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hs, hw]
    rfl

/-- **Tier 1, `x++` on a resolved name.** In a mode with tier 1 off, the arm's own code
(`Tier1.updateGen` over `lookupLocal`, `assignLocal`, `toPrim`, `toNum` at the arm's fuel) is
`Le` the fast path followed by it. -/
theorem update_site (t : Mode) (n : Nat) (ctx : Ctx) (pre inc : Bool) (x : String) (h i : Nat) :
    t.tier1 = false →
    Le (Tier1.updateGen (lookupLocal (H := H) (md := t) n ctx x h i)
          (fun v => assignLocal (md := t) n ctx x h i v) (fun p => toPrim (md := t) n p "number")
          (fun p => toNum (md := t) n p) pre inc)
      (Tier1.attempt (Tier1.incLocal? pre inc x h i ctx) pure
        (Tier1.updateGen (lookupLocal (H := H) (md := t) n ctx x h i)
          (fun v => assignLocal (md := t) n ctx x h i v) (fun p => toPrim (md := t) n p "number")
          (fun p => toNum (md := t) n p) pre inc)) := by
  intro _
  apply le_attempt
  intro s
  rcases n with _ | k
  · exact Or.inl ⟨s, rfl⟩
  · right
    rcases incLocal?_spec (H := H) pre inc x h i ctx s with ⟨-, hf⟩ | ⟨e, old, s1, hs, hw, hf⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro b s' hb; rw [hf] at hb; cases hb
      · intro s' hb; rw [hf] at hb; cases hb; rfl
      · intro e s' hb; rw [hf] at hb; cases hb
    · refine ⟨?_, ?_, ?_⟩
      · intro b s' hb
        rw [hf] at hb
        cases hb
        have hl := lookupLocal_of_slotNum (H := H) t k ctx x h i s e old hs
        have ha := assignLocal_of_slotSet (H := H) t k ctx x h i
          (.num (if inc then old + 1 else old - 1)) s e (slotSet_of_slotNum s ctx x h i e old hs)
        first
          | (simp only [Tier1.updateGen, bind, EStateM.bind, hl, ha, hw]; done)
          | (simp only [Tier1.updateGen, bind, EStateM.bind, hl, ha, hw]; rfl)
      · intro s' hb; rw [hf] at hb; cases hb
      · intro e s' hb; rw [hf] at hb; cases hb

/-! ## The write of a plain assignment to a resolved name -/

theorem putTarget_local (t : Mode) (j : Nat) (ctx : Ctx) (x : String) (h i : Nat)
    (b : Option Value) (k : Option String) (v : Value) :
    putTarget (H := H) (md := t) (j + 1) ctx (.local x h i) b k v =
      assignLocal (md := t) j ctx x h i v := rfl

/-- What `setLocal?` does on a resolved name: nothing and `none`, or the slot written. -/
theorem setLocal?_spec (x : String) (hops idx : Nat) (v : Value) (ctx : Ctx) (s : HeapOf H) :
    (Tier1.slotSet? s ctx x hops idx = none ∧ Tier1.setLocal? (.local x hops idx) v ctx s = .ok none s) ∨
    (∃ e s', Tier1.slotSet? s ctx x hops idx = some e ∧ setSlot e idx v s = .ok () s' ∧
      Tier1.setLocal? (.local x hops idx) v ctx s = .ok (some ()) s') := by
  rcases hs : Tier1.slotSet? s ctx x hops idx with _ | e
  · left
    refine ⟨rfl, ?_⟩
    simp only [Tier1.setLocal?, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hs]
    rfl
  · right
    obtain ⟨s', hw⟩ := setSlot_ok e idx v s
    refine ⟨e, s', rfl, hw, ?_⟩
    simp only [Tier1.setLocal?, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hs, hw]
    rfl

/-- **Tier 1, the write to a resolved name.** In a mode with tier 1 off, `putTarget` is `Le` the
fast write followed by it. -/
theorem setLocal_site (t : Mode) (n : Nat) (ctx : Ctx) (target : Expr) (b : Option Value)
    (k : Option String) (v : Value) :
    t.tier1 = false →
    Le (putTarget (H := H) (md := t) n ctx target b k v)
      (Tier1.attempt (Tier1.setLocal? target v ctx) pure (putTarget (md := t) n ctx target b k v)) := by
  intro _
  apply le_attempt
  intro s
  cases target
  case «local» x h i =>
    rcases n with _ | _ | j
    · exact Or.inl ⟨s, rfl⟩
    · exact Or.inl ⟨s, rfl⟩
    · right
      rcases setLocal?_spec (H := H) x h i v ctx s with ⟨-, hf⟩ | ⟨e, s1, hs, hw, hf⟩
      · refine ⟨?_, ?_, ?_⟩
        · intro u s' hb; rw [hf] at hb; cases hb
        · intro s' hb; rw [hf] at hb; cases hb; rfl
        · intro e s' hb; rw [hf] at hb; cases hb
      · refine ⟨?_, ?_, ?_⟩
        · intro u s' hb
          rw [hf] at hb
          cases hb
          rw [putTarget_local, assignLocal_of_slotSet (H := H) t j ctx x h i v s e hs, hw]
          rfl
        · intro s' hb; rw [hf] at hb; cases hb
        · intro e s' hb; rw [hf] at hb; cases hb
  all_goals
    right
    refine ⟨?_, ?_, ?_⟩
    · intro u s' hb; cases hb
    · intro s' hb; cases hb; rfl
    · intro e s' hb; cases hb

/-! ## `a op b` for `+ - * /` -/

/-- An operand that evaluates, by the arm's own code, to the number `p` with the heap unchanged,
unless its evaluation runs out of fuel: a leaf that holds `p`, or an expression the evaluator
`ev` takes to `p`. -/
def OperandNum (ev : Expr → JSM H Value) (s : HeapOf H) (ctx : Ctx) (c : Expr) (p : Float) : Prop :=
  leafV s ctx c = .num p ∨ (leafV s ctx c = .hole ∧ (Out (ev c s) ∨ ev c s = .ok (.num p) s))

/-- The arm's own code on two such operands and an operation of `isArith`: out of fuel, or the
number of `arithOp` with the heap unchanged. -/
theorem binaryGen_num (ev : Expr → JSM H Value) (bo : BinOp → Value → Value → JSM H Value)
    (ctx : Ctx) (op : BinOp) (a b : Expr) (s : HeapOf H) (p q : Float)
    (hop : Tier1.isArith op = true) (ha : OperandNum ev s ctx a p) (hb : OperandNum ev s ctx b q) :
    Out (Tier1.binaryGen ev bo ctx op a b s) ∨
      Tier1.binaryGen ev bo ctx op a b s = .ok (.num (Tier1.arithOp op p q)) s := by
  rcases ha with ha | ⟨ha, ⟨sa, ha'⟩ | ha'⟩
  · rcases hb with hb | ⟨hb, ⟨sb, hb'⟩ | hb'⟩
    · right; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, hb]; cases op <;> simp [Tier1.isArith] at hop <;> rfl
    · left; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, hb, hb']; exact ⟨sb, rfl⟩
    · right; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, hb, hb']; cases op <;> simp [Tier1.isArith] at hop <;> rfl
  · left; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, ha']; exact ⟨sa, rfl⟩
  · rcases hb with hb | ⟨hb, ⟨sb, hb'⟩ | hb'⟩
    · right; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, ha', hb]; cases op <;> simp [Tier1.isArith] at hop <;> rfl
    · left; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, ha', hb, hb']; exact ⟨sb, rfl⟩
    · right; simp only [Tier1.binaryGen, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, ha, ha', hb, hb']; cases op <;> simp [Tier1.isArith] at hop <;> rfl

/-- The evaluator on `a op b` for an operation of `isArith`, one step unfolded. -/
theorem binary_succ (t : Mode) (n : Nat) (ctx : Ctx) (op : BinOp) (a b : Expr)
    (hop : Tier1.isArith op = true) :
    evalExpr (H := H) (md := t) (n + 1) ctx (.binary op a b) =
      Tier1.withFast t.tier1 (Tier1.arith? ctx op a b) pure
        (Tier1.binaryGen (fun e => evalExpr (md := t) n ctx e) (fun o x y => binop (md := t) n o x y)
          ctx op a b) := by
  cases op <;> (try simp only [Tier1.isArith, Bool.false_eq_true] at hop) <;> rfl

theorem pureNum_binary (hp : HeapOf H) (ctx : Ctx) (k : Nat) (op : BinOp) (a b : Expr) :
    Tier1.pureNum hp ctx (k + 1) (.binary op a b) =
      if Tier1.isArith op then
        match Tier1.pureNum hp ctx k a, Tier1.pureNum hp ctx k b with
        | some p, some q => some (Tier1.arithOp op p q)
        | _, _ => none
      else none := rfl

theorem pureNum_binary_zero (hp : HeapOf H) (ctx : Ctx) (op : BinOp) (a b : Expr) :
    Tier1.pureNum hp ctx 0 (.binary op a b) = none := rfl

/-- On an operand that is not `a op b`, `pureNum` knows only a leaf's number. -/
theorem pureNum_leaf (s : HeapOf H) (ctx : Ctx) (k : Nat) (c : Expr) (p : Float)
    (hnb : ∀ op a b, c ≠ .binary op a b) (h : Tier1.pureNum s ctx k c = some p) :
    leafV s ctx c = .num p := by
  unfold Tier1.pureNum at h
  split at h
  · rename_i hl; cases h; exact hl
  · split at h <;> first
      | cases h
      | exact absurd rfl (hnb _ _ _)
      | exact absurd (by assumption) (hnb _ _ _)
  · cases h

/-- What `pureNum` knows about an operand is what the reference's evaluator gives for it. -/
theorem pureNum_sound (t : Mode) (ht : t.tier1 = false) (s : HeapOf H) (ctx : Ctx) :
    ∀ (k n : Nat) (c : Expr) (p : Float), Tier1.pureNum s ctx k c = some p →
      OperandNum (fun e => evalExpr (H := H) (md := t) n ctx e) s ctx c p := by
  intro k
  induction k with
  | zero =>
    intro n c p h
    by_cases hb : ∃ op a b, c = .binary op a b
    · obtain ⟨op, a, b, rfl⟩ := hb
      rw [pureNum_binary_zero] at h
      cases h
    · exact Or.inl (pureNum_leaf s ctx 0 c p (fun op a b hc => hb ⟨op, a, b, hc⟩) h)
  | succ k ih =>
    intro n c p h
    by_cases hb : ∃ op a b, c = .binary op a b
    · obtain ⟨op, a, b, rfl⟩ := hb
      rw [pureNum_binary] at h
      split at h
      · rename_i hop
        split at h
        · rename_i pa pb hpa hpb
          cases h
          refine Or.inr ⟨rfl, ?_⟩
          rcases n with _ | n'
          · exact Or.inl ⟨s, rfl⟩
          · show Out (evalExpr (H := H) (md := t) (n' + 1) ctx (.binary op a b) s) ∨
              evalExpr (H := H) (md := t) (n' + 1) ctx (.binary op a b) s =
                .ok (.num (Tier1.arithOp op pa pb)) s
            rw [binary_succ t n' ctx op a b hop, ht]
            exact binaryGen_num _ _ ctx op a b s pa pb hop (ih n' a pa hpa) (ih n' b pb hpb)
        · cases h
      · cases h
    · exact Or.inl (pureNum_leaf s ctx (k + 1) c p (fun op a b hc => hb ⟨op, a, b, hc⟩) h)

/-- What `arith?` does: `none` and nothing, or the number of two operands `pureNum` knows. -/
theorem arith?_spec (ctx : Ctx) (op : BinOp) (a b : Expr) (s : HeapOf H) :
    Tier1.arith? ctx op a b s = .ok none s ∨
    (∃ p q, Tier1.isArith op = true ∧ Tier1.pureNum s ctx Tier1.depth a = some p ∧
      Tier1.pureNum s ctx Tier1.depth b = some q ∧
      Tier1.arith? ctx op a b s = .ok (some (.num (Tier1.arithOp op p q))) s) := by
  cases hop : Tier1.isArith op with
  | false =>
    left
    simp [Tier1.arith?, hop, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  | true =>
    rcases hpa : Tier1.pureNum s ctx Tier1.depth a with _ | p
    · left
      simp [Tier1.arith?, hop, hpa, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure,
        EStateM.pure]
    · rcases hpb : Tier1.pureNum s ctx Tier1.depth b with _ | q
      · left
        simp [Tier1.arith?, hop, hpa, hpb, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
          pure, EStateM.pure]
      · right
        refine ⟨p, q, rfl, rfl, rfl, ?_⟩
        simp [Tier1.arith?, hop, hpa, hpb, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
          pure, EStateM.pure]

/-- **Tier 1, `a op b` for `+ - * /`.** In a mode with tier 1 off, the arm's own code
(`Tier1.binaryGen` over `evalExpr` and `binop` at the arm's fuel) is `Le` the fast path followed
by it. -/
theorem binary_site (t : Mode) (n : Nat) (ctx : Ctx) (op : BinOp) (a b : Expr) :
    t.tier1 = false →
    Le (Tier1.binaryGen (fun e => evalExpr (H := H) (md := t) n ctx e)
          (fun o x y => binop (md := t) n o x y) ctx op a b)
      (Tier1.attempt (Tier1.arith? ctx op a b) pure
        (Tier1.binaryGen (fun e => evalExpr (H := H) (md := t) n ctx e)
          (fun o x y => binop (md := t) n o x y) ctx op a b)) := by
  intro ht
  apply le_attempt
  intro s
  rcases arith?_spec (H := H) ctx op a b s with hf | ⟨p, q, hop, hpa, hpb, hf⟩
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro v s' hb; rw [hf] at hb; cases hb
    · intro s' hb; rw [hf] at hb; cases hb; rfl
    · intro e s' hb; rw [hf] at hb; cases hb
  · rcases binaryGen_num (fun e => evalExpr (H := H) (md := t) n ctx e)
        (fun o x y => binop (md := t) n o x y) ctx op a b s p q hop
        (pureNum_sound t ht s ctx _ n a p hpa) (pureNum_sound t ht s ctx _ n b q hpb) with ho | he
    · exact Or.inl ho
    · right
      refine ⟨?_, ?_, ?_⟩
      · intro v s' hb; rw [hf] at hb; cases hb; exact he
      · intro s' hb; rw [hf] at hb; cases hb
      · intro e s' hb; rw [hf] at hb; cases hb

#print axioms update_site
#print axioms setLocal_site
#print axioms binary_site
#print axioms block_site

end L4Factoidal.JS.Tier1Proofs
