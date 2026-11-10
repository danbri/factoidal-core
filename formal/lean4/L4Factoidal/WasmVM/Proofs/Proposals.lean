/-
L4Factoidal.WasmVM.Proofs.Proposals: exception handling and tail calls against the
spec layer (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Exception handling", "Tail calls").

Spec side (rules of `Spec.Step`, `Spec.Step_read` generated from WebAssembly 3.0):
- `throw_reaches_catch`: `throw x` with its payload, directly inside a handler whose
  first clause is `catch x l`, reaches `br l` with the payload in two steps (`throw`,
  then `throw_ref_handler_catch`). `throw_reaches_catch_all`: the same for `catch_all l`.
- `skip_clauses`: clauses whose tag is not the exception's are passed over, in order
  (`throw_ref_handler_next`, whose premise since spectec patch 0005 is that no
  earlier rule, `Step_read_before_throw_ref_handler_next`, applies to the clause). With the two above, this is the rule the engine's
  `catchFor` follows: the first clause whose tag matches, or the first catch-all.
- `return_call_keeps_args`: a tail call from a frame drops every value of the frame
  except the callee's arguments, the top `n` (`return_call_ref_frame_addr`). The
  engine's `enterTail` moves exactly the top `nParams` slots down to `fp`.

Engine side:
- `cold_tail_frames`: the tail-call ops (`return_call`, `return_call_indirect`,
  `return_call_ref`) continue with the same frame stack and the same `fp`. So a tail
  call never grows the frame stack (the 10^6-call test in `Tests/Proposals.lean`
  checks the same at run time).

Also `vals_beq_self`: the generated `BEq` on spec values is reflexive (the side
conditions `exn == {..}` and `val_lst == FIELDS` of the rules need it).
-/
import L4Factoidal.WasmVM.Spec
import L4Factoidal.WasmVM.Exec.Run

namespace L4Factoidal.WasmVM.Proofs.Proposals
open L4Factoidal.WasmVM

/-! ### Reflexivity of the generated `BEq` on values -/

theorem uN_beq_self (u : Spec.uN) : (u == u) = true := by
  cases u; simp [BEq.beq, Spec.instBEqUN.beq]

theorem ref_beq_self (r : Spec.ref) : (r == r) = true := by
  induction r <;> simp_all [BEq.beq, Spec.instBEqRef.beq, Spec.instBEqUN.beq]

theorem num_beq_self (n : Spec.num_) : (n == n) = true := by
  cases n with
  | mk_num__0 i x => cases i <;> cases x <;> simp [BEq.beq, Spec.instBEqNum_.beq, Spec.instBEqInn.beq, Spec.instBEqUN.beq]
  | mk_num__1 i x =>
    cases i <;> cases x <;> rename_i m <;> cases m <;>
      simp [BEq.beq, Spec.instBEqNum_.beq, Spec.instBEqFnn.beq, Spec.instBEqFN.beq, Spec.instBEqFNmag.beq]

theorem val_beq_self (v : Spec.val) : (v == v) = true := by
  cases v with
  | CONST t n =>
    have := num_beq_self n
    cases t <;> simp_all [BEq.beq, Spec.instBEqVal.beq, Spec.instBEqNumtype.beq] <;>
      (split <;> first | rfl | (rename_i h _; exact absurd rfl h))
  | REF_EXTERN r =>
    have := ref_beq_self r
    simp_all [BEq.beq, Spec.instBEqVal.beq] <;> (split <;> first | rfl | (rename_i h _; exact absurd rfl h))
  | VCONST t x =>
    cases t <;> cases x <;> simp [BEq.beq, Spec.instBEqVal.beq, Spec.instBEqVectype.beq, Spec.instBEqUN.beq] <;>
      (split <;> first | rfl | (rename_i h _; exact absurd rfl h))
  | _ =>
    simp [BEq.beq, Spec.instBEqVal.beq, Spec.instBEqUN.beq] <;>
      (split <;> first | rfl | (rename_i h _; exact absurd rfl h))

theorem vals_beq_self (vs : List Spec.val) : (vs == vs) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [val_beq_self, ih]

theorem exninst_beq_self (e : Spec.exninst) : (e == e) = true := by
  cases e
  simp [BEq.beq, Spec.instBEqExninst.beq]
  exact vals_beq_self _

/-! ### Throw reaches its handler -/

/-- The exception that `throw x` with payload `vals` makes in state `z`. -/
noncomputable def exnOf (z : Spec.state) (x : Spec.idx) (vals : List Spec.val) : Spec.exninst :=
  { TAG := (Spec.f z).MODULE.TAGS[Spec.proj_uN_0 x]!, FIELDS := vals }

/-- Step 1 of both theorems: `throw x` inside a handler becomes `ref.exn a; throw_ref`
there, with the new exception at address `a` = the number of exceptions before. -/
theorem throw_step (st : Spec.store) (fr : Spec.frame) (vals : List Spec.val) (x : Spec.idx)
    (n : Nat) (cs : List Spec.catch) (ts : List Spec.valtype)
    (hexp : Spec.Expand (Spec.as_deftype ((Spec.fun_tag (.mk_state st fr) x).TYPE))
      (.FUNC (.mk_list ts) (.mk_list [])))
    (hx : Spec.proj_uN_0 x < fr.MODULE.TAGS.length) :
    Spec.Step (.mk_config (.mk_state st fr) [.HANDLER_ n cs (vals.map Spec.instr_val ++ [.THROW x])])
      (.mk_config (Spec.add_exninst (.mk_state st fr) (exnOf (.mk_state st fr) x vals))
        [.HANDLER_ n cs [.REF_EXN_ADDR st.EXNS.length, .THROW_REF]]) := by
  refine Spec.Step.ctxt_handler _ _ _ _ _ _ ?_
  exact Spec.Step.throw _ vals 0 x _ _ ts hexp (by simp [Spec.s, Spec.fun_store])
    (by simpa [Spec.f, Spec.fun_frame] using hx) (exninst_beq_self _)

theorem exns_after (st : Spec.store) (fr : Spec.frame) (e : Spec.exninst) :
    Spec.s (Spec.add_exninst (.mk_state st fr) e) = { st with EXNS := st.EXNS ++ [e] } ∧
    Spec.f (Spec.add_exninst (.mk_state st fr) e) = fr := by
  simp [Spec.add_exninst, Spec.s, Spec.f, Spec.fun_store, Spec.fun_frame, Spec.sof, Spec.fof]

/-- `throw x` directly inside `handler{catch x l, ..}` reaches `br l` with its payload. -/
theorem throw_reaches_catch (st : Spec.store) (fr : Spec.frame) (vals : List Spec.val)
    (x : Spec.idx) (l : Spec.labelidx) (n : Nat) (cs : List Spec.catch) (ts : List Spec.valtype)
    (hexp : Spec.Expand (Spec.as_deftype ((Spec.fun_tag (.mk_state st fr) x).TYPE))
      (.FUNC (.mk_list ts) (.mk_list [])))
    (hx : Spec.proj_uN_0 x < fr.MODULE.TAGS.length) :
    Spec.Steps (.mk_config (.mk_state st fr) [.HANDLER_ n (.CATCH x l :: cs) (vals.map Spec.instr_val ++ [.THROW x])])
      (.mk_config (Spec.add_exninst (.mk_state st fr) (exnOf (.mk_state st fr) x vals))
        (vals.map Spec.instr_val ++ [.BR l])) := by
  refine Spec.Steps.trans _ _ _ _ _ _ (throw_step st fr vals x n _ ts hexp hx) ?_
  refine Spec.Steps.trans _ _ _ _ _ _ (Spec.Step.read _ _ _ ?_) (Spec.Steps.refl _ _)
  obtain ⟨hs, hf⟩ := exns_after st fr (exnOf (.mk_state st fr) x vals)
  refine Spec.Step_read.throw_ref_handler_catch _ n x l cs _ vals ?_ ?_ ?_ ?_
  · rw [hs]; simp
  · rw [hf]; exact hx
  · rw [hs, hf]; simp [exnOf, Spec.f, Spec.fun_frame]
  · rw [hs]; simp [exnOf, vals_beq_self]

/-- `throw x` directly inside `handler{catch_all l, ..}` reaches `br l`. -/
theorem throw_reaches_catch_all (st : Spec.store) (fr : Spec.frame) (vals : List Spec.val)
    (x : Spec.idx) (l : Spec.labelidx) (n : Nat) (cs : List Spec.catch) (ts : List Spec.valtype)
    (hexp : Spec.Expand (Spec.as_deftype ((Spec.fun_tag (.mk_state st fr) x).TYPE))
      (.FUNC (.mk_list ts) (.mk_list [])))
    (hx : Spec.proj_uN_0 x < fr.MODULE.TAGS.length) :
    Spec.Steps (.mk_config (.mk_state st fr) [.HANDLER_ n (.CATCH_ALL l :: cs) (vals.map Spec.instr_val ++ [.THROW x])])
      (.mk_config (Spec.add_exninst (.mk_state st fr) (exnOf (.mk_state st fr) x vals)) [.BR l]) :=
  Spec.Steps.trans _ _ _ _ _ _ (throw_step st fr vals x n _ ts hexp hx)
    (Spec.Steps.trans _ _ _ _ _ _
      (Spec.Step.read _ _ _ (Spec.Step_read.throw_ref_handler_catch_all _ n l cs _))
      (Spec.Steps.refl _ _))

/-- A clause the engine passes over: a tagged clause whose tag is not the exception's. -/
def Skipped (z : Spec.state) (a : Nat) : Spec.catch → Prop
  | .CATCH x _ | .CATCH_REF x _ =>
    Spec.proj_uN_0 x < (Spec.f z).MODULE.TAGS.length ∧
      (Spec.s z).EXNS[a]!.TAG ≠ (Spec.f z).MODULE.TAGS[Spec.proj_uN_0 x]!
  | _ => False

/-- Clauses whose tag does not match are passed over in order, as `catchFor` does. -/
theorem skip_clauses (z : Spec.state) (n : Nat) (a : Nat) (ha : a < (Spec.s z).EXNS.length) :
    ∀ (pre rest : List Spec.catch), (∀ c ∈ pre, Skipped z a c) →
    Spec.Steps (.mk_config z [.HANDLER_ n (pre ++ rest) [.REF_EXN_ADDR a, .THROW_REF]])
      (.mk_config z [.HANDLER_ n rest [.REF_EXN_ADDR a, .THROW_REF]])
  | [], rest, _ => Spec.Steps.refl _ _
  | c :: pre, rest, h => by
    have hc := h c (by simp)
    refine Spec.Steps.trans _ _ _ _ _ _ (Spec.Step.read _ _ _ ?_)
      (skip_clauses z n a ha pre rest fun c' hc' => h c' (by simp [hc']))
    refine Spec.Step_read.throw_ref_handler_next z n c (pre ++ rest) a ?_
    intro hb
    cases c <;> simp only [Skipped] at hc <;> first
      | exact hc.elim
      | (cases hb <;> simp_all)

/-! ### Tail calls -/

/-- A tail call from a frame keeps the callee's arguments (the top `nargs` values)
and drops the rest of the frame. -/
theorem return_call_keeps_args (z : Spec.state) (k : Nat) (fr : Spec.frame) (vs : List Spec.val)
    (nargs a : Nat) (yy : Spec.typeuse) (rest : List Spec.instr) (t1 t2 : List Spec.valtype)
    (ha : a < (Spec.s z).FUNCS.length)
    (hexp : Spec.Expand ((Spec.s z).FUNCS[a]!.TYPE) (.FUNC (.mk_list t1) (.mk_list t2))) :
    Spec.Step_read
      (.mk_config z [.FRAME_ k fr (vs.map Spec.instr_val ++ ([.REF_FUNC_ADDR a] ++ ([.RETURN_CALL_REF yy] ++ rest)))])
      ((vs.drop (vs.length - nargs)).map Spec.instr_val ++ [.REF_FUNC_ADDR a, .CALL_REF yy]) := by
  have h := Spec.Step_read.return_call_ref_frame_addr z k fr (vs.take (vs.length - nargs))
    (vs.drop (vs.length - nargs)) 0 a yy rest t1 t2 0 ha hexp
  rw [← List.append_assoc, ← List.map_append, List.take_append_drop] at h
  simpa using h

section
variable {M : Type} [LinearMemory M]
open Run

/-- The tail-call ops go on with the same frame stack and frame base. -/
theorem cold_tail_frames (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) (o : Op)
    (ho : (∃ f, o = .returnCall f) ∨ (∃ t x, o = .returnCallIndirect t x) ∨ o = .returnCallRef)
    (st' : StoreOf M) (stack' : Slots) (sp' fp' pc' : USize) (code' : Array Op) (inst' : ModuleInst)
    (frames' : Array Frame)
    (h : cold lim st stack sp fp pc code inst frames o = .go st' stack' sp' fp' pc' code' inst' frames') :
    frames' = frames ∧ fp' = fp := by
  rcases ho with ⟨f, rfl⟩ | ⟨t, x, rfl⟩ | rfl <;> simp only [cold] at h <;>
    (repeat' split at h) <;> simp_all

end

end L4Factoidal.WasmVM.Proofs.Proposals
