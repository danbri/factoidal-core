/-
L4Factoidal.WasmVM.Proofs.SpecWP: a verified symbolic-execution layer over the
WebAssembly SPEC semantics (`Spec.Steps`, generated from WebAssembly 3.0), for proofs
about whole functions of a real binary (record:
docs/designissues/2026-11-09-verified-foaf-layout.md).

`Sem z vs is Q B` says: from state `z` with the values `vs` on the stack, the spec
semantics runs the instructions `is` (in any surrounding code `tail`) either to a normal
end, in a state `z'` with values `vs'` such that `Q z' vs'`, or to a branch `br k`
out of `is`, in a state with `B k z' vs'`. It is a definition over `Spec.Steps`, not a
second semantics: every rule below is a theorem proved from the generated rules
(`Step_pure`, `Step_read`, `Step`), so a proof built from them is a proof of
`Spec.Steps`.

The rules are in continuation-passing style (the postcondition of a block is "the rest
of the code runs"), so a function body is proved by applying them instruction by
instruction; loops by an induction of the user's choosing over `Sem` of the loop
(`sem_loop` unfolds one iteration).

Scope: blocks, loops and `if` of block type `[] -> []` (`_RESULT none`), as a
compiler or a hand-written kernel without block results emits; a branch then keeps no
values. The generated rules `br_label_zero` and `block` do not tie the label arity to
the values kept (spec-layer record, section 9b, third defect); every use here keeps
none, which is the official arity of an empty block type, so no rule is used outside
its official instances.
-/
import L4Factoidal.WasmVM.Proofs.Refine

namespace L4Factoidal.WasmVM.Proofs.SpecWP
open L4Factoidal.WasmVM Proofs.Refine

/-- Values as instructions. -/
noncomputable abbrev vals (vs : List Spec.val) : List Spec.instr := vs.map Spec.instr_val

abbrev Post := Spec.state → List Spec.val → Prop
abbrev BrPost := Nat → Spec.state → List Spec.val → Prop

/-- The spec semantics runs `is` from `z` with stack `vs` to a normal end satisfying `Q`
or to a branch out of `is` satisfying `B`, inside any following code `tail`. -/
def Sem (z : Spec.state) (vs : List Spec.val) (is : List Spec.instr) (Q : Post) (B : BrPost) : Prop :=
  ∀ tail : List Spec.instr,
    (∃ z' vs', Q z' vs' ∧
      Spec.Steps (.mk_config z (vals vs ++ (is ++ tail))) (.mk_config z' (vals vs' ++ tail))) ∨
    (∃ k z' vs' junk, B k z' vs' ∧
      Spec.Steps (.mk_config z (vals vs ++ (is ++ tail)))
        (.mk_config z' (vals vs' ++ (Spec.instr.BR (.mk_uN k) :: junk))))

/-! ### Steps under contexts -/

theorem steps_ctx (vs : List Spec.val) (rest : List Spec.instr) :
    ∀ {z z' : Spec.state} {x x' : List Spec.instr},
    Spec.Steps (.mk_config z x) (.mk_config z' x') →
    Spec.Steps (.mk_config z (vals vs ++ (x ++ rest))) (.mk_config z' (vals vs ++ (x' ++ rest))) := by
  intro z z' x x' h
  generalize hc : Spec.config.mk_config z x = c at h
  generalize hc' : Spec.config.mk_config z' x' = c' at h
  induction h generalizing z x with
  | refl => cases hc; cases hc'; exact Spec.Steps.refl _ _
  | trans z0 i0 z2 i2 z1 i1 hs _ ih =>
    cases hc; cases hc'
    exact Spec.Steps.trans _ _ _ _ _ _ (step_ctx _ _ vs _ _ rest hs) (ih rfl rfl)

theorem steps_label (n : Nat) (cont : List Spec.instr) :
    ∀ {z z' : Spec.state} {x x' : List Spec.instr},
    Spec.Steps (.mk_config z x) (.mk_config z' x') →
    Spec.Steps (.mk_config z [.LABEL_ n cont x]) (.mk_config z' [.LABEL_ n cont x']) := by
  intro z z' x x' h
  generalize hc : Spec.config.mk_config z x = c at h
  generalize hc' : Spec.config.mk_config z' x' = c' at h
  induction h generalizing z x with
  | refl => cases hc; cases hc'; exact Spec.Steps.refl _ _
  | trans z0 i0 z2 i2 z1 i1 hs _ ih =>
    cases hc; cases hc'
    exact Spec.Steps.trans _ _ _ _ _ _ (Spec.Step.ctxt_label _ _ _ _ _ _ hs) (ih rfl rfl)

/-- Steps of a function body lift through its `FRAME_`; the caller's frame is kept. -/
theorem steps_frame (n : Nat) (f0 : Spec.frame) :
    ∀ {S S' : Spec.store} {f f' : Spec.frame} {x x' : List Spec.instr},
    Spec.Steps (.mk_config (.mk_state S f) x) (.mk_config (.mk_state S' f') x') →
    Spec.Steps (.mk_config (.mk_state S f0) [.FRAME_ n f x])
      (.mk_config (.mk_state S' f0) [.FRAME_ n f' x']) := by
  intro S S' f f' x x' h
  generalize hc : Spec.config.mk_config (.mk_state S f) x = c at h
  generalize hc' : Spec.config.mk_config (.mk_state S' f') x' = c' at h
  induction h generalizing S f x with
  | refl => cases hc; cases hc'; exact Spec.Steps.refl _ _
  | trans z0 i0 z2 i2 z1 i1 hs _ ih =>
    cases hc; cases hc'
    cases z1 with
    | mk_state S1 f1 =>
      exact Spec.Steps.trans _ _ _ _ _ _ (Spec.Step.ctxt_frame _ _ _ _ _ _ _ _ hs) (ih rfl rfl)

theorem vals_append (a b : List Spec.val) : vals (a ++ b) = vals a ++ vals b := by
  simp [vals]

/-! ### The rules -/

theorem sem_nil {z vs Q B} (h : Q z vs) : Sem z vs [] Q B :=
  fun _ => .inl ⟨z, vs, h, by simpa using Spec.Steps.refl _ _⟩

/-- One local computation: the top values `ws` and the instruction `i` take some spec
steps to the values `ws'` in state `z'`; the values `pre` below are not touched. -/
theorem sem_steps {z z' : Spec.state} {pre ws ws' : List Spec.val} {i : Spec.instr}
    {rest : List Spec.instr} {Q : Post} {B : BrPost}
    (hs : Spec.Steps (.mk_config z (vals ws ++ [i])) (.mk_config z' (vals ws')))
    (h : Sem z' (pre ++ ws') rest Q B) : Sem z (pre ++ ws) (i :: rest) Q B := by
  intro tail
  have h1 := steps_ctx pre (rest ++ tail) hs
  have e1 : vals pre ++ ((vals ws ++ [i]) ++ (rest ++ tail)) = vals (pre ++ ws) ++ (i :: rest ++ tail) := by
    simp [vals_append]
  have e2 : vals pre ++ (vals ws' ++ (rest ++ tail)) = vals (pre ++ ws') ++ (rest ++ tail) := by
    simp [vals_append]
  rw [e1, e2] at h1
  rcases h tail with ⟨z2, vs2, hq, h2⟩ | ⟨k, z2, vs2, junk, hb, h2⟩
  · exact .inl ⟨z2, vs2, hq, steps_trans h1 h2⟩
  · exact .inr ⟨k, z2, vs2, junk, hb, steps_trans h1 h2⟩

theorem sem_step {z z' : Spec.state} {pre ws ws' : List Spec.val} {i : Spec.instr}
    {rest : List Spec.instr} {Q : Post} {B : BrPost}
    (hs : Spec.Step (.mk_config z (vals ws ++ [i])) (.mk_config z' (vals ws')))
    (h : Sem z' (pre ++ ws') rest Q B) : Sem z (pre ++ ws) (i :: rest) Q B :=
  sem_steps (steps_one hs) h

/-- A pure step on the top values. -/
theorem sem_pure {z : Spec.state} {pre ws ws' : List Spec.val} {i : Spec.instr}
    {rest : List Spec.instr} {Q : Post} {B : BrPost}
    (hs : Spec.Step_pure (vals ws ++ [i]) (vals ws'))
    (h : Sem z (pre ++ ws') rest Q B) : Sem z (pre ++ ws) (i :: rest) Q B :=
  sem_step (Spec.Step.pure _ _ _ hs) h

/-- A constant is a value: it moves to the stack with no step. -/
theorem sem_val {z vs v rest Q B} (h : Sem z (vs ++ [v]) rest Q B) :
    Sem z vs (Spec.instr_val v :: rest) Q B := by
  intro tail
  have e : vals vs ++ (Spec.instr_val v :: rest ++ tail) = vals (vs ++ [v]) ++ (rest ++ tail) := by
    simp [vals_append]
  rw [e]; exact h tail

theorem sem_br {z vs k rest Q} {B : BrPost} (h : B k z vs) :
    Sem z vs (.BR (.mk_uN k) :: rest) Q B :=
  fun tail => .inr ⟨k, z, vs, rest ++ tail, h, by simpa using Spec.Steps.refl _ _⟩

theorem wf_i32_mod (c : Nat) : Spec.wf_num_ .I32 (.mk_num__0 .I32 (.mk_uN (c % 2^32))) :=
  wf_i32 _ (Nat.mod_lt _ (by decide))

/-- `br_if l` on an i32 condition `c` (taken iff `c mod 2^32 ≠ 0`). -/
theorem sem_brIf {z pre c k rest Q} {B : BrPost}
    (h : if c % 2^32 = 0 then Sem z pre rest Q B else B k z pre) :
    Sem z (pre ++ [i32c (c % 2^32)]) (.BR_IF (.mk_uN k) :: rest) Q B := by
  by_cases hc : c % 2^32 = 0
  · rw [if_pos hc] at h
    have := sem_pure (pre := pre) (ws := [i32c (c % 2^32)]) (ws' := []) (z := z) (rest := rest) (Q := Q) (B := B)
      (i := .BR_IF (.mk_uN k))
      (Spec.Step_pure.br_if_false _ (.mk_uN k) (wf_i32_mod c) (by rfl)
        (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])) (by simpa using h)
    exact this
  · rw [if_neg hc] at h
    intro tail
    have hs : Spec.Step_pure (vals [i32c (c % 2^32)] ++ [.BR_IF (.mk_uN k)]) [.BR (.mk_uN k)] :=
      Spec.Step_pure.br_if_true _ _ (wf_i32_mod c) (by rfl)
        (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])
    have h1 := steps_ctx pre (rest ++ tail) (steps_one (Spec.Step.pure z _ _ hs) : Spec.Steps _ (.mk_config z [.BR (.mk_uN k)]))
    refine .inr ⟨k, z, pre, rest ++ tail, h, ?_⟩
    have e : vals pre ++ ((vals [i32c (c % 2^32)] ++ [.BR_IF (.mk_uN k)]) ++ (rest ++ tail)) =
        vals (pre ++ [i32c (c % 2^32)]) ++ (.BR_IF (.mk_uN k) :: rest ++ tail) := by simp [vals_append]
    rw [e] at h1; simpa using h1

theorem blocktype_empty (z : Spec.state) :
    Spec.fun_blocktype_ z (._RESULT none) (.mk_instrtype (.mk_list []) [] (.mk_list [])) :=
  Spec.fun_blocktype_.fun_blocktype__case_1 z none

/-- The branch postcondition inside a label: a branch to the label itself (depth 0) goes on
with `go`; a deeper one leaves with one level less. -/
def labelBr (pre : List Spec.val) (go : Spec.state → Prop) (B : BrPost) : BrPost
  | 0, z', _ => go z'
  | k + 1, z', vs' => B k z' (pre ++ vs')

/-- The common part of `block` and `loop`: a label with continuation `cont` around a body
that the spec runs to a normal end (label_vals) or a branch (br_label_zero, br_label_succ). -/
theorem sem_label {z pre body rest Q} {B : BrPost} {cont : List Spec.instr} {i : Spec.instr}
    (henter : Spec.Step_read (.mk_config z [i]) [.LABEL_ 0 cont body])
    (hb : Sem z [] body (fun z' vs' => Sem z' (pre ++ vs') rest Q B)
      (labelBr pre (fun z' => Sem z' pre (cont ++ rest) Q B) B)) :
    Sem z pre (i :: rest) Q B := by
  intro tail
  have h1 : Spec.Steps (.mk_config z (vals pre ++ (i :: rest ++ tail)))
      (.mk_config z (vals pre ++ ([.LABEL_ 0 cont body] ++ (rest ++ tail)))) := by
    have := steps_ctx pre (rest ++ tail) (steps_one (Spec.Step.read z [i] _ henter))
    simpa using this
  rcases hb [] with ⟨z2, vs2, hq, h2⟩ | ⟨k, z2, vs2, junk, hbr, h2⟩
  · simp only [List.append_nil] at h2
    have h3 := steps_ctx pre (rest ++ tail) (steps_label 0 cont h2)
    have h4 : Spec.Steps (.mk_config z2 (vals pre ++ ([.LABEL_ 0 cont (vals vs2)] ++ (rest ++ tail))))
        (.mk_config z2 (vals (pre ++ vs2) ++ (rest ++ tail))) := by
      have := steps_ctx pre (rest ++ tail)
        (steps_one (Spec.Step.pure z2 _ _ (Spec.Step_pure.label_vals 0 cont vs2)))
      simpa [vals_append] using this
    rcases hq tail with ⟨z3, vs3, hq3, h5⟩ | ⟨k, z3, vs3, junk, hb3, h5⟩
    · exact .inl ⟨z3, vs3, hq3, steps_trans h1 (steps_trans h3 (steps_trans h4 h5))⟩
    · exact .inr ⟨k, z3, vs3, junk, hb3, steps_trans h1 (steps_trans h3 (steps_trans h4 h5))⟩
  · simp only [List.append_nil] at h2
    have h3 := steps_ctx pre (rest ++ tail) (steps_label 0 cont h2)
    cases k with
    | zero =>
      have h4 : Spec.Steps (.mk_config z2 (vals pre ++ ([.LABEL_ 0 cont (vals vs2 ++ (.BR (.mk_uN 0) :: junk))] ++ (rest ++ tail))))
          (.mk_config z2 (vals pre ++ ((cont ++ rest) ++ tail))) := by
        have hs := Spec.Step_pure.br_label_zero 0 cont vs2 [] (.mk_uN 0) junk (by simp [Spec.proj_uN_0])
        have := steps_ctx pre (rest ++ tail) (steps_one (Spec.Step.pure z2 _ _ hs))
        simpa using this
      rcases hbr tail with ⟨z3, vs3, hq3, h5⟩ | ⟨k, z3, vs3, junk', hb3, h5⟩
      · exact .inl ⟨z3, vs3, hq3, steps_trans h1 (steps_trans h3 (steps_trans h4 h5))⟩
      · exact .inr ⟨k, z3, vs3, junk', hb3, steps_trans h1 (steps_trans h3 (steps_trans h4 h5))⟩
    | succ k =>
      have h4 : Spec.Steps (.mk_config z2 (vals pre ++ ([.LABEL_ 0 cont (vals vs2 ++ (.BR (.mk_uN (k + 1)) :: junk))] ++ (rest ++ tail))))
          (.mk_config z2 (vals (pre ++ vs2) ++ (.BR (.mk_uN k) :: (rest ++ tail)))) := by
        have hs := Spec.Step_pure.br_label_succ 0 cont vs2 (.mk_uN (k + 1)) junk (by simp [Spec.proj_uN_0])
        have := steps_ctx pre (rest ++ tail) (steps_one (Spec.Step.pure z2 _ _ hs))
        simpa [vals, Spec.proj_uN_0] using this
      exact .inr ⟨k, z2, pre ++ vs2, rest ++ tail, hbr, steps_trans h1 (steps_trans h3 h4)⟩

/-- `block` with block type `[] -> []`. -/
theorem sem_block {z pre body rest Q} {B : BrPost}
    (hb : Sem z [] body (fun z' vs' => Sem z' (pre ++ vs') rest Q B)
      (labelBr pre (fun z' => Sem z' pre rest Q B) B)) :
    Sem z pre (.BLOCK (._RESULT none) body :: rest) Q B := by
  refine sem_label (cont := []) ?_ (by simpa using hb)
  have := Spec.Step_read.block z [] 0 (._RESULT none) body 0 [] [] _ (blocktype_empty z) (instrtype_beq _ _)
  simpa using this

/-- `loop` with block type `[] -> []`: a branch to it runs the loop again. -/
theorem sem_loop {z pre body rest Q} {B : BrPost}
    (hb : Sem z [] body (fun z' vs' => Sem z' (pre ++ vs') rest Q B)
      (labelBr pre (fun z' => Sem z' pre (.LOOP (._RESULT none) body :: rest) Q B) B)) :
    Sem z pre (.LOOP (._RESULT none) body :: rest) Q B := by
  refine sem_label (cont := [.LOOP (._RESULT none) body]) ?_ (by simpa using hb)
  have := Spec.Step_read.loop z [] 0 (._RESULT none) body [] [] 0 _ (blocktype_empty z) (instrtype_beq _ _)
  simpa using this

/-- A pure step of the top values and `i` to other code `is'`. -/
theorem sem_pure_to {z : Spec.state} {pre ws : List Spec.val} {i : Spec.instr} {is' : List Spec.instr}
    {rest : List Spec.instr} {Q : Post} {B : BrPost}
    (hs : Spec.Step_pure (vals ws ++ [i]) is')
    (h : Sem z pre (is' ++ rest) Q B) : Sem z (pre ++ ws) (i :: rest) Q B := by
  intro tail
  have h1 := steps_ctx pre (rest ++ tail) (steps_one (Spec.Step.pure z _ _ hs))
  have e1 : vals pre ++ ((vals ws ++ [i]) ++ (rest ++ tail)) = vals (pre ++ ws) ++ (i :: rest ++ tail) := by
    simp [vals_append]
  rw [e1] at h1
  have h2 := h tail
  simp only [List.append_assoc] at h2
  rcases h2 with ⟨z2, vs2, hq, h2⟩ | ⟨k, z2, vs2, junk, hb, h2⟩
  · exact .inl ⟨z2, vs2, hq, steps_trans h1 h2⟩
  · exact .inr ⟨k, z2, vs2, junk, hb, steps_trans h1 h2⟩

/-- `if` without `else` (an empty else branch), block type `[] -> []`. -/
theorem sem_if {z pre c body rest Q} {B : BrPost}
    (h : if c % 2^32 = 0 then Sem z pre rest Q B else
      Sem z [] body (fun z' vs' => Sem z' (pre ++ vs') rest Q B)
        (labelBr pre (fun z' => Sem z' pre rest Q B) B)) :
    Sem z (pre ++ [i32c (c % 2^32)]) (.IFELSE (._RESULT none) body [] :: rest) Q B := by
  by_cases hc : c % 2^32 = 0
  · rw [if_pos hc] at h
    refine sem_pure_to (Spec.Step_pure.if_false _ _ _ _ (wf_i32_mod c) (by rfl)
        (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])) ?_
    exact sem_block (sem_nil (by simpa using h))
  · rw [if_neg hc] at h
    refine sem_pure_to (Spec.Step_pure.if_true _ _ _ _ (wf_i32_mod c) (by rfl)
        (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc])) ?_
    exact sem_block h

/-- Weakening of the postconditions. -/
theorem sem_mono {z vs is} {Q Q' : Post} {B B' : BrPost} (h : Sem z vs is Q B)
    (hq : ∀ z vs, Q z vs → Q' z vs) (hb : ∀ k z vs, B k z vs → B' k z vs) : Sem z vs is Q' B' := by
  intro tail
  rcases h tail with ⟨z2, vs2, hq2, h2⟩ | ⟨k, z2, vs2, junk, hb2, h2⟩
  · exact .inl ⟨z2, vs2, hq _ _ hq2, h2⟩
  · exact .inr ⟨k, z2, vs2, junk, hb _ _ _ hb2, h2⟩

end L4Factoidal.WasmVM.Proofs.SpecWP
