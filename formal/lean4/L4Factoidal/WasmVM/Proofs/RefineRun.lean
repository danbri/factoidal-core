/-
L4Factoidal.WasmVM.Proofs.RefineRun: the whole-state relation `R` between the engine's
registers and the spec configuration, and the step theorem `step_refines`
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Refinement: the state abstraction").

`R e c`: the configuration `c` is the running function's body (`ActR`, or `DoneR` once
it has branched to its own label) inside `FRAME_` inside its callers' bodies (`wrap`,
`CallersR`), with the spec store holding the engine's memories (`StoreR`).

`stepE` is one engine step for the ops covered so far; `stepE_run` shows that `run`
makes that step; `step_refines`: `R e c → stepE e = some e' → ∃ c', Spec.Steps c c' ∧ R e' c'`.
-/
import L4Factoidal.WasmVM.Proofs.Refine
import L4Factoidal.WasmVM.Proofs.Fuse

namespace L4Factoidal.WasmVM.Proofs.Refine
open L4Factoidal.WasmVM SlotLemmas MemLaws Run

/-! ### Normal form: enter and leave blocks first -/

/-- The current code starts with an instruction that is not a block, or the function's
code is done. -/
def Canon (is : List Spec.instr) (H : List Hole) : Prop :=
  (is = [] → H.length ≤ 1) ∧ (∀ st b r, is ≠ .BLOCK (._RESULT st) b :: r) ∧
    (∀ st b r, is ≠ .LOOP (._RESULT st) b :: r)

theorem norm {code locals maxH s fp sp pc f} (z : Spec.state) : ∀ (n : Nat) {body L H d e te tsC valsC is},
    meas is H < n → ActW code locals maxH s fp sp pc f body L H d e te tsC valsC is →
    ∃ body' L' H' d' e' te' tsC' valsC' is',
      ActW code locals maxH s fp sp pc f body' L' H' d' e' te' tsC' valsC' is' ∧
      Spec.Steps (.mk_config z body) (.mk_config z body') ∧ Canon is' H' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ n ih =>
    intro body L H d e te tsC valsC is hm hw
    by_cases hb : ∃ st b r, is = .BLOCK (._RESULT st) b :: r
    · obtain ⟨st, b, r, rfl⟩ := hb
      obtain ⟨body', _, _, _, _, _, _, _, _, hw', hs, hm'⟩ := enter_block hw z
      obtain ⟨b2, _, _, _, _, _, _, _, _, hw2, hs2, hc2⟩ := ih (by omega) hw'
      exact ⟨b2, _, _, _, _, _, _, _, _, hw2, steps_trans hs hs2, hc2⟩
    by_cases hl : ∃ st b r, is = .LOOP (._RESULT st) b :: r
    · obtain ⟨st, b, r, rfl⟩ := hl
      obtain ⟨body', _, _, _, _, _, _, _, _, hw', hs, hm'⟩ := enter_loop hw z
      obtain ⟨b2, _, _, _, _, _, _, _, _, hw2, hs2, hc2⟩ := ih (by omega) hw'
      exact ⟨b2, _, _, _, _, _, _, _, _, hw2, steps_trans hs hs2, hc2⟩
    by_cases hx : is = [] ∧ 2 ≤ H.length
    · obtain ⟨rfl, h2⟩ := hx
      obtain ⟨body', _, _, _, _, _, _, _, _, hw', hs, hm'⟩ := exit_level hw h2 z
      obtain ⟨b2, _, _, _, _, _, _, _, _, hw2, hs2, hc2⟩ := ih (by omega) hw'
      exact ⟨b2, _, _, _, _, _, _, _, _, hw2, steps_trans hs hs2, hc2⟩
    refine ⟨body, _, _, _, _, _, _, _, _, hw, Spec.Steps.refl _ _, fun h0 => ?_, fun st b r h => hb ⟨st, b, r, h⟩,
      fun st b r h => hl ⟨st, b, r, h⟩⟩
    have : ¬ (2 ≤ H.length) := fun h2 => hx ⟨h0, h2⟩
    omega

/-! ### Callers -/

/-- A caller: its frame, the arity of the callee's frame, its open blocks, its values
below the call and its code after the call. -/
structure Caller where
  f : Spec.frame
  m : Nat
  H : List Hole
  vals : List Spec.val
  rest : List Spec.instr

/-- The whole instruction sequence: `FRAME_ m f x` inside the callers, innermost first. -/
noncomputable def wrap : List Caller → Nat → Spec.frame → List Spec.instr → List Spec.instr
  | [], m, f, x => [.FRAME_ m f x]
  | c :: cs, m, f, x => wrap cs c.m c.f (plug c.H (c.vals.map Spec.instr_val ++ (.FRAME_ m f x :: c.rest)))

theorem step_wrap (S S' : Spec.store) (f0 : Spec.frame) : ∀ (cs : List Caller) (m : Nat) (f f' : Spec.frame)
    (x x' : List Spec.instr),
    Spec.Step (.mk_config (.mk_state S f) x) (.mk_config (.mk_state S' f') x') →
    Spec.Step (.mk_config (.mk_state S f0) (wrap cs m f x)) (.mk_config (.mk_state S' f0) (wrap cs m f' x'))
  | [], m, f, f', x, x', h => Spec.Step.ctxt_frame S f0 m f x S' f' x' h
  | c :: cs, m, f, f', x, x', h => by
    apply step_wrap S S' f0 cs c.m c.f c.f
    apply step_plug
    have := step_ctx (.mk_state S c.f) (.mk_state S' c.f) c.vals [.FRAME_ m f x] [.FRAME_ m f' x'] c.rest
      (Spec.Step.ctxt_frame S c.f m f x S' f' x' h)
    simpa using this

theorem steps_wrap (f0 : Spec.frame) (cs : List Caller) (m : Nat) : ∀ {S f x S' f' x'},
    Spec.Steps (.mk_config (.mk_state S f) x) (.mk_config (.mk_state S' f') x') →
    Spec.Steps (.mk_config (.mk_state S f0) (wrap cs m f x)) (.mk_config (.mk_state S' f0) (wrap cs m f' x')) := by
  intro S f x S' f' x' h
  generalize hc : Spec.config.mk_config (.mk_state S f) x = c at h
  generalize hc' : Spec.config.mk_config (.mk_state S' f') x' = c' at h
  induction h generalizing S f x with
  | refl => cases hc; cases hc'; exact Spec.Steps.refl _ _
  | trans z0 i0 z2 i2 z1 i1 hs _ ih =>
    cases hc
    cases z1 with
    | mk_state S1 f1 =>
      exact Spec.Steps.trans _ _ _ _ _ _ (step_wrap _ _ f0 cs m _ _ _ _ hs) (ih rfl hc')

/-- The callers' parts of the slots: below `bound` (the running function's `fp`). The
engine's frames are listed innermost first (`frames.toList.reverse`). -/
def CallersR (s : Slots) : Nat → List Frame → List Caller → Prop
  | _, [], [] => True
  | bound, fr :: frs, c :: cs =>
    ∃ locals maxH L d e te tsC rs,
      Nest fr.code locals maxH s fr.fp.toNat L c.H d e te ∧
      SlotsR s (fr.fp.toNat + locals.length + d) tsC c.vals ∧
      Comp fr.code locals maxH L d fr.pc.toNat (tsC ++ rs) c.rest e te ∧
      fr.fp.toNat + locals.length + d + tsC.length ≤ bound ∧
      LocalsR s fr.fp.toNat locals c.f ∧ CallersR s fr.fp.toNat frs cs
  | _, _, _ => False

theorem CallersR.frame {s s' : Slots} : ∀ {bound frs cs}, CallersR s bound frs cs →
    (∀ i, i < bound → slot s' i = slot s i) → CallersR s' bound frs cs
  | _, [], [], _, _ => trivial
  | _, _ :: _, _ :: _, ⟨locals, maxH, L, d, e, te, tsC, rs, hn, hsl, hc, hb, hloc, hrest⟩, hs =>
    ⟨locals, maxH, L, d, e, te, tsC, rs, Nest.frame hn fun i _ h => hs i (by omega),
      SlotsR.frame hsl fun i _ h => hs i (by omega), hc, hb,
      LocalsR.frame hloc fun x hx => hs _ (by omega), CallersR.frame hrest fun i h => hs i (by omega)⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-! ### Code positions are in range -/

theorem Comp.le {code locals maxH L d pc ts is pe te} (h : Comp code locals maxH L d pc ts is pe te) : pc ≤ pe := by
  induction h <;> omega

theorem Nest.bounds {code locals maxH s fp L H d e te} (hn : Nest code locals maxH s fp L H d e te) :
    e < code.size ∧ ∀ lb ∈ L, lb.pc < code.size := by
  induction hn with
  | func pe rs m h =>
    have := (Array.getElem?_eq_some_iff.mp h).1
    exact ⟨this, by intro lb hl; simp at hl; subst hl; exact this⟩
  | block vals tsH rs pe1 rest _ _ hc ih =>
    have := hc.le
    refine ⟨by omega, fun lb hl => ?_⟩
    simp at hl; rcases hl with rfl | hl
    · simp; omega
    · exact ih.2 lb hl
  | loop vals tsH rs ps pe1 rest st body _ _ hb hc ih =>
    have := hc.le; have := hb.le
    refine ⟨by omega, fun lb hl => ?_⟩
    simp at hl; rcases hl with rfl | hl
    · simp; omega
    · exact ih.2 lb hl

/-! ### One engine step -/

/-- The engine's registers and store (`run`'s arguments). -/
structure EState (M : Type) where
  st : StoreOf M
  stack : Slots
  sp : USize
  fp : USize
  pc : USize
  code : Array Op
  inst : ModuleInst
  frames : Array Frame

section Engine
variable {M : Type} [LinearMemory M]

def EState.run (lim : RunLimits) (e : EState M) (n : Nat) : StoreOf M × Machine × Nat × Event :=
  Run.run lim e.st e.stack e.sp e.fp e.pc e.code e.inst e.frames n

/-- A straight-line op, then the next pc. -/
def simpleNext (e : EState M) (o : Simple) : EState M :=
  { e with stack := (Simple.exec e.fp o e.stack e.sp).stack, sp := (Simple.exec e.fp o e.stack e.sp).sp,
           pc := e.pc + 1 }

/-- What the engine does with op `o`, for the ops covered so far (`none` for the others
and for a trap). The definitions copy the cases of `run`. -/
def stepOp (e : EState M) : Op → Option (EState M)
  | .const v => some (simpleNext e (.const v))
  | .localGet x => some (simpleNext e (.localGet x.toUSize))
  | .localSet x => some (simpleNext e (.localSet x.toUSize))
  | .localTee x => some (simpleNext e (.localTee x.toUSize))
  | .num op => if op.isBinary && !op.mayTrap then some (simpleNext e (.bin op)) else none
  | .br t =>
    let x := brMove e.stack e.sp e.fp t
    some { e with stack := x.stack, sp := x.sp, pc := t.pc.toUSize }
  | .brIf t =>
    if rd e.stack (e.sp - 1) != 0 then
      let x := brMove e.stack (e.sp - 1) e.fp t
      some { e with stack := x.stack, sp := x.sp, pc := t.pc.toUSize }
    else some { e with sp := e.sp - 1, pc := e.pc + 1 }
  | .load op mem off =>
    match op with
    | .i32 =>
      let ea := (rd e.stack (e.sp - 1)).toNat + off
      let d := memData e.st e.inst mem
      if h : ea + LoadOp.width .i32 ≤ LinearMemory.size d then
        some { e with stack := wr e.stack (e.sp - 1) (loadVal d ea .i32 h), pc := e.pc + 1 }
      else none
    | _ => none
  | .store op mem off =>
    match op with
    | .i32 =>
      let v := rd e.stack (e.sp - 1)
      let ea := (rd e.stack (e.sp - 2)).toNat + off
      let ma := e.inst.mems[mem]!
      if ea + StoreOp.width .i32 ≤ LinearMemory.size (e.st.mems[ma]!).data then
        some { e with st := storeMem e.st ma ea v .i32, sp := e.sp - 2, pc := e.pc + 1 }
      else none
    | _ => none
  | _ => none

/-- One engine step for the covered ops. -/
def stepE (e : EState M) : Option (EState M) :=
  if h : e.pc < e.code.usize then stepOp e (e.code[e.pc.toNat]'(pc_ok h)) else none

/-- `run` makes the step that `stepE` names: one fuel unit, then the loop goes on from
`e'`. So every theorem about `stepE` is a theorem about the engine's own loop. -/
theorem stepE_run (lim : RunLimits) (e e' : EState M) (n : Nat) (h : stepE e = some e') :
    e.run lim (n + 1) = e'.run lim n := by
  unfold stepE at h
  split at h
  · rename_i hpc
    generalize hc : e.code[e.pc.toNat]'(pc_ok hpc) = o at h
    unfold EState.run
    conv => lhs; unfold run
    rw [dif_pos hpc]
    simp only [Array.uget, hc]
    cases o <;> simp only [stepOp, reduceCtorEq] at h
    case const v => injection h with h; subst h; rfl
    case localGet x => injection h with h; subst h; rfl
    case localSet x => injection h with h; subst h; rfl
    case localTee x => injection h with h; subst h; rfl
    case num op =>
      split at h
      · rename_i hb
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
        injection h with h; subst h
        simp only [hb.1, hb.2, ↓reduceIte, Bool.false_eq_true]; rfl
      · simp at h
    case br t => injection h with h; subst h; rfl
    case brIf t =>
      split at h
      · rename_i hc0
        injection h with h; subst h
        simp only [hc0, ↓reduceIte]
      · rename_i hc0
        injection h with h; subst h
        simp only [Bool.not_eq_true] at hc0
        simp only [hc0, Bool.false_eq_true, ↓reduceIte]
    case load op mem off =>
      cases op <;> simp only [reduceCtorEq] at h
      split at h
      · rename_i hin
        injection h with h; subst h
        simp only [hin, ↓reduceDIte]
      · simp at h
    case store op mem off =>
      cases op <;> simp only [reduceCtorEq] at h
      split at h
      · rename_i hin
        injection h with h; subst h
        simp only [hin, ↓reduceIte]
      · simp at h
  · simp at h

end Engine

/-! ### Helpers for the registers -/

theorem rd_slot (s : Slots) (u : USize) (n : Nat) (h : u.toNat = n) (hn : n < USize.size) :
    Slots.rd s u = slot s n := by
  unfold slot; congr 1; apply USize.toNat_inj.mp; rw [natU n hn, h]

theorem stepE_of {M : Type} [LinearMemory M] (e : EState M) (o : Op) (h : e.code[e.pc.toNat]? = some o)
    (hC : e.code.size < USize.size) : stepE e = stepOp e o := by
  have hlt := (Array.getElem?_eq_some_iff.mp h).1
  have hpc : e.pc < e.code.usize := by
    rw [USize.lt_iff_toNat_lt]; simp only [Array.usize]; rw [natU _ hC]; exact hlt
  unfold stepE; rw [dif_pos hpc]
  rw [Array.getElem?_eq_getElem hlt] at h; injection h with h; rw [h]

theorem callers_wr {s : Slots} {fp : Nat} {frs cs} (h : CallersR s fp frs cs) (u : USize) (v : UInt64)
    (hS : s.size < USize.size) (hfp : fp ≤ s.size) (hu : fp ≤ u.toNat) : CallersR (Slots.wr s u v) fp frs cs :=
  CallersR.frame h fun i hi => slot_wr_ne s u v i hS (by
    have : i < s.size := by omega
    omega) (by omega)

/-- `brMove` moves the kept values down to the target height and leaves the slots below. -/
theorem brMove_moved (s : Slots) (sp fp : USize) (t : BrTarget) (hS : s.size < USize.size)
    (h1 : fp.toNat + t.height + t.keep ≤ sp.toNat) (h2 : sp.toNat ≤ s.size / 8) :
    Moved s (brMove s sp fp t).stack (sp.toNat - t.keep) (fp.toNat + t.height) t.keep ∧
      (brMove s sp fp t).sp.toNat = fp.toNat + t.height + t.keep := by
  have hk : t.keep.toUSize.toNat = t.keep := natU _ (by omega)
  have hh : t.height.toUSize.toNat = t.height := natU _ (by omega)
  have hdst : (fp + t.height.toUSize).toNat = fp.toNat + t.height := by rw [addU _ _ (by omega), hh]
  have hsrc : (sp - t.keep.toUSize).toNat = sp.toNat - t.keep := by rw [subU _ _ (by omega), hk]
  unfold brMove
  simp only
  refine ⟨?_, by rw [addU _ _ (by rw [hdst, hk]; omega), hdst, hk]⟩
  split
  · rename_i heq
    have e1 : sp.toNat - t.keep = fp.toNat + t.height := by
      have := congrArg USize.toNat (of_decide_eq_true (by simpa using heq) : sp - t.keep.toUSize = fp + t.height.toUSize)
      rw [hsrc, hdst] at this; exact this
    refine ⟨rfl, fun i _ => rfl, fun j _ => by rw [e1]⟩
  · refine ⟨moveDown_size _ _ _ _, fun i hi => ?_, fun j hj => ?_⟩
    · unfold slot
      rw [moveDown_rd _ _ _ _ hS (by rw [hsrc]; omega) (by rw [hsrc, hdst]; omega), if_neg (by
        rw [natU i (by omega), hdst]; omega)]
    · unfold slot
      rw [moveDown_rd _ _ _ _ hS (by rw [hsrc]; omega) (by rw [hsrc, hdst]; omega), if_pos (by
        rw [natU _ (by omega), hdst]; omega)]
      congr 1
      apply USize.toNat_inj.mp
      have hj' : (fp.toNat + t.height + j).toUSize.toNat = fp.toNat + t.height + j := natU _ (by omega)
      have hsub : ((fp.toNat + t.height + j).toUSize - (fp + t.height.toUSize)).toNat = j := by
        rw [subU _ _ (by rw [hj', hdst]; omega), hj', hdst]; omega
      have hadd : ((sp - t.keep.toUSize) + ((fp.toNat + t.height + j).toUSize - (fp + t.height.toUSize))).toNat =
          sp.toNat - t.keep + j := by
        rw [addU _ _ (by rw [hsrc, hsub]; omega), hsrc, hsub]
      rw [hadd, natU _ (by omega)]

end L4Factoidal.WasmVM.Proofs.Refine
