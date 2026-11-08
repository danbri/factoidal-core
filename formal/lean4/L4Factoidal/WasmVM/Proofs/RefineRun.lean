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

/-! ### The whole-state relation -/

section Top
variable {M : Type} [LinearMemory M] [LinearMemoryLaws M]

/-- The spec store holds the engine's memories (other store parts are not related yet). -/
def StoreR (st : StoreOf M) (S : Spec.store) : Prop :=
  ∀ a, a < st.mems.size → a < S.MEMS.length ∧ MemR (st.mems[a]!).data S.MEMS[a]!

/-- Memory 0 of the instance is memory 0 of the frame's module. -/
def MemOk (st : StoreOf M) (inst : ModuleInst) (f : Spec.frame) : Prop :=
  ∀ a, inst.mems[0]? = some a → f.MODULE.MEMS[0]? = some a ∧ a < st.mems.size

/-- Code without loads and stores (an instance without memory runs only such code). -/
def NoMem (code : Array Op) : Prop :=
  ∀ (pc : Nat) mem off, (∀ op, code[pc]? ≠ some (Op.load op mem off)) ∧ (∀ op, code[pc]? ≠ some (Op.store op mem off))

/-- What `R` says besides the running function's body. -/
structure Ctx (e : EState M) (S : Spec.store) (f : Spec.frame) (cs : List Caller) (maxH : Nat) : Prop where
  store : StoreR e.st S
  memok : MemOk e.st e.inst f
  mem : (e.inst.mems[0]?).isSome ∨ NoMem e.code
  callers : CallersR e.stack e.fp.toNat e.frames.toList.reverse cs
  hS : e.stack.size < USize.size
  hC : e.code.size < USize.size
  hcap : e.fp.toNat + maxH ≤ e.stack.size / 8

/-- THE STATE ABSTRACTION. The spec configuration `c` is: the store `S` (holding the
engine's memories), and the running function's body (`ActR`: open blocks, values,
locals, code position; or `DoneR`) inside `FRAME_ m f`, inside the callers' bodies. -/
def R (e : EState M) (c : Spec.config) : Prop :=
  ∃ S f0 cs m f locals maxH body,
    c = .mk_config (.mk_state S f0) (wrap cs m f body) ∧ Ctx e S f cs maxH ∧
    (ActR e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body ∨
      DoneR e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body)

/-- One engine step `e'`, matched by spec steps under the function's frame. -/
def Next (e' : EState M) (S : Spec.store) (f : Spec.frame) (body : List Spec.instr) (cs : List Caller)
    (locals : List ValType) (maxH : Nat) : Prop :=
  ∃ S' f' body', Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S' f') body') ∧
    Ctx e' S' f' cs maxH ∧
    (ActR e'.code locals maxH e'.stack e'.fp.toNat e'.sp.toNat e'.pc.toNat f' body' ∨
      DoneR e'.code locals maxH e'.stack e'.fp.toNat e'.sp.toNat e'.pc.toNat f' body')

theorem Ctx.regs {e : EState M} {S f cs maxH} (hx : Ctx e S f cs maxH) (e' : EState M) (f' : Spec.frame)
    (hst : e'.st = e.st) (hinst : e'.inst = e.inst) (hcode : e'.code = e.code) (hfp : e'.fp = e.fp)
    (hfr : e'.frames = e.frames) (hsize : e'.stack.size = e.stack.size)
    (hbelow : ∀ i, i < e.fp.toNat → slot e'.stack i = slot e.stack i) (hmod : f'.MODULE = f.MODULE) :
    Ctx e' S f' cs maxH := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hst]; exact h1
  · intro a ha; rw [hinst] at ha; rw [hmod, hst]; exact h2 a ha
  · rw [hinst, hcode]; exact h3
  · rw [hfp, hfr]; exact CallersR.frame h4 fun i hi => hbelow i hi
  · rw [hsize]; exact h5
  · rw [hcode]; exact h6
  · rw [hfp, hsize]; exact h7

theorem pc_succ (e : EState M) (o : Op) (hcode : e.code[e.pc.toNat]? = some o) (hC : e.code.size < USize.size) :
    (e.pc + 1).toNat = e.pc.toNat + 1 := by
  have := (Array.getElem?_eq_some_iff.mp hcode).1
  exact addLit e.pc 1 (by decide) (by omega)

end Top

/-! ### The step, case by case -/

section Cases
variable {M : Type} [LinearMemory M] [LinearMemoryLaws M]
variable {e e' : EState M} {S : Spec.store} {f : Spec.frame} {cs : List Caller} {maxH : Nat}
  {locals : List ValType} {body : List Spec.instr} {L : List Lbl} {H : List Hole} {d en : Nat}
  {te tsC : List ValType} {valsC : List Spec.val} {rest : List Spec.instr}

theorem ActW.sp_le (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC rest)
    (hx : Ctx e S f cs maxH) : e.fp.toNat + locals.length ≤ e.sp.toNat ∧ e.sp.toNat ≤ e.stack.size / 8 := by
  have h1 := hw.2.2.2.1; have h2 := hw.2.2.2.2.1; have h3 := hx.hcap
  omega

theorem case_const32 {n : Nat} {b : UInt64} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)) :: rest))
    (hcode : e.code[e.pc.toNat]? = some (.const b)) (hs : stepE e = some e') :
    Next e' S f body cs locals maxH := by
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hw' := op_const32 hcode hw hx.hS hx.hcap e.sp rfl
  have hsp := hw'.2.2.2.1; have hmax := hw'.2.2.2.2.1; have hcap := hx.hcap; have hS := hx.hS
  simp at hsp hmax
  have hsp1 : (e.sp + 1).toNat = e.sp.toNat + 1 := addLit e.sp 1 (by decide) (by omega)
  refine ⟨S, f, body, Spec.Steps.refl _ _, Ctx.regs hx _ f rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, tsC ++ [.i32], valsC ++ [i32c n], rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack e.sp b) e.fp.toNat (e.sp + 1).toNat (e.pc + 1).toNat f body
    L H d en te (tsC ++ [.i32]) (valsC ++ [i32c n]) rest
  rw [hsp1, pc_succ e _ hcode hx.hC]; exact hw'

theorem case_const64 {n : Nat} {b : UInt64} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN n)) :: rest))
    (hcode : e.code[e.pc.toNat]? = some (.const b)) (hs : stepE e = some e') :
    Next e' S f body cs locals maxH := by
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hw' := op_const64 hcode hw hx.hS hx.hcap e.sp rfl
  have hsp := hw'.2.2.2.1; have hmax := hw'.2.2.2.2.1; have hcap := hx.hcap; have hS := hx.hS
  simp at hsp hmax
  have hsp1 : (e.sp + 1).toNat = e.sp.toNat + 1 := addLit e.sp 1 (by decide) (by omega)
  refine ⟨S, f, body, Spec.Steps.refl _ _, Ctx.regs hx _ f rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, tsC ++ [.i64], valsC ++ [i64c n], rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack e.sp b) e.fp.toNat (e.sp + 1).toNat (e.pc + 1).toNat f body
    L H d en te (tsC ++ [.i64]) (valsC ++ [i64c n]) rest
  rw [hsp1, pc_succ e _ hcode hx.hC]; exact hw'

theorem case_localGet {x : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.LOCAL_GET (.mk_uN x) :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @localGet _ _ _ _ _ _ _ _ t hcode hloct hroom hnext =>
  have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  obtain ⟨_, t', v, body', hw', hst⟩ := op_localGet S hw hx.hS hx.hcap e.sp rfl
  have hsp := hw'.2.2.2.1; have hmax := hw'.2.2.2.2.1; have hcap := hx.hcap; have hS := hx.hS
  simp at hsp hmax
  have hsp1 : (e.sp + 1).toNat = e.sp.toNat + 1 := addLit e.sp 1 (by decide) (by omega)
  have hrd : Slots.rd e.stack (e.fp + x.toUSize) = slot e.stack (e.fp.toNat + x) :=
    rd_slot _ _ _ (by rw [addU _ _ (by rw [natU x (by omega)]; omega), natU x (by omega)]) (by omega)
  refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, tsC ++ [t'], valsC ++ [v], rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack e.sp (Slots.rd e.stack (e.fp + x.toUSize))) e.fp.toNat
    (e.sp + 1).toNat (e.pc + 1).toNat f body' L H d en te (tsC ++ [t']) (valsC ++ [v]) rest
  rw [hsp1, pc_succ e _ hcode hx.hC, hrd]; exact hw'

theorem case_localSet {x : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.LOCAL_SET (.mk_uN x) :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @localSet _ _ _ ts _ _ _ _ t hcode hloct hnext =>
  have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hsp0 := hw.2.2.2.1; simp at hsp0
  have hcap := hx.hcap; have hS := hx.hS
  have hu : (e.fp + x.toUSize).toNat = e.fp.toNat + x := by
    rw [addU _ _ (by rw [natU x (by omega)]; omega), natU x (by omega)]
  obtain ⟨_, ts', v, vs', body', hw', hst⟩ := op_localSet S hw hx.hS hx.hcap (e.fp + x.toUSize) hu
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  have hrd : Slots.rd e.stack (e.sp - 1) = slot e.stack (e.sp.toNat - 1) := rd_slot _ _ _ hsm1 (by omega)
  refine ⟨S, setLocal f x v, body', hst, Ctx.regs hx _ _ rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, ts', vs', rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack (e.fp + x.toUSize) (Slots.rd e.stack (e.sp - 1))) e.fp.toNat
    (e.sp - 1).toNat (e.pc + 1).toNat (setLocal f x v) body' L H d en te ts' vs' rest
  rw [hsm1, pc_succ e _ hcode hx.hC, hrd]; exact hw'

theorem case_localTee {x : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.LOCAL_TEE (.mk_uN x) :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @localTee _ _ _ ts _ _ _ _ t hcode hloct hnext =>
  have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hsp0 := hw.2.2.2.1; simp at hsp0
  have hcap := hx.hcap; have hS := hx.hS
  have hu : (e.fp + x.toUSize).toNat = e.fp.toNat + x := by
    rw [addU _ _ (by rw [natU x (by omega)]; omega), natU x (by omega)]
  obtain ⟨_, v, body', hw', hst⟩ := op_localTee S hw hx.hS hx.hcap (e.fp + x.toUSize) hu
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  have hrd : Slots.rd e.stack (e.sp - 1) = slot e.stack (e.sp.toNat - 1) := rd_slot _ _ _ hsm1 (by omega)
  refine ⟨S, setLocal f x v, body', hst, Ctx.regs hx _ _ rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, ts ++ [t], valsC, rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack (e.fp + x.toUSize) (Slots.rd e.stack (e.sp - 1))) e.fp.toNat
    e.sp.toNat (e.pc + 1).toNat (setLocal f x v) body' L H d en te (ts ++ [t]) valsC rest
  rw [pc_succ e _ hcode hx.hC, hrd]; exact hw'

theorem case_binop {nt : Spec.numtype} {bop : Spec.binop_} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.BINOP nt bop :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @binop _ _ _ ts _ _ _ op t _ _ hcode hbin hnext =>
  rw [stepE_of e _ hcode hx.hC] at hs
  have hp := hbin.pure
  simp only [NumOp.pureBin] at hp
  simp only [stepOp, hp, ↓reduceIte, Option.some.injEq] at hs; subst hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hsp0 := hw.2.2.2.1; simp at hsp0
  have hcap := hx.hcap; have hS := hx.hS
  have hsm2 : (e.sp - 2).toNat = e.sp.toNat - 2 := by rw [subU _ _ (by rw [lit 2 (by decide)]; omega), lit 2 (by decide)]
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  obtain ⟨t', ts', vr, vs', body', _, hw', hst⟩ := op_binop S hw hx.hS hx.hcap (e.sp - 2) hsm2 hcode
  have hrd1 : Slots.rd e.stack (e.sp - 1) = slot e.stack (e.sp.toNat - 1) := rd_slot _ _ _ hsm1 (by omega)
  have hrd2 : Slots.rd e.stack (e.sp - 2) = slot e.stack (e.sp.toNat - 2) := rd_slot _ _ _ hsm2 (by omega)
  refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl (wr_size _ _ _)
    (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
    Or.inl ⟨L, H, d, en, te, ts' ++ [t'], vs' ++ [vr], rest, ?_⟩⟩
  show ActW e.code locals maxH (Slots.wr e.stack (e.sp - 2) (op.evalBin (Slots.rd e.stack (e.sp - 2))
    (Slots.rd e.stack (e.sp - 1)))) e.fp.toNat (e.sp - 1).toNat (e.pc + 1).toNat f body' L H d en te
    (ts' ++ [t']) (vs' ++ [vr]) rest
  rw [hsm1, pc_succ e _ hcode hx.hC, hrd1, hrd2]; exact hw'

theorem mem0 (hx : Ctx e S f cs maxH) {op : LoadOp ⊕ StoreOp} {off : Nat}
    (hcode : e.code[e.pc.toNat]? = some (match op with | .inl o => Op.load o 0 off | .inr o => Op.store o 0 off)) :
    ∃ a, e.inst.mems[0]? = some a ∧ f.MODULE.MEMS[0]? = some a ∧ a < e.st.mems.size ∧
      a < S.MEMS.length ∧ MemR (e.st.mems[a]!).data S.MEMS[a]! ∧ e.inst.mems[0]! = a ∧ f.MODULE.MEMS[0]! = a := by
  obtain ⟨a, ha⟩ : ∃ a, e.inst.mems[0]? = some a := by
    rcases hx.mem with h | h
    · exact Option.isSome_iff_exists.mp h
    · cases op with
      | inl o => exact absurd hcode ((h _ 0 off).1 o)
      | inr o => exact absurd hcode ((h _ 0 off).2 o)
  obtain ⟨hfa, hal⟩ := hx.memok a ha
  obtain ⟨hsl, hmr⟩ := hx.store a hal
  exact ⟨a, ha, hfa, hal, hsl, hmr, by simp [getElem!_def, ha], by simp [getElem!_def, hfa]⟩

theorem case_load {al off : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.LOAD .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @load _ _ _ ts _ _ _ _ _ hcode hnext =>
  rw [stepE_of e _ hcode hx.hC] at hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hsp0 := hw.2.2.2.1; simp at hsp0
  have hcap := hx.hcap; have hS := hx.hS
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  have hrd1 := rd_slot e.stack (e.sp - 1) _ hsm1 (by omega)
  obtain ⟨a, ha, hfa, hal, _, hmr, hia, hfa'⟩ := mem0 (op := .inl .i32) hx hcode
  have hmem : MemR (memData e.st e.inst 0) (Spec.fun_mem (.mk_state S f) (.mk_uN 0)) := by
    simp only [memData, Spec.fun_mem, Spec.sof, Spec.fof, Spec.fun_store, Spec.fun_frame, Spec.proj_uN_0, hia, hfa']
    exact hmr
  simp only [stepOp] at hs
  split at hs
  · rename_i hin
    simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨_, ts', vs', body', hw', hst⟩ := op_load S (memData e.st e.inst 0) hmem hw hx.hS hx.hcap _
      (by rw [← hrd1]; rfl) hin (e.sp - 1) hsm1
    refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl (wr_size _ _ _)
      (fun i hi => slot_wr_ne _ _ _ _ hx.hS (by omega) (by omega)) rfl,
      Or.inl ⟨L, H, d, en, te, ts' ++ [.i32], vs' ++ [i32c (LinearMemory.load32 (memData e.st e.inst 0) _ hin).toNat],
        rest, ?_⟩⟩
    show ActW e.code locals maxH (Slots.wr e.stack (e.sp - 1) (LinearMemory.load32 (memData e.st e.inst 0) _ hin))
      e.fp.toNat e.sp.toNat (e.pc + 1).toNat f body' L H d en te (ts' ++ [.i32])
      (vs' ++ [i32c (LinearMemory.load32 (memData e.st e.inst 0) _ hin).toNat]) rest
    rw [pc_succ e _ hcode hx.hC]; exact hw'
  · simp at hs

theorem case_br {l : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.BR (.mk_uN l) :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hn := hw.1
  have hsp0 := hw.2.2.2.1
  have hcap := hx.hcap; have hS := hx.hS; have hC := hx.hC
  obtain ⟨lb, ts0, hl, hcode, hts, har, hk⟩ := op_br (.mk_state S f) hw
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp, Option.some.injEq] at hs; subst hs
  have hbase := Nest.base_le hn lb (List.mem_of_getElem? hl)
  have hlbpc := (Nest.bounds hn).2 lb (List.mem_of_getElem? hl)
  subst hts
  simp only [List.length_append] at hsp0
  obtain ⟨hmv, hsp'⟩ := brMove_moved e.stack e.sp e.fp lb.target hx.hS
    (by simp only [Lbl.target]; omega) hss
  have hsrc : e.sp.toNat - lb.target.keep = e.fp.toNat + locals.length + d + ts0.length := by
    simp only [Lbl.target]; omega
  rw [hsrc] at hmv
  obtain ⟨body', hst, hres⟩ := hk _ hmv
  have hpc' : lb.target.pc.toUSize.toNat = lb.pc := natU _ (by simp only [Lbl.target]; omega)
  refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl hmv.1 (fun i hi => hmv.2.1 i (by
    simp only [Lbl.target]; omega)) rfl, ?_⟩
  show ActR e.code locals maxH (brMove e.stack e.sp e.fp lb.target).stack e.fp.toNat
      (brMove e.stack e.sp e.fp lb.target).sp.toNat lb.target.pc.toUSize.toNat f body' ∨
    DoneR e.code locals maxH (brMove e.stack e.sp e.fp lb.target).stack e.fp.toNat
      (brMove e.stack e.sp e.fp lb.target).sp.toNat lb.target.pc.toUSize.toNat f body'
  rw [hsp', hpc']; simpa [Lbl.target] using hres

theorem case_brIf {l : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.BR_IF (.mk_uN l) :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hn := hw.1
  have hsp0 := hw.2.2.2.1
  have hcap := hx.hcap; have hS := hx.hS; have hC := hx.hC
  have hc := hw.2.2.1
  cases hc with
  | @brIf _ _ _ ts _ _ _ _ lb ts0 hl hcode hts har hbase hnext =>
  subst hts
  simp only [List.length_append, List.length_singleton] at hsp0
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  have hrd1 := rd_slot e.stack (e.sp - 1) _ hsm1 (by omega)
  rw [stepE_of e _ hcode hx.hC] at hs
  simp only [stepOp] at hs
  split at hs
  · rename_i hc0
    simp only [Option.some.injEq] at hs; subst hs
    have hne : slot e.stack (e.sp.toNat - 1) ≠ 0 := by rw [← hrd1]; simpa [Run.rd] using hc0
    obtain ⟨lb', ts0', hl', _, hts', har', hk⟩ := op_brIf_true (.mk_state S f) hw hne
    rw [hl] at hl'; cases hl'
    have hts0 : ts0' = ts0 := by have h := hts'; simp at h; exact h.symm
    subst hts0
    have hbase' := Nest.base_le hn lb (List.mem_of_getElem? hl)
    have hlbpc := (Nest.bounds hn).2 lb (List.mem_of_getElem? hl)
    obtain ⟨hmv, hsp'⟩ := brMove_moved e.stack (e.sp - 1) e.fp lb.target hx.hS
      (by simp only [Lbl.target]; rw [hsm1]; omega) (by omega)
    have hsrc : (e.sp - 1).toNat - lb.target.keep = e.fp.toNat + locals.length + d + ts0'.length := by
      simp only [Lbl.target]; rw [hsm1]; omega
    rw [hsrc] at hmv
    obtain ⟨body', hst, hres⟩ := hk _ hmv
    have hpc' : lb.target.pc.toUSize.toNat = lb.pc := natU _ (by simp only [Lbl.target]; omega)
    refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl hmv.1 (fun i hi => hmv.2.1 i (by
      simp only [Lbl.target]; omega)) rfl, ?_⟩
    show ActR e.code locals maxH (brMove e.stack (e.sp - 1) e.fp lb.target).stack e.fp.toNat
        (brMove e.stack (e.sp - 1) e.fp lb.target).sp.toNat lb.target.pc.toUSize.toNat f body' ∨
      DoneR e.code locals maxH (brMove e.stack (e.sp - 1) e.fp lb.target).stack e.fp.toNat
        (brMove e.stack (e.sp - 1) e.fp lb.target).sp.toNat lb.target.pc.toUSize.toNat f body'
    rw [hsp', hpc']; simpa [Lbl.target] using hres
  · rename_i hc0
    simp only [Option.some.injEq] at hs; subst hs
    have hz : slot e.stack (e.sp.toNat - 1) = 0 := by rw [← hrd1]; simpa [Run.rd] using hc0
    obtain ⟨ts', vs', body', hw', hst⟩ := op_brIf_false (.mk_state S f) hw hz
    refine ⟨S, f, body', hst, Ctx.regs hx _ f rfl rfl rfl rfl rfl rfl (fun i hi => rfl) rfl,
      Or.inl ⟨L, H, d, en, te, ts', vs', rest, ?_⟩⟩
    show ActW e.code locals maxH e.stack e.fp.toNat (e.sp - 1).toNat (e.pc + 1).toNat f body' L H d en te ts' vs' rest
    rw [hsm1, pc_succ e _ hcode hx.hC]; exact hw'

theorem storeS_mems (S : Spec.store) (f : Spec.frame) (ea v a : Nat) (hfa : f.MODULE.MEMS[0]! = a) :
    (storeS S f ea v).MEMS = S.MEMS.modify a (fun mi =>
      { mi with BYTES := Spec.list_slice_update mi.BYTES ea 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN v))) }) := by
  simp only [storeS, Spec.with_mem, Spec.fun_store, Spec.sof, Spec.fof, Spec.fun_frame, Spec.list_update_func,
    Spec.proj_uN_0, hfa]

theorem storeR_store {st : StoreOf M} {S : Spec.store} {f : Spec.frame} {a ea : Nat} {v : UInt64}
    (hst : StoreR st S) (ha : a < st.mems.size) (hfa : f.MODULE.MEMS[0]! = a) (hv : v.toNat < 2^32)
    (hin : ea + StoreOp.width .i32 ≤ LinearMemory.size (st.mems[a]!).data) :
    StoreR (storeMem st a ea v .i32) (storeS S f ea v.toNat) := by
  intro a' ha'
  simp only [storeMem, Array.size_modify] at ha'
  obtain ⟨hlt, hmr⟩ := hst a' ha'
  rw [storeS_mems S f ea v.toNat a hfa]
  refine ⟨by simpa using hlt, ?_⟩
  simp only [storeMem]
  rw [getElem!_pos (st.mems.modify a _) a' (by simpa using ha'), Array.getElem_modify,
    getElem!_pos (S.MEMS.modify a _) a' (by simpa using hlt), List.getElem_modify]
  by_cases h : a = a'
  · subst h
    rw [if_pos rfl, if_pos rfl]
    rw [getElem!_pos st.mems a ha] at hin hmr
    rw [getElem!_pos S.MEMS a hlt] at hmr
    rcases hm : st.mems[a] with ⟨data, mx⟩
    rw [hm] at hin hmr
    simp only [dif_pos hin]
    exact MemR.store hmr ea v hv hin
  · rw [if_neg h, if_neg h]
    rw [getElem!_pos st.mems a' ha', getElem!_pos S.MEMS a' hlt] at hmr
    exact hmr

theorem case_store {al off : Nat} (hx : Ctx e S f cs maxH)
    (hw : ActW e.code locals maxH e.stack e.fp.toNat e.sp.toNat e.pc.toNat f body L H d en te tsC valsC
      (.STORE .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: rest))
    (hs : stepE e = some e') : Next e' S f body cs locals maxH := by
  have hc := hw.2.2.1
  cases hc with
  | @store _ _ _ ts _ _ _ _ _ hcode hnext =>
  rw [stepE_of e _ hcode hx.hC] at hs
  obtain ⟨hfs, hss⟩ := hw.sp_le hx
  have hsp0 := hw.2.2.2.1; simp at hsp0
  have hcap := hx.hcap; have hS := hx.hS
  have hsm1 : (e.sp - 1).toNat = e.sp.toNat - 1 := by rw [subU _ _ (by rw [lit 1 (by decide)]; omega), lit 1 (by decide)]
  have hsm2 : (e.sp - 2).toNat = e.sp.toNat - 2 := by rw [subU _ _ (by rw [lit 2 (by decide)]; omega), lit 2 (by decide)]
  have hrd1 := rd_slot e.stack (e.sp - 1) _ hsm1 (by omega)
  have hrd2 := rd_slot e.stack (e.sp - 2) _ hsm2 (by omega)
  obtain ⟨a, ha, hfa, hal, _, hmr, hia, hfa'⟩ := mem0 (op := .inr .i32) hx hcode
  simp only [stepOp, hia] at hs
  split at hs
  · rename_i hin
    simp only [Option.some.injEq] at hs; subst hs
    obtain ⟨_, hv32, ts', vs', body', hw', hst⟩ := op_store S hw ((Slots.rd e.stack (e.sp - 2)).toNat + off)
      (by rw [hrd2])
    rw [← hrd1] at hv32 hst
    refine ⟨_, f, body', hst, ⟨storeR_store hx.store hal hfa' hv32 hin, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      Or.inl ⟨L, H, d, en, te, ts', vs', rest, ?_⟩⟩
    · intro a' ha'; obtain ⟨h1, h2⟩ := hx.memok a' ha'; exact ⟨h1, by simpa [storeMem] using h2⟩
    · exact hx.mem
    · exact hx.callers
    · exact hx.hS
    · exact hx.hC
    · exact hx.hcap
    show ActW e.code locals maxH e.stack e.fp.toNat (e.sp - 2).toNat (e.pc + 1).toNat f body' L H d en te ts' vs' rest
    rw [hsm2, pc_succ e _ hcode hx.hC]; exact hw'
  · simp at hs

theorem Nest.len_pos {code locals maxH s fp L H d e te} (hn : Nest code locals maxH s fp L H d e te) :
    1 ≤ H.length := by
  cases hn <;> simp

/-- THE STEP THEOREM. If the spec configuration `c` is the abstraction of the engine
state `e`, and the engine takes one step from `e` to `e'` (one of the covered ops:
`stepE`, which `run` makes by `stepE_run`), then the spec takes zero or more steps from
`c` to a configuration `c'` that is the abstraction of `e'`. -/
theorem step_refines (e e' : EState M) (c : Spec.config) (hR : R e c) (hs : stepE e = some e') :
    ∃ c', Spec.Steps c c' ∧ R e' c' := by
  obtain ⟨S, f0, cs, m, f, locals, maxH, body, rfl, hx, hact⟩ := hR
  suffices hN : Next e' S f body cs locals maxH by
    obtain ⟨S', f', body', hst, hx', hact'⟩ := hN
    exact ⟨_, steps_wrap f0 cs m hst, S', f0, cs, m, f', locals, maxH, body', rfl, hx', hact'⟩
  rcases hact with ⟨L, H, d, en, te, tsC, valsC, is, hw⟩ | ⟨rs, vals, hret, _⟩
  · obtain ⟨body1, L1, H1, d1, e1, te1, tsC1, valsC1, is1, hw1, hst1, hcan⟩ :=
      norm (.mk_state S f) _ (Nat.lt_succ_self _) hw
    suffices hN : Next e' S f body1 cs locals maxH by
      obtain ⟨S', f', body', hst, hx', hact'⟩ := hN
      exact ⟨S', f', body', steps_trans hst1 hst, hx', hact'⟩
    have hc := hw1.2.2.1
    cases hc with
    | nil =>
      have hlen := hcan.1 rfl
      have hn := hw1.1
      cases hn with
      | func pe rs' m' hret =>
        rw [stepE_of e _ hret hx.hC] at hs; simp [stepOp] at hs
      | block => have := Nest.len_pos (by assumption); simp only [List.length_cons] at hlen; omega
      | loop => have := Nest.len_pos (by assumption); simp only [List.length_cons] at hlen; omega
    | const32 => exact case_const32 hx hw1 (by assumption) hs
    | const64 => exact case_const64 hx hw1 (by assumption) hs
    | localGet => exact case_localGet hx hw1 hs
    | localSet => exact case_localSet hx hw1 hs
    | localTee => exact case_localTee hx hw1 hs
    | binop => exact case_binop hx hw1 hs
    | load => exact case_load hx hw1 hs
    | store => exact case_store hx hw1 hs
    | block => exact absurd rfl (hcan.2.1 _ _ _)
    | loop => exact absurd rfl (hcan.2.2 _ _ _)
    | br => exact case_br hx hw1 hs
    | brIf => exact case_brIf hx hw1 hs
  · exfalso; rw [stepE_of e _ hret hx.hC] at hs; simp [stepOp] at hs

end Cases

end L4Factoidal.WasmVM.Proofs.Refine
