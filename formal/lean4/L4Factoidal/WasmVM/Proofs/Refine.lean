/-
L4Factoidal.WasmVM.Proofs.Refine: the state abstraction from the fast engine to the
spec configuration, and the first step-refinement theorems
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Refinement: the state abstraction").

The engine runs flat code (`Array Op`, branch targets precomputed) over untyped 64-bit
slots. The spec (`Spec.Step`, generated from WebAssembly 3.0) rewrites nested
instruction sequences with `LABEL_` and `FRAME_`. The abstraction is a RELATION, built
from three parts:

- `ValR t b v`: slot bits `b` stand for the spec value `v` at type `t`. The types are
  not in the engine state; they come from `Comp`.
- `Comp code locals maxH L pc ts is pe te` (the compiler's relation): the spec
  instructions `is` are compiled to the ops of `code` from `pc` to `pe`, starting with
  operand types `ts` and ending with `te`, under the labels `L` (innermost first).
  Each label `Lbl` is the side-table entry a branch to it uses: target pc, arity and
  operand height. A `block` compiles to no op (its body starts at the same pc); its
  label's target is the pc after its body. A `loop`'s label targets its first pc.
- `Nest`: the open blocks around the current code. Each is a `Hole`, the spec context
  `vals ++ [LABEL_ n cont □] ++ rest`, whose values are slots and whose `rest` is
  compiled (by `Comp`) from the block's end pc.

`ActR` puts these together for the running function: the spec function body is
`plug H (valsC ++ is)`; the slots from `fp + nLocals` up to `sp` hold the values of
all holes then `valsC`; locals are slots `fp + x`. `R` adds the store (memories, read
through `LinearMemoryLaws`), the callers (`Caller`, `wrap`) and the size side conditions.

The theorem shape (`step_refines`): if `R e c` and the engine takes one step from `e`
to `e'` (`stepE e = some e'`, and `stepE_run`: `run` makes that step), then
`Spec.Steps c c'` and `R e' c'` for some `c'`.
-/
import L4Factoidal.WasmVM.Spec
import L4Factoidal.WasmVM.Proofs.Numerics
import L4Factoidal.WasmVM.Proofs.Proposals
import L4Factoidal.WasmVM.Proofs.Memory

namespace L4Factoidal.WasmVM.Proofs.Refine
open L4Factoidal.WasmVM SlotLemmas MemLaws Run

/-! ### Values -/

/-- The spec's i32 and i64 constants. -/
noncomputable def i32c (n : Nat) : Spec.val := .CONST .I32 (.mk_num__0 .I32 (.mk_uN n))
noncomputable def i64c (n : Nat) : Spec.val := .CONST .I64 (.mk_num__0 .I64 (.mk_uN n))

/-- Slot bits `b` stand for spec value `v` at type `t`. An i32 slot is zero-extended
(the engine's slot normal form). Floats are related only as "a float constant": the
spec's float encodings are opaque in the generated layer. -/
def ValR : ValType → UInt64 → Spec.val → Prop
  | .i32, b, v => b.toNat < 2^32 ∧ v = i32c b.toNat
  | .i64, b, v => v = i64c b.toNat
  | .f32, b, v => b.toNat < 2^32 ∧ ∃ c, v = .CONST .F32 c
  | .f64, _, v => ∃ c, v = .CONST .F64 c
  | .v128, _, _ => False
  | .ref _, b, v => (b = nullRef ∧ v = .REF_NULL_ADDR) ∨
      (b ≠ nullRef ∧ (v = .REF_FUNC_ADDR b.toNat ∨ v = .REF_EXN_ADDR b.toNat ∨ v = .REF_HOST_ADDR b.toNat))

/-- Slot `n`, at a `Nat` index. -/
def slot (s : Slots) (n : Nat) : UInt64 := Slots.rd s n.toUSize

/-- The slots from `p` hold `vs`, at types `ts`. -/
def SlotsR (s : Slots) : Nat → List ValType → List Spec.val → Prop
  | _, [], [] => True
  | p, t :: ts, v :: vs => ValR t (slot s p) v ∧ SlotsR s (p + 1) ts vs
  | _, _, _ => False

theorem SlotsR.length {s : Slots} : ∀ {p ts vs}, SlotsR s p ts vs → ts.length = vs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, ⟨_, h⟩ => by simp [SlotsR.length h]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

theorem SlotsR.append {s : Slots} : ∀ {p ts1 vs1 ts2 vs2},
    SlotsR s p ts1 vs1 → SlotsR s (p + ts1.length) ts2 vs2 → SlotsR s p (ts1 ++ ts2) (vs1 ++ vs2)
  | _, [], [], _, _, _, h => by simpa using h
  | p, _ :: ts1, _ :: vs1, _, _, ⟨h1, h2⟩, h => ⟨h1, SlotsR.append h2 (by simpa [Nat.add_assoc, Nat.add_comm 1] using h)⟩
  | _, [], _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, h, _ => h.elim

theorem SlotsR.split {s : Slots} : ∀ {p ts1 ts2 vs}, SlotsR s p (ts1 ++ ts2) vs →
    ∃ vs1 vs2, vs = vs1 ++ vs2 ∧ SlotsR s p ts1 vs1 ∧ SlotsR s (p + ts1.length) ts2 vs2
  | _, [], _, vs, h => ⟨[], vs, rfl, trivial, by simpa using h⟩
  | p, _ :: ts1, ts2, v :: vs, ⟨h1, h2⟩ => by
    obtain ⟨vs1, vs2, rfl, a, b⟩ := SlotsR.split (p := p + 1) (ts1 := ts1) h2
    exact ⟨v :: vs1, vs2, rfl, ⟨h1, a⟩, by simpa [Nat.add_assoc, Nat.add_comm 1] using b⟩
  | _, _ :: _, _, [], h => h.elim

/-- `SlotsR` reads only the slots in its range. -/
theorem SlotsR.frame {s s' : Slots} : ∀ {p ts vs}, SlotsR s p ts vs →
    (∀ i, p ≤ i → i < p + ts.length → slot s' i = slot s i) → SlotsR s' p ts vs
  | _, [], [], _, _ => trivial
  | p, _ :: ts, _ :: vs, ⟨h1, h2⟩, hs => by
    refine ⟨by rw [hs p (Nat.le_refl _) (by simp)]; exact h1, SlotsR.frame h2 fun i a b => hs i (by omega) (by simp; omega)⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-! ### Spec contexts -/

/-- One open block: the spec context `vals ++ [LABEL_ n cont □] ++ rest`. -/
structure Hole where
  vals : List Spec.val
  n : Nat
  cont : List Spec.instr
  rest : List Spec.instr

/-- Put `x` into the holes, innermost first. -/
noncomputable def plug : List Hole → List Spec.instr → List Spec.instr
  | [], x => x
  | h :: hs, x => plug hs (h.vals.map Spec.instr_val ++ (Spec.instr.LABEL_ h.n h.cont x :: h.rest))

/-- `Step.ctxt_instrs`, also when the context is empty. -/
theorem step_ctx (z z' : Spec.state) (vs : List Spec.val) (x x' rest : List Spec.instr)
    (h : Spec.Step (.mk_config z x) (.mk_config z' x')) :
    Spec.Step (.mk_config z (vs.map Spec.instr_val ++ (x ++ rest))) (.mk_config z' (vs.map Spec.instr_val ++ (x' ++ rest))) := by
  by_cases hv : vs = [] ∧ rest = []
  · obtain ⟨rfl, rfl⟩ := hv; simpa using h
  · refine Spec.Step.ctxt_instrs z vs x rest z' x' h ?_
    simp only [Bool.or_eq_true]
    cases vs with
    | cons => left; rfl
    | nil =>
      cases rest with
      | cons => right; rfl
      | nil => exact absurd ⟨rfl, rfl⟩ hv

theorem step_plug (z z' : Spec.state) : ∀ (H : List Hole) (x x' : List Spec.instr),
    Spec.Step (.mk_config z x) (.mk_config z' x') →
    Spec.Step (.mk_config z (plug H x)) (.mk_config z' (plug H x'))
  | [], _, _, h => h
  | hl :: H, x, x', h => by
    apply step_plug z z' H
    have := step_ctx z z' hl.vals [.LABEL_ hl.n hl.cont x] [.LABEL_ hl.n hl.cont x'] hl.rest
      (Spec.Step.ctxt_label z hl.n hl.cont x z' x' h)
    simpa using this

theorem steps_plug (H : List Hole) : ∀ {z z' : Spec.state} {x x' : List Spec.instr},
    Spec.Steps (.mk_config z x) (.mk_config z' x') →
    Spec.Steps (.mk_config z (plug H x)) (.mk_config z' (plug H x')) := by
  intro z z' x x' h
  generalize hc : Spec.config.mk_config z x = c at h
  generalize hc' : Spec.config.mk_config z' x' = c' at h
  induction h generalizing z x with
  | refl => cases hc; cases hc'; exact Spec.Steps.refl _ _
  | trans z0 i0 z2 i2 z1 i1 hs _ ih =>
    cases hc; cases hc'
    exact Spec.Steps.trans _ _ _ _ _ _ (step_plug _ _ H _ _ hs) (ih rfl rfl)

theorem steps_trans {a b c : Spec.config} (h1 : Spec.Steps a b) (h2 : Spec.Steps b c) : Spec.Steps a c := by
  induction h1 with
  | refl => exact h2
  | trans _ _ _ _ _ _ s _ ih => exact Spec.Steps.trans _ _ _ _ _ _ s (ih h2)

theorem steps_one {z z' x x'} (h : Spec.Step (.mk_config z x) (.mk_config z' x')) :
    Spec.Steps (.mk_config z x) (.mk_config z' x') :=
  Spec.Steps.trans _ _ _ _ _ _ h (Spec.Steps.refl _ _)

/-! ### Numeric operations -/

/-- The engine's numeric op `op` at type `t` is the spec's `BINOP nt bop`. -/
inductive BinR : NumOp → ValType → Spec.numtype → Spec.binop_ → Prop
  | i32_add : BinR .i32_add .i32 .I32 (.mk_binop__0 .I32 .ADD)
  | i32_sub : BinR .i32_sub .i32 .I32 (.mk_binop__0 .I32 .SUB)
  | i32_mul : BinR .i32_mul .i32 .I32 (.mk_binop__0 .I32 .MUL)
  | i64_add : BinR .i64_add .i64 .I64 (.mk_binop__0 .I64 .ADD)
  | i64_sub : BinR .i64_sub .i64 .I64 (.mk_binop__0 .I64 .SUB)
  | i64_mul : BinR .i64_mul .i64 .I64 (.mk_binop__0 .I64 .MUL)

theorem BinR.pure {op t nt bop} (h : BinR op t nt bop) : op.pureBin = true := by
  cases h <;> rfl

/-- The spec's i64 constant for a slot. -/
noncomputable def absI64 (a : UInt64) : Spec.num_ := .mk_num__0 .I64 (.mk_uN a.toNat)

theorem wf_absI64 (a : UInt64) : Spec.wf_num_ .I64 (absI64 a) := by
  refine Spec.wf_num_.num__case_0 _ _ _ ?_ (by rfl)
  refine Spec.wf_uN.uN_case_0 _ _ ?_
  have := a.toNat_lt
  have e : (Int.ofNat (2 ^ 64) - Int.ofNat 1).toNat = 2 ^ 64 - 1 := by decide
  simp only [Spec.size, Spec.numtype_Inn, e, ge_iff_le, Nat.zero_le, decide_true, Bool.true_and,
    decide_eq_true_eq]
  omega

theorem num64_beq_self (n : Nat) :
    (Spec.num_.mk_num__0 .I64 (.mk_uN n) == Spec.num_.mk_num__0 .I64 (.mk_uN n)) = true := by
  simp [BEq.beq, Spec.instBEqNum_.beq, Spec.instBEqUN.beq, Spec.instBEqInn.beq]

/-- The i64 pattern of `Proofs.i32_bin_refines`. -/
theorem i64_bin_refines (bop : Spec.binop_Inn) (f : Spec.uN → Spec.uN → Spec.uN)
    (op : NumOp) (a b : UInt64)
    (hfun : ∀ i1 i2, Spec.wf_num_ .I64 (.mk_num__0 .I64 (f i1 i2)) →
      Spec.fun_binop_ .I64 (.mk_binop__0 .I64 bop) (.mk_num__0 .I64 i1) (.mk_num__0 .I64 i2)
        [.mk_num__0 .I64 (f i1 i2)])
    (hkey : f (.mk_uN a.toNat) (.mk_uN b.toNat) = .mk_uN (op.evalBin a b).toNat) :
    Spec.Step_pure
      [.CONST .I64 (absI64 a), .CONST .I64 (absI64 b), .BINOP .I64 (.mk_binop__0 .I64 bop)]
      [.CONST .I64 (absI64 (op.evalBin a b))] := by
  have hw : Spec.wf_num_ .I64 (.mk_num__0 .I64 (f (.mk_uN a.toNat) (.mk_uN b.toNat))) := by
    rw [hkey]; exact wf_absI64 _
  refine Spec.Step_pure.binop_val .I64 (absI64 a) (absI64 b) (.mk_binop__0 .I64 bop)
    (absI64 (op.evalBin a b))
    [.mk_num__0 .I64 (f (.mk_uN a.toNat) (.mk_uN b.toNat))]
    (hfun _ _ hw) (wf_absI64 a) (wf_absI64 b) (.binop__case_0 _ .I64 _ (by decide))
    (wf_absI64 _) (by simp) ?_
  rw [hkey]
  simp [List.contains, List.elem, absI64, num64_beq_self]

theorem i64_add_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I64 (absI64 a), .CONST .I64 (absI64 b), .BINOP .I64 (.mk_binop__0 .I64 .ADD)]
      [.CONST .I64 (absI64 (NumOp.evalBin .i64_add a b))] :=
  i64_bin_refines .ADD (Spec.iadd_ (Spec.sizenn (Spec.numtype_Inn .I64))) .i64_add a b
    (fun _ _ h => .fun_binop__case_1 _ _ h)
    (by simp [Spec.iadd_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0, NumOp.evalBin])

theorem i64_sub_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I64 (absI64 a), .CONST .I64 (absI64 b), .BINOP .I64 (.mk_binop__0 .I64 .SUB)]
      [.CONST .I64 (absI64 (NumOp.evalBin .i64_sub a b))] :=
  i64_bin_refines .SUB (Spec.isub_ (Spec.sizenn (Spec.numtype_Inn .I64))) .i64_sub a b
    (fun _ _ h => .fun_binop__case_3 _ _ h)
    (by
      have := a.toNat_lt; have := b.toNat_lt
      simp [Spec.isub_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0, NumOp.evalBin,
        UInt64.toNat_sub]
      omega)

theorem i64_mul_refines (a b : UInt64) :
    Spec.Step_pure
      [.CONST .I64 (absI64 a), .CONST .I64 (absI64 b), .BINOP .I64 (.mk_binop__0 .I64 .MUL)]
      [.CONST .I64 (absI64 (NumOp.evalBin .i64_mul a b))] :=
  i64_bin_refines .MUL (Spec.imul_ (Spec.sizenn (Spec.numtype_Inn .I64))) .i64_mul a b
    (fun _ _ h => .fun_binop__case_5 _ _ h)
    (by simp [Spec.imul_, Spec.sizenn, Spec.size, Spec.numtype_Inn, Spec.proj_uN_0, NumOp.evalBin])

theorem i32_lt (a : UInt64) (h : a.toNat < 2^32) : a.toUInt32.toNat = a.toNat := by
  simp [UInt64.toNat_toUInt32]; omega

theorem i32_ofI32 (x : UInt32) : (Num.ofI32 x).toNat < 2^32 := by
  simp [Num.ofI32]; exact x.toNat_lt

/-- One engine binary op on two related slots is one `Step_pure` step, and the result
slot is related to the result value. -/
theorem bin_step {op t nt bop} (hb : BinR op t nt bop) {a b : UInt64} {va vb : Spec.val}
    (ha : ValR t a va) (hbv : ValR t b vb) :
    ∃ vr, ValR t (op.evalBin a b) vr ∧
      Spec.Step_pure [Spec.instr_val va, Spec.instr_val vb, .BINOP nt bop] [Spec.instr_val vr] := by
  cases hb
  all_goals first
    | (obtain ⟨ha1, rfl⟩ := ha; obtain ⟨hb1, rfl⟩ := hbv
       refine ⟨i32c (NumOp.evalBin _ a b).toNat, ⟨i32_ofI32 _, rfl⟩, ?_⟩
       have e1 : Spec.instr_val (i32c a.toNat) = .CONST .I32 (Proofs.absI32 a) := by
         simp [i32c, Spec.instr_val, Proofs.absI32, i32_lt a ha1]
       have e2 : Spec.instr_val (i32c b.toNat) = .CONST .I32 (Proofs.absI32 b) := by
         simp [i32c, Spec.instr_val, Proofs.absI32, i32_lt b hb1]
       rw [e1, e2]
       first
         | (have h := Proofs.i32_add_refines a b
            simpa [i32c, Spec.instr_val, Proofs.absI32, i32_lt _ (i32_ofI32 _), NumOp.evalBin] using h)
         | (have h := Proofs.i32_sub_refines a b
            simpa [i32c, Spec.instr_val, Proofs.absI32, i32_lt _ (i32_ofI32 _), NumOp.evalBin] using h)
         | (have h := Proofs.i32_mul_refines a b
            simpa [i32c, Spec.instr_val, Proofs.absI32, i32_lt _ (i32_ofI32 _), NumOp.evalBin] using h))
    | (subst ha; subst hbv
       refine ⟨i64c (NumOp.evalBin _ a b).toNat, rfl, ?_⟩
       first
         | simpa [i64c, Spec.instr_val, absI64] using i64_add_refines a b
         | simpa [i64c, Spec.instr_val, absI64] using i64_sub_refines a b
         | simpa [i64c, Spec.instr_val, absI64] using i64_mul_refines a b)

/-! ### The compiler's relation -/

/-- A label as the side table holds it: the branch target pc, the number of values a
branch keeps, the operand height (relative to `fp`) they go to, and their types. -/
structure Lbl where
  pc : Nat
  arity : Nat
  base : Nat
  types : List ValType

def Lbl.target (lb : Lbl) : BrTarget := ⟨lb.pc, lb.arity, lb.base⟩

/-- `Comp code locals maxH L d pc ts is pe te`: the spec instructions `is` are compiled
to `code` from `pc` to `pe`. `L` are the labels in scope (innermost first), `d` the
number of operand values below the current block, `ts` and `te` the operand types of the
current block at `pc` and at `pe`. `maxH` is the function's maximum height (locals plus
operands). This is what the validator's compiler (`Valid.step`) establishes; the
theorem that it does is open (record: `compile_establishes`). Block types are restricted
to `_RESULT` (no parameters). -/
inductive Comp (code : Array Op) (locals : List ValType) (maxH : Nat) :
    List Lbl → Nat → Nat → List ValType → List Spec.instr → Nat → List ValType → Prop
  | nil {L d pc ts} : Comp code locals maxH L d pc ts [] pc ts
  | const32 {L d pc ts is pe te} (b : UInt64) (n : Nat) :
      code[pc]? = some (.const b) → b.toNat = n → n < 2^32 →
      locals.length + d + ts.length + 1 ≤ maxH →
      Comp code locals maxH L d (pc + 1) (ts ++ [.i32]) is pe te →
      Comp code locals maxH L d pc ts (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)) :: is) pe te
  | const64 {L d pc ts is pe te} (b : UInt64) (n : Nat) :
      code[pc]? = some (.const b) → b.toNat = n →
      locals.length + d + ts.length + 1 ≤ maxH →
      Comp code locals maxH L d (pc + 1) (ts ++ [.i64]) is pe te →
      Comp code locals maxH L d pc ts (.CONST .I64 (.mk_num__0 .I64 (.mk_uN n)) :: is) pe te
  | localGet {L d pc ts is pe te} (x : Nat) (t : ValType) :
      code[pc]? = some (.localGet x) → locals[x]? = some t →
      locals.length + d + ts.length + 1 ≤ maxH →
      Comp code locals maxH L d (pc + 1) (ts ++ [t]) is pe te →
      Comp code locals maxH L d pc ts (.LOCAL_GET (.mk_uN x) :: is) pe te
  | localSet {L d pc ts is pe te} (x : Nat) (t : ValType) :
      code[pc]? = some (.localSet x) → locals[x]? = some t →
      Comp code locals maxH L d (pc + 1) ts is pe te →
      Comp code locals maxH L d pc (ts ++ [t]) (.LOCAL_SET (.mk_uN x) :: is) pe te
  | localTee {L d pc ts is pe te} (x : Nat) (t : ValType) :
      code[pc]? = some (.localTee x) → locals[x]? = some t →
      Comp code locals maxH L d (pc + 1) (ts ++ [t]) is pe te →
      Comp code locals maxH L d pc (ts ++ [t]) (.LOCAL_TEE (.mk_uN x) :: is) pe te
  | binop {L d pc ts is pe te} (op : NumOp) (t : ValType) (nt : Spec.numtype) (bop : Spec.binop_) :
      code[pc]? = some (.num op) → BinR op t nt bop →
      Comp code locals maxH L d (pc + 1) (ts ++ [t]) is pe te →
      Comp code locals maxH L d pc (ts ++ [t, t]) (.BINOP nt bop :: is) pe te
  | load {L d pc ts is pe te} (al off : Nat) :
      code[pc]? = some (.load .i32 0 off) →
      Comp code locals maxH L d (pc + 1) (ts ++ [.i32]) is pe te →
      Comp code locals maxH L d pc (ts ++ [.i32])
        (.LOAD .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: is) pe te
  | store {L d pc ts is pe te} (al off : Nat) :
      code[pc]? = some (.store .i32 0 off) →
      Comp code locals maxH L d (pc + 1) ts is pe te →
      Comp code locals maxH L d pc (ts ++ [.i32, .i32])
        (.STORE .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: is) pe te
  | block {L d pc ts is pe te} (rs : List ValType) (st : Option Spec.valtype) (body : List Spec.instr)
      (pe1 : Nat) :
      Comp code locals maxH (⟨pe1, rs.length, locals.length + d + ts.length, rs⟩ :: L)
        (d + ts.length) pc [] body pe1 rs →
      Comp code locals maxH L d pe1 (ts ++ rs) is pe te →
      Comp code locals maxH L d pc ts (.BLOCK (._RESULT st) body :: is) pe te
  | loop {L d pc ts is pe te} (rs : List ValType) (st : Option Spec.valtype) (body : List Spec.instr)
      (pe1 : Nat) :
      Comp code locals maxH (⟨pc, 0, locals.length + d + ts.length, []⟩ :: L)
        (d + ts.length) pc [] body pe1 rs →
      Comp code locals maxH L d pe1 (ts ++ rs) is pe te →
      Comp code locals maxH L d pc ts (.LOOP (._RESULT st) body :: is) pe te
  | br {L d pc ts is pe te} (l : Nat) (lb : Lbl) (ts0 ts' : List ValType) :
      L[l]? = some lb → code[pc]? = some (.br lb.target) →
      ts = ts0 ++ lb.types → lb.arity = lb.types.length → lb.base ≤ locals.length + d →
      Comp code locals maxH L d (pc + 1) ts' is pe te →
      Comp code locals maxH L d pc ts (.BR (.mk_uN l) :: is) pe te
  | brIf {L d pc ts is pe te} (l : Nat) (lb : Lbl) (ts0 : List ValType) :
      L[l]? = some lb → code[pc]? = some (.brIf lb.target) →
      ts = ts0 ++ lb.types → lb.arity = lb.types.length → lb.base ≤ locals.length + d →
      Comp code locals maxH L d (pc + 1) ts is pe te →
      Comp code locals maxH L d pc (ts ++ [.i32]) (.BR_IF (.mk_uN l) :: is) pe te

/-! ### Open blocks and the running function -/

/-- The open blocks around the current code, innermost first. `Nest .. L H d e te`: the
holes `H` with labels `L`; `d` operand values sit in the holes (below the current block);
the current block ends at pc `e` with its own operand types `te`. The outermost hole is
the function's own label (`LABEL_ m [] □`), whose end pc holds `return`. -/
inductive Nest (code : Array Op) (locals : List ValType) (maxH : Nat) (s : Slots) (fp : Nat) :
    List Lbl → List Hole → Nat → Nat → List ValType → Prop
  | func (pe : Nat) (rs : List ValType) (m : Nat) :
      code[pe]? = some (.return_ rs.length) →
      Nest code locals maxH s fp [⟨pe, rs.length, locals.length, rs⟩] [⟨[], m, [], []⟩] 0 pe rs
  | block {L H d e te} (vals : List Spec.val) (tsH rs : List ValType) (pe1 : Nat) (rest : List Spec.instr) :
      Nest code locals maxH s fp L H d e te →
      SlotsR s (fp + locals.length + d) tsH vals →
      Comp code locals maxH L d pe1 (tsH ++ rs) rest e te →
      Nest code locals maxH s fp (⟨pe1, rs.length, locals.length + d + tsH.length, rs⟩ :: L)
        (⟨vals, rs.length, [], rest⟩ :: H) (d + tsH.length) pe1 rs
  | loop {L H d e te} (vals : List Spec.val) (tsH rs : List ValType) (ps pe1 : Nat)
      (rest : List Spec.instr) (st : Option Spec.valtype) (body : List Spec.instr) :
      Nest code locals maxH s fp L H d e te →
      SlotsR s (fp + locals.length + d) tsH vals →
      Comp code locals maxH (⟨ps, 0, locals.length + d + tsH.length, []⟩ :: L) (d + tsH.length)
        ps [] body pe1 rs →
      Comp code locals maxH L d pe1 (tsH ++ rs) rest e te →
      Nest code locals maxH s fp (⟨ps, 0, locals.length + d + tsH.length, []⟩ :: L)
        (⟨vals, 0, [.LOOP (._RESULT st) body], rest⟩ :: H) (d + tsH.length) pe1 rs

/-- The locals: slot `fp + x` holds local `x`. -/
def LocalsR (s : Slots) (fp : Nat) (locals : List ValType) (f : Spec.frame) : Prop :=
  f.LOCALS.length = locals.length ∧
    ∀ x t, locals[x]? = some t → ∃ v, f.LOCALS[x]? = some (some v) ∧ ValR t (slot s (fp + x)) v

/-- The running function at the spec level of its body, with every part named. -/
def ActW (code : Array Op) (locals : List ValType) (maxH : Nat) (s : Slots) (fp sp pc : Nat)
    (f : Spec.frame) (body : List Spec.instr) (L : List Lbl) (H : List Hole) (d e : Nat)
    (te tsC : List ValType) (valsC : List Spec.val) (is : List Spec.instr) : Prop :=
  Nest code locals maxH s fp L H d e te ∧ SlotsR s (fp + locals.length + d) tsC valsC ∧
    Comp code locals maxH L d pc tsC is e te ∧ sp = fp + locals.length + d + tsC.length ∧
    locals.length + d + tsC.length ≤ maxH ∧ body = plug H (valsC.map Spec.instr_val ++ is) ∧
    LocalsR s fp locals f

/-- The running function: its spec body `body` under frame `f` stands for the engine's
slots `s`, registers `fp`, `sp`, `pc` and code. -/
def ActR (code : Array Op) (locals : List ValType) (maxH : Nat) (s : Slots) (fp sp pc : Nat)
    (f : Spec.frame) (body : List Spec.instr) : Prop :=
  ∃ L H d e te tsC valsC is, ActW code locals maxH s fp sp pc f body L H d e te tsC valsC is

/-- The measure that entering and leaving blocks decreases. -/
noncomputable def meas (is : List Spec.instr) (H : List Hole) : Nat :=
  sizeOf is + (H.map fun h => sizeOf h.rest + 1).sum

theorem plug_cons (hl : Hole) (H : List Hole) (x : List Spec.instr) :
    plug (hl :: H) x = plug H (hl.vals.map Spec.instr_val ++ (Spec.instr.LABEL_ hl.n hl.cont x :: hl.rest)) := rfl

/-- Leaving a block whose code is done: `label_vals`. The values of the block join
those of the enclosing block, and the code goes on with the block's `rest`. -/
theorem exit_level {code locals maxH s fp sp pc f body L H d e te tsC valsC}
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC []) (hH : 2 ≤ H.length)
    (z : Spec.state) :
    ∃ body' L' H' d' e' te' tsC' valsC' is',
      ActW code locals maxH s fp sp pc f body' L' H' d' e' te' tsC' valsC' is' ∧
      Spec.Steps (.mk_config z body) (.mk_config z body') ∧ meas is' H' < meas [] H := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc
  cases hn with
  | func => simp at hH
  | @block L0 H0 d0 e0 te0 vals tsH rs pe1 rest hn0 hsl0 hc0 =>
    refine ⟨_, _, _, _, _, _, tsH ++ te, vals ++ valsC, rest,
      ⟨hn0, SlotsR.append hsl0 (by simpa [Nat.add_assoc] using hsl), hc0, by simp; omega,
        by simp; omega, rfl, hloc⟩, ?_, ?_⟩
    · subst hb
      have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ te.length [] (valsC.map Spec.instr_val)]
        (valsC.map Spec.instr_val) rest (Spec.Step.pure z _ _ (Spec.Step_pure.label_vals _ _ _)))
      exact steps_one (by simpa [plug_cons] using h)
    · simp [meas]; omega
  | @loop L0 H0 d0 e0 te0 vals tsH rs ps pe1 rest st body0 hn0 hsl0 hb0 hc0 =>
    refine ⟨_, _, _, _, _, _, tsH ++ te, vals ++ valsC, rest,
      ⟨hn0, SlotsR.append hsl0 (by simpa [Nat.add_assoc] using hsl), hc0, by simp; omega,
        by simp; omega, rfl, hloc⟩, ?_, ?_⟩
    · subst hb
      have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ 0 [.LOOP (._RESULT st) body0] (valsC.map Spec.instr_val)]
        (valsC.map Spec.instr_val) rest (Spec.Step.pure z _ _ (Spec.Step_pure.label_vals _ _ _)))
      exact steps_one (by simpa [plug_cons] using h)
    · simp [meas]; omega

theorem instrtype_beq (a c : List Spec.valtype) :
    (Spec.instrtype.mk_instrtype (.mk_list a) [] (.mk_list c) ==
      Spec.instrtype.mk_instrtype (.mk_list a) [] (.mk_list c)) = true := by
  simp [BEq.beq, Spec.instBEqInstrtype.beq]

/-- Entering `block`: `Step_read.block`, the block's body becomes the current code. -/
theorem enter_block {code locals maxH s fp sp pc f body L H d e te tsC valsC st body0 rest}
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.BLOCK (._RESULT st) body0 :: rest))
    (z : Spec.state) :
    ∃ body' L' H' d' e' te' tsC' valsC' is',
      ActW code locals maxH s fp sp pc f body' L' H' d' e' te' tsC' valsC' is' ∧
      Spec.Steps (.mk_config z body) (.mk_config z body') ∧
      meas is' H' < meas (.BLOCK (._RESULT st) body0 :: rest) H := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @block _ _ _ _ _ _ _ rs _ _ pe1 hbody hrest =>
    refine ⟨_, _, ⟨valsC, rs.length, [], rest⟩ :: H, _, _, _, [], [], body0,
      ⟨Nest.block valsC tsC rs pe1 rest hn hsl hrest, trivial, hbody, by simp; omega, by simp; omega,
        rfl, hloc⟩, ?_, ?_⟩
    · subst hb
      refine steps_one (step_plug z z _ _ _ ?_)
      have h := step_ctx z z valsC [.BLOCK (._RESULT st) body0] [.LABEL_ rs.length [] body0] rest
        (Spec.Step.read z _ _ (by
          have := Spec.Step_read.block z [] 0 (._RESULT st) body0 rs.length [] st.toList _
            (Spec.fun_blocktype_.fun_blocktype__case_1 z st) (instrtype_beq _ _)
          simpa using this))
      simpa [plug_cons] using h
    · simp [meas]; omega

/-- Entering `loop`: `Step_read.loop`, the label's continuation is the loop again. -/
theorem enter_loop {code locals maxH s fp sp pc f body L H d e te tsC valsC st body0 rest}
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.LOOP (._RESULT st) body0 :: rest))
    (z : Spec.state) :
    ∃ body' L' H' d' e' te' tsC' valsC' is',
      ActW code locals maxH s fp sp pc f body' L' H' d' e' te' tsC' valsC' is' ∧
      Spec.Steps (.mk_config z body) (.mk_config z body') ∧
      meas is' H' < meas (.LOOP (._RESULT st) body0 :: rest) H := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @loop _ _ _ _ _ _ _ rs _ _ pe1 hbody hrest =>
    refine ⟨_, _, ⟨valsC, 0, [.LOOP (._RESULT st) body0], rest⟩ :: H, _, _, _, [], [], body0,
      ⟨Nest.loop valsC tsC rs pc pe1 rest st body0 hn hsl hbody hrest, trivial, hbody, by simp; omega,
        by simp; omega, rfl, hloc⟩, ?_, ?_⟩
    · subst hb
      refine steps_one (step_plug z z _ _ _ ?_)
      have h := step_ctx z z valsC [.LOOP (._RESULT st) body0] [.LABEL_ 0 [.LOOP (._RESULT st) body0] body0] rest
        (Spec.Step.read z _ _ (by
          have := Spec.Step_read.loop z [] 0 (._RESULT st) body0 [] st.toList 0 _
            (Spec.fun_blocktype_.fun_blocktype__case_1 z st) (instrtype_beq _ _)
          simpa using this))
      simpa [plug_cons] using h
    · simp [meas]; omega

/-! ### What a step may change -/

theorem slot_wr_ne (s : Slots) (u : USize) (v : UInt64) (i : Nat) (hS : s.size < USize.size)
    (hi : i < USize.size) (hu : u.toNat ≠ i) : slot (Slots.wr s u v) i = slot s i := by
  unfold slot; rw [rd_wr_ne _ _ _ _ hS (by rw [natU i hi]; exact hu)]

theorem slot_wr_same (s : Slots) (u : USize) (v : UInt64) (hS : s.size < USize.size)
    (hu : u.toNat < s.size / 8) : slot (Slots.wr s u v) u.toNat = v := by
  unfold slot
  have : u.toNat.toUSize = u := by simp [Nat.toUSize_eq]
  rw [this, rd_wr_same _ _ _ hS hu]

/-- `SlotsR` read at another place: the values moved with their slots. -/
theorem SlotsR.move {s s' : Slots} : ∀ {p q ts vs}, SlotsR s p ts vs →
    (∀ j, j < ts.length → slot s' (q + j) = slot s (p + j)) → SlotsR s' q ts vs
  | _, _, [], [], _, _ => trivial
  | p, q, _ :: ts, _ :: vs, ⟨h1, h2⟩, hs => by
    refine ⟨by have := hs 0 (by simp); simp at this; rw [this]; exact h1,
      SlotsR.move h2 fun j hj => by
        have := hs (j + 1) (by simp; omega)
        rw [show q + 1 + j = q + (j + 1) by omega, show p + 1 + j = p + (j + 1) by omega]; exact this⟩
  | _, _, [], _ :: _, h, _ => h.elim
  | _, _, _ :: _, [], h, _ => h.elim

theorem Nest.frame {code locals maxH s fp L H d e te} (hn : Nest code locals maxH s fp L H d e te)
    {s' : Slots} (hs : ∀ i, fp + locals.length ≤ i → i < fp + locals.length + d → slot s' i = slot s i) :
    Nest code locals maxH s' fp L H d e te := by
  induction hn with
  | func pe rs m h => exact Nest.func pe rs m h
  | block vals tsH rs pe1 rest _ hsl hc ih =>
    exact Nest.block vals tsH rs pe1 rest (ih fun i a b => hs i a (by omega))
      (SlotsR.frame hsl fun i a b => hs i (by omega) (by omega)) hc
  | loop vals tsH rs ps pe1 rest st body _ hsl hb hc ih =>
    exact Nest.loop vals tsH rs ps pe1 rest st body (ih fun i a b => hs i a (by omega))
      (SlotsR.frame hsl fun i a b => hs i (by omega) (by omega)) hb hc

theorem LocalsR.frame {s s' : Slots} {fp locals f} (h : LocalsR s fp locals f)
    (hs : ∀ x, x < locals.length → slot s' (fp + x) = slot s (fp + x)) : LocalsR s' fp locals f := by
  refine ⟨h.1, fun x t hx => ?_⟩
  obtain ⟨v, h1, h2⟩ := h.2 x t hx
  refine ⟨v, h1, ?_⟩
  rw [hs x (by have := List.getElem?_eq_some_iff.mp hx; exact this.1)]; exact h2

/-! ### Straight-line ops at the level of the function body

Each lemma: from `ActW` at an instruction, the engine's change of the slots (a write at
`u`, with `u.toNat` the slot index) and registers gives `ActW` again, and the spec takes
the matching steps under the function's frame. The size side conditions: the stack is
smaller than `USize.size` bytes (`hS`) and has room for the function's `maxH` slots
above `fp` (`hcap`). -/

section Ops
variable {code : Array Op} {locals : List ValType} {maxH : Nat} {s : Slots} {fp sp pc : Nat}
  {f : Spec.frame} {body : List Spec.instr} {L : List Lbl} {H : List Hole} {d e : Nat}
  {te tsC : List ValType} {valsC : List Spec.val} {is : List Spec.instr}

theorem map_snoc (vs : List Spec.val) (v : Spec.val) (is : List Spec.instr) :
    (vs ++ [v]).map Spec.instr_val ++ is = vs.map Spec.instr_val ++ (Spec.instr_val v :: is) := by
  simp

/-- `i32.const`: no spec step (a constant is a value); the engine pushes the bits. -/
theorem op_const32 {n : Nat} {b : UInt64} (hcb : code[pc]? = some (.const b))
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC
      (.CONST .I32 (.mk_num__0 .I32 (.mk_uN n)) :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = sp) :
    ActW code locals maxH (Slots.wr s u b) fp (sp + 1) (pc + 1) f body L H d e te
      (tsC ++ [.i32]) (valsC ++ [i32c n]) is := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @const32 _ _ _ _ _ _ _ b' _ hcode hbn hb32 hroom hnext =>
    rw [hcb] at hcode; cases hcode
    have hlen := hsl.length
    have hfr : ∀ i, i < sp → slot (Slots.wr s u b) i = slot s i := fun i h =>
      slot_wr_ne s u b i hS (by omega) (by omega)
    have hnew : slot (Slots.wr s u b) (fp + locals.length + d + tsC.length) = b := by
      rw [← hsp, ← hu]; exact slot_wr_same s u b hS (by omega)
    refine ⟨Nest.frame hn (fun i _ h => hfr i (by omega)),
      SlotsR.append (SlotsR.frame hsl fun i _ h => hfr i (by omega)) ⟨?_, trivial⟩, hnext,
      by simp; omega, by simp; omega, by rw [hb, map_snoc]; rfl,
      LocalsR.frame hloc fun x hx => hfr _ (by omega)⟩
    simp only [Nat.add_assoc] at hnew ⊢
    rw [hnew]; exact ⟨by omega, by rw [hbn]⟩

/-- `i64.const`. -/
theorem op_const64 {n : Nat} {b : UInt64} (hcb : code[pc]? = some (.const b))
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC
      (.CONST .I64 (.mk_num__0 .I64 (.mk_uN n)) :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = sp) :
    ActW code locals maxH (Slots.wr s u b) fp (sp + 1) (pc + 1) f body L H d e te
      (tsC ++ [.i64]) (valsC ++ [i64c n]) is := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @const64 _ _ _ _ _ _ _ b' _ hcode hbn hroom hnext =>
    rw [hcb] at hcode; cases hcode
    have hlen := hsl.length
    have hfr : ∀ i, i < sp → slot (Slots.wr s u b) i = slot s i := fun i h =>
      slot_wr_ne s u b i hS (by omega) (by omega)
    have hnew : slot (Slots.wr s u b) (fp + locals.length + d + tsC.length) = b := by
      rw [← hsp, ← hu]; exact slot_wr_same s u b hS (by omega)
    refine ⟨Nest.frame hn (fun i _ h => hfr i (by omega)),
      SlotsR.append (SlotsR.frame hsl fun i _ h => hfr i (by omega)) ⟨?_, trivial⟩, hnext,
      by simp; omega, by simp; omega, by rw [hb, map_snoc]; rfl,
      LocalsR.frame hloc fun x hx => hfr _ (by omega)⟩
    simp only [Nat.add_assoc] at hnew ⊢
    rw [hnew]; show i64c n = i64c b.toNat; rw [hbn]

theorem option_val_beq_self (o : Option Spec.val) : (o == o) = true := by
  cases o with
  | none => rfl
  | some v => show (v == v) = true; exact Proposals.val_beq_self v

/-- `local.get x`: `Step_read.local_get`; the engine copies slot `fp + x` to the top. -/
theorem op_localGet {x : Nat} (S : Spec.store)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.LOCAL_GET (.mk_uN x) :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = sp) :
    code[pc]? = some (.localGet x) ∧ ∃ t v body',
    ActW code locals maxH (Slots.wr s u (slot s (fp + x))) fp (sp + 1) (pc + 1) f body' L H d e te
      (tsC ++ [t]) (valsC ++ [v]) is ∧
    Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S f) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @localGet _ _ _ _ _ _ _ _ t hcode hloct hroom hnext =>
    have hlen := hsl.length
    have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
    obtain ⟨v, hv1, hv2⟩ := hloc.2 x t hloct
    have hfr : ∀ i, i < sp → slot (Slots.wr s u (slot s (fp + x))) i = slot s i := fun i h =>
      slot_wr_ne s u _ i hS (by omega) (by omega)
    have hnew : slot (Slots.wr s u (slot s (fp + x))) (fp + locals.length + d + tsC.length) = slot s (fp + x) := by
      rw [← hsp, ← hu]; exact slot_wr_same s u _ hS (by omega)
    refine ⟨hcode, t, v, _, ⟨Nest.frame hn (fun i _ h => hfr i (by omega)),
      SlotsR.append (SlotsR.frame hsl fun i _ h => hfr i (by omega)) ⟨?_, trivial⟩, hnext,
      by simp; omega, by simp; omega, rfl, LocalsR.frame hloc fun y hy => hfr _ (by omega)⟩, ?_⟩
    · simp only [Nat.add_assoc] at hnew ⊢
      rw [hnew]; exact hv2
    · subst hb
      refine steps_one (step_plug _ _ H _ _ ?_)
      rw [map_snoc]
      have h := step_ctx (.mk_state S f) (.mk_state S f) valsC [.LOCAL_GET (.mk_uN x)] [Spec.instr_val v] is
        (Spec.Step.read _ _ _ (Spec.Step_read.local_get _ _ v (by
          simp only [Spec.fun_local, Spec.fof, Spec.fun_frame, Spec.proj_uN_0]
          rw [List.getElem!_eq_getElem?_getD, hv1]; exact option_val_beq_self _)))
      simpa using h

theorem SlotsR.one {s : Slots} {p t vs} (h : SlotsR s p [t] vs) : ∃ v, vs = [v] ∧ ValR t (slot s p) v := by
  match vs, h with
  | [v], ⟨h1, _⟩ => exact ⟨v, rfl, h1⟩

theorem SlotsR.two {s : Slots} {p t1 t2 vs} (h : SlotsR s p [t1, t2] vs) :
    ∃ a b, vs = [a, b] ∧ ValR t1 (slot s p) a ∧ ValR t2 (slot s (p + 1)) b := by
  match vs, h with
  | [a, b], ⟨h1, h2, _⟩ => exact ⟨a, b, rfl, h1, h2⟩

/-- The frame after `local.set x` to `v`. -/
def setLocal (f : Spec.frame) (x : Nat) (v : Spec.val) : Spec.frame :=
  { f with LOCALS := f.LOCALS.modify x fun _ => some v }

theorem with_local_eq (S : Spec.store) (f : Spec.frame) (x : Nat) (v : Spec.val) :
    Spec.with_local (.mk_state S f) (.mk_uN x) v = .mk_state S (setLocal f x v) := rfl

theorem LocalsR.set {s s' : Slots} {fp locals f x t v} (h : LocalsR s fp locals f)
    (hx : locals[x]? = some t) (hv : ValR t (slot s' (fp + x)) v)
    (hs : ∀ y, y < locals.length → y ≠ x → slot s' (fp + y) = slot s (fp + y)) :
    LocalsR s' fp locals (setLocal f x v) := by
  refine ⟨by simp [setLocal, h.1], fun y t' hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx
    rw [hx] at hy; cases hy
    have hxl : y < f.LOCALS.length := by rw [h.1]; exact (List.getElem?_eq_some_iff.mp hx).1
    exact ⟨v, by simp [setLocal, List.getElem?_modify, hxl], hv⟩
  · obtain ⟨w, h1, h2⟩ := h.2 y t' hy
    refine ⟨w, by simp [setLocal, List.getElem?_modify, Ne.symm hyx, h1], ?_⟩
    rw [hs y (List.getElem?_eq_some_iff.mp hy).1 hyx]; exact h2

/-- `local.set x`: `Step.local_set` changes the frame; the engine writes slot `fp + x`. -/
theorem op_localSet {x : Nat} (S : Spec.store)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.LOCAL_SET (.mk_uN x) :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = fp + x) :
    code[pc]? = some (.localSet x) ∧ ∃ ts v valsC' body',
    ActW code locals maxH (Slots.wr s u (slot s (sp - 1))) fp (sp - 1) (pc + 1) (setLocal f x v) body' L H d e te
      ts valsC' is ∧
    Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S (setLocal f x v)) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @localSet _ _ _ ts _ _ _ _ t hcode hloct hnext =>
    have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨v, rfl, hv⟩ := SlotsR.one h2
    have hl1 := h1.length
    simp at hsp hmax
    have hfr : ∀ i, i ≠ fp + x → i < USize.size → slot (Slots.wr s u (slot s (sp - 1))) i = slot s i := fun i h h' =>
      slot_wr_ne s u _ i hS h' (by omega)
    refine ⟨hcode, ts, v, vs1, _, ⟨Nest.frame hn (fun i a b => hfr i (by omega) (by omega)),
      SlotsR.frame h1 fun i a b => hfr i (by omega) (by omega), hnext,
      by omega, by omega, rfl, LocalsR.set hloc hloct ?_ ?_⟩, ?_⟩
    · rw [← hu, slot_wr_same s u _ hS (by omega)]
      have : sp - 1 = fp + locals.length + d + ts.length := by omega
      rw [this]; exact hv
    · intro y hy hyx; exact hfr _ (by omega) (by omega)
    · subst hb
      refine steps_one (step_plug _ _ H _ _ ?_)
      have h := step_ctx (.mk_state S f) (.mk_state S (setLocal f x v)) vs1
        [Spec.instr_val v, .LOCAL_SET (.mk_uN x)] [] is
        (by rw [← with_local_eq]; exact Spec.Step.local_set _ v _)
      simpa using h

/-- `local.tee x`: `Step_pure.local_tee` then `Step.local_set`. -/
theorem op_localTee {x : Nat} (S : Spec.store)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.LOCAL_TEE (.mk_uN x) :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = fp + x) :
    code[pc]? = some (.localTee x) ∧ ∃ v body',
    ActW code locals maxH (Slots.wr s u (slot s (sp - 1))) fp sp (pc + 1) (setLocal f x v) body' L H d e te
      tsC valsC is ∧
    Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S (setLocal f x v)) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @localTee _ _ _ ts _ _ _ _ t hcode hloct hnext =>
    have hq : (ts ++ [t]).length = ts.length + 1 := by simp
    have hxl : x < locals.length := (List.getElem?_eq_some_iff.mp hloct).1
    have hsl0 := hsl
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨v, rfl, hv⟩ := SlotsR.one h2
    have hl1 := h1.length
    simp at hsp hmax
    have hfr : ∀ i, i ≠ fp + x → i < USize.size → slot (Slots.wr s u (slot s (sp - 1))) i = slot s i := fun i h h' =>
      slot_wr_ne s u _ i hS h' (by omega)
    refine ⟨hcode, v, _, ⟨Nest.frame hn (fun i a b => hfr i (by omega) (by omega)),
      SlotsR.frame hsl0 fun i a b => hfr i (by omega) (by omega), hnext,
      by simp; omega, by simp; omega, rfl, LocalsR.set hloc hloct ?_ ?_⟩, ?_⟩
    · rw [← hu, slot_wr_same s u _ hS (by omega)]
      have : sp - 1 = fp + locals.length + d + ts.length := by omega
      rw [this]; exact hv
    · intro y hy hyx; exact hfr _ (by omega) (by omega)
    · subst hb
      have e1 : (vs1 ++ [v]).map Spec.instr_val ++ (Spec.instr.LOCAL_TEE (.mk_uN x) :: is) =
          vs1.map Spec.instr_val ++ ([Spec.instr_val v, .LOCAL_TEE (.mk_uN x)] ++ is) := by simp
      have e2 : vs1.map Spec.instr_val ++ ([Spec.instr_val v, Spec.instr_val v, .LOCAL_SET (.mk_uN x)] ++ is) =
          (vs1 ++ [v]).map Spec.instr_val ++ ([Spec.instr_val v, .LOCAL_SET (.mk_uN x)] ++ is) := by simp
      rw [e1]
      refine Spec.Steps.trans _ _ _ _ _ _ (step_plug _ _ H _ _
        (step_ctx _ _ vs1 _ _ is (Spec.Step.pure _ _ _ (Spec.Step_pure.local_tee v _)))) ?_
      rw [e2]
      refine steps_one (step_plug _ _ H _ _ ?_)
      have h := step_ctx (.mk_state S f) (.mk_state S (setLocal f x v)) (vs1 ++ [v])
        [Spec.instr_val v, .LOCAL_SET (.mk_uN x)] [] is
        (by rw [← with_local_eq]; exact Spec.Step.local_set _ v _)
      simpa using h

/-- A binary numeric op (`BinR`): `Step_pure.binop_val`; the engine's `Simple.exec (.bin op)`. -/
theorem op_binop {op : NumOp} {nt : Spec.numtype} {bop : Spec.binop_} (S : Spec.store)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.BINOP nt bop :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8) (u : USize) (hu : u.toNat = sp - 2)
    (hop : code[pc]? = some (.num op)) :
    ∃ t ts vr valsC' body', BinR op t nt bop ∧
    ActW code locals maxH (Slots.wr s u (op.evalBin (slot s (sp - 2)) (slot s (sp - 1)))) fp (sp - 1) (pc + 1)
      f body' L H d e te (ts ++ [t]) (valsC' ++ [vr]) is ∧
    Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S f) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @binop _ _ _ ts _ _ _ op' t _ _ hcode hbin hnext =>
    rw [hop] at hcode; cases hcode
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨a, b, rfl, ha, hb2⟩ := SlotsR.two h2
    have hl1 := h1.length
    simp at hsp hmax
    have e2 : sp - 2 = fp + locals.length + d + ts.length := by omega
    have e1 : sp - 1 = fp + locals.length + d + ts.length + 1 := by omega
    have hu' : u.toNat = fp + locals.length + d + ts.length := by omega
    rw [e1, e2]
    obtain ⟨vr, hvr, hstep⟩ := bin_step hbin ha hb2
    have hfr : ∀ i, i < fp + locals.length + d + ts.length → slot (Slots.wr s u (op.evalBin
        (slot s (fp + locals.length + d + ts.length)) (slot s (fp + locals.length + d + ts.length + 1)))) i = slot s i :=
      fun i h => slot_wr_ne s u _ i hS (by omega) (by omega)
    refine ⟨t, ts, vr, vs1, _, hbin, ⟨Nest.frame hn (fun i a b => hfr i (by omega)),
      SlotsR.append (SlotsR.frame h1 fun i a b => hfr i (by omega)) ⟨?_, trivial⟩, hnext,
      by simp; omega, by simp; omega, rfl, LocalsR.frame hloc fun y hy => hfr _ (by omega)⟩, ?_⟩
    · have hw' := slot_wr_same s u (op.evalBin (slot s (fp + locals.length + d + ts.length))
        (slot s (fp + locals.length + d + ts.length + 1))) hS (by omega)
      rw [hu'] at hw'; rw [hw']; exact hvr
    · subst hb
      refine steps_one (step_plug _ _ H _ _ ?_)
      have h := step_ctx (.mk_state S f) (.mk_state S f) vs1
        [Spec.instr_val a, Spec.instr_val b, .BINOP nt bop] [Spec.instr_val vr] is (Spec.Step.pure _ _ _ hstep)
      simpa using h

/-! ### Branches -/

/-- The slots after a branch moved `k` values from `src` down to `dst`. -/
def Moved (s s' : Slots) (src dst k : Nat) : Prop :=
  s'.size = s.size ∧ (∀ i, i < dst → slot s' i = slot s i) ∧
    (∀ j, j < k → slot s' (dst + j) = slot s (src + j))

/-- The function body has returned to its frame: only the result values are left, and
the engine is at the function's final `return`. -/
def DoneR (code : Array Op) (locals : List ValType) (maxH : Nat) (s : Slots) (fp sp pc : Nat)
    (f : Spec.frame) (body : List Spec.instr) : Prop :=
  ∃ rs vals, code[pc]? = some (.return_ rs.length) ∧ SlotsR s (fp + locals.length) rs vals ∧
    sp = fp + locals.length + rs.length ∧ locals.length + rs.length ≤ maxH ∧
    body = vals.map Spec.instr_val ∧ LocalsR s fp locals f

theorem Nest.base_le {code locals maxH s fp L H d e te} (hn : Nest code locals maxH s fp L H d e te) :
    ∀ lb ∈ L, lb.base ≤ locals.length + d := by
  induction hn with
  | func => intro lb h; simp at h; subst h; simp
  | block vals tsH rs pe1 rest _ _ _ ih =>
    intro lb h; simp at h
    rcases h with rfl | h
    · simp; omega
    · have := ih lb h; omega
  | loop vals tsH rs ps pe1 rest st body _ _ _ _ ih =>
    intro lb h; simp at h
    rcases h with rfl | h
    · simp; omega
    · have := ih lb h; omega

theorem slot_eq_of {s s' : Slots} {a a' b b' : Nat} (h : slot s' a' = slot s b') (ha : a = a') (hb : b = b') :
    slot s' a = slot s b := by subst ha hb; exact h

theorem uN_pred (k : Nat) :
    Spec.uN.mk_uN (Int.toNat (Int.ofNat (Spec.proj_uN_0 (.mk_uN (k + 1))) - Int.ofNat 1)) = .mk_uN k := by
  simp [Spec.proj_uN_0]

/-- `br l` (and a taken `br_if`): the spec leaves `l` labels by `br_label_succ`, then
`br_label_zero` keeps the label's arity of values and goes on with its continuation;
the engine moved those values to the label's height (the side-table entry) and jumped
to its pc. The proof is by induction on `l`. -/
theorem br_up {code locals maxH} {s s' : Slots} {fp : Nat} {f : Spec.frame} (lb : Lbl)
    (z : Spec.state) (hloc : LocalsR s fp locals f) (harity : lb.arity = lb.types.length) :
    ∀ (l : Nat) (L : List Lbl) (H : List Hole) (d e : Nat) (te ts0 : List ValType) (vs : List Spec.val)
      (is : List Spec.instr),
      Nest code locals maxH s fp L H d e te →
      SlotsR s (fp + locals.length + d) (ts0 ++ lb.types) vs → L[l]? = some lb →
      locals.length + d + (ts0 ++ lb.types).length ≤ maxH →
      Moved s s' (fp + locals.length + d + ts0.length) (fp + lb.base) lb.arity →
      ∃ body', Spec.Steps (.mk_config z (plug H (vs.map Spec.instr_val ++ (.BR (.mk_uN l) :: is))))
        (.mk_config z body') ∧
        (ActR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body' ∨
          DoneR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body') := by
  intro l
  induction l with
  | zero =>
    intro L H d e te ts0 vs is hn hsl hl hmax hmv
    obtain ⟨hsz, hlo, hmo⟩ := hmv
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    have hl1 := h1.length
    simp only [List.length_append] at hmax
    cases hn with
    | func pe rs m hret =>
      simp at hl; subst hl
      have hl2 : te.length = vs2.length := h2.length
      dsimp only at hmax
      simp at hlo hmo harity ⊢
      refine ⟨_, ?_, Or.inr ⟨te, vs2, hret, SlotsR.move h2 fun j hj => ?_, by omega, by omega, rfl,
        LocalsR.frame hloc fun x hx => hlo _ (by omega)⟩⟩
      · refine steps_one (Spec.Step.pure _ _ _ ?_)
        have := Spec.Step_pure.br_label_zero m [] vs1 vs2 (.mk_uN 0) is (by decide)
        simpa [plug] using this
      · exact slot_eq_of (hmo j (by omega)) (by omega) (by omega)
    | @block L0 H0 d0 e0 te0 vals tsH rs pe1 rest hn0 hsl0 hc0 =>
      simp at hl; subst hl
      have hl2 : te.length = vs2.length := h2.length
      dsimp only at hmax
      simp at hlo hmo harity ⊢
      have hh := hsl0.length
      refine ⟨_, ?_, Or.inl ⟨_, _, _, _, _, tsH ++ te, vals ++ vs2, rest,
        Nest.frame hn0 (fun i a b => hlo i (by omega)),
        SlotsR.append (SlotsR.frame hsl0 fun i a b => hlo i (by omega))
          (SlotsR.move h2 fun j hj => ?_), hc0, by simp; omega, by simp; omega, rfl,
        LocalsR.frame hloc fun x hx => hlo _ (by omega)⟩⟩
      · have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ te.length [] (vs1.map Spec.instr_val ++
            (vs2.map Spec.instr_val ++ ([.BR (.mk_uN 0)] ++ is)))] (vs2.map Spec.instr_val ++ []) rest
          (Spec.Step.pure _ _ _ (Spec.Step_pure.br_label_zero _ [] vs1 vs2 (.mk_uN 0) is (by decide))))
        exact steps_one (by simpa [plug_cons] using h)
      · exact slot_eq_of (hmo j (by omega)) (by omega) (by omega)
    | @loop L0 H0 d0 e0 te0 vals tsH rs ps pe1 rest st body0 hn0 hsl0 hb0 hc0 =>
      simp at hl; subst hl
      simp at hlo hmo harity ⊢
      obtain rfl : vs2 = [] := by cases vs2 with | nil => rfl | cons => exact h2.elim
      have hh := hsl0.length
      refine ⟨_, ?_, Or.inl ⟨_, _, _, _, _, tsH, vals, .LOOP (._RESULT st) body0 :: rest,
        Nest.frame hn0 (fun i a b => hlo i (by omega)),
        SlotsR.frame hsl0 fun i a b => hlo i (by omega), Comp.loop te st body0 e hb0 hc0,
        by omega, by omega, rfl, LocalsR.frame hloc fun x hx => hlo _ (by omega)⟩⟩
      have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ 0 [.LOOP (._RESULT st) body0]
          (vs1.map Spec.instr_val ++ (([] : List Spec.val).map Spec.instr_val ++ ([.BR (.mk_uN 0)] ++ is)))]
          (([] : List Spec.val).map Spec.instr_val ++ [.LOOP (._RESULT st) body0]) rest
        (Spec.Step.pure _ _ _ (Spec.Step_pure.br_label_zero _ _ vs1 [] (.mk_uN 0) is (by decide))))
      exact steps_one (by simpa [plug_cons] using h)
  | succ k ih =>
    intro L H d e te ts0 vs is hn hsl hl hmax hmv
    cases hn with
    | func pe rs m hret => simp at hl
    | @block L0 H0 d0 e0 te0 vals tsH rs pe1 rest hn0 hsl0 hc0 =>
      simp at hl
      have hh := hsl0.length
      have hsl' : SlotsR s (fp + locals.length + d0) ((tsH ++ ts0) ++ lb.types) (vals ++ vs) := by
        rw [List.append_assoc]; exact SlotsR.append hsl0 (by simpa [Nat.add_assoc] using hsl)
      obtain ⟨body', hst, hres⟩ := ih L0 H0 d0 e0 te0 (tsH ++ ts0) (vals ++ vs) rest hn0 hsl' hl
        (by simp at hmax ⊢; omega)
        (by rw [show fp + locals.length + d0 + (tsH ++ ts0).length =
          fp + locals.length + (d0 + tsH.length) + ts0.length by simp; omega]; exact hmv)
      refine ⟨body', steps_trans ?_ hst, hres⟩
      have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ te.length []
          (vs.map Spec.instr_val ++ ([.BR (.mk_uN (k + 1))] ++ is))]
          (vs.map Spec.instr_val ++ [.BR (.mk_uN (Int.toNat (Int.ofNat (Spec.proj_uN_0 (.mk_uN (k + 1))) - Int.ofNat 1)))]) rest
        (Spec.Step.pure _ _ _ (Spec.Step_pure.br_label_succ _ [] vs (.mk_uN (k + 1)) is (by simp [Spec.proj_uN_0]))))
      rw [uN_pred] at h
      exact steps_one (by simpa [plug_cons] using h)
    | @loop L0 H0 d0 e0 te0 vals tsH rs ps pe1 rest st body0 hn0 hsl0 hb0 hc0 =>
      simp at hl
      have hh := hsl0.length
      have hsl' : SlotsR s (fp + locals.length + d0) ((tsH ++ ts0) ++ lb.types) (vals ++ vs) := by
        rw [List.append_assoc]; exact SlotsR.append hsl0 (by simpa [Nat.add_assoc] using hsl)
      obtain ⟨body', hst, hres⟩ := ih L0 H0 d0 e0 te0 (tsH ++ ts0) (vals ++ vs) rest hn0 hsl' hl
        (by simp at hmax ⊢; omega)
        (by rw [show fp + locals.length + d0 + (tsH ++ ts0).length =
          fp + locals.length + (d0 + tsH.length) + ts0.length by simp; omega]; exact hmv)
      refine ⟨body', steps_trans ?_ hst, hres⟩
      have h := step_plug z z H0 _ _ (step_ctx z z vals [.LABEL_ 0 [.LOOP (._RESULT st) body0]
          (vs.map Spec.instr_val ++ ([.BR (.mk_uN (k + 1))] ++ is))]
          (vs.map Spec.instr_val ++ [.BR (.mk_uN (Int.toNat (Int.ofNat (Spec.proj_uN_0 (.mk_uN (k + 1))) - Int.ofNat 1)))]) rest
        (Spec.Step.pure _ _ _ (Spec.Step_pure.br_label_succ _ _ vs (.mk_uN (k + 1)) is (by simp [Spec.proj_uN_0]))))
      rw [uN_pred] at h
      exact steps_one (by simpa [plug_cons] using h)

end Ops

/-! ### Memory -/

theorem wf_i32 (n : Nat) (h : n < 2^32) : Spec.wf_num_ .I32 (.mk_num__0 .I32 (.mk_uN n)) := by
  refine Spec.wf_num_.num__case_0 _ _ _ ?_ (by rfl)
  refine Spec.wf_uN.uN_case_0 _ _ ?_
  have e : (Int.ofNat (2 ^ 32) - Int.ofNat 1).toNat = 2 ^ 32 - 1 := by decide
  simp only [Spec.size, Spec.numtype_Inn, Spec.sizenn, e, ge_iff_le, Nat.zero_le, decide_true, Bool.true_and,
    decide_eq_true_eq]
  omega

theorem floor4 : (Int.toNat (Rat.floor ((Rat.ofInt (Int.ofNat (Spec.size .I32))) / (Rat.ofInt (Int.ofNat 8))))) = 4 := by
  have h1 : Rat.ofInt (Int.ofNat 32) = Rat.ofInt (Int.ofNat 4) * Rat.ofInt (Int.ofNat 8) := Rat.intCast_mul 4 8
  have h2 : Rat.ofInt (Int.ofNat 4) * Rat.ofInt (Int.ofNat 8) / Rat.ofInt (Int.ofNat 8) = Rat.ofInt (Int.ofNat 4) :=
    Rat.mul_div_cancel (by decide)
  have h3 : (Rat.ofInt (Int.ofNat 4)).floor = 4 := Rat.floor_intCast 4
  simp only [Spec.size]; rw [h1, h2, h3]; rfl

theorem ibytes32 (r : Nat) (h : r < 2^32) :
    Spec.Builtins.OnNat.ibytes_ 32 r = [r % 256, r / 256 % 256, r / 65536 % 256, r / 16777216 % 256] := by
  simp [Spec.Builtins.OnNat.ibytes_, Spec.Builtins.ibytes_, List.range_succ, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem take4 {α} (l : List α) (ea : Nat) (h : ea + 4 ≤ l.length) :
    List.take 4 (List.drop ea l) = [l[ea], l[ea + 1], l[ea + 2], l[ea + 3]] := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_drop]
  match n with
  | 0 => simp [List.getElem?_eq_getElem (by omega : ea < l.length)]
  | 1 => simp [List.getElem?_eq_getElem (by omega : ea + 1 < l.length)]
  | 2 => simp [List.getElem?_eq_getElem (by omega : ea + 2 < l.length)]
  | 3 => simp [List.getElem?_eq_getElem (by omega : ea + 3 < l.length)]
  | n + 4 => simp; omega

theorem byte_beq_self (b : Spec.byte) : (b == b) = true := by
  cases b; simp [BEq.beq, Spec.instBEqByte.beq]

theorem bytes_beq_self (l : List Spec.byte) : (l == l) = true := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [byte_beq_self, ih]

section MemOps
variable {M : Type} [LinearMemory M] [LinearMemoryLaws M]

/-- A spec memory instance holds the bytes of an engine memory. -/
def MemR (m : M) (mi : Spec.meminst) : Prop :=
  mi.BYTES.length = LinearMemory.size m ∧
    ∀ n, n < LinearMemory.size m → mi.BYTES[n]? = some (.mk_byte (LinearMemoryLaws.byte m n).toNat)

theorem MemR.bytes4 {m : M} {mi : Spec.meminst} (h : MemR m mi) (ea : Nat) (hin : ea + 4 ≤ LinearMemory.size m) :
    List.take 4 (List.drop ea mi.BYTES) =
      [.mk_byte (LinearMemoryLaws.byte m ea).toNat, .mk_byte (LinearMemoryLaws.byte m (ea + 1)).toNat,
       .mk_byte (LinearMemoryLaws.byte m (ea + 2)).toNat, .mk_byte (LinearMemoryLaws.byte m (ea + 3)).toNat] := by
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_take, List.getElem?_drop]
  match n with
  | 0 => simpa using h.2 ea (by omega)
  | 1 => simpa using h.2 (ea + 1) (by omega)
  | 2 => simpa using h.2 (ea + 2) (by omega)
  | 3 => simpa using h.2 (ea + 3) (by omega)
  | n + 4 => simp; omega

theorem nbytes_le32 (m : M) (ea : Nat) :
    Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN (le32 (LinearMemoryLaws.byte m) ea).toNat)) =
      [.mk_byte (LinearMemoryLaws.byte m ea).toNat, .mk_byte (LinearMemoryLaws.byte m (ea + 1)).toNat,
       .mk_byte (LinearMemoryLaws.byte m (ea + 2)).toNat, .mk_byte (LinearMemoryLaws.byte m (ea + 3)).toNat] := by
  have hv := le32_toNat (LinearMemoryLaws.byte m) ea
  have b0 := (LinearMemoryLaws.byte m (ea + 0)).toNat_lt; have b1 := (LinearMemoryLaws.byte m (ea + 1)).toNat_lt
  have b2 := (LinearMemoryLaws.byte m (ea + 2)).toNat_lt; have b3 := (LinearMemoryLaws.byte m (ea + 3)).toNat_lt
  simp only [Nat.add_zero] at hv b0
  simp only [Spec.nbytes_, Spec.ibytes_, Spec.proj_uN_0]
  rw [ibytes32 _ (by simp only [Nat.reducePow] at *; omega)]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Spec.byte.mk_byte.injEq, and_true]
  simp only [Nat.reducePow] at *
  omega

/-- `i32.load` (memory 0): `Step_read.load_num_val`; the engine reads four bytes through
`LinearMemory.load32` after its one bounds check. -/
theorem op_load {code : Array Op} {locals : List ValType} {maxH : Nat} {s : Slots} {fp sp pc : Nat}
    {f : Spec.frame} {body : List Spec.instr} {L : List Lbl} {H : List Hole} {d e : Nat}
    {te tsC : List ValType} {valsC : List Spec.val} {is : List Spec.instr} {al off : Nat}
    (S : Spec.store) (dm : M) (hmem : MemR dm (Spec.fun_mem (.mk_state S f) (.mk_uN 0)))
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC
      (.LOAD .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: is))
    (hS : s.size < USize.size) (hcap : fp + maxH ≤ s.size / 8)
    (ea : Nat) (hea : ea = (slot s (sp - 1)).toNat + off)
    (hin : ea + 4 ≤ LinearMemory.size dm) (u : USize) (hu : u.toNat = sp - 1) :
    code[pc]? = some (.load .i32 0 off) ∧ ∃ ts vs1 body',
    ActW code locals maxH (Slots.wr s u (LinearMemory.load32 dm ea hin)) fp sp (pc + 1) f body' L H d e te
      (ts ++ [.i32]) (vs1 ++ [i32c (LinearMemory.load32 dm ea hin).toNat]) is ∧
    Spec.Steps (.mk_config (.mk_state S f) body) (.mk_config (.mk_state S f) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @load _ _ _ ts _ _ _ _ _ hcode hnext =>
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨va, rfl, hva⟩ := SlotsR.one h2
    have hl1 := h1.length
    simp at hsp hmax
    have ep : sp - 1 = fp + locals.length + d + ts.length := by omega
    have hu' : u.toNat = fp + locals.length + d + ts.length := by omega
    rw [ep] at hea
    obtain ⟨ha32, rfl⟩ := hva
    obtain ⟨r, hr⟩ : ∃ r, r = LinearMemory.load32 dm ea hin := ⟨_, rfl⟩
    rw [← hr]
    have hrv : r = le32 (LinearMemoryLaws.byte dm) ea := hr.trans (LinearMemoryLaws.load32_eq dm ea hin)
    have hr32 : r.toNat < 2^32 := by
      have := le32_toNat (LinearMemoryLaws.byte dm) ea
      have b0 := (LinearMemoryLaws.byte dm (ea + 0)).toNat_lt
      have b1 := (LinearMemoryLaws.byte dm (ea + 1)).toNat_lt
      have b2 := (LinearMemoryLaws.byte dm (ea + 2)).toNat_lt
      have b3 := (LinearMemoryLaws.byte dm (ea + 3)).toNat_lt
      rw [hrv, this]; simp only [Nat.reducePow] at *; omega
    have hfr : ∀ i, i < fp + locals.length + d + ts.length → slot (Slots.wr s u r) i = slot s i :=
      fun i h => slot_wr_ne s u _ i hS (by omega) (by omega)
    refine ⟨hcode, ts, vs1, _, ⟨Nest.frame hn (fun i a b => hfr i (by omega)),
      SlotsR.append (SlotsR.frame h1 fun i a b => hfr i (by omega)) ⟨?_, trivial⟩, hnext,
      by simp; omega, by simp; omega, rfl, LocalsR.frame hloc fun y hy => hfr _ (by omega)⟩, ?_⟩
    · have hw' := slot_wr_same s u r hS (by omega)
      rw [hu'] at hw'; rw [hw']; exact ⟨hr32, rfl⟩
    · subst hb
      refine steps_one (step_plug _ _ H _ _ ?_)
      have hst := Spec.Step_read.load_num_val (.mk_state S f) .I32
        (.mk_num__0 .I32 (.mk_uN (slot s (fp + locals.length + d + ts.length)).toNat)) .I32 (.mk_uN 0)
        ⟨.mk_uN al, .mk_uN off⟩ (.mk_num__0 .I32 (.mk_uN r.toNat))
        (wf_i32 _ ha32) (wf_i32 _ hr32) rfl (by
          simp only [Spec.proj_num__0, Option.get!_some, Spec.proj_uN_0, floor4]
          rw [← hea, MemR.bytes4 hmem _ hin, hrv, nbytes_le32]; exact bytes_beq_self _)
      have h := step_ctx (.mk_state S f) (.mk_state S f) vs1
        [Spec.instr_val (i32c (slot s (fp + locals.length + d + ts.length)).toNat),
          .LOAD .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩] [Spec.instr_val (i32c r.toNat)] is
        (Spec.Step.read _ _ _ hst)
      simpa using h

end MemOps

section BrOps
variable {code : Array Op} {locals : List ValType} {maxH : Nat} {s : Slots} {fp sp pc : Nat}
  {f : Spec.frame} {body : List Spec.instr} {L : List Lbl} {H : List Hole} {d e : Nat}
  {te tsC : List ValType} {valsC : List Spec.val} {is : List Spec.instr}

/-- `br l`: what the side table says (`Comp.br`), and `br_up`. -/
theorem op_br {l : Nat} (z : Spec.state) {s' : Slots}
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.BR (.mk_uN l) :: is)) :
    ∃ lb ts0, L[l]? = some lb ∧ code[pc]? = some (.br lb.target) ∧ tsC = ts0 ++ lb.types ∧
      lb.arity = lb.types.length ∧
      (Moved s s' (fp + locals.length + d + ts0.length) (fp + lb.base) lb.arity →
      ∃ body', Spec.Steps (.mk_config z body) (.mk_config z body') ∧
        (ActR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body' ∨
          DoneR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body')) := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @br _ _ _ _ _ _ _ _ lb ts0 _ hl hcode hts har hbase hnext =>
    refine ⟨lb, ts0, hl, hcode, hts, har, fun hmv => ?_⟩
    subst hts hb
    exact br_up lb z hloc har l L H d e te ts0 valsC is hn hsl hl hmax hmv

/-- `br_if l`, not taken: `br_if_false`. -/
theorem op_brIf_false {l : Nat} (z : Spec.state)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.BR_IF (.mk_uN l) :: is))
    (hc0 : slot s (sp - 1) = 0) :
    ∃ ts vs body', ActW code locals maxH s fp (sp - 1) (pc + 1) f body' L H d e te ts vs is ∧
      Spec.Steps (.mk_config z body) (.mk_config z body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @brIf _ _ _ ts _ _ _ _ lb ts0 hl hcode hts har hbase hnext =>
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨vc, rfl, hvc⟩ := SlotsR.one h2
    have hl1 := h1.length
    simp at hsp hmax
    have ep : sp - 1 = fp + locals.length + d + ts.length := by omega
    rw [ep] at hc0
    obtain ⟨_, rfl⟩ := hvc
    refine ⟨ts, vs1, _, ⟨hn, h1, hnext, by omega, by omega, rfl, hloc⟩, ?_⟩
    subst hb
    refine steps_one (step_plug _ _ H _ _ ?_)
    have h := step_ctx z z vs1 [Spec.instr_val (i32c (slot s (fp + locals.length + d + ts.length)).toNat),
      .BR_IF (.mk_uN l)] [] is (Spec.Step.pure _ _ _ (Spec.Step_pure.br_if_false _ _ (wf_i32 _ (by rw [hc0]; decide))
        rfl (by simp [Spec.proj_num__0, Spec.proj_uN_0, hc0])))
    simpa [i32c, Spec.instr_val] using h

/-- `br_if l`, taken: `br_if_true`, then as `br`. -/
theorem op_brIf_true {l : Nat} (z : Spec.state) {s' : Slots}
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC (.BR_IF (.mk_uN l) :: is))
    (hc0 : slot s (sp - 1) ≠ 0) :
    ∃ lb ts0, L[l]? = some lb ∧ code[pc]? = some (.brIf lb.target) ∧ tsC = ts0 ++ lb.types ++ [.i32] ∧
      lb.arity = lb.types.length ∧
      (Moved s s' (fp + locals.length + d + ts0.length) (fp + lb.base) lb.arity →
      ∃ body', Spec.Steps (.mk_config z body) (.mk_config z body') ∧
        (ActR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body' ∨
          DoneR code locals maxH s' fp (fp + lb.base + lb.arity) lb.pc f body')) := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @brIf _ _ _ ts _ _ _ _ lb ts0 hl hcode hts har hbase hnext =>
    refine ⟨lb, ts0, hl, hcode, by rw [hts], har, fun hmv => ?_⟩
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨vc, rfl, hvc⟩ := SlotsR.one h2
    have hl1 := h1.length
    simp at hsp hmax
    have ep : sp - 1 = fp + locals.length + d + ts.length := by omega
    rw [ep] at hc0
    obtain ⟨h32, rfl⟩ := hvc
    subst hts hb
    obtain ⟨body', hst, hres⟩ := br_up lb z hloc har l L H d e te ts0 vs1 is hn h1 hl (by simp at hmax ⊢; omega) hmv
    refine ⟨body', steps_trans (steps_one (step_plug _ _ H _ _ ?_)) hst, hres⟩
    have h := step_ctx z z vs1 [Spec.instr_val (i32c (slot s (fp + locals.length + d + (ts0 ++ lb.types).length)).toNat),
      .BR_IF (.mk_uN l)] [.BR (.mk_uN l)] is (Spec.Step.pure _ _ _ (Spec.Step_pure.br_if_true _ _ (wf_i32 _ h32)
        rfl (by
          simp [Spec.proj_num__0, Spec.proj_uN_0]
          intro h0; exact hc0 (UInt64.toNat_inj.mp (by simpa using h0)))))
    simpa [i32c, Spec.instr_val] using h

end BrOps

theorem slice_get {α} (l bs : List α) (ea n : Nat) (hb : bs.length = 4) (hl : ea + 4 ≤ l.length) :
    (Spec.list_slice_update l ea 4 bs)[n]? = if n < ea then l[n]? else if n < ea + 4 then bs[n - ea]? else l[n]? := by
  unfold Spec.list_slice_update
  by_cases h1 : n < ea
  · rw [if_pos h1, List.append_assoc, List.getElem?_append_left (by simp; omega), List.getElem?_take, if_pos h1]
  · rw [if_neg h1, List.append_assoc, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_take, Nat.min_eq_left (by omega : ea ≤ l.length)]
    by_cases h2 : n < ea + 4
    · rw [if_pos h2, List.getElem?_append_left (by omega)]
    · rw [if_neg h2, List.getElem?_append_right (by omega), List.getElem?_drop, hb]
      congr 1; omega

theorem slice_length {α} (l bs : List α) (ea : Nat) (hb : bs.length = 4) (hl : ea + 4 ≤ l.length) :
    (Spec.list_slice_update l ea 4 bs).length = l.length := by
  simp [Spec.list_slice_update, hb]; omega

section StoreOps
variable {M : Type} [LinearMemory M] [LinearMemoryLaws M]

theorem nbytes_i32 (v : Nat) (h : v < 2^32) :
    Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN v)) =
      [.mk_byte (v % 256), .mk_byte (v / 256 % 256), .mk_byte (v / 65536 % 256), .mk_byte (v / 16777216 % 256)] := by
  simp only [Spec.nbytes_, Spec.ibytes_, Spec.proj_uN_0]
  rw [ibytes32 _ h]; rfl

/-- After `store32` of an i32 value, the memory holds the spec's slice update with the
value's `nbytes_`. -/
theorem MemR.store {m : M} {mi : Spec.meminst} (h : MemR m mi) (ea : Nat) (v : UInt64) (hv : v.toNat < 2^32)
    (hin : ea + 4 ≤ LinearMemory.size m) :
    MemR (LinearMemory.store32 m ea v hin)
      { mi with BYTES := Spec.list_slice_update mi.BYTES ea 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN v.toNat))) } := by
  rw [nbytes_i32 _ hv]
  refine ⟨?_, fun n hn => ?_⟩
  · simp only [LinearMemoryLaws.store32_size]; rw [slice_length _ _ _ rfl (by rw [h.1]; exact hin), h.1]
  · rw [LinearMemoryLaws.store32_size] at hn
    simp only
    rw [slice_get _ _ _ _ rfl (by rw [h.1]; exact hin), LinearMemoryLaws.store32_byte]
    by_cases h1 : n < ea
    · rw [if_pos h1, h.2 n hn, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [if_neg h1]
      by_cases h2 : n < ea + 4
      · rw [if_pos h2]
        have : n = ea + 0 ∨ n = ea + 1 ∨ n = ea + 2 ∨ n = ea + 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;>
          simp [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;> omega
      · rw [if_neg h2, h.2 n hn, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The spec store after `i32.store` of `v` at `ea` in memory 0 of frame `f`. -/
noncomputable def storeS (S : Spec.store) (f : Spec.frame) (ea : Nat) (v : Nat) : Spec.store :=
  Spec.fun_store (Spec.with_mem (.mk_state S f) (.mk_uN 0) ea 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN v))))

theorem with_mem_eq (S : Spec.store) (f : Spec.frame) (ea v : Nat) :
    Spec.with_mem (.mk_state S f) (.mk_uN 0) ea 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN v))) =
      .mk_state (storeS S f ea v) f := rfl

/-- `i32.store` (memory 0): `Step.store_num_val`. The spec store changes by `with_mem`
(`storeS`); `MemR.store` relates it to the engine's `store32`. -/
theorem op_store {code : Array Op} {locals : List ValType} {maxH : Nat} {s : Slots} {fp sp pc : Nat}
    {f : Spec.frame} {body : List Spec.instr} {L : List Lbl} {H : List Hole} {d e : Nat}
    {te tsC : List ValType} {valsC : List Spec.val} {is : List Spec.instr} {al off : Nat}
    (S : Spec.store)
    (hw : ActW code locals maxH s fp sp pc f body L H d e te tsC valsC
      (.STORE .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩ :: is))
    (ea : Nat) (hea : ea = (slot s (sp - 2)).toNat + off) :
    code[pc]? = some (.store .i32 0 off) ∧ (slot s (sp - 1)).toNat < 2^32 ∧ ∃ ts vs1 body',
    ActW code locals maxH s fp (sp - 2) (pc + 1) f body' L H d e te ts vs1 is ∧
    Spec.Steps (.mk_config (.mk_state S f) body)
      (.mk_config (.mk_state (storeS S f ea (slot s (sp - 1)).toNat) f) body') := by
  obtain ⟨hn, hsl, hc, hsp, hmax, hb, hloc⟩ := hw
  cases hc with
  | @store _ _ _ ts _ _ _ _ _ hcode hnext =>
    obtain ⟨vs1, vs2, rfl, h1, h2⟩ := SlotsR.split hsl
    obtain ⟨va, vv, rfl, hva, hvv⟩ := SlotsR.two h2
    have hl1 := h1.length
    simp at hsp hmax
    have e2 : sp - 2 = fp + locals.length + d + ts.length := by omega
    have e1 : sp - 1 = fp + locals.length + d + ts.length + 1 := by omega
    rw [e2] at hea; rw [e1]
    obtain ⟨ha32, rfl⟩ := hva
    obtain ⟨hv32, rfl⟩ := hvv
    refine ⟨hcode, hv32, ts, vs1, _, ⟨hn, h1, hnext, by omega, by omega, rfl, hloc⟩, ?_⟩
    subst hb
    refine steps_one (step_plug _ _ H _ _ ?_)
    have hst := Spec.Step.store_num_val (.mk_state S f) .I32
      (.mk_num__0 .I32 (.mk_uN (slot s (fp + locals.length + d + ts.length)).toNat)) .I32
      (.mk_num__0 .I32 (.mk_uN (slot s (fp + locals.length + d + ts.length + 1)).toNat)) (.mk_uN 0)
      ⟨.mk_uN al, .mk_uN off⟩ _ rfl (wf_i32 _ ha32) (wf_i32 _ hv32) (bytes_beq_self _)
    simp only [Spec.proj_num__0, Option.get!_some, Spec.proj_uN_0, floor4, ← hea] at hst
    rw [with_mem_eq] at hst
    have h := step_ctx _ _ vs1
      [Spec.instr_val (i32c (slot s (fp + locals.length + d + ts.length)).toNat),
        Spec.instr_val (i32c (slot s (fp + locals.length + d + ts.length + 1)).toNat),
        .STORE .I32 none (.mk_uN 0) ⟨.mk_uN al, .mk_uN off⟩] [] is hst
    simpa using h

end StoreOps

end L4Factoidal.WasmVM.Proofs.Refine
