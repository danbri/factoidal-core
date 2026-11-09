/-
L4Factoidal.WasmVM.Proofs.SpecWPSubset: the instruction subset that `SpecWPOps` covers,
as a small structured syntax `KI` with decidable equality, its reading from WasmVM's
decoded (flat) instructions, and its meaning as spec instructions (record:
docs/designissues/2026-11-09-verified-foaf-layout.md).

The chain from a binary to the spec is: bytes → `Binary.decode` (WasmVM's decoder) →
flat `Instr` → `FKI.ofBody` (the subset, flat) → `FKI.nestBody` → `KI.toSpec`. The first two steps are Lean
functions that the kernel evaluates on the actual bytes (`decide`), so a proof is
about the bytes. What is not proved is that this chain gives the bytes the meaning the
WebAssembly binary format gives them: the spec layer has no binary grammar (spec-layer
record, G3), so there is nothing to prove it against. The opcode table below is the
whole of that gap, and the doc names it as an assumption.

Every `KI` instruction is an integer instruction or structured control with block type
`[] -> []`; anything else makes `parse` fail, so a body that parses has no float
instruction, no call, no `memory.grow` and no host import.
-/
import L4Factoidal.WasmVM.Proofs.SpecWPOps
import L4Factoidal.WasmVM.Binary.Decode

namespace L4Factoidal.WasmVM.Proofs.SpecWP
open L4Factoidal.WasmVM

mutual
inductive KI where
  | i32const (k : Nat) | i64const (k : Nat)
  | localGet (x : Nat) | localSet (x : Nat) | localTee (x : Nat)
  | i32add | i32mul | i32geu | i32ne
  | i64add | i64sub | i64mul | i64gts | i64lts | i64les | i64extu
  | select
  | load32 (off : Nat) | store32 (off : Nat)
  | block (body : KIs) | loop (body : KIs) | ifThen (body : KIs)
  | br (l : Nat) | brIf (l : Nat)
/-- A sequence of `KI` (a separate type, so that `DecidableEq` derives). -/
inductive KIs where
  | nil
  | cons (i : KI) (is : KIs)
end

/-- One flat instruction of the subset, as the binary has it (`block`/`loop`/`if` open a
body, `end` closes one). Not recursive, so its derived equality is a flat comparison and
the kernel evaluates it. -/
inductive OpK where
  | i32const (k : Nat) | i64const (k : Nat)
  | localGet (x : Nat) | localSet (x : Nat) | localTee (x : Nat)
  | i32add | i32mul | i32geu | i32ne
  | i64add | i64sub | i64mul | i64gts | i64lts | i64les | i64extu
  | select
  | load32 (off : Nat) | store32 (off : Nat)
  | br (l : Nat) | brIf (l : Nat)
  deriving DecidableEq

def OpK.toKI : OpK → KI
  | .i32const k => .i32const k | .i64const k => .i64const k
  | .localGet x => .localGet x | .localSet x => .localSet x | .localTee x => .localTee x
  | .i32add => .i32add | .i32mul => .i32mul | .i32geu => .i32geu | .i32ne => .i32ne
  | .i64add => .i64add | .i64sub => .i64sub | .i64mul => .i64mul | .i64gts => .i64gts
  | .i64lts => .i64lts | .i64les => .i64les | .i64extu => .i64extu | .select => .select
  | .load32 o => .load32 o | .store32 o => .store32 o | .br l => .br l | .brIf l => .brIf l

inductive FKI where
  | op (k : OpK)
  | block | loop | ifThen | end_
  deriving DecidableEq

/-- One WasmVM instruction in the subset, flat. -/
def FKI.ofInstr : Instr → Option FKI
  | .i32Const v => some (.op (.i32const v.toNat))
  | .i64Const v => some (.op (.i64const v.toNat))
  | .localGet x => some (.op (.localGet x))
  | .localSet x => some (.op (.localSet x))
  | .localTee x => some (.op (.localTee x))
  | .num .i32_add => some (.op .i32add)
  | .num .i32_mul => some (.op .i32mul)
  | .num .i32_ge_u => some (.op .i32geu)
  | .num .i32_ne => some (.op .i32ne)
  | .num .i64_add => some (.op .i64add)
  | .num .i64_sub => some (.op .i64sub)
  | .num .i64_mul => some (.op .i64mul)
  | .num .i64_gt_s => some (.op .i64gts)
  | .num .i64_lt_s => some (.op .i64lts)
  | .num .i64_le_s => some (.op .i64les)
  | .num .i64_extend_i32_u => some (.op .i64extu)
  | .select none => some (.op .select)
  | .load .i32 ⟨2, 0, off⟩ => some (.op (.load32 off))
  | .store .i32 ⟨2, 0, off⟩ => some (.op (.store32 off))
  | .br l => some (.op (.br l))
  | .brIf l => some (.op (.brIf l))
  | .block .empty => some .block
  | .loop .empty => some .loop
  | .if_ .empty => some .ifThen
  | .end_ => some .end_
  | _ => none

/-- A function body (flat, ending in `end`) in the subset, flat. -/
noncomputable def FKI.ofBody (body : Array Instr) : Option (List FKI) := body.toList.mapM FKI.ofInstr

/-- Nest a flat sequence up to its `end`: the body and what follows. Fuel bounds the
nesting; proof-only (`noncomputable`: no compiled code). -/
noncomputable def FKI.nest : Nat → List FKI → Option (KIs × List FKI)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, i :: rest =>
    match i with
    | .end_ => some (.nil, rest)
    | .block => (FKI.nest fuel rest).bind fun (b, r) => (FKI.nest fuel r).map fun (is, r') => (.cons (.block b) is, r')
    | .loop => (FKI.nest fuel rest).bind fun (b, r) => (FKI.nest fuel r).map fun (is, r') => (.cons (.loop b) is, r')
    | .ifThen => (FKI.nest fuel rest).bind fun (b, r) => (FKI.nest fuel r).map fun (is, r') => (.cons (.ifThen b) is, r')
    | .op k => (FKI.nest fuel rest).map fun (is, r) => (.cons k.toKI is, r)

/-- A whole flat body as `KIs`. -/
noncomputable def FKI.nestBody (fl : List FKI) : Option KIs :=
  match FKI.nest (fl.length + 1) fl with
  | some (is, []) => some is
  | _ => none

mutual
/-- The meaning of a `KI` instruction as a spec instruction. -/
noncomputable def KI.toSpec : KI → Spec.instr
  | .i32const k => .CONST .I32 (.mk_num__0 .I32 (.mk_uN k))
  | .i64const k => .CONST .I64 (.mk_num__0 .I64 (.mk_uN k))
  | .localGet x => .LOCAL_GET (.mk_uN x)
  | .localSet x => .LOCAL_SET (.mk_uN x)
  | .localTee x => .LOCAL_TEE (.mk_uN x)
  | .i32add => .BINOP .I32 (.mk_binop__0 .I32 .ADD)
  | .i32mul => .BINOP .I32 (.mk_binop__0 .I32 .MUL)
  | .i32geu => .RELOP .I32 (.mk_relop__0 .I32 (.GE .U))
  | .i32ne => .RELOP .I32 (.mk_relop__0 .I32 .NE)
  | .i64add => .BINOP .I64 (.mk_binop__0 .I64 .ADD)
  | .i64sub => .BINOP .I64 (.mk_binop__0 .I64 .SUB)
  | .i64mul => .BINOP .I64 (.mk_binop__0 .I64 .MUL)
  | .i64gts => .RELOP .I64 (.mk_relop__0 .I64 (.GT .S))
  | .i64lts => .RELOP .I64 (.mk_relop__0 .I64 (.LT .S))
  | .i64les => .RELOP .I64 (.mk_relop__0 .I64 (.LE .S))
  | .i64extu => .CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U))
  | .select => .SELECT none
  | .load32 off => .LOAD .I32 none (.mk_uN 0) (ma4 off)
  | .store32 off => .STORE .I32 none (.mk_uN 0) (ma4 off)
  | .block b => .BLOCK (._RESULT none) (KI.toSpecs b)
  | .loop b => .LOOP (._RESULT none) (KI.toSpecs b)
  | .ifThen b => .IFELSE (._RESULT none) (KI.toSpecs b) []
  | .br l => .BR (.mk_uN l)
  | .brIf l => .BR_IF (.mk_uN l)
noncomputable def KI.toSpecs : KIs → List Spec.instr
  | .nil => []
  | .cons i is => KI.toSpec i :: KI.toSpecs is
end

end L4Factoidal.WasmVM.Proofs.SpecWP

namespace L4Factoidal.WasmVM.Proofs.SpecWP
open L4Factoidal.WasmVM Proofs.Refine

/-! ### Stack top first

`SemR z stk` is `Sem` with the stack written top first, so that each rule's stack is a
`::` pattern that `refine` matches without list arithmetic. -/

def SemR (z : Spec.state) (stk : List Spec.val) (is : List Spec.instr) (Q : Post) (B : BrPost) : Prop :=
  Sem z stk.reverse is Q B

/-- A list of `KI` as `KIs`. -/
noncomputable def ks : List KI → KIs
  | [] => .nil
  | i :: is => .cons i (ks is)

theorem toSpecs_ks (l : List KI) : KI.toSpecs (ks l) = l.map KI.toSpec := by
  induction l with
  | nil => rfl
  | cons i is ih => simp [ks, KI.toSpecs, ih]

theorem modify_const {α} (l : List α) (i : Nat) (a : α) : l.modify i (fun _ => a) = l.set i a := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => simp [List.modify_succ_cons, ih]

theorem with_local_mk (S : Spec.store) (L : List (Option Spec.val)) (M : Spec.moduleinst) (x : Nat) (v : Spec.val) :
    Spec.with_local (.mk_state S ⟨L, M⟩) (.mk_uN x) v = .mk_state S ⟨L.set x (some v), M⟩ := by
  simp only [Spec.with_local, Spec.sof, Spec.fof, Spec.fun_store, Spec.fun_frame, Spec.proj_uN_0, modify_const]

theorem fun_mem_mk (S : Spec.store) (L : List (Option Spec.val)) (M : Spec.moduleinst) :
    Spec.fun_mem (.mk_state S ⟨L, M⟩) (.mk_uN 0) = S.MEMS[M.MEMS[0]!]! := rfl

theorem with_mem_mk (S : Spec.store) (L : List (Option Spec.val)) (M : Spec.moduleinst) (ea : Nat) (bs : List Spec.byte) :
    Spec.with_mem (.mk_state S ⟨L, M⟩) (.mk_uN 0) ea 4 bs =
      .mk_state { S with MEMS := S.MEMS.modify M.MEMS[0]! (fun mi => { mi with BYTES := Spec.list_slice_update mi.BYTES ea 4 bs }) }
        ⟨L, M⟩ := rfl

theorem semR_nil {z stk Q B} (h : Q z stk.reverse) : SemR z stk [] Q B := sem_nil h

theorem semR_localGet {z stk x v rest Q} {B : BrPost} (hv : Spec.fun_local z (.mk_uN x) = some v)
    (h : SemR z (v :: stk) rest Q B) : SemR z stk (.LOCAL_GET (.mk_uN x) :: rest) Q B :=
  sem_localGet hv (by simpa [SemR] using h)

theorem semR_localSet {z stk x v rest Q} {B : BrPost}
    (h : SemR (Spec.with_local z (.mk_uN x) v) stk rest Q B) :
    SemR z (v :: stk) (.LOCAL_SET (.mk_uN x) :: rest) Q B := by
  simpa [SemR] using sem_localSet (pre := stk.reverse) h

theorem semR_localTee {z stk x v rest Q} {B : BrPost}
    (h : SemR (Spec.with_local z (.mk_uN x) v) (v :: stk) rest Q B) :
    SemR z (v :: stk) (.LOCAL_TEE (.mk_uN x) :: rest) Q B := by
  simpa [SemR] using sem_localTee (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i32const {z stk k rest Q} {B : BrPost} (hk : k < 2^32) (h : SemR z (i32v k :: stk) rest Q B) :
    SemR z stk (.CONST .I32 (.mk_num__0 .I32 (.mk_uN k)) :: rest) Q B :=
  sem_i32const (by simpa [SemR] using h) hk

theorem semR_i64const {z stk} {k : Nat} {rest Q} {B : BrPost} (hk : k < 2^64)
    (h : SemR z (i64v (k : Int) :: stk) rest Q B) :
    SemR z stk (.CONST .I64 (.mk_num__0 .I64 (.mk_uN k)) :: rest) Q B :=
  sem_i64const (by simpa [SemR] using h) hk

theorem semR_i64add {z stk x y rest Q} {B : BrPost} (h : SemR z (i64v (x + y) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.BINOP .I64 (.mk_binop__0 .I64 .ADD) :: rest) Q B := by
  simpa [SemR] using sem_i64add (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i64sub {z stk x y rest Q} {B : BrPost} (h : SemR z (i64v (x - y) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.BINOP .I64 (.mk_binop__0 .I64 .SUB) :: rest) Q B := by
  simpa [SemR] using sem_i64sub (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i64mul {z stk x y rest Q} {B : BrPost} (h : SemR z (i64v (x * y) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.BINOP .I64 (.mk_binop__0 .I64 .MUL) :: rest) Q B := by
  simpa [SemR] using sem_i64mul (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i32add {z stk a b rest Q} {B : BrPost} (h : SemR z (i32v (a + b) :: stk) rest Q B) :
    SemR z (i32v b :: i32v a :: stk) (.BINOP .I32 (.mk_binop__0 .I32 .ADD) :: rest) Q B := by
  simpa [SemR] using sem_i32add (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i32mul {z stk a b rest Q} {B : BrPost} (h : SemR z (i32v (a * b) :: stk) rest Q B) :
    SemR z (i32v b :: i32v a :: stk) (.BINOP .I32 (.mk_binop__0 .I32 .MUL) :: rest) Q B := by
  simpa [SemR] using sem_i32mul (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i64gts {z stk x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : SemR z (i32v (if x > y then 1 else 0) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.RELOP .I64 (.mk_relop__0 .I64 (.GT .S)) :: rest) Q B := by
  simpa [SemR] using sem_i64gts (pre := stk.reverse) hx1 hx2 hy1 hy2 (by simpa [SemR] using h)

theorem semR_i64lts {z stk x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : SemR z (i32v (if x < y then 1 else 0) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.RELOP .I64 (.mk_relop__0 .I64 (.LT .S)) :: rest) Q B := by
  simpa [SemR] using sem_i64lts (pre := stk.reverse) hx1 hx2 hy1 hy2 (by simpa [SemR] using h)

theorem semR_i64les {z stk x y rest Q} {B : BrPost}
    (hx1 : -2^63 ≤ x) (hx2 : x < 2^63) (hy1 : -2^63 ≤ y) (hy2 : y < 2^63)
    (h : SemR z (i32v (if x ≤ y then 1 else 0) :: stk) rest Q B) :
    SemR z (i64v y :: i64v x :: stk) (.RELOP .I64 (.mk_relop__0 .I64 (.LE .S)) :: rest) Q B := by
  simpa [SemR] using sem_i64les (pre := stk.reverse) hx1 hx2 hy1 hy2 (by simpa [SemR] using h)

theorem semR_i32geu {z stk a b rest Q} {B : BrPost} (ha : a < 2^32) (hb : b < 2^32)
    (h : SemR z (i32v (if a ≥ b then 1 else 0) :: stk) rest Q B) :
    SemR z (i32v b :: i32v a :: stk) (.RELOP .I32 (.mk_relop__0 .I32 (.GE .U)) :: rest) Q B := by
  simpa [SemR] using sem_i32geu (pre := stk.reverse) ha hb (by simpa [SemR] using h)

theorem semR_i32ne {z stk a b rest Q} {B : BrPost}
    (h : SemR z (i32v (if a % 2^32 ≠ b % 2^32 then 1 else 0) :: stk) rest Q B) :
    SemR z (i32v b :: i32v a :: stk) (.RELOP .I32 (.mk_relop__0 .I32 .NE) :: rest) Q B := by
  simpa [SemR] using sem_i32ne (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_i64extu {z stk} {k : Nat} {rest Q} {B : BrPost} (hk : k < 2^32)
    (h : SemR z (i64v (k : Int) :: stk) rest Q B) :
    SemR z (i32v k :: stk) (.CVTOP .I64 .I32 (.mk_cvtop___0 .I32 .I64 (.EXTEND .U)) :: rest) Q B := by
  simpa [SemR] using sem_i64extu (pre := stk.reverse) hk (by simpa [SemR] using h)

theorem semR_select {z stk v1 v2 c rest Q} {B : BrPost}
    (h : SemR z ((if c % 2^32 = 0 then v2 else v1) :: stk) rest Q B) :
    SemR z (i32v c :: v2 :: v1 :: stk) (.SELECT none :: rest) Q B := by
  simpa [SemR] using sem_select (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_load32 {z stk a off k rest Q} {B : BrPost} (hk : k < 2^32)
    (hbytes : List.take 4 (List.drop (a % 2^32 + off) (Spec.fun_mem z (.mk_uN 0)).BYTES) =
      Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN k)))
    (h : SemR z (i32v k :: stk) rest Q B) :
    SemR z (i32v a :: stk) (.LOAD .I32 none (.mk_uN 0) (ma4 off) :: rest) Q B := by
  simpa [SemR] using sem_load32 (pre := stk.reverse) hk hbytes (by simpa [SemR] using h)

theorem semR_store32 {z stk a off k rest Q} {B : BrPost}
    (h : SemR (Spec.with_mem z (.mk_uN 0) (a % 2^32 + off) 4 (Spec.nbytes_ .I32 (.mk_num__0 .I32 (.mk_uN (k % 2^32)))))
      stk rest Q B) :
    SemR z (i32v k :: i32v a :: stk) (.STORE .I32 none (.mk_uN 0) (ma4 off) :: rest) Q B := by
  simpa [SemR] using sem_store32 (pre := stk.reverse) (by simpa [SemR] using h)

theorem semR_br {z stk k rest Q} {B : BrPost} (h : B k z stk.reverse) :
    SemR z stk (.BR (.mk_uN k) :: rest) Q B := sem_br h

theorem semR_brIf {z stk c k rest Q} {B : BrPost}
    (h : if c % 2^32 = 0 then SemR z stk rest Q B else B k z stk.reverse) :
    SemR z (i32v c :: stk) (.BR_IF (.mk_uN k) :: rest) Q B := by
  have := sem_brIf (z := z) (pre := stk.reverse) (c := c) (k := k) (rest := rest) (Q := Q) (B := B)
    (by by_cases hc : c % 2^32 = 0 <;> simp_all [SemR])
  simpa [SemR, i32v] using this

/-- `block` on an empty stack. -/
theorem semR_block {z body rest Q} {B : BrPost}
    (hb : SemR z [] body (fun z' vs' => Sem z' vs' rest Q B)
      (labelBr [] (fun z' => Sem z' [] rest Q B) B)) :
    SemR z [] (.BLOCK (._RESULT none) body :: rest) Q B :=
  sem_block (pre := []) (by simpa [SemR] using hb)

/-- `loop` on an empty stack. -/
theorem semR_loop {z body rest Q} {B : BrPost}
    (hb : SemR z [] body (fun z' vs' => Sem z' vs' rest Q B)
      (labelBr [] (fun z' => Sem z' [] (.LOOP (._RESULT none) body :: rest) Q B) B)) :
    SemR z [] (.LOOP (._RESULT none) body :: rest) Q B :=
  sem_loop (pre := []) (by simpa [SemR] using hb)

/-- `if` (no `else`) on a stack holding only the condition. -/
theorem semR_if {z c body rest Q} {B : BrPost}
    (h : if c % 2^32 = 0 then SemR z [] rest Q B else
      SemR z [] body (fun z' vs' => Sem z' vs' rest Q B)
        (labelBr [] (fun z' => Sem z' [] rest Q B) B)) :
    SemR z [i32v c] (.IFELSE (._RESULT none) body [] :: rest) Q B := by
  have := sem_if (z := z) (pre := []) (c := c) (body := body) (rest := rest) (Q := Q) (B := B)
    (by by_cases hc : c % 2^32 = 0 <;> simp_all [SemR])
  simpa [SemR, i32v] using this

theorem semR_mono {z stk is} {Q Q' : Post} {B B' : BrPost} (h : SemR z stk is Q B)
    (hq : ∀ z vs, Q z vs → Q' z vs) (hb : ∀ k z vs, B k z vs → B' k z vs) : SemR z stk is Q' B' :=
  sem_mono h hq hb

/-! ### Normal forms for the values the rules produce -/

theorem ite01_mod (p : Prop) [Decidable p] : ((if p then 1 else 0) % 2^32 = 0) ↔ ¬p := by
  by_cases h : p <;> simp [h]

theorem ite_i64v (p : Prop) [Decidable p] (a b : Int) :
    (if p then i64v a else i64v b) = i64v (if p then a else b) := by split <;> rfl

theorem ite_i32v (p : Prop) [Decidable p] (a b : Nat) :
    (if p then i32v a else i32v b) = i32v (if p then a else b) := by split <;> rfl

theorem ite_lt_min (a b : Int) : (if a < b then a else b) = min a b := by
  by_cases h : a < b
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem ite_gt_max (a b : Int) : (if a > b then a else b) = max a b := by
  by_cases h : a > b
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-! ### Reflexive `==` on the spec records a call compares

`call_ref_func` compares the function instance and the new frame with the generated
`==`; these instances say each is reflexive. -/

theorem list_beq_self {α} [BEq α] [ReflBEq α] (l : List α) : l.beq l = true := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.beq, ih]
instance : ReflBEq Spec.uN := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqUN.beq]⟩
instance : ReflBEq Spec.char := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqChar.beq]⟩
instance : ReflBEq Spec.name := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqName.beq, list_beq_self]⟩
instance : ReflBEq Spec.externaddr := ⟨by intro a; cases a <;> simp [BEq.beq, Spec.instBEqExternaddr.beq]⟩
instance : ReflBEq Spec.exportinst := ⟨by
  intro a; cases a with
  | MKexportinst nm ad =>
    simp only [BEq.beq, Spec.instBEqExportinst.beq]
    have h1 : (nm == nm) = true := BEq.rfl
    have h2 : (ad == ad) = true := BEq.rfl
    simp only [BEq.beq] at h1 h2; simp [h1, h2]⟩
instance : ReflBEq Spec.rectype := ⟨by intro a; simp [BEq.beq]⟩
instance : ReflBEq Spec.deftype := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqDeftype.beq]⟩
instance : ReflBEq Spec.moduleinst := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqModuleinst.beq, list_beq_self]⟩
instance : ReflBEq Spec.val := ⟨Proofs.Proposals.val_beq_self _⟩
instance : ReflBEq Spec.frame := ⟨by
  intro a; cases a with
  | MKframe L Mo =>
    simp only [BEq.beq, Spec.instBEqFrame.beq]
    have h2 : (Mo == Mo) = true := BEq.rfl
    simp only [BEq.beq] at h2; simp [h2, list_beq_self]⟩
instance : ReflBEq Spec.valtype := ⟨by intro a; simp [BEq.beq]⟩
instance : ReflBEq Spec.instr := ⟨by intro a; simp [BEq.beq]⟩
instance : ReflBEq Spec.local := ⟨by intro a; cases a; simp [BEq.beq, Spec.instBEqLocal.beq]⟩
instance : ReflBEq Spec.funccode := ⟨by
  intro a; cases a with
  | FUNC x ls e =>
    simp only [BEq.beq, Spec.instBEqFunccode.beq]
    have h1 : (x == x) = true := BEq.rfl
    simp only [BEq.beq] at h1; simp [h1, list_beq_self]
  | _HOSTFUNC t => simp [BEq.beq, Spec.instBEqFunccode.beq]⟩
instance : ReflBEq Spec.funcinst := ⟨by
  intro a; cases a with
  | MKfuncinst T Mo C =>
    simp only [BEq.beq, Spec.instBEqFuncinst.beq]
    have h1 : (T == T) = true := BEq.rfl
    have h2 : (Mo == Mo) = true := BEq.rfl
    have h3 : (C == C) = true := BEq.rfl
    simp only [BEq.beq] at h1 h2 h3; simp [h1, h2, h3]⟩

end L4Factoidal.WasmVM.Proofs.SpecWP
