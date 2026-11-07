/-
L4Factoidal.WasmVM.Proofs.Fuse: fused ops are their parts in sequence
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "Fused ops").

- `run_simple`: `run` executes a straight-line op (`local.get/set/tee`, `const`,
  `drop`, a numeric op that cannot trap) as `Simple.exec`, then goes to `pc + 1`.
- `run_parts` (THE GENERAL LEMMA): `k` straight-line ops in the code from `pc`, run one
  at a time, are `Simple.execAll` of them, then `run` at `pc + k` with `k` less fuel.
- `run_fused`, `run_fusedJump`: the small proof for each fusion, by cases on the
  fused op: `run` executes it as `Simple.execAll` of its parts (`fusedSimple`), then
  the jump if it has one.
- `fused_agrees`: from `pc`, the code with the fused op and any code with its parts
  there reach the same registers after the parts, with the same fuel left.
- `fuseAt_sound`, `fuse_sound`, `fuse_agrees`: the pass `fuse` keeps the length, puts
  only well-formed fused ops, each where the original code holds its parts; so
  `fused_agrees` applies to every fused op in compiled code.

Not proved yet: that whole runs of `fuse c` and `c` agree (an induction on fuel over
`run`, which also needs every function of the store to be fused the same way).
-/
import L4Factoidal.WasmVM.Exec.Run

namespace L4Factoidal.WasmVM.Proofs.Fuse
open L4Factoidal.WasmVM Run

/-- The straight-line op that `o` is, when it is one. -/
def simple? : Op → Option Simple
  | .localGet x => some (.localGet x.toUSize)
  | .localSet x => some (.localSet x.toUSize)
  | .localTee x => some (.localTee x.toUSize)
  | .const v => some (.const v)
  | .drop => some .drop
  | .num op => if op.pureBin then some (.bin op) else if op.pureUn then some (.un op) else none
  | _ => none

variable {M : Type} [LinearMemory M]

theorem run_simple (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (o : Op) (s : Simple)
    (hpc : pc < code.usize) (hc : code[pc.toNat]'(pc_ok hpc) = o) (hs : simple? o = some s) :
    run lim st stack sp fp pc code inst frames (n + 1) =
      run lim st (s.exec fp ⟨stack, sp⟩).stack (s.exec fp ⟨stack, sp⟩).sp fp (pc + 1) code inst frames n := by
  conv => lhs; unfold run
  rw [dif_pos hpc]
  simp only [Array.uget, hc]
  cases o <;> simp only [simple?, Option.some.injEq, reduceCtorEq] at hs
  case num op =>
    unfold NumOp.pureBin NumOp.pureUn at hs
    cases hb : op.isBinary <;> cases ht : op.mayTrap <;> simp [hb, ht] at hs <;> subst hs <;>
      simp only [hb, ht, Bool.false_eq_true, ↓reduceIte] <;> rfl
  all_goals (subst hs; rfl)


theorem run_condJump (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (t : Nat) (z : Bool)
    (hpc : pc < code.usize) (hc : code[pc.toNat]'(pc_ok hpc) = Op.condJump t z) :
    run lim st stack sp fp pc code inst frames (n + 1) =
      run lim st stack (sp - 1) fp (jumpTo (rd stack (sp - 1)) z t.toUSize (pc + 1)) code inst frames n := by
  conv => lhs; unfold run
  rw [dif_pos hpc]
  simp only [Array.uget, hc]
  cases z <;> rfl

/-- The straight-line parts of a fused op, as `run` executes them. -/
def fusedSimple : Op → List Simple
  | .llBin x y op => [.localGet x.toUSize, .localGet y.toUSize, .bin op]
  | .lcBin x c op => [.localGet x.toUSize, .const c, .bin op]
  | .cBin c op => [.const c, .bin op]
  | .lUn x op => [.localGet x.toUSize, .un op]
  | .binSet op z => [.bin op, .localSet z.toUSize]
  | .lcBinSet x c op z => [.localGet x.toUSize, .const c, .bin op, .localSet z.toUSize]
  | .llBinJump x y op _ _ => [.localGet x.toUSize, .localGet y.toUSize, .bin op]
  | .lcBinJump x c op _ _ => [.localGet x.toUSize, .const c, .bin op]
  | .binJump op _ _ => [.bin op]
  | _ => []

/-- The conditional jump that ends a fused op, if any. -/
def fusedJump? : Op → Option (Nat × Bool)
  | .llBinJump _ _ _ t z | .lcBinJump _ _ _ t z | .binJump _ t z => some (t, z)
  | _ => none

theorem run_fused (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (f : Op)
    (hpc : pc < code.usize) (hc : code[pc.toNat]'(pc_ok hpc) = f)
    (hf : fusedSimple f ≠ []) (hj : fusedJump? f = none) :
    run lim st stack sp fp pc code inst frames (n + (fusedSimple f).length) =
      run lim st (Simple.execAll fp (fusedSimple f) ⟨stack, sp⟩).stack
        (Simple.execAll fp (fusedSimple f) ⟨stack, sp⟩).sp fp
        (pc + (fusedSimple f).length.toUSize) code inst frames n := by
  cases f <;> simp only [fusedSimple, ne_eq, not_true_eq_false, reduceCtorEq, fusedJump?] at hf hj <;>
  · simp only [fusedSimple, List.length_cons, List.length_nil]
    conv => lhs; unfold run
    rw [dif_pos hpc]
    simp only [Array.uget, hc]
    rfl


theorem run_fusedJump (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (f : Op) (t : Nat) (z : Bool)
    (hpc : pc < code.usize) (hc : code[pc.toNat]'(pc_ok hpc) = f) (hj : fusedJump? f = some (t, z)) :
    run lim st stack sp fp pc code inst frames (n + 1 + (fusedSimple f).length) =
      let x := Simple.execAll fp (fusedSimple f) ⟨stack, sp⟩
      run lim st x.stack (x.sp - 1) fp
        (jumpTo (rd x.stack (x.sp - 1)) z t.toUSize (pc + ((fusedSimple f).length + 1).toUSize))
        code inst frames n := by
  cases f <;> simp only [fusedJump?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hj <;>
  · obtain ⟨rfl, rfl⟩ := hj
    simp only [fusedSimple, List.length_cons, List.length_nil]
    conv => lhs; unfold run
    rw [dif_pos hpc]
    simp only [Array.uget, hc]
    rfl

/-- `ops` sit in `code` from `pc` on, each at a pc in range. -/
def At (code : Array Op) : USize → List Op → Prop
  | _, [] => True
  | pc, o :: os => (∃ h : pc < code.usize, code[pc.toNat]'(pc_ok h) = o) ∧ At code (pc + 1) os

theorem usize_succ (pc : USize) (k : Nat) : pc + 1 + k.toUSize = pc + (k + 1).toUSize := by
  rw [Nat.toUSize_eq, Nat.toUSize_eq, USize.ofNat_add, USize.add_assoc, USize.add_comm 1]; rfl

theorem usize_succ' (pc : USize) (k : Nat) : pc + k.toUSize + 1 = pc + (k + 1).toUSize := by
  rw [Nat.toUSize_eq, Nat.toUSize_eq, USize.ofNat_add, USize.add_assoc]; rfl

theorem usize_zero (pc : USize) : pc + (0 : Nat).toUSize = pc := USize.add_zero pc

theorem At_append (code : Array Op) :
    ∀ (ops₁ ops₂ : List Op) (pc : USize), At code pc (ops₁ ++ ops₂) →
      At code pc ops₁ ∧ At code (pc + ops₁.length.toUSize) ops₂
  | [], _, pc, h => ⟨trivial, by rw [List.length_nil, usize_zero]; exact h⟩
  | o :: os, ops₂, pc, ⟨h1, h2⟩ => by
    obtain ⟨a, b⟩ := At_append code os ops₂ (pc + 1) h2
    refine ⟨⟨h1, a⟩, ?_⟩
    rw [List.length_cons, ← usize_succ]; exact b

/-- THE GENERAL LEMMA. Running straight-line ops one at a time, from `pc`, is
`Simple.execAll` of them, then the loop at `pc + k` with `k` less fuel. -/
theorem run_parts (lim : RunLimits) (st : StoreOf M) (inst : ModuleInst) (frames : Array Frame)
    (code : Array Op) (fp : USize) :
    ∀ (ss : List Simple) (ops : List Op) (stack : Slots) (sp pc : USize) (n : Nat),
      At code pc ops → ops.map simple? = ss.map some →
      run lim st stack sp fp pc code inst frames (n + ss.length) =
        run lim st (Simple.execAll fp ss ⟨stack, sp⟩).stack (Simple.execAll fp ss ⟨stack, sp⟩).sp fp
          (pc + ss.length.toUSize) code inst frames n
  | [], _, stack, sp, pc, n, _, _ => by simp only [List.length_nil, Nat.add_zero, usize_zero]; rfl
  | s :: ss, [], _, _, _, _, _, h => by simp at h
  | s :: ss, o :: os, stack, sp, pc, n, ⟨⟨hpc, hc⟩, hat⟩, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.length_cons, ← Nat.add_assoc, run_simple lim st stack sp fp pc code inst frames _ o s hpc hc h1,
      run_parts lim st inst frames code fp ss os _ _ (pc + 1) n hat h2, usize_succ]
    rfl

/-- The fused ops that `run` knows, with a numeric op that cannot trap: then their
parts are straight-line ops (and the conditional jump). -/
def WF (f : Op) : Prop :=
  (f.parts.take (fusedSimple f).length).map simple? = (fusedSimple f).map some ∧
  (match fusedJump? f with
   | none => f.parts.length = (fusedSimple f).length
   | some (t, z) => f.parts = f.parts.take (fusedSimple f).length ++ [Op.condJump t z])

/-- The state after a fused op's parts: slots, `sp` and `pc`. -/
def after (fp pc : USize) (f : Op) (x : SP) : Slots × USize × USize :=
  let y := Simple.execAll fp (fusedSimple f) x
  let k := (fusedSimple f).length
  match fusedJump? f with
  | none => (y.stack, y.sp, pc + k.toUSize)
  | some (t, z) => (y.stack, y.sp - 1, jumpTo (rd y.stack (y.sp - 1)) z t.toUSize (pc + (k + 1).toUSize))

/-- A fused op is its parts in sequence: from `pc`, the code with the fused op and
any code that holds its parts there both reach the same registers, with the same
fuel left. -/
theorem fused_agrees (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (code code₀ : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (f : Op)
    (hf : fusedSimple f ≠ []) (hw : WF f)
    (hpc : pc < code.usize) (hc : code[pc.toNat]'(pc_ok hpc) = f) (hat : At code₀ pc f.parts) :
    let r := after fp pc f ⟨stack, sp⟩
    run lim st stack sp fp pc code inst frames (n + f.parts.length) =
      run lim st r.1 r.2.1 fp r.2.2 code inst frames n ∧
    run lim st stack sp fp pc code₀ inst frames (n + f.parts.length) =
      run lim st r.1 r.2.1 fp r.2.2 code₀ inst frames n := by
  obtain ⟨hs, hj⟩ := hw
  intro r
  cases hjf : fusedJump? f with
  | none =>
    rw [hjf] at hj
    simp only at hj
    have hat' : At code₀ pc (f.parts.take (fusedSimple f).length) := by
      rw [List.take_of_length_le (by omega)]; exact hat
    simp only [r, after, hjf, hj]
    exact ⟨run_fused lim st stack sp fp pc code inst frames n f hpc hc hf hjf,
      run_parts lim st inst frames code₀ fp _ _ stack sp pc n hat' hs⟩
  | some tz =>
    obtain ⟨t, z⟩ := tz
    rw [hjf] at hj
    simp only at hj
    have hlen : f.parts.length = (fusedSimple f).length + 1 := by
      rw [hj]; simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
      have : (fusedSimple f).length ≤ f.parts.length := by
        have := congrArg List.length hs; simp at this; omega
      omega
    simp only [r, after, hjf, hlen]
    constructor
    · rw [show n + ((fusedSimple f).length + 1) = n + 1 + (fusedSimple f).length by omega]
      exact run_fusedJump lim st stack sp fp pc code inst frames n f t z hpc hc hjf
    · have hat2 := hat
      rw [hj] at hat2
      obtain ⟨hat1, hat3⟩ := At_append code₀ _ _ pc hat2
      have hk : (f.parts.take (fusedSimple f).length).length = (fusedSimple f).length := by
        have := congrArg List.length hs; simpa using this
      rw [hk] at hat3
      obtain ⟨⟨hpc', hc'⟩, -⟩ := hat3
      rw [show n + ((fusedSimple f).length + 1) = n + 1 + (fusedSimple f).length by omega,
        run_parts lim st inst frames code₀ fp _ _ stack sp pc (n + 1) hat1 hs,
        run_condJump lim st _ _ fp _ code₀ inst frames n t z hpc' hc', usize_succ']


/-! ### The fusion pass -/

theorem jumpAt_some {o : Option Op} {t : Nat} {z : Bool} (h : jumpAt o = some (t, z)) :
    o = some (Op.condJump t z) := by
  unfold jumpAt at h
  split at h <;> simp_all [Op.condJump]

/-- Each op `fuseAt` makes is well formed, is a fused op, and has its parts in the
code from `i` on. -/
theorem fuseAt_sound (c : Array Op) (i : Nat) (f : Op) (h : fuseAt c i = some f) :
    (∀ j (hj : j < f.parts.length), c[i + j]? = some (f.parts[j])) ∧ WF f ∧ fusedSimple f ≠ [] := by
  unfold fuseAt at h
  split at h
  all_goals first
    | (simp at h; done)
    | skip
  all_goals (split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h)
  all_goals (try (have hj := jumpAt_some ‹jumpAt _ = some _›))
  all_goals refine ⟨?_, ?_, by simp [fusedSimple]⟩
  all_goals first
    | (intro j hj
       simp only [Op.parts, List.length_cons, List.length_nil] at hj
       rcases j with _ | _ | _ | _ | j <;> simp_all [Op.parts] <;> omega)
    | (simp_all [WF, Op.parts, fusedSimple, fusedJump?, simple?, NumOp.pureBin, NumOp.pureUn, Op.condJump]; done)


theorem fuse_go_spec (c : Array Op) (i : Nat) (out : Array Op) (hs : out.size = c.size)
    (hinv : ∀ k, k < c.size → out[k]? = c[k]? ∨ fuseAt c k = out[k]?) :
    (fuse.go c i out).size = c.size ∧
      ∀ k, k < c.size → (fuse.go c i out)[k]? = c[k]? ∨ fuseAt c k = (fuse.go c i out)[k]? := by
  unfold fuse.go
  split
  · split
    · next f hf =>
      apply fuse_go_spec c (i + max 1 f.parts.length) (out.set! i f) (by simp [hs])
      intro k hk
      by_cases hik : i = k
      · subst hik; right; simp [Array.set!, hs, hk, hf]
      · have := hinv k hk
        simp only [Array.set!, Array.getElem?_setIfInBounds, hik, if_false]
        exact this
    · exact fuse_go_spec c (i + 1) out hs hinv
  · exact ⟨hs, hinv⟩
termination_by c.size - i

/-- `fuse` keeps the length, and each op of `fuse c` is the op of `c` at that pc or a
fused op that `fuseAt` made there (so `fuseAt_sound` applies to it). -/
theorem fuse_sound (c : Array Op) :
    (fuse c).size = c.size ∧ ∀ k, k < c.size → (fuse c)[k]? = c[k]? ∨ fuseAt c k = (fuse c)[k]? :=
  fuse_go_spec c 0 c rfl (fun _ _ => Or.inl rfl)


theorem At_of_get (c : Array Op) (hsz : c.size < USize.size) :
    ∀ (ops : List Op) (pc : USize),
      (∀ j (hj : j < ops.length), c[pc.toNat + j]? = some ops[j]) → At c pc ops
  | [], _, _ => trivial
  | o :: os, pc, h => by
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hlt : pc.toNat < c.size := by
      rcases Nat.lt_or_ge pc.toNat c.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at h0
    have hu : c.usize.toNat = c.size := by
      simp only [Array.usize, Nat.toUSize_eq, USize.toNat_ofNat']; exact Nat.mod_eq_of_lt hsz
    have hpc : pc < c.usize := by rw [USize.lt_iff_toNat_lt, hu]; exact hlt
    refine ⟨⟨hpc, ?_⟩, At_of_get c hsz os (pc + 1) ?_⟩
    · rw [Array.getElem?_eq_getElem hlt] at h0; simpa using h0
    · intro j hj
      have hj1 := h (j + 1) (by simp; omega)
      have hlt2 : pc.toNat + (j + 1) < c.size := by
        rcases Nat.lt_or_ge (pc.toNat + (j + 1)) c.size with h' | h'
        · exact h'
        · simp [Array.getElem?_eq_none h'] at hj1
      have : (pc + 1).toNat = pc.toNat + 1 := by
        rw [USize.toNat_add]; have : (1 : USize).toNat = 1 := by simp
        rw [this]; exact Nat.mod_eq_of_lt (by have hs : USize.size = 2 ^ System.Platform.numBits := rfl; omega)
      rw [this, Nat.add_assoc, Nat.add_comm 1 j]; simpa using hj1

/-- The fusion pass and the loop together: at a pc where `fuse` put a fused op, `run`
on the fused code and `run` on the original code reach the same registers after the
op's parts, with the same fuel left. -/
theorem fuse_agrees (lim : RunLimits) (st : StoreOf M) (stack : Slots) (sp fp pc : USize)
    (c : Array Op) (inst : ModuleInst) (frames : Array Frame) (n : Nat) (f : Op)
    (hsz : c.size < USize.size) (hpc : pc < (fuse c).usize)
    (hc : (fuse c)[pc.toNat]'(pc_ok hpc) = f) (hfa : fuseAt c pc.toNat = some f) :
    let r := after fp pc f ⟨stack, sp⟩
    run lim st stack sp fp pc (fuse c) inst frames (n + f.parts.length) =
      run lim st r.1 r.2.1 fp r.2.2 (fuse c) inst frames n ∧
    run lim st stack sp fp pc c inst frames (n + f.parts.length) =
      run lim st r.1 r.2.1 fp r.2.2 c inst frames n := by
  obtain ⟨hparts, hw, hf⟩ := fuseAt_sound c pc.toNat f hfa
  exact fused_agrees lim st stack sp fp pc (fuse c) c inst frames n f hf hw hpc hc
    (At_of_get c hsz f.parts pc hparts)

end L4Factoidal.WasmVM.Proofs.Fuse
