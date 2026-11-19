/-
L4Factoidal.GpuKernel.Race — when the order in which a GPU runs the invocations of a
dispatch can not change the result (core issue 398, GPU compute managed by Lean).

The model. One dispatch has `n` invocations. Each invocation reads only buffers that no
invocation of the dispatch writes (the kernel IR has no way to read its output, see
`Expr.lean`), and its effect is a list of writes `(index, value)` into one output memory.
A GPU may interleave the individual writes of different invocations. Without a
race-freedom condition, that need not equal either whole-invocation order. The theorem
below permutes completed invocations; it does not itself quantify over individual-write
shuffles. The companion TraceInterleavingTheorems covers individual-event permutations
and their prefixes under the stronger unique-address profile used by stable packing.

- `runOrder_perm`: if the writes of two different invocations never name the same index
  (`RaceFree`), every order of the invocations (any permutation of `0 .. n-1`) gives the
  memory of the sequential order `0, 1, .., n-1`. This is the data-race-freedom theorem: a
  kernel whose footprints are disjoint is deterministic and equal to the sequential loop.
- `runAdd_perm`: atomics, only for a commutative operation. If every write is an atomic add
  (`index += delta`), every order gives the same memory, with no disjointness needed.

Barriers: a dispatch boundary is a full barrier (WebGPU orders dispatches of one pass), so a
pipeline of dispatches is the composition of their memories. Workgroup barriers and
workgroup memory are not in this model yet; a kernel that needs them is not in the IR.
-/
namespace L4Factoidal.GpuKernel

/-- An output memory: a value at every index. -/
abbrev Mem (α : Type) := Nat → α

/-- One write. -/
def Mem.write {α : Type} (m : Mem α) (i : Nat) (v : α) : Mem α := fun j => if j = i then v else m j

/-- Apply writes in list order (the last write of an index wins). -/
def applyWrites {α : Type} (m : Mem α) (ws : List (Nat × α)) : Mem α :=
  ws.foldl (fun m w => m.write w.1 w.2) m

/-- The value the last write of index `j` in `ws` leaves, if any. -/
def lastWrite {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (i, v) :: ws, j =>
    match lastWrite ws j with
    | some u => some u
    | none => if j = i then some v else none

/-- The indices a list of writes names. -/
def keys {α : Type} (ws : List (Nat × α)) : List Nat := ws.map Prod.fst

/-- Two lists of writes name no index in common. -/
def Disjoint {α : Type} (a b : List (Nat × α)) : Prop := ∀ i, i ∈ keys a → i ∉ keys b

theorem applyWrites_apply {α : Type} (ws : List (Nat × α)) :
    ∀ (m : Mem α) (j : Nat), applyWrites m ws j = (lastWrite ws j).getD (m j) := by
  induction ws with
  | nil => intro m j; rfl
  | cons w ws ih =>
    intro m j
    obtain ⟨i, v⟩ := w
    show applyWrites (m.write i v) ws j = _
    rw [ih]
    simp only [lastWrite, Mem.write]
    cases lastWrite ws j with
    | some u => rfl
    | none => by_cases h : j = i <;> simp [h]

theorem lastWrite_none {α : Type} (ws : List (Nat × α)) (j : Nat) (h : j ∉ keys ws) :
    lastWrite ws j = none := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨i, v⟩ := w
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    have h2 : j ∉ keys ws := h.2
    simp only [lastWrite, ih h2]
    simp [h.1]

/-- Two lists of writes with no index in common commute. -/
theorem applyWrites_comm {α : Type} (m : Mem α) (a b : List (Nat × α)) (h : Disjoint a b) :
    applyWrites (applyWrites m a) b = applyWrites (applyWrites m b) a := by
  funext j
  simp only [applyWrites_apply]
  by_cases ha : j ∈ keys a
  · rw [lastWrite_none b j (h j ha)]
    simp
  · rw [lastWrite_none a j ha]
    simp

/-! ## Invocations of one dispatch -/

/-- A dispatch: `n` invocations, and the writes of each. The writes may depend on read-only
input (captured in the function); they never depend on the output memory. -/
structure Dispatch (α : Type) where
  n : Nat
  writes : Nat → List (Nat × α)

/-- Run the invocations in the order `order`. -/
def Dispatch.runOrder {α : Type} (d : Dispatch α) (m : Mem α) (order : List Nat) : Mem α :=
  order.foldl (fun m t => applyWrites m (d.writes t)) m

/-- The sequential reference: invocation 0, then 1, ..., then `n - 1`. -/
def Dispatch.runSeq {α : Type} (d : Dispatch α) (m : Mem α) : Mem α :=
  d.runOrder m (List.range d.n)

/-- Different invocations write different indices. -/
def Dispatch.RaceFree {α : Type} (d : Dispatch α) : Prop :=
  ∀ t u, t < d.n → u < d.n → t ≠ u → Disjoint (d.writes t) (d.writes u)

theorem Dispatch.runOrder_perm_aux {α : Type} (d : Dispatch α) (h : d.RaceFree) :
    ∀ {l₁ l₂ : List Nat}, l₁.Perm l₂ → (∀ x ∈ l₁, x < d.n) → l₁.Nodup →
      ∀ m, d.runOrder m l₁ = d.runOrder m l₂ := by
  intro l₁ l₂ hp
  induction hp with
  | nil => intro _ _ m; rfl
  | cons x _ ih =>
    intro hb hn m
    simp only [Dispatch.runOrder, List.foldl_cons]
    exact ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.mp hn).2 _
  | swap x y l =>
    intro hb hn m
    simp only [Dispatch.runOrder, List.foldl_cons]
    have hyx : y ≠ x := by
      have := (List.nodup_cons.mp hn).1
      intro e; exact this (by simp [e])
    have hy : y < d.n := hb y (by simp)
    have hx : x < d.n := hb x (by simp)
    rw [applyWrites_comm _ _ _ (h y x hy hx hyx)]
  | trans h₁ _ ih₁ ih₂ =>
    intro hb hn m
    rw [ih₁ hb hn m]
    exact ih₂ (fun y hy => hb y (h₁.mem_iff.mpr hy)) (h₁.nodup_iff.mp hn) m

/-- Data-race freedom: a race-free dispatch gives the sequential result in every order. -/
theorem Dispatch.runOrder_perm {α : Type} (d : Dispatch α) (h : d.RaceFree)
    (order : List Nat) (hp : order.Perm (List.range d.n)) (m : Mem α) :
    d.runOrder m order = d.runSeq m := by
  unfold Dispatch.runSeq
  exact Dispatch.runOrder_perm_aux d h hp.symm.symm
    (fun x hx => List.mem_range.mp (hp.mem_iff.mp hx)) (hp.nodup_iff.mpr (List.nodup_range)) m

/-! ## Atomics, only for a commutative operation -/

/-- Atomic adds in list order. -/
def applyAdds (m : Mem Nat) (ws : List (Nat × Nat)) : Mem Nat :=
  ws.foldl (fun m w => m.write w.1 (m w.1 + w.2)) m

theorem applyAdds_apply (ws : List (Nat × Nat)) :
    ∀ (m : Mem Nat) (j : Nat), applyAdds m ws j = m j + ((ws.filter (·.1 = j)).map (·.2)).sum := by
  induction ws with
  | nil => intro m j; simp [applyAdds]
  | cons w ws ih =>
    intro m j
    obtain ⟨i, v⟩ := w
    show applyAdds (m.write i (m i + v)) ws j = _
    rw [ih]
    by_cases hj : i = j
    · subst hj; simp [Mem.write, Nat.add_assoc]
    · have : ¬ j = i := fun e => hj e.symm
      simp [Mem.write, hj, this]

theorem applyAdds_comm (m : Mem Nat) (a b : List (Nat × Nat)) :
    applyAdds (applyAdds m a) b = applyAdds (applyAdds m b) a := by
  funext j
  simp only [applyAdds_apply]
  omega

/-- A dispatch whose writes are all atomic adds. -/
def Dispatch.runAddOrder (d : Dispatch Nat) (m : Mem Nat) (order : List Nat) : Mem Nat :=
  order.foldl (fun m t => applyAdds m (d.writes t)) m

/-- Atomic adds: every order of the invocations gives the same memory, races or not. -/
theorem Dispatch.runAdd_perm (d : Dispatch Nat) {l₁ l₂ : List Nat} (hp : l₁.Perm l₂) :
    ∀ m, d.runAddOrder m l₁ = d.runAddOrder m l₂ := by
  induction hp with
  | nil => intro m; rfl
  | cons x _ ih => intro m; simp only [Dispatch.runAddOrder, List.foldl_cons]; exact ih _
  | swap x y l => intro m; simp only [Dispatch.runAddOrder, List.foldl_cons]; rw [applyAdds_comm]
  | trans _ _ ih₁ ih₂ => intro m; rw [ih₁, ih₂]

end L4Factoidal.GpuKernel
