/-
L4Factoidal.Storage.Sbm11.ParallelScan — the split of a scan into block
ranges (stage 1 of issue https://github.com/danbri/factoidal/issues/799;
record docs/designissues/2026-10-12-parallel-block-scans.md).

`chunksOf c l` cuts the list `l` of selected block numbers into consecutive
chunks of at most `c` elements (`c` below 1 is read as 1), in order. The
native query driver runs one scan per chunk as a Lean task and appends the
results in chunk order. `chunksOf_flatten` is the fact that makes this a
partition: the chunks, concatenated, are `l`.

Every recursion here is a tail call with an accumulator. The fuel argument
`f` of `chunksAcc` is the list length at the start, so each step drops at
least one element.
-/
namespace L4Factoidal.Storage.Sbm11.ParallelScan

/-- The chunks of `l`, built by `chunksAcc` onto the reversed accumulator
    `acc`; `f` bounds the number of steps (the length of `l`). -/
def chunksAcc {α : Type} (n : Nat) : Nat → List α → List (List α) → List (List α)
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | f + 1, l@(_ :: _), acc => chunksAcc n f (l.drop n) (l.take n :: acc)

/-- The consecutive chunks of `l` of at most `max c 1` elements each. -/
def chunksOf {α : Type} (c : Nat) (l : List α) : List (List α) :=
  chunksAcc (max c 1) l.length l []

/-- The chunks, concatenated after the reversed accumulator. -/
theorem chunksAcc_flatten {α : Type} (n : Nat) (hn : 1 ≤ n) :
    ∀ (f : Nat) (l : List α) (acc : List (List α)), l.length ≤ f →
      (chunksAcc n f l acc).flatten = acc.reverse.flatten ++ l := by
  intro f
  induction f with
  | zero =>
    intro l acc hl
    have hnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    simp [chunksAcc]
  | succ f ih =>
    intro l acc hl
    match l, hl with
    | [], _ => simp [chunksAcc]
    | a :: t, hl =>
      have hd : ((a :: t).drop n).length ≤ f := by
        simp only [List.length_drop, List.length_cons] at hl ⊢
        omega
      simp only [chunksAcc]
      rw [ih _ _ hd]
      simp [List.reverse_cons, List.flatten_append, List.take_append_drop, List.append_assoc]

/-- The chunks of `l` concatenated are `l`. -/
theorem chunksOf_flatten {α : Type} (c : Nat) (l : List α) :
    (chunksOf c l).flatten = l := by
  unfold chunksOf
  rw [chunksAcc_flatten (max c 1) (by omega) l.length l [] (Nat.le_refl _)]
  simp

/-- Every element of a chunk is an element of `l`. -/
theorem mem_of_mem_chunksOf {α : Type} (c : Nat) (l : List α) {X : List α}
    (hX : X ∈ chunksOf c l) {k : α} (hk : k ∈ X) : k ∈ l := by
  rw [← chunksOf_flatten c l]
  exact List.mem_flatten.mpr ⟨X, hX, hk⟩

end L4Factoidal.Storage.Sbm11.ParallelScan
