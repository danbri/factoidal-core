namespace L4Factoidal.SPARQL

/-- Merge at most `count` rows, preserving the exact tie choices of `List.merge`.
    Recursion is bounded by the requested output size. -/
def mergePrefix (xs ys : List α) (le : α → α → Bool) : Nat → List α
  | 0 => []
  | count + 1 =>
      match xs, ys with
      | [], _ => ys.take (count + 1)
      | _, [] => xs.take (count + 1)
      | x :: xs, y :: ys =>
          if le x y then x :: mergePrefix xs (y :: ys) le count
          else y :: mergePrefix (x :: xs) ys le count

theorem mergePrefix_eq_take_merge (xs ys : List α) (le : α → α → Bool)
    (count : Nat) :
    mergePrefix xs ys le count = (xs.merge ys le).take count := by
  induction count generalizing xs ys with
  | zero => simp [mergePrefix]
  | succ count ih =>
      cases xs <;> cases ys <;> simp only [mergePrefix, List.merge]
      all_goals first | rfl | (split <;> simp_all)

theorem mergePrefix_take_inputs (xs ys : List α) (le : α → α → Bool)
    (count : Nat) :
    mergePrefix (xs.take count) (ys.take count) le count
      = mergePrefix xs ys le count := by
  induction count generalizing xs ys with
  | zero => rfl
  | succ count ih =>
      cases xs with
      | nil => simp [mergePrefix, List.take_take]
      | cons x xs =>
          cases ys with
          | nil => simp [mergePrefix, List.take_take]
          | cons y ys =>
              simp only [List.take_succ_cons, mergePrefix]
              split <;> congr 1
              · rw [← ih, ← ih xs (y :: ys)]
                cases count <;> simp [List.take_take]
              · rw [← ih, ← ih (x :: xs) ys]
                cases count <;> simp [List.take_take]

/-- Tail-recursive runtime merge, including large finite LIMIT values. -/
def mergePrefixTR (xs ys : List α) (le : α → α → Bool) (count : Nat) : List α :=
  go xs ys count []
where
  go (xs ys : List α) (count : Nat) (acc : List α) : List α :=
    match count, xs, ys with
    | 0, _, _ => acc.reverse
    | count + 1, [], _ => ((ys.take (count + 1)).reverseAux acc).reverse
    | count + 1, _, [] => ((xs.take (count + 1)).reverseAux acc).reverse
    | count + 1, x :: xs, y :: ys =>
        if le x y then go xs (y :: ys) count (x :: acc)
        else go (x :: xs) ys count (y :: acc)

theorem mergePrefixTR_go_eq (xs ys : List α) (le : α → α → Bool)
    (count : Nat) (acc : List α) :
    mergePrefixTR.go le xs ys count acc = acc.reverse ++ mergePrefix xs ys le count := by
  induction count generalizing xs ys acc with
  | zero => simp [mergePrefixTR.go, mergePrefix]
  | succ count ih =>
      cases xs <;> cases ys <;>
        simp only [mergePrefixTR.go, mergePrefix]
      all_goals first
        | simp [List.reverseAux_eq, List.reverse_append]
        | (split <;> simp [ih, List.reverse_cons, List.append_assoc])

@[csimp] theorem mergePrefix_eq_TR : @mergePrefix = @mergePrefixTR := by
  funext α xs ys le count
  simp [mergePrefixTR, mergePrefixTR_go_eq]

/-- Stable prefix of the current runtime sort. Each subtree retains only the
    rows the final prefix can consume. This refinement assumes no comparator
    laws, so it also preserves the existing behavior for incomparable terms. -/
def mergeSortPrefix (xs : List α) (le : α → α → Bool) (count : Nat) : List α :=
  match count, xs with
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | _ + 1, a :: b :: rest =>
      let halves := List.MergeSort.Internal.splitInTwo ⟨a :: b :: rest, rfl⟩
      have := by simpa using halves.1.2
      have := by simpa using halves.2.2
      mergePrefix (mergeSortPrefix halves.1 le count)
        (mergeSortPrefix halves.2 le count) le count
termination_by xs.length

theorem mergeSortPrefix_eq_take (xs : List α) (le : α → α → Bool) (count : Nat) :
    mergeSortPrefix xs le count = (xs.mergeSort le).take count := by
  cases count with
  | zero => simp [mergeSortPrefix]
  | succ count =>
      cases xs with
      | nil => simp [mergeSortPrefix]
      | cons a xs =>
          cases xs with
          | nil => simp [mergeSortPrefix]
          | cons b rest =>
              rw [mergeSortPrefix, List.mergeSort]
              rw [mergeSortPrefix_eq_take, mergeSortPrefix_eq_take,
                mergePrefix_take_inputs, mergePrefix_eq_take_merge]
termination_by xs.length
decreasing_by all_goals simp [List.MergeSort.Internal.splitInTwo, List.splitAt_eq]; omega

#print axioms mergeSortPrefix_eq_take
#print axioms mergePrefix_eq_TR

end L4Factoidal.SPARQL
