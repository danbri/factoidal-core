/-
L4Factoidal.RDF.Runs — the runs of a list by a key: the maximal sublists of
consecutive items with the same key.

The serialiser layer (`L4Factoidal/RDF/Sink.lean`) writes RDF/XML and JSON-LD one
subject at a time: it keeps the items of the current subject and writes them when
the next item has another subject (https://github.com/danbri/factoidal/issues/846
and https://github.com/danbri/factoidal/issues/847). `runsFrom` is the
specification of what such a writer sees: the state is the current key and its
items, newest first. `runs_flatten` and `mem_runs` say that the runs are a
partition of the list into non-empty pieces of one key each.

`runsFrom` is a specification for theorems and build-time checks; the writers
keep its state and are not this function.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.RDF.Runs

variable {α : Type}

/-- The runs of `l` by `key`, after the open run `cur` (its key and items, the
    newest first). -/
def runsFrom (key : α → String) : Option (String × List α) → List α → List (String × List α)
  | none, [] => []
  | some (k, xs), [] => [(k, xs.reverse)]
  | none, x :: l => runsFrom key (some (key x, [x])) l
  | some (k, xs), x :: l =>
      if k == key x then runsFrom key (some (k, x :: xs)) l
      else (k, xs.reverse) :: runsFrom key (some (key x, [x])) l

/-- The runs of `l` by `key`. -/
def runs (key : α → String) (l : List α) : List (String × List α) := runsFrom key none l

/-- The open run and the rest of the list are the concatenation of the runs. -/
theorem runsFrom_flatten (key : α → String) :
    ∀ (k : String) (xs l : List α),
      (runsFrom key (some (k, xs)) l).flatMap (·.2) = xs.reverse ++ l
  | k, xs, [] => by simp [runsFrom]
  | k, xs, x :: l => by
      unfold runsFrom
      split
      · rw [runsFrom_flatten key k (x :: xs) l]; simp
      · simp only [List.flatMap_cons]
        rw [runsFrom_flatten key (key x) [x] l]; simp

theorem runs_flatten (key : α → String) (l : List α) : (runs key l).flatMap (·.2) = l := by
  cases l with
  | nil => rfl
  | cons x l => unfold runs runsFrom; rw [runsFrom_flatten]; simp

/-- Each run of an open run whose items all have key `k` (and that has an item) is
    not empty, and its items have the run's key. -/
theorem mem_runsFrom (key : α → String) :
    ∀ (k : String) (xs l : List α), xs ≠ [] → (∀ y ∈ xs, key y = k) →
      ∀ r ∈ runsFrom key (some (k, xs)) l, r.2 ≠ [] ∧ ∀ y ∈ r.2, key y = r.1
  | k, xs, [], hne, hk, r, hr => by
      simp only [runsFrom, List.mem_singleton] at hr
      subst hr
      exact ⟨by simpa using hne, fun y hy => hk y (by simpa using hy)⟩
  | k, xs, x :: l, hne, hk, r, hr => by
      unfold runsFrom at hr
      split at hr
      · rename_i h
        have hkx : key x = k := (beq_iff_eq.mp h).symm
        refine mem_runsFrom key k (x :: xs) l (by simp) ?_ r hr
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hkx
        · exact hk y hy
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨by simpa using hne, fun y hy => hk y (by simpa using hy)⟩
        · exact mem_runsFrom key (key x) [x] l (by simp) (by simp) r hr

theorem mem_runs (key : α → String) (l : List α) :
    ∀ r ∈ runs key l, r.2 ≠ [] ∧ ∀ y ∈ r.2, key y = r.1 := by
  cases l with
  | nil => simp [runs, runsFrom]
  | cons x l =>
      unfold runs runsFrom
      exact mem_runsFrom key (key x) [x] l (by simp) (by simp)

#print axioms runs_flatten
#print axioms mem_runs

#guard (runs (fun (n : Nat) => toString (n / 10)) [1, 2, 11, 3, 12]).map (fun r => (r.1, r.2)) ==
  [("0", [1, 2]), ("1", [11]), ("0", [3]), ("1", [12])]
#guard runs (fun (n : Nat) => toString n) [] == []

end L4Factoidal.RDF.Runs
