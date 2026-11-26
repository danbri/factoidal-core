def slowSum : Nat → Nat | 0 => 0 | n+1 => (n+1) + slowSum n
theorem sum_eq (n : Nat) : 2 * slowSum n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [slowSum, Nat.mul_add, ih]
    simp only [Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
theorem small1 : ∀ x : Fin 256, x.val % 8 = x.val &&& 7 := by decide +kernel
theorem small2 : ∀ x : Fin 256, x.val % 8 = x.val &&& 7 := by
  set_option maxRecDepth 100000 in decide
theorem idx (i n : Nat) (h : i < n) (hn : n ≤ 10) : i < 10 := by omega
-- Counterexample search (core only): exhaustive search with #eval
#eval (List.range 300).filter (fun x => (x + 200) / 2 != (x / 2 + 100)) |>.take 3
