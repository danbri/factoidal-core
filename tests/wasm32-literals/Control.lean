

@[noinline] def keepA (x n : Nat) : Array Nat := #[x, n]
@[noinline] def keepB (x n : Nat) : List Nat := [x, n]

/-- One literal given to two owning callees. -/
@[noinline] def twoOwners (x : Nat) : Array Nat × List Nat :=
  let k : Nat := x + 4000000000
  (keepA x k, keepB x k)

/-- Takes ownership of the array, and frees it and its elements. -/
@[noinline] def dropIt (a : Array Nat) : Nat := a.size

@[export repro_run] def run (n : Nat) : IO Unit := do
  let (a, b) := twoOwners n
  let size := dropIt a
  let y := n + 3000000000
  IO.println s!"size {size}, y {y}, kept {b}"
