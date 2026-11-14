/-
L4Factoidal.WebNN.Shape: tensor shapes for the Web Neural Network API (and for any other
tensor code of the engine): element counts, NumPy-style broadcasting, and the row-major
correspondence between a flat element number and a multi-index.

Self-contained: core Lean only (no Mathlib, no other module of this library), so that other
parts of the engine can reuse it.

Record: docs/designissues/2026-11-14-webnn.md.
-/

namespace L4Factoidal.WebNN

/-- A tensor shape: the size of each dimension, outermost first. `[]` is a scalar. -/
abbrev Shape := List Nat

namespace Shape

/-- The number of elements of a tensor of this shape (1 for a scalar). -/
def size : Shape → Nat
  | [] => 1
  | d :: ds => d * size ds

@[simp] theorem size_nil : size [] = 1 := rfl
@[simp] theorem size_cons (d : Nat) (ds : Shape) : size (d :: ds) = d * size ds := rfl

/-- `size` as a loop (the compiled form of `size`: `size_eq_sizeTR`). -/
def sizeTR (s : Shape) : Nat := s.foldl (· * ·) 1

/-- Kind: accumulator invariant. Says: folding dimensions from `x` gives `x` times their
product. Does not say: that dimensions satisfy operand limits. -/
theorem foldl_mul_size (s : Shape) (x : Nat) : s.foldl (· * ·) x = x * size s := by
  induction s generalizing x with
  | nil => simp
  | cons d ds ih => simp [ih, Nat.mul_assoc]

/-- Kind: implementation equals specification (`csimp`: compiled code runs `sizeTR`, a loop,
where the source says `size`). Says: the loop computes the element count for every shape.
Does not say: anything about allocation or execution time. -/
@[csimp] theorem size_eq_sizeTR : @size = @sizeTR := by
  funext s; simp [sizeTR, foldl_mul_size]

/-- Kind: algebraic identity. Says: the element count of two shapes joined is the product of
their counts. Does not say: anything about data. -/
theorem size_append (a b : Shape) : size (a ++ b) = size a * size b := by
  induction a with
  | nil => simp
  | cons d ds ih => simp [ih, Nat.mul_assoc]

/-! ## Broadcasting (WebNN "bidirectionally broadcastable", as NumPy) -/

/-- Broadcast two dimension sizes: equal sizes stay, a size of 1 gives way to the other. -/
def bdim (x y : Nat) : Option Nat :=
  if x = y then some x else if x = 1 then some y else if y = 1 then some x else none

/-- Broadcast two shapes given innermost dimension first. -/
def broadcastRev : List Nat → List Nat → Option (List Nat)
  | [], ys => some ys
  | xs, [] => some xs
  | x :: xs, y :: ys => (bdim x y).bind fun d => (broadcastRev xs ys).map (d :: ·)

/-- `broadcastRev` as a loop with the result so far (innermost last) in `acc`. -/
def broadcastRevTR (acc : List Nat) : List Nat → List Nat → Option (List Nat)
  | [], ys => some (acc.reverse ++ ys)
  | xs, [] => some (acc.reverse ++ xs)
  | x :: xs, y :: ys =>
    match bdim x y with
    | some d => broadcastRevTR (d :: acc) xs ys
    | none => none

/-- Kind: accumulator invariant. Says: the loop prefixes the reverse accumulator to the
reference broadcast result. Does not say: that the shapes are broadcastable. -/
theorem broadcastRevTR_eq : ∀ (acc xs ys : List Nat),
    broadcastRevTR acc xs ys = (broadcastRev xs ys).map (acc.reverse ++ ·)
  | acc, [], ys => by simp [broadcastRevTR, broadcastRev]
  | acc, x :: xs, [] => by simp [broadcastRevTR, broadcastRev]
  | acc, x :: xs, y :: ys => by
    simp only [broadcastRevTR, broadcastRev]
    cases h : bdim x y with
    | none => simp
    | some d =>
      simp only [Option.bind_some]
      rw [broadcastRevTR_eq (d :: acc) xs ys]
      cases broadcastRev xs ys <;> simp

/-- The loop started with an empty accumulator (a constant, as `csimp` needs). -/
def broadcastRevLoop (xs ys : List Nat) : Option (List Nat) := broadcastRevTR [] xs ys

/-- Kind: implementation equals specification (`csimp`). Says: the loop gives the same
answer as `broadcastRev` for every pair of shapes. Does not say: anything about tensor data. -/
@[csimp] theorem broadcastRev_eq_TR : @broadcastRev = @broadcastRevLoop := by
  funext xs ys
  rw [broadcastRevLoop, broadcastRevTR_eq]
  cases broadcastRev xs ys <;> simp

/-- The shape two operands broadcast to (WebNN "bidirectionally broadcasting the shapes"),
or `none` when they are not broadcastable. -/
def broadcast (a b : Shape) : Option Shape :=
  (broadcastRev a.reverse b.reverse).map List.reverse

/-- `a` is unidirectionally broadcastable to `b` (WebNN): broadcasting gives exactly `b`. -/
def broadcastsTo (a b : Shape) : Bool := broadcast a b == some b

theorem bdim_comm (x y : Nat) : bdim x y = bdim y x := by
  unfold bdim
  by_cases h : x = y
  · subst h; rfl
  · have h' : ¬ y = x := fun e => h e.symm
    simp only [h, h', if_false]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]

theorem broadcastRev_comm : ∀ (a b : List Nat), broadcastRev a b = broadcastRev b a
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [broadcastRev, bdim_comm x y, broadcastRev_comm xs ys]

/-- Kind: algebraic law of a shape function. Says: broadcasting two shapes does not depend
on their order (both fail, or both give the same shape). Does not say: that the element-wise
operation applied afterwards is commutative. -/
theorem broadcast_comm (a b : Shape) : broadcast a b = broadcast b a := by
  simp [broadcast, broadcastRev_comm a.reverse b.reverse]

/-- Broadcasting three dimension sizes, either grouping: `none` propagates. -/
theorem bdim_assoc (x y z : Nat) :
    (bdim x y).bind (fun d => bdim d z) = (bdim y z).bind (fun d => bdim x d) := by
  unfold bdim
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> by_cases hx : x = 1 <;> by_cases hy : y = 1 <;>
    by_cases hz : z = 1 <;> by_cases hxz : x = z <;> simp_all <;> omega

theorem broadcastRev_nil_right (a : List Nat) : broadcastRev a [] = some a := by
  cases a <;> rfl

theorem broadcastRev_assoc : ∀ (a b c : List Nat),
    (broadcastRev a b).bind (fun d => broadcastRev d c) =
    (broadcastRev b c).bind (fun d => broadcastRev a d)
  | [], b, c => by
    simp only [broadcastRev, Option.bind_some]
    cases h : broadcastRev b c <;> simp
  | a, [], c => by
    simp only [broadcastRev_nil_right, Option.bind_some, broadcastRev]
  | a, b, [] => by
    simp only [broadcastRev_nil_right, Option.bind_some]
    cases h : broadcastRev a b <;> simp
  | x :: xs, y :: ys, z :: zs => by
    have h1 := bdim_assoc x y z
    have h2 := broadcastRev_assoc xs ys zs
    simp only [broadcastRev]
    cases hxy : bdim x y with
    | none =>
      rw [hxy] at h1
      cases hyz : bdim y z with
      | none => simp
      | some d2 =>
        rw [hyz] at h1
        simp only [Option.bind_none, Option.bind_some] at h1
        cases ryz : broadcastRev ys zs with
        | none => simp
        | some r2 => simp [broadcastRev, ← h1]
    | some d1 =>
      rw [hxy] at h1
      cases rxy : broadcastRev xs ys with
      | none =>
        rw [rxy] at h2
        cases hyz : bdim y z with
        | none => simp
        | some d2 =>
          cases ryz : broadcastRev ys zs with
          | none => simp
          | some r2 =>
            rw [ryz] at h2
            simp only [Option.bind_none, Option.bind_some] at h2
            simp [broadcastRev, ← h2]
      | some r1 =>
        rw [rxy] at h2
        cases hyz : bdim y z with
        | none =>
          rw [hyz] at h1
          simp only [Option.bind_none, Option.bind_some] at h1
          simp [broadcastRev, h1]
        | some d2 =>
          rw [hyz] at h1
          simp only [Option.bind_some] at h1
          cases ryz : broadcastRev ys zs with
          | none =>
            rw [ryz] at h2
            simp only [Option.bind_none, Option.bind_some] at h2
            simp [broadcastRev, h2]
          | some r2 =>
            rw [ryz] at h2
            simp only [Option.bind_some] at h2
            simp [broadcastRev, h1, h2]

/-- Kind: algebraic law of a shape function. Says: broadcasting three shapes gives the same
result (the same shape, or failure) whichever pair is broadcast first. Does not say: anything
about the rounding of the arithmetic done on the broadcast operands. -/
theorem broadcast_assoc (a b c : Shape) :
    (broadcast a b).bind (fun d => broadcast d c) = (broadcast b c).bind (fun d => broadcast a d) := by
  have h := broadcastRev_assoc a.reverse b.reverse c.reverse
  unfold broadcast
  cases hab : broadcastRev a.reverse b.reverse with
  | none =>
    rw [hab] at h
    cases hbc : broadcastRev b.reverse c.reverse with
    | none => rfl
    | some r =>
      rw [hbc] at h
      simp only [Option.bind_none, Option.bind_some] at h
      simp [← h]
  | some r1 =>
    rw [hab] at h
    cases hbc : broadcastRev b.reverse c.reverse with
    | none =>
      rw [hbc] at h
      simp only [Option.bind_none, Option.bind_some] at h
      simp [h]
    | some r2 =>
      rw [hbc] at h
      simp only [Option.bind_some] at h
      simp [h]

/-- Kind: identity element. Says: a scalar broadcasts with any shape to that shape. -/
theorem broadcast_scalar (a : Shape) : broadcast [] a = some a := by
  simp [broadcast, broadcastRev]

/-- Kind: idempotence. Says: a shape broadcasts with itself to itself. -/
theorem broadcast_self (a : Shape) : broadcast a a = some a := by
  have h : ∀ l : List Nat, broadcastRev l l = some l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp [broadcastRev, bdim, ih]
  simp [broadcast, h]

/-! ## Flat element numbers and multi-indices (row-major: the last dimension varies fastest) -/

/-- A multi-index is within a shape: one index per dimension, each below the dimension's size. -/
def Valid : Shape → List Nat → Prop
  | [], [] => True
  | d :: ds, i :: is => i < d ∧ Valid ds is
  | _, _ => False

/-- The flat element number of a multi-index. -/
def ravel : Shape → List Nat → Nat
  | _ :: ds, i :: is => i * size ds + ravel ds is
  | _, _ => 0

/-- The multi-index of a flat element number. -/
def unravel : Shape → Nat → List Nat
  | [], _ => []
  | _ :: ds, k => (k / size ds) :: unravel ds (k % size ds)

/-- `ravel` as a loop (Horner's rule), with the number so far in `acc`. -/
def ravelTR (acc : Nat) : Shape → List Nat → Nat
  | d :: ds, i :: is => ravelTR (acc * d + i) ds is
  | s, _ => acc * size s

/-- Kind: accumulator invariant. Says: the loop adds the prefix contribution to the
reference flat index. Does not say: that the index is in bounds. -/
theorem ravelTR_eq : ∀ (acc : Nat) (s : Shape) (idx : List Nat), ravelTR acc s idx = acc * size s + ravel s idx
  | acc, [], idx => by simp [ravelTR, ravel]
  | acc, d :: ds, [] => by simp [ravelTR, ravel]
  | acc, d :: ds, i :: is => by
    simp only [ravelTR, ravel, size_cons]
    rw [ravelTR_eq (acc * d + i) ds is, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- Horner's loop started at 0 (a constant, as `csimp` needs). -/
def ravelLoop (s : Shape) (idx : List Nat) : Nat := ravelTR 0 s idx

/-- Kind: implementation equals specification (`csimp`). Says: Horner's loop computes `ravel`.
Does not say: that its arguments describe a valid index. -/
@[csimp] theorem ravel_eq_TR : @ravel = @ravelLoop := by
  funext s idx; simp [ravelLoop, ravelTR_eq]

/-- `unravel` as a loop, with the indices so far (innermost first) in `acc`. -/
def unravelTR (acc : List Nat) : Shape → Nat → List Nat
  | [], _ => acc.reverse
  | _ :: ds, k => unravelTR ((k / size ds) :: acc) ds (k % size ds)

/-- Kind: accumulator invariant. Says: the loop prefixes the reverse accumulator to the
reference indices. Does not say: that the flat index is in bounds. -/
theorem unravelTR_eq : ∀ (acc : List Nat) (s : Shape) (k : Nat), unravelTR acc s k = acc.reverse ++ unravel s k
  | acc, [], k => by simp [unravelTR, unravel]
  | acc, d :: ds, k => by
    simp only [unravelTR, unravel]
    rw [unravelTR_eq]; simp

/-- The `unravel` loop started with no indices (a constant, as `csimp` needs). -/
def unravelLoop (s : Shape) (k : Nat) : List Nat := unravelTR [] s k

/-- Kind: implementation equals specification (`csimp`). Says: the loop computes `unravel`.
Does not say: that the resulting indices are in bounds without a bound on `k`. -/
@[csimp] theorem unravel_eq_TR : @unravel = @unravelLoop := by
  funext s k; simp [unravelLoop, unravelTR_eq]

/-- Kind: bound. Says: the flat number of a multi-index that is within the shape is below the
shape's element count, so reading it never leaves the tensor's data. -/
theorem ravel_lt : ∀ (s : Shape) (idx : List Nat), Valid s idx → ravel s idx < size s
  | [], [], _ => by simp [ravel]
  | [], _ :: _, h => by simp [Valid] at h
  | _ :: _, [], h => by simp [Valid] at h
  | d :: ds, i :: is, h => by
    obtain ⟨hi, hv⟩ := h
    have ih := ravel_lt ds is hv
    simp only [ravel, size_cons]
    calc i * size ds + ravel ds is < i * size ds + size ds := Nat.add_lt_add_left ih _
      _ = (i + 1) * size ds := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ d * size ds := Nat.mul_le_mul_right _ hi

/-- Kind: round trip. Says: a multi-index within the shape is recovered from its flat number. -/
theorem unravel_ravel : ∀ (s : Shape) (idx : List Nat), Valid s idx → unravel s (ravel s idx) = idx
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Valid] at h
  | _ :: _, [], h => by simp [Valid] at h
  | d :: ds, i :: is, h => by
    obtain ⟨_, hv⟩ := h
    have hlt := ravel_lt ds is hv
    have hpos : 0 < size ds := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    simp only [ravel, unravel]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt, unravel_ravel ds is hv]

/-- Kind: bound. Says: the multi-index of a flat number below the element count is within the
shape. -/
theorem unravel_valid : ∀ (s : Shape) (k : Nat), k < size s → Valid s (unravel s k)
  | [], _, _ => trivial
  | d :: ds, k, h => by
    simp only [size_cons] at h
    have hpos : 0 < size ds := by
      rcases Nat.eq_zero_or_pos (size ds) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    refine ⟨?_, unravel_valid ds _ (Nat.mod_lt _ hpos)⟩
    exact (Nat.div_lt_iff_lt_mul hpos).mpr h

/-- Kind: round trip. Says: a flat number below the element count is recovered from its
multi-index. With `unravel_ravel`: flat numbers and multi-indices of a shape correspond one to
one. -/
theorem ravel_unravel : ∀ (s : Shape) (k : Nat), k < size s → ravel s (unravel s k) = k
  | [], k, h => by simp at h; simp [ravel, h]
  | d :: ds, k, h => by
    simp only [size_cons] at h
    have hpos : 0 < size ds := by
      rcases Nat.eq_zero_or_pos (size ds) with h0 | h0
      · rw [h0] at h; simp at h
      · exact h0
    simp only [unravel, ravel]
    rw [ravel_unravel ds _ (Nat.mod_lt _ hpos)]
    exact Nat.div_add_mod' k (size ds)

#guard broadcast [2, 3, 4] [3, 1] == some [2, 3, 4]
#guard broadcast [8, 1, 6, 1] [7, 1, 5] == some [8, 7, 6, 5]
#guard broadcast [2, 3] [3, 2] == none
#guard broadcast [] [5] == some [5]
#guard broadcastsTo [3, 1] [2, 3, 4] && !broadcastsTo [2, 3, 4] [3, 1]
#guard ravel [2, 3, 4] [1, 2, 3] == 23 && unravel [2, 3, 4] 23 == [1, 2, 3]
#guard size [2, 3, 4] == 24 && size [] == 1 && size [0, 5] == 0

-- Shapes from webnn/validation_tests/expand.https.any.js and transpose.https.any.js.
#guard broadcastRevTR [] [5, 1, 3] [5, 4, 3] == some [5, 4, 3]
#guard broadcastRevTR [] [] [5, 4, 3] == some [5, 4, 3]
#guard sizeTR [1, 2, 3, 4] == 24
#guard ravelTR 0 [1, 2, 3, 4] [0, 1, 2, 3] == 23
#guard unravelTR [] [1, 2, 3, 4] 23 == [0, 1, 2, 3]

end Shape
end L4Factoidal.WebNN
