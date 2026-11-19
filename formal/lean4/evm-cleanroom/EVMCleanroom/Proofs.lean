import EVMCleanroom.Core
/-! Properties about the *implemented* subset, not an Ethereum consensus proof. -/

namespace EVMCleanroom

/-- Every Word value is actually below 2^256. -/
theorem word_bounded (x : Word) : x.val < modulus := x.isLt

/-- Addition is commutative modulo 2^256. -/
theorem word_add_comm (a b : Word) : a.add b = b.add a := by
  simp only [Word.add, Nat.add_comm]

/-- Each successful commit preserves the EVM's 1024-word stack limit. -/
theorem commit_stack_bounded {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool}
    (_h : commit s pc xs cost halt = .ok out) :
    out.stack.items.length ≤ 1024 := out.stack.bounded

/-- Gas never increases on a successful committed transition. -/
theorem commit_gas_nonincreasing {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool}
    (h : commit s pc xs cost halt = .ok out) : out.gas ≤ s.gas := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      exact Nat.sub_le _ _
    · cases h
  · cases h

/-- A transition cannot change bytecode. -/
theorem commit_code_unchanged {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool}
    (h : commit s pc xs cost halt = .ok out) : out.code = s.code := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

#print axioms word_add_comm
#print axioms commit_stack_bounded
#print axioms commit_gas_nonincreasing
#print axioms commit_code_unchanged

end EVMCleanroom
