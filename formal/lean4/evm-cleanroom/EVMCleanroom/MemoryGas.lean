import EVMCleanroom.Core

/-!
# EVM memory expansion gas

Based on the execution-specs (Prague) vm/gas.py functions
calculate_memory_gas_cost and calculate_gas_extend_memory.
This model is parameterized over *memory size in 32-byte words*, and does
not attempt to represent EVM memory contents.

An important subtlety: an access of length zero must not expand memory,
even if its offset is enormous (such as 2^256-1).

Reference:
https://github.com/ethereum/execution-specs/blob/master/src/ethereum/forks/prague/vm/gas.py
-/

namespace EVMCleanroom.MemoryGas

/-- C_mem(w) = 3w + floor(w² / 512), where w is the number of
    allocated 32-byte words. -/
def cost (words : Nat) : Nat :=
  3 * words + words * words / 512

/-- Calculate the additional memory gas owed for a requested number of
    active words, never shrinking the previously paid-for allocation. -/
def expansion (oldWords requestedWords : Nat) : Nat :=
  cost (max oldWords requestedWords) - cost oldWords

/-- Word demand for a memory access. A zero-length access does not touch
    memory even when offset is extremely large. -/
def requestedWords (offset length : Nat) : Nat :=
  if length == 0 then 0 else (offset + length + 31) / 32

/-- Exact gas for one access that may expand memory. -/
def accessCost (oldWords offset length : Nat) : Nat :=
  expansion oldWords (requestedWords offset length)

/-- The EVM memory-cost function is monotone, including quadratic terms. -/
theorem cost_monotone {a b : Nat} (h : a ≤ b) : cost a ≤ cost b := by
  unfold cost
  have hsq : a * a ≤ b * b := Nat.mul_le_mul h h
  have hdiv : a * a / 512 ≤ b * b / 512 := Nat.div_le_div_right hsq
  have hlinear : 3 * a ≤ 3 * b := Nat.mul_le_mul_left 3 h
  omega

/-- Reopening an already allocated memory range incurs no expansion cost. -/
theorem expansion_self (n : Nat) : expansion n n = 0 := by
  simp [expansion]

/-- For two ordered memory sizes the max can be eliminated. -/
theorem expansion_of_le {a b : Nat} (h : a ≤ b) :
    expansion a b = cost b - cost a := by
  simp [expansion, Nat.max_eq_right h]

/-- Path independence of EVM memory gas: expansion in two phases costs
    exactly as much as jumping to the final high-water mark in one step.
    Thus strategically splitting allocations cannot evade quadratic gas. -/
theorem expansion_path_independent {a b c : Nat}
    (hab : a ≤ b) (hbc : b ≤ c) :
    expansion a b + expansion b c = expansion a c := by
  rw [expansion_of_le hab, expansion_of_le hbc,
      expansion_of_le (Nat.le_trans hab hbc)]
  have h1 := cost_monotone hab
  have h2 := cost_monotone hbc
  omega

/-- All zero-length memory accesses cost zero, no matter the offset,
    including huge offsets that would be invalid for nonempty accesses. -/
theorem zero_length_access_free (oldWords offset : Nat) :
    accessCost oldWords offset 0 = 0 := by
  simp [accessCost, requestedWords, expansion]

/-- Once memory includes the touched final byte, the same access costs zero. -/
theorem previously_allocated_access_free (oldWords offset length : Nat)
    (h : requestedWords offset length ≤ oldWords) :
    accessCost oldWords offset length = 0 := by
  simp [accessCost, expansion, Nat.max_eq_left h]

-- Boundary tests for the nonlinear pricing and 32-byte rounding.
#guard cost 0 == 0
#guard cost 1 == 3
#guard cost 22 == 66
#guard cost 23 == 70
#guard cost 32 == 98
#guard accessCost 0 0 1 == 3
#guard accessCost 0 31 1 == 3
#guard accessCost 0 32 1 == 6
#guard accessCost 1 31 1 == 0
#guard accessCost 0 (2 ^ 256 - 1) 0 == 0

#print axioms cost_monotone
#print axioms expansion_path_independent
#print axioms zero_length_access_free
#print axioms previously_allocated_access_free

end EVMCleanroom.MemoryGas
