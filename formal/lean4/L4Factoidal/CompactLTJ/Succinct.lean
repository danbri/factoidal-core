/-!
Copyright 2026 Factoidal contributors. SPDX-License-Identifier: Apache-2.0

Fresh LOUDS-style unary-degree topology and rank/select reference operations.
No external succinct-index implementation has been translated.

These definitions are intentionally simple List-based specifications. Fast
packed UInt64 rank/select implementations should be proved equivalent to
these definitions before being used by the CompactLTJ cursor.
-/
import Std

namespace L4Factoidal.CompactLTJ.Succinct

/-- Number of set bits in the first n positions (n is exclusive). -/
def rank1 (bits : List Bool) (n : Nat) : Nat :=
  ((bits.take n).filter (fun b => b)).length

/-- The number of unset bits within the first n positions. -/
def rank0 (bits : List Bool) (n : Nat) : Nat :=
  ((bits.take n).filter (fun b => !b)).length

theorem rank1_zero (bits : List Bool) : rank1 bits 0 = 0 := by
  simp [rank1]

theorem rank0_zero (bits : List Bool) : rank0 bits 0 = 0 := by
  simp [rank0]

theorem rank1_empty (n : Nat) : rank1 [] n = 0 := by
  simp [rank1]

theorem rank0_empty (n : Nat) : rank0 [] n = 0 := by
  simp [rank0]

theorem rank1_cons_succ (bit : Bool) (bits : List Bool) (n : Nat) :
    rank1 (bit :: bits) (n + 1) =
      (if bit then 1 else 0) + rank1 bits n := by
  cases bit <;> simp [rank1, List.take]

theorem rank0_cons_succ (bit : Bool) (bits : List Bool) (n : Nat) :
    rank0 (bit :: bits) (n + 1) =
      (if bit then 0 else 1) + rank0 bits n := by
  cases bit <;> simp [rank0, List.take]

/-- Locate the k-th true bit (zero-based), or none if too few exist. -/
def select1 (k : Nat) : List Bool → Option Nat
  | [] => none
  | bit :: rest =>
      if bit then
        if k == 0 then some 0
        else (select1 (k - 1) rest).map Nat.succ
      else (select1 k rest).map Nat.succ

/-- Locate the k-th false bit (zero-based), or none. -/
def select0 (k : Nat) : List Bool → Option Nat
  | [] => none
  | bit :: rest =>
      if !bit then
        if k == 0 then some 0
        else (select0 (k - 1) rest).map Nat.succ
      else (select0 k rest).map Nat.succ

theorem select1_nil (k : Nat) : select1 k [] = none := rfl
theorem select0_nil (k : Nat) : select0 k [] = none := rfl

theorem select1_true_head (rest : List Bool) :
    select1 0 (true :: rest) = some 0 := by
  simp [select1]

theorem select0_false_head (rest : List Bool) :
    select0 0 (false :: rest) = some 0 := by
  simp [select0]

theorem select1_false_head (k : Nat) (rest : List Bool) :
    select1 k (false :: rest) = (select1 k rest).map Nat.succ := by
  simp [select1]

theorem select0_true_head (k : Nat) (rest : List Bool) :
    select0 k (true :: rest) = (select0 k rest).map Nat.succ := by
  simp [select0]

/-- Unary degree sequences in BFS node order: d ones then one zero
for each node. This is the classical LOUDS degree-bitstream convention. -/
def encodeDegrees (degrees : List Nat) : List Bool :=
  degrees.flatMap (fun degree => List.replicate degree true ++ [false])

theorem encodeDegrees_nil : encodeDegrees [] = [] := rfl

theorem encodeDegrees_cons (d : Nat) (rest : List Nat) :
    encodeDegrees (d :: rest) =
      List.replicate d true ++ [false] ++ encodeDegrees rest := by
  simp [encodeDegrees]

/-- The degree of a BFS-indexed node is the gap between successive zeros
in the unary-degree encoding, subtracting its terminating zero. -/
def degreeAt (bits : List Bool) (node : Nat) : Option Nat := do
  let finish ← select0 node bits
  let start ←
    if node == 0 then some 0
    else (select0 (node - 1) bits).map (· + 1)
  some (finish - start)

/-- Child numbers are BFS-order node indices, beginning at 0 for the root.
The first child of node i is 1 + the number of ones before its segment. -/
def firstChildAt (bits : List Bool) (node : Nat) : Option Nat := do
  let start ←
    if node == 0 then some 0
    else (select0 (node - 1) bits).map (· + 1)
  some (rank1 bits start + 1)

theorem degreeAt_empty (node : Nat) :
    degreeAt [] node = none := by
  simp [degreeAt, select0]

theorem firstChildAt_empty (node : Nat) :
    firstChildAt [] node = none := by
  simp [firstChildAt, select0]

/-! A root with two leaf children has degrees [2,0,0] and LOUDS
bits 11000; the children are nodes 1 and 2. -/
#guard encodeDegrees [2,0,0] == [true,true,false,false,false]
#guard rank1 [true,true,false,false,false] 3 == 2
#guard rank0 [true,true,false,false,false] 3 == 1
#guard select1 1 [true,true,false,false,false] == some 1
#guard select0 0 [true,true,false,false,false] == some 2
#guard select0 2 [true,true,false,false,false] == some 4
#guard degreeAt (encodeDegrees [2,0,0]) 0 == some 2
#guard degreeAt (encodeDegrees [2,0,0]) 1 == some 0
#guard firstChildAt (encodeDegrees [2,0,0]) 0 == some 1

end L4Factoidal.CompactLTJ.Succinct
