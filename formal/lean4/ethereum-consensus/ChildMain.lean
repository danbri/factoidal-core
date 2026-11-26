import EthereumConsensus.ForkChoice.ChildSelection

/-!
Source-emitted synthetic LMD-GHOST one-step selection cases.
The independent Python checker reconstructs every input and rule. The
data are NOT authenticated beacon blocks or justified checkpoint state.
-/

open EthereumConsensus.ForkChoice

private def syntheticBlocks (n root : Nat) : Option BlockPosition :=
  if root == 0 then some ⟨0, none⟩
  else if root < 13 then
    if n % 19 == 0 && root == n % 12 + 1 then none
    else if n % 23 == 0 && root == 3 then some ⟨3, some 12⟩
    else if n % 29 == 0 && root == 4 then some ⟨0, some 0⟩
    else if root < 5 then some ⟨root, some 0⟩
    else some ⟨root, some (1 + (root - 5) % 4)⟩
  else none

private def syntheticStore (n : Nat) : VoteStore := {
  latest := fun i =>
    if (n + i) % 5 == 0 then none
    else some ⟨n % 12, 5 + (17 * n + 3 * i) % 8⟩
  equivocating := fun i => (n + 3 * i) % 11 == 0
}

private def syntheticRoster (n : Nat) : List EligibleWeight :=
  let entries : List EligibleWeight :=
    [(0, 7 + n % 11), (1, 3 + (n / 2) % 5),
     (2, n % 29), (3, 10 + (3 * n) % 13)]
  if n % 13 == 0 then (0, 1) :: entries else entries

private def syntheticChildren (mode : Nat) : List Nat :=
  match mode with
  | 0 => []
  | 1 => [1]
  | 2 => [1, 2]
  | 3 => [1, 2, 3]
  | 4 => [1, 1]
  | 5 => [3, 4]
  | 6 => [1, 2, 4]
  | 7 => [2, 5]
  | 8 => [1, 99]
  | 9 => [3]
  | 10 => [2, 3, 4]
  | _ => [4, 2, 1]

private def syntheticBoost (n : Nat) : Option Nat :=
  if n % 3 == 0 then none else some (5 + (7 * n) % 8)

private def syntheticTotal (n : Nat) : Nat :=
  if n % 127 == 0 then 80
  else if n % 17 == 0 then n % 101
  else 1000000000 + (n % 41) * 123456789

private def displaySelection : Option (Option Nat) → String
  | none => "R"
  | some none => "E"
  | some (some root) => toString root

def main : IO Unit := do
  for n in [:1024] do
    let blocks := syntheticBlocks n
    let store := syntheticStore n
    let roster := syntheticRoster n
    let parent := if n % 31 == 0 then 99 else 0
    let fuel := n % 11
    let mode := n % 12
    let children := syntheticChildren mode
    let boost := syntheticBoost n
    let total := syntheticTotal n
    let base := selectCheckedChild store blocks parent fuel roster
      none total children
    let current := selectCheckedChild store blocks parent fuel roster
      boost total children
    let candidate : LatestMessage := ⟨n % 12 + 1, (19 * n + 1) % 13⟩
    let admitted := updateStore store (n % 4) candidate (n % 5 != 0)
    let after := selectCheckedChild admitted blocks parent fuel roster
      boost total children
    let refused := selectCheckedChild
      (updateStore store (n % 4) candidate false) blocks parent fuel
      roster boost total children
    IO.println s!"{n}\t{parent}\t{fuel}\t{mode}\t{displaySelection base}\t{displaySelection current}\t{displaySelection after}\t{displaySelection refused}"
