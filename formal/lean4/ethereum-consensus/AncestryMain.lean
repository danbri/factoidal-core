import EthereumConsensus.ForkChoice.CheckedAncestry

/-!
Source-observed, synthetic block-parent ancestry and LMD score cases.
This never contacts an Ethereum network or parses authenticated blocks.
The independent Python reference reconstructs inputs and evaluates rules
without importing Lean outputs as expected results.
-/

open EthereumConsensus.ForkChoice

private def syntheticBlocks (n : Nat) (root : Nat) : Option BlockPosition :=
  if root == 0 then some ⟨0, none⟩
  else if root < 28 then
    if n % 19 == 0 && root == n % 13 + 1 then none
    else if n % 23 == 0 && root == 7 then some ⟨7, some 8⟩
    else some ⟨root, some (root / 2)⟩
  else none

private def syntheticStore (n : Nat) : VoteStore := {
  latest := fun i =>
    if (n + i) % 5 == 0 then none
    else some ⟨n % 12, (13 * n + 7 * i) % 31⟩
  equivocating := fun i => (n + 3 * i) % 11 == 0
}

private def syntheticRoster (n : Nat) : List EligibleWeight :=
  let standard : List EligibleWeight :=
    [(0, 7 + n % 11), (1, 3 + (n / 2) % 5),
     (2, n % 29), (3, 10 + (3 * n) % 13)]
  if n % 13 == 0 then (0, 1) :: standard else standard

private def syntheticBoostRoot (n : Nat) : Option Nat :=
  if n % 3 == 0 then none else some ((5 * n + 3) % 32)

private def syntheticTotalActiveBalance (n : Nat) : Nat :=
  if n % 127 == 0 then 80
  else if n % 17 == 0 then n % 101
  else 1000000000 + (n % 41) * 123456789

private def display : Option Nat → String
  | none => "R"
  | some value => toString value

private def displayVerdict : Option Bool → String
  | none => "U"
  | some true => "T"
  | some false => "F"

def main : IO Unit := do
  for n in [:1024] do
    let node := (11 * n + 2) % 28
    let fuel := n % 11
    let probe := (13 * n + 7) % 32
    let blocks := syntheticBlocks n
    let store := syntheticStore n
    let roster := syntheticRoster n
    let boost := syntheticBoostRoot n
    let total := syntheticTotalActiveBalance n
    let trial := checkedDescends blocks probe node fuel
    let boostTrial := match boost with
      | none => "-"
      | some root => displayVerdict (checkedDescends blocks root node fuel)
    let base := weightWithCheckedAncestry store blocks node fuel roster none total
    let now := weightWithCheckedAncestry store blocks node fuel roster boost total
    let candidate : LatestMessage := ⟨n % 12 + 1, (19 * n + 1) % 37⟩
    let updated := updateStore store (n % 4) candidate (n % 5 != 0)
    let after := weightWithCheckedAncestry updated blocks node fuel roster boost total
    IO.println s!"{n}\t{node}\t{fuel}\t{displayVerdict trial}\t{boostTrial}\t{display base}\t{display now}\t{display after}"
