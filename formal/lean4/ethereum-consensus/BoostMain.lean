import EthereumConsensus.ForkChoice.ProposerScore

/-!
Source-observed computed proposer-score cases. The independent Python oracle
does not import or evaluate Lean. Modular ancestry is a synthetic stand-in,
not a verified beacon block DAG. No signature or checkpoint witness is read.
-/

open EthereumConsensus.ForkChoice

private def syntheticAncestor (supported node : Nat) : Bool :=
  supported % 7 == node % 7

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
  if n % 3 == 0 then none else some ((5 * n + 3) % 37)

private def syntheticTotalActiveBalance (n : Nat) : Nat :=
  if n % 127 == 0 then 80
  else if n % 17 == 0 then n % 101
  else 1000000000 + (n % 41) * 123456789

private def display : Option Nat → String
  | none => "R"
  | some x => toString x

def main : IO Unit := do
  for n in [:1024] do
    let node := (11 * n + 2) % 37
    let store := syntheticStore n
    let roster := syntheticRoster n
    let root := syntheticBoostRoot n
    let total := syntheticTotalActiveBalance n
    let base := attestationScore store syntheticAncestor node roster
    let actual := weightWithComputedBoost store syntheticAncestor node roster root total
    let candidate : LatestMessage := ⟨n % 12 + 1, (19 * n + 1) % 37⟩
    let updated := updateStore store (n % 4) candidate (n % 5 != 0)
    let after := weightWithComputedBoost updated syntheticAncestor node roster root total
    IO.println s!"{n}\t{total}\t{computeProposerScore total}\t{display base}\t{display actual}\t{display after}"
