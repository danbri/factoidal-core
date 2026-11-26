import EthereumConsensus.ForkChoice.AttestationScore

/-! Source-observed LMD attestation score, refusal and proposer-boost cases.
    The independent Python program derives these results separately.
    Synthetic modulo arithmetic is only a stand-in for authenticated ancestry. -/

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

private def syntheticBoost (n : Nat) : Option (Nat × Nat) :=
  if n % 3 == 0 then none
  else some ((5 * n + 3) % 37, n % 17)

private def display : Option Nat → String
  | none => "R"
  | some n => toString n

def main : IO Unit := do
  for n in [:1024] do
    let node := (11 * n + 2) % 37
    let store := syntheticStore n
    let roster := syntheticRoster n
    let boost := syntheticBoost n
    let first := attestationScore store syntheticAncestor node roster
    let total := weight store syntheticAncestor node roster boost
    let candidate : LatestMessage :=
      ⟨n % 12 + 1, (19 * n + 1) % 37⟩
    let updated := updateStore store (n % 4) candidate (n % 5 != 0)
    let after := weight updated syntheticAncestor node roster boost
    IO.println s!"{n}\t{display first}\t{display total}\t{display after}"
