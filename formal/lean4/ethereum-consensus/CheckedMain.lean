import EthereumConsensus.SSZ.CheckedBranch

/-! Emit executable Lean branch-admission and toy-fold observations. The
    independent Python checker derives both the branch length and fold
    result separately; neither implementation supplies real SHA-256. -/

private def toyPair (a b : Nat) : Nat := 5 * a + b

private def encodeResult : Option Nat → Int
  | none => -1
  | some n => Int.ofNat n

def main : IO Unit := do
  for index in [:1025] do
    let peers := List.replicate (EthereumConsensus.SSZ.depth index) (3 : Nat)
    let expectedLength := EthereumConsensus.SSZ.branchLength index
    let calculated := EthereumConsensus.SSZ.calculateBranch toyPair 7 peers index
    let malformed := EthereumConsensus.SSZ.calculateBranch toyPair 7 (peers ++ [3]) index
    IO.println s!"{index}\t{encodeResult expectedLength}\t{encodeResult calculated}\t{encodeResult malformed}"
