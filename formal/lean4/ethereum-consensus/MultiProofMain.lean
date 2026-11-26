import EthereumConsensus

/-! Emit real Lean helper-index results, including refused inputs, for the
    independent Python reference. These rows test positional derivation only. -/

open EthereumConsensus.SSZ

private def caseFor (i : Nat) : List Nat :=
  match i % 13 with
  | 0 => []
  | 1 => [0, 2 + i % 32]
  | 2 => [1, 2 + i % 32]
  | 3 => [2 + i % 40, 2 + i % 40]
  | 4 => [2, 4]
  | 5 => [4, 5]
  | 6 => [4, 6]
  | 7 => [2, 3]
  | 8 => [4]
  | 9 => [2 + i % 128, 2 + ((i * 7 + 3) % 128)]
  | 10 => [2 ^ 65 + i]
  | 11 => [2, 3, 4, 5, 6]
  | _ => [2 + i % 80, 3 + ((i * 5) % 80), 4 + ((i * 11) % 80)]

private def csv (xs : List Nat) : String :=
  String.intercalate "," (xs.map toString)

private def answer : Option (List Nat) → String
  | none => "reject"
  | some xs => "ok:" ++ csv xs

def main : IO Unit := do
  for i in [:2048] do
    let claims := caseFor i
    IO.println s!"{csv claims}\t{answer (checkedHelpers 4 64 claims)}"
