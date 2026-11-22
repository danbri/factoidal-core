import EthereumConsensus.ForkChoice.LatestMessage

/-! Deterministic, synthetic observations of the ACTUAL Lean helper.
    The independent oracle checks every output field and update decision.
    No input is a real signed attestation or cryptographic Root. -/

open EthereumConsensus.ForkChoice

private def fields : Option LatestMessage → String
  | none => "-1\t-1"
  | some message => s!"{message.epoch}\t{message.root}"

def main : IO Unit := do
  for i in [:2048] do
    let previous : Option LatestMessage :=
      if i % 4 == 0 then none
      else some ⟨i % 29, (i * 7 + 5) % 65536⟩
    let equivocating := i % 7 == 0
    let epoch := if i % 5 == 0 then i % 29 else i % 31
    let candidate : LatestMessage := ⟨epoch, (i * 17 + 3) % 65536⟩
    let updated := updateLatest previous equivocating candidate
    IO.println s!"{i}\t{if equivocating then 1 else 0}\t{fields previous}\t{candidate.epoch}\t{candidate.root}\t{fields updated}"
