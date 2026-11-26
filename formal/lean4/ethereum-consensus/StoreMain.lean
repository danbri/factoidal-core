import EthereumConsensus.ForkChoice.VoteStore

/-!
Deterministic sequential update trace from the actual Lean Store adapter.
Every before/after field is checked against a separate Python dictionary.
The Nat root is synthetic; no BLS/SSZ/authentication assertions are made.
-/

open EthereumConsensus.ForkChoice

private def initialStore : VoteStore := {
  latest := fun index =>
    if index = 0 then some ⟨4, 100⟩
    else if index = 2 then some ⟨6, 500⟩
    else none
  equivocating := fun index => decide (index = 2)
}

private def fields : Option LatestMessage → String
  | none => "-1\t-1"
  | some message => s!"{message.epoch}\t{message.root}"

def main : IO Unit := do
  let mut state := initialStore
  for i in [:1024] do
    let validator := i % 8
    let admitted := i % 11 != 0
    let candidate : LatestMessage :=
      ⟨if i % 5 == 0 then i % 7 else i / 8, (i * 17 + 3) % 65536⟩
    let old := state.latest validator
    let other := (validator + 1) % 8
    let otherOld := state.latest other
    let next := updateStore state validator candidate admitted
    IO.println s!"{i}\t{validator}\t{if admitted then 1 else 0}\t{if state.equivocating validator then 1 else 0}\t{candidate.epoch}\t{candidate.root}\t{fields old}\t{fields (next.latest validator)}\t{other}\t{fields otherOld}\t{fields (next.latest other)}"
    state := next
