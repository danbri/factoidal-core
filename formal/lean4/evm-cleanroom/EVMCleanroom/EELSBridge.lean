import EVMCleanroom.Core

/-! # The precise Lean EVM obligation for an empty-code transaction frame

This only establishes that our interpreter's machine-level execution of
the empty bytecode is a zero-gas STOP and does not mutate its stack or memory.
The surrounding Ethereum transaction rules (EIP-7623 fee floor, signatures,
balances, nonces, trie roots) remain in the **unverified host** and must be
reviewed and independently checked. It is NOT an Ethereum state-transition
or Solidity compiler correctness proof.
-/

namespace EVMCleanroom

def emptyFrame (gas : Nat) : State :=
  { code := #[], gas := gas }

def haltedEmptyFrame (gas : Nat) : State :=
  { (emptyFrame gas) with pc := 1, halted := true }

/-- Empty EVM code halts in one interpreter step with gas unchanged.
    This is the machine property required by the restricted EELS
    no-contract-code executor; it is not full transaction correctness. -/
theorem empty_code_halts_without_spending_gas (gas : Nat) :
    run 1 (emptyFrame gas) = .ok (haltedEmptyFrame gas) := by
  rfl

theorem empty_code_preserves_machine_memory (gas : Nat) :
    (haltedEmptyFrame gas).memory.words = (emptyFrame gas).memory.words := by
  rfl

theorem empty_code_preserves_machine_stack (gas : Nat) :
    (haltedEmptyFrame gas).stack.items = (emptyFrame gas).stack.items := by
  rfl

#print axioms empty_code_halts_without_spending_gas
#print axioms empty_code_preserves_machine_memory
#print axioms empty_code_preserves_machine_stack

end EVMCleanroom
