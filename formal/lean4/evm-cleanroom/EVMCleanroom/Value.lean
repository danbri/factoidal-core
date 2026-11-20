import EVMCleanroom.World

/-!
# Bounded value-transfer primitive for future CALL/CREATE integration

A *separate, pure* account operation, not yet connected recipient EVM opcodes.
Addresses and balance arithmetic are validated before any state mutation.
No gas stipends, CALL 63/64 gas forwarding, EIP-2929 address warming,
static-mode restrictions or contract creation are implied.

Ethereum addresses are 160 bits; account balances are 256-bit quantities.
A valid transfer changes precisely two distinct balances and does not
mutate storage, nonces, code or transaction-original snapshots.
-/

namespace EVMCleanroom.World

inductive TransferError where
  | invalidAddress
  | invalidBalance
  | insufficientBalance
  | recipientOverflow
  deriving Repr, DecidableEq

def addressBound : Nat := 2 ^ 160

/-- This functional update is only used after checked transfer validity.
    Self-transfers are handled separately as an identity operation. -/
def payUnchecked (w : TxWorld) (sender recipient amount : Nat) : TxWorld :=
  { w with
    accounts := fun a =>
      if a = sender then
        { w.accounts sender with balance := (w.accounts sender).balance - amount }
      else if a = recipient then
        { w.accounts recipient with balance := (w.accounts recipient).balance + amount }
      else w.accounts a }

/-- Value conservation is an arithmetic theorem for any two distinct
    accounts, provided the sender can cover the debit. -/
theorem payUnchecked_conserves_pair (w : TxWorld) (sender recipient amount : Nat)
    (hdiff : sender ≠ recipient)
    (hfunded : amount ≤ (w.accounts sender).balance) :
    ((payUnchecked w sender recipient amount).accounts sender).balance +
      ((payUnchecked w sender recipient amount).accounts recipient).balance =
        (w.accounts sender).balance + (w.accounts recipient).balance := by
  simp [payUnchecked, hdiff, Ne.symm hdiff]
  omega

/-- Account balances cannot change a third-party address. -/
theorem payUnchecked_other (w : TxWorld) (sender recipient other amount : Nat)
    (hf : other ≠ sender) (ht : other ≠ recipient) :
    (payUnchecked w sender recipient amount).accounts other =
      w.accounts other := by
  simp [payUnchecked, hf, ht]

theorem payUnchecked_preserves_original (w : TxWorld)
    (sender recipient amount address key : Nat) :
    (payUnchecked w sender recipient amount).original address key =
      w.original address key := rfl

/-- A rejected transfer carries no modified World result.
    A self-transfer leaves account state unchanged after checking funds. -/
def pay (w : TxWorld) (sender recipient amount : Nat) : Except TransferError TxWorld :=
  if sender ≥ addressBound || recipient ≥ addressBound then .error .invalidAddress
  else if (w.accounts sender).balance ≥ modulus ||
          (w.accounts recipient).balance ≥ modulus then .error .invalidBalance
  else if amount > (w.accounts sender).balance then .error .insufficientBalance
  else if sender = recipient then .ok w
  else if (w.accounts recipient).balance + amount ≥ modulus then
    .error .recipientOverflow
  else .ok (payUnchecked w sender recipient amount)

/-- Successful transfers cannot change the snapshot of transaction-original
    storage for any address and key (including both transfer participants). -/
theorem pay_preserves_original {w out : TxWorld} {sender recipient amount : Nat}
    (h : pay w sender recipient amount = .ok out) (address key : Nat) :
    out.original address key = w.original address key := by
  unfold pay at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  · cases h
    rfl
  · split at h <;> try contradiction
    cases h
    rfl

/-- Every *accepted, checked* two-account transfer conserves the combined
    balance. Self-transfers are exact identity transitions. This theorem
    applies to the public pay operation, not merely payUnchecked. -/
theorem pay_conserves_pair {w out : TxWorld} {sender recipient amount : Nat}
    (h : pay w sender recipient amount = .ok out) :
    (out.accounts sender).balance + (out.accounts recipient).balance =
      (w.accounts sender).balance + (w.accounts recipient).balance := by
  unfold pay at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  · cases h
    rfl
  · split at h <;> try contradiction
    cases h
    apply payUnchecked_conserves_pair
    · omega
    · omega

#print axioms pay_conserves_pair

#print axioms payUnchecked_conserves_pair
#print axioms payUnchecked_other
#print axioms payUnchecked_preserves_original
#print axioms pay_preserves_original

end EVMCleanroom.World
