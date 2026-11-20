import EVMCleanroom.World

/-!
# Bounded value-transfer primitive for future CALL/CREATE integration

A *separate, pure* account operation, not yet connected to EVM opcodes.
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
  | insufficientBalance
  | recipientOverflow
  deriving Repr, DecidableEq

def addressBound : Nat := 2 ^ 160

/-- This functional update is only used after checked transfer validity.
    Self-transfers are handled separately as an identity operation. -/
def payUnchecked (w : TxWorld) (from to amount : Nat) : TxWorld :=
  { w with
    accounts := fun a =>
      if a = from then
        { w.accounts from with balance := (w.accounts from).balance - amount }
      else if a = to then
        { w.accounts to with balance := (w.accounts to).balance + amount }
      else w.accounts a }

/-- Value conservation is an arithmetic theorem for any two distinct
    accounts, provided the sender can cover the debit. -/
theorem payUnchecked_conserves_pair (w : TxWorld) (from to amount : Nat)
    (hdiff : from ≠ to)
    (hfunded : amount ≤ (w.accounts from).balance) :
    ((payUnchecked w from to amount).accounts from).balance +
      ((payUnchecked w from to amount).accounts to).balance =
        (w.accounts from).balance + (w.accounts to).balance := by
  simp [payUnchecked, hdiff, Ne.symm hdiff]
  omega

/-- Account balances cannot change a third-party address. -/
theorem payUnchecked_other (w : TxWorld) (from to other amount : Nat)
    (hf : other ≠ from) (ht : other ≠ to) :
    (payUnchecked w from to amount).accounts other =
      w.accounts other := by
  simp [payUnchecked, hf, ht]

theorem payUnchecked_preserves_original (w : TxWorld)
    (from to amount address key : Nat) :
    (payUnchecked w from to amount).original address key =
      w.original address key := rfl

/-- A rejected transfer carries no modified World result.
    A self-transfer leaves account state unchanged after checking funds. -/
def pay (w : TxWorld) (from to amount : Nat) : Except TransferError TxWorld :=
  if from ≥ addressBound || to ≥ addressBound then .error .invalidAddress
  else if amount > (w.accounts from).balance then .error .insufficientBalance
  else if from = to then .ok w
  else if (w.accounts to).balance + amount ≥ modulus then
    .error .recipientOverflow
  else .ok (payUnchecked w from to amount)

/-- Successful transfers cannot change the snapshot of transaction-original
    storage for any address and key (including both transfer participants). -/
theorem pay_preserves_original {w out : TxWorld} {from to amount : Nat}
    (h : pay w from to amount = .ok out) (address key : Nat) :
    out.original address key = w.original address key := by
  unfold pay at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  · cases h
    rfl
  · split at h <;> try contradiction
    cases h
    rfl

#print axioms payUnchecked_conserves_pair
#print axioms payUnchecked_other
#print axioms payUnchecked_preserves_original
#print axioms pay_preserves_original

end EVMCleanroom.World
