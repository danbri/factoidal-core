import EVMCleanroom.CallTransaction

/-!
# Transaction scope of EIP-1153 transient storage, and executable checks

Transient storage lives in the transaction world (`TxWorld.transient`), is
projected into each frame by `frameInput`, written back by `commitFrame`,
and saved in every CALL checkpoint. These theorems connect it to the actual
transaction entry (`CallTransaction.runWithBlobHashes` and `entryFrame`):
every transaction starts with all transient slots zero. `TransactionList`
builds each transaction's request through `CallTransaction.run`, so no
transient value crosses a transaction boundary. Rollback on REVERT or an
exceptional halt is `CallOpcode.resumeChild_failure_transient` for a child
and `CallOpcode.settle_parent_revert_atomic` (whole world) for the entry frame.

The `#guard` checks below run the real dispatcher; they are tests, not proofs.
-/

namespace EVMCleanroom.AccountTransient

open EVMCleanroom.World
open EVMCleanroom.CallTransaction

/-- Kind: transaction boundary (EIP-1153).
    Says: the world built for every admitted transaction has every transient
    slot of every account equal to zero.
    Does not say: the witnesses that build the rest of the world are authentic. -/
theorem witnessWorld_transient_empty (p : Request) (hashes : Array Word) :
    ({ witnessWorld p with txBlobHashes := hashes } : TxWorld).transient = fun _ _ => 0 := rfl

/-- Kind: preservation.
    Says: fee escrow and nonce advancement leave transient storage unchanged.
    Does not say: anything about balances. -/
theorem debitSender_transient (w : TxWorld) (sender : Nat) (budget : Budget) :
    (debitSender w sender budget).transient = w.transient := rfl

/-- Kind: preservation.
    Says: a successful value transfer leaves transient storage unchanged.
    Does not say: the transfer succeeds. -/
theorem pay_transient {w out : TxWorld} {sender recipient amount : Nat}
    (h : pay w sender recipient amount = .ok out) : out.transient = w.transient := by
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

/-- Kind: transaction boundary (EIP-1153), executable correspondence.
    Says: the top-level frame of every transaction that reaches execution
    through `runAdmitted` starts with all of its transient slots zero, because
    the escrow and the value transfer preserve the fresh world's empty map.
    Does not say: what the transaction does afterwards. -/
theorem entryFrame_transient_empty (p : Request) (hashes : Array Word) (budget : Budget)
    (entered : TxWorld)
    (hPay : pay (debitSender { witnessWorld p with txBlobHashes := hashes } p.tx.sender budget)
      p.tx.sender p.tx.to p.tx.value = .ok entered) (key : Nat) :
    (entryFrame p entered budget).storage.transient key = 0 := by
  have h := pay_transient hPay
  show entered.transient p.tx.to key = 0
  rw [h]
  rfl

/-- Kind: projection.
    Says: a frame sees exactly its own account's transient storage.
    Does not say: which instructions read it. -/
theorem frameInput_transient (w : TxWorld) (address gas : Nat) (readOnly : Bool) (profile : Profile)
    (origin caller : Nat) :
    (frameInput w address gas readOnly profile origin caller).storage.transient = w.transient address := rfl

/-- Kind: projection.
    Says: committing a frame writes back only that account's transient storage.
    Does not say: the frame was allowed to commit. -/
theorem commitFrame_transient (w : TxWorld) (address : Nat) (out : State) (other : Nat) :
    (commitFrame w address out).transient other =
      if other = address then out.storage.transient else w.transient other := rfl

#print axioms witnessWorld_transient_empty
#print axioms debitSender_transient
#print axioms pay_transient
#print axioms entryFrame_transient_empty
#print axioms frameInput_transient
#print axioms commitFrame_transient

/-- Kind: transaction boundary (EIP-2929, EIP-3651).
    Says: the initial access set of every admitted transaction is exactly the
    sender, the recipient, the coinbase, the fork's active precompiles
    (`Fork.precompiles`, the single definition) and the access-list addresses.
    Does not say: that the access list was validated. -/
theorem witnessWorld_warm_exact (p : Request) (hashes : Array Word) (address : Nat) :
    ({ witnessWorld p with txBlobHashes := hashes } : TxWorld).warmAddresses address =
      (address == p.tx.sender || address == p.tx.to || address == p.block.coinbase ||
        p.fork.precompiles.active address ||
        p.tx.accessList.any (fun entry => entry.address == address)) := rfl

/-- Kind: preservation.
    Says: a successful value transfer leaves the warm address set unchanged.
    Does not say: the transfer succeeds. -/
theorem pay_warmAddresses {w out : TxWorld} {sender recipient amount : Nat}
    (h : pay w sender recipient amount = .ok out) : out.warmAddresses = w.warmAddresses := by
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

/-- Kind: transaction boundary (EIP-2929), executable correspondence.
    Says: every active precompile of the transaction's fork is warm in the
    world the top-level frame starts in, after fee escrow and value transfer.
    Does not say: that the precompile is implemented (others refuse first). -/
theorem entry_precompiles_warm (p : Request) (hashes : Array Word) (budget : Budget)
    (entered : TxWorld)
    (hPay : pay (debitSender { witnessWorld p with txBlobHashes := hashes } p.tx.sender budget)
      p.tx.sender p.tx.to p.tx.value = .ok entered) (address : Nat)
    (hActive : p.fork.precompiles.active address = true) :
    entered.warmAddresses address = true := by
  rw [pay_warmAddresses hPay]
  show ({ witnessWorld p with txBlobHashes := hashes } : TxWorld).warmAddresses address = true
  rw [witnessWorld_warm_exact]
  simp [hActive]

#print axioms witnessWorld_warm_exact
#print axioms pay_warmAddresses
#print axioms entry_precompiles_warm

/-! ## Executable checks through the actual dispatcher (tests) -/

private def bytes (xs : List Nat) : Array UInt8 := (xs.map UInt8.ofNat).toArray

private def runAt (accounts : Nat → Account) (code : List Nat) (gas : Nat := 100000)
    (profile : Profile := .cancunPlus) : CallOpcode.Outcome :=
  let accounts' := fun a => if a = 0xc1 then { accounts a with code := bytes code } else accounts a
  let w := beginTransaction accounts'
  CallOpcode.settle w (frameInput w 0xc1 gas false profile 0xc2 0xc2)
    (CallOpcode.execute 200 w 0xc1 (frameInput w 0xc1 gas false profile 0xc2 0xc2))

private def top : CallOpcode.Outcome → Option (Nat × Nat)
  | .stopped _ s => s.stack.items.head?.map (fun x => (x.val, s.gas))
  | _ => none

private def fixture (a : Nat) : Account :=
  if a = 0xc3 then { balance := 77, code := bytes [0x00, 0x01] } else {}

-- BALANCE cold (2600) then warm (100) on the actual dispatcher.
#guard top (runAt fixture [0x60, 0xc3, 0x31, 0x00]) == some (77, 100000 - 3 - 2600)
#guard top (runAt fixture [0x60, 0xc3, 0x31, 0x50, 0x60, 0xc3, 0x31, 0x00]) ==
  some (77, 100000 - 3 - 2600 - 2 - 3 - 100)
-- EXTCODESIZE.
#guard top (runAt fixture [0x60, 0xc3, 0x3b, 0x00]) == some (2, 100000 - 3 - 2600)
-- TSTORE then TLOAD, 100 gas each.
#guard top (runAt fixture [0x60, 0x2a, 0x60, 0x01, 0x5d, 0x60, 0x01, 0x5c, 0x00]) ==
  some (42, 100000 - 3 - 3 - 100 - 3 - 100)
-- Cancun opcodes refuse on the profile that spans the Cancun boundary.
#guard match runAt fixture [0x5f, 0x5c, 0x00] 100000 .shanghaiPlus with
  | .indeterminate .unsupportedFork => true | _ => false
-- An underfunded TSTORE halts exceptionally.
#guard match runAt fixture [0x60, 0x2a, 0x60, 0x01, 0x5d] 105 with
  | .exceptional _ _ .outOfGas => true | _ => false
-- BLOCKHASH out of the window is zero for 20 gas.
#guard top (runAt fixture [0x60, 0x05, 0x40, 0x00]) == some (0, 100000 - 3 - 20)

end EVMCleanroom.AccountTransient
