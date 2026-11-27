import EVMCleanroom.ValueCall

/-!
# World-reading account instructions: BALANCE, EXTCODESIZE, EXTCODECOPY, EXTCODEHASH

These four instructions read another account from the transaction world and
price the access under EIP-2929: 100 gas if the address is already in the
transaction's accessed set, otherwise 2600 gas, after which the address is
warm for the rest of the enclosing frame (and for its caller only if the
frame succeeds, because the warm set lives in the checkpointed world).

Normative reference: ethereum/execution-specs, `forks/cancun/vm/instructions/
environment.py` (`balance`, `extcodesize`, `extcodecopy`, `extcodehash`), and
`forks/prague` for the same rules after EIP-7702 (the EXTCODE* instructions
read a delegation designator as ordinary code).

`accountStep` is called by the world-aware dispatcher in `CallOpcode.lean`;
it returns the world with the target warmed and the committed frame state.
The coarse `preShanghai` profile spans the Tangerine Whistle, Istanbul and
Berlin repricings, so it refuses rather than guess a price.
-/

namespace EVMCleanroom.AccountOpcode

open EVMCleanroom.World

/-- EIP-2929: GAS_WARM_ACCESS or GAS_COLD_ACCOUNT_ACCESS. -/
def accessCost (warm : Bool) : Nat := if warm then 100 else 2600

/-- EIP-1052 after EIP-161: an empty account (no code, zero nonce and
    balance) has code hash zero; otherwise the Keccak-256 of its code. -/
def codeHash (acceptance : Keccak.Acceptance) (account : Account) : Nat :=
  if CallValue.accountAlive account then
    Keccak.experimentalDigestWord acceptance (ByteView.ofArray account.code)
  else 0

/-- EXTCODECOPY gas: access, 3 per copied word and memory expansion.
    Since Berlin the old 700-gas base is replaced by the access charge. -/
def extCodeCopyCost (warm : Bool) (oldWords memOffset size : Nat) : Nat :=
  accessCost warm + 3 * ((size + 31) / 32) + MemoryGas.accessCost oldWords memOffset size

/-- Operands decoded in EVM pop order before any account is read. -/
inductive Operands where
  | single (target : Nat) (rest : List Word)
  | copy (target memOffset codeOffset size : Nat) (rest : List Word)

def decode (opcode : Nat) (stack : List Word) : Option Operands :=
  if opcode == 0x3c then
    match stack with
    | t :: m :: c :: z :: rest => some (.copy (t.val % addressBound) m.val c.val z.val rest)
    | _ => none
  else
    match stack with
    | t :: rest => some (.single (t.val % addressBound) rest)
    | [] => none

def Operands.target : Operands → Nat
  | .single t _ => t
  | .copy t _ _ _ _ => t

/-- The single-word result of BALANCE, EXTCODESIZE or EXTCODEHASH. -/
def wordResult (s : State) (opcode : Nat) (account : Account) : Except Error Word :=
  if opcode == 0x31 then .ok (word account.balance)
  else if opcode == 0x3b then .ok (word account.code.size)
  else
    match s.keccakAcceptance with
    | none => .error .unsupportedFork
    | some acceptance =>
      if Keccak.maxInputBytes < account.code.size then .error .resourceLimit
      else .ok (word (codeHash acceptance account))

/-- The committed frame state of one account instruction, before the
    world's warm set is updated. -/
def accountCommit (w : TxWorld) (s : State) (opcode : Nat) : Operands → Except Error State
  | .single target rest =>
    let account := w.accounts target
    match wordResult s opcode account with
    | .error e => .error e
    | .ok result => commit s (s.pc + 1) (result :: rest) (accessCost (w.warmAddresses target))
  | .copy target memOffset codeOffset size rest =>
    let cost := extCodeCopyCost (w.warmAddresses target) s.memory.words memOffset size
    if s.gas < cost then .error .outOfGas
    else
      let memory := (s.memory.expand (MemoryGas.requestedWords memOffset size)).copyFrom
        (ByteView.ofArray (w.accounts target).code) codeOffset memOffset size
      commit s (s.pc + 1) rest cost false (some memory)

/-- Execute one of 0x31, 0x3b, 0x3c, 0x3f in the active frame. Failure
    leaves the world unchanged; the frame then halts exceptionally and its
    checkpoint discards the frame's own warm-ups. -/
def accountStep (w : TxWorld) (s : State) (opcode : Nat) : Except Error (TxWorld × State) :=
  if s.profile = .preShanghai then .error .unsupportedFork
  else
    match decode opcode s.stack.items with
    | none => .error .stackUnderflow
    | some ops =>
      if !w.hasAccount ops.target then .error (.incompleteState ops.target none)
      else (accountCommit w s opcode ops).map (WorldCall.warmTarget w ops.target, ·)

/-- Kind: executable correspondence (gas schedule).
    Says: BALANCE of a covered address pushes its world balance and charges
    exactly 100 gas if warm and 2600 if cold, then the address is warm.
    Does not say: the balance was authenticated against a state root. -/
theorem accountStep_balance (w : TxWorld) (s : State) (t : Word) (rest : List Word)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true) :
    accountStep w s 0x31 =
      (commit s (s.pc + 1) (word (w.accounts (t.val % addressBound)).balance :: rest)
        (if w.warmAddresses (t.val % addressBound) then 100 else 2600)).map
        (WorldCall.warmTarget w (t.val % addressBound), ·) := by
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, wordResult, accessCost] <;> rfl

/-- Kind: executable correspondence (gas schedule).
    Says: EXTCODESIZE pushes the code length of the covered target at the
    same EIP-2929 price as BALANCE.
    Does not say: anything about a code-size limit for supplied accounts. -/
theorem accountStep_extCodeSize (w : TxWorld) (s : State) (t : Word) (rest : List Word)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true) :
    accountStep w s 0x3b =
      (commit s (s.pc + 1) (word (w.accounts (t.val % addressBound)).code.size :: rest)
        (if w.warmAddresses (t.val % addressBound) then 100 else 2600)).map
        (WorldCall.warmTarget w (t.val % addressBound), ·) := by
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, wordResult, accessCost] <;> rfl

/-- Kind: executable correspondence.
    Says: EXTCODEHASH of an empty covered account pushes zero (EIP-1052 with
    EIP-161 emptiness), at the EIP-2929 access price.
    Does not say: the experimental Keccak is proved equal to Keccak-256. -/
theorem accountStep_extCodeHash_empty (w : TxWorld) (s : State) (t : Word) (rest : List Word)
    (acceptance : Keccak.Acceptance)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true)
    (hAccept : s.keccakAcceptance = some acceptance)
    (hEmpty : CallValue.accountAlive (w.accounts (t.val % addressBound)) = false) :
    accountStep w s 0x3f =
      (commit s (s.pc + 1) (word 0 :: rest)
        (if w.warmAddresses (t.val % addressBound) then 100 else 2600)).map
        (WorldCall.warmTarget w (t.val % addressBound), ·) := by
  have hSize : ¬ Keccak.maxInputBytes < (w.accounts (t.val % addressBound)).code.size := by
    unfold CallValue.accountAlive at hEmpty
    simp at hEmpty
    simp [hEmpty.2, Keccak.maxInputBytes]
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, wordResult, accessCost,
    hAccept, hSize, codeHash, hEmpty] <;> rfl

/-- Kind: admission.
    Says: EXTCODEHASH refuses (indeterminate) without the explicit opt-in to
    the experimental Keccak implementation; it never returns a guessed hash.
    Does not say: the instruction is invalid on Ethereum. -/
theorem accountStep_extCodeHash_disabled (w : TxWorld) (s : State) (t : Word) (rest : List Word)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true)
    (hAccept : s.keccakAcceptance = none) :
    accountStep w s 0x3f = .error .unsupportedFork := by
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, wordResult, hAccept, Except.map]

/-- Kind: executable correspondence (gas schedule).
    Says: a funded EXTCODECOPY charges access + 3/word + expansion, copies the
    target code (zero-padded) into the expanded window and warms the target.
    Does not say: the code bytes were authenticated against a code hash. -/
theorem accountStep_extCodeCopy (w : TxWorld) (s : State) (t m c z : Word) (rest : List Word)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: m :: c :: z :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true)
    (hGas : extCodeCopyCost (w.warmAddresses (t.val % addressBound)) s.memory.words m.val z.val ≤ s.gas) :
    accountStep w s 0x3c =
      (commit s (s.pc + 1) rest
        (extCodeCopyCost (w.warmAddresses (t.val % addressBound)) s.memory.words m.val z.val) false
        (some ((s.memory.expand (MemoryGas.requestedWords m.val z.val)).copyFrom
          (ByteView.ofArray (w.accounts (t.val % addressBound)).code) c.val m.val z.val))).map
        (WorldCall.warmTarget w (t.val % addressBound), ·) := by
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, Nat.not_lt_of_ge hGas]

/-- Kind: gas boundary.
    Says: an underfunded EXTCODECOPY is out of gas and returns no world, so
    the target is not warmed by the failed instruction.
    Does not say: which other checks come later. -/
theorem accountStep_extCodeCopy_outOfGas (w : TxWorld) (s : State) (t m c z : Word) (rest : List Word)
    (hProfile : s.profile ≠ .preShanghai) (hStack : s.stack.items = t :: m :: c :: z :: rest)
    (hCovered : w.hasAccount (t.val % addressBound) = true)
    (hGas : s.gas < extCodeCopyCost (w.warmAddresses (t.val % addressBound)) s.memory.words m.val z.val) :
    accountStep w s 0x3c = .error .outOfGas := by
  simp [accountStep, accountCommit, hProfile, decode, hStack, Operands.target, hCovered, hGas, Except.map]

/-- Kind: boundary.
    Says: an address outside the supplied witness coverage is a refusal
    naming that address, never a read of a defaulted zero account.
    Does not say: the account is absent from the real state. -/
theorem accountStep_uncovered (w : TxWorld) (s : State) (opcode : Nat) (ops : Operands)
    (hProfile : s.profile ≠ .preShanghai) (hDecode : decode opcode s.stack.items = some ops)
    (hMissing : w.hasAccount ops.target = false) :
    accountStep w s opcode = .error (.incompleteState ops.target none) := by
  simp [accountStep, hProfile, hDecode, hMissing]

/-- Kind: fork admission.
    Says: the coarse pre-Shanghai profile refuses all four instructions.
    Does not say: the instructions are absent on those forks. -/
theorem accountStep_preShanghai (w : TxWorld) (s : State) (opcode : Nat)
    (hProfile : s.profile = .preShanghai) : accountStep w s opcode = .error .unsupportedFork := by
  simp [accountStep, hProfile]

/-- Kind: invariant.
    Says: every successful account instruction changes the world only by
    warming its target; balances, code, storage and transient storage of every
    account are unchanged.
    Does not say: the committed frame state is the only state change. -/
theorem accountStep_world (w w' : TxWorld) (s s' : State) (opcode : Nat)
    (h : accountStep w s opcode = .ok (w', s')) :
    ∃ target, w' = WorldCall.warmTarget w target := by
  unfold accountStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · next ops _ =>
      split at h
      · cases h
      · cases hc : accountCommit w s opcode ops with
        | error e => simp [hc, Except.map] at h
        | ok st =>
          simp [hc, Except.map] at h
          exact ⟨ops.target, h.1.symm⟩

#print axioms accountStep_balance
#print axioms accountStep_extCodeSize
#print axioms accountStep_extCodeHash_empty
#print axioms accountStep_extCodeHash_disabled
#print axioms accountStep_extCodeCopy
#print axioms accountStep_extCodeCopy_outOfGas
#print axioms accountStep_uncovered
#print axioms accountStep_preShanghai
#print axioms accountStep_world

end EVMCleanroom.AccountOpcode
