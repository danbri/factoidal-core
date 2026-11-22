import EVMCleanroom.Frame

/-!
# Transaction-scoped multi-account state and per-account frame isolation

Each account has independent storage, code, balance and nonce. A transaction
records the original values of all storage slots before any frame is run.
Account and slot warmth and the refund counter are transaction-scoped.
`frameInput` projects the current account's journal into an interpreter
frame, while `commitFrame` writes its current storage, warmth and refund
back. The world-aware CALL dispatcher uses these operations at suspension
and resumption boundaries. The standalone `runAt` runs one frame and
commits only on success. The world is a functional journal without trie
authentication.
-/

namespace EVMCleanroom.World

structure Account where
  balance : Nat := 0
  nonce : Nat := 0
  code : Array UInt8 := #[]
  storage : Nat → Nat := fun _ => 0

/-- Original storage is captured once at the transaction boundary, not at
    the beginning of each subsequent execution frame. -/
structure TxWorld where
  accounts : Nat → Account
  original : Nat → Nat → Nat
  warmSlots : Nat → Nat → Bool := fun _ _ => false
  warmAddresses : Nat → Bool := fun _ => false
  refund : Int := 0
  /-- The chain identifier supplied by a selected chain environment. Not a
      signed-transaction or consensus-authenticated datum in this model. -/
  chainId : Nat := 0

def beginTransaction (accounts : Nat → Account) : TxWorld :=
  { accounts := accounts
    original := fun address slot => (accounts address).storage slot }

/-- Project one account's transaction-scoped storage into Frame.run. -/
def frameInput (w : TxWorld) (address gas : Nat)
    (readOnly : Bool := false) (profile : Profile := .shanghaiPlus)
    (originAddress : Nat := 0) (callerAddress : Nat := 0) : State :=
  { code := (w.accounts address).code
    gas := gas
    currentAddress := address
    txOrigin := originAddress
    chainId := w.chainId
    callerAddress := callerAddress
    callValue := 0
    selfBalance := (w.accounts address).balance
    readOnly := readOnly
    profile := profile
    storage := {
      original := w.original address
      current := (w.accounts address).storage
      warm := w.warmSlots address
      refund := w.refund
    } }

/-- The executing address and its pre-instruction balance come from the
    supplied transaction world. This is the actual executable projection
    consumed by the CALL context opcodes, not a detached specification. -/
theorem frameInput_address (w : TxWorld) (address gas : Nat) :
    (frameInput w address gas).currentAddress = address := rfl

theorem frameInput_balance (w : TxWorld) (address gas : Nat) :
    (frameInput w address gas).selfBalance =
      (w.accounts address).balance := rfl

/-- Actual frame entry reads the transaction world's chain selection.
    Nested CALL creates its child through this same projection. -/
theorem frameInput_chainId (w : TxWorld) (address gas : Nat)
    (readOnly : Bool) (profile : Profile) (originAddress callerAddress : Nat) :
    (frameInput w address gas readOnly profile originAddress callerAddress).chainId = w.chainId := rfl

theorem frameInput_value_zero (w : TxWorld) (address gas : Nat) :
    (frameInput w address gas).callValue = 0 := rfl

/-- Projection.
    Says: the executable frame receives the supplied static flag and opcode profile.
    Does not say: which opcode or fork rules the frame interpreter implements. -/
theorem frameInput_context (w : TxWorld) (address gas : Nat)
    (readOnly : Bool) (profile : Profile) :
    (frameInput w address gas readOnly profile).readOnly = readOnly ∧
    (frameInput w address gas readOnly profile).profile = profile :=
  ⟨rfl, rfl⟩

/-- World frame entry preserves explicitly supplied caller and transaction origin. -/
theorem frameInput_participants (w : TxWorld) (address gas : Nat)
    (readOnly : Bool) (profile : Profile) (originAddress callerAddress : Nat) :
    (frameInput w address gas readOnly profile originAddress callerAddress).txOrigin = originAddress ∧
    (frameInput w address gas readOnly profile originAddress callerAddress).callerAddress = callerAddress :=
  ⟨rfl, rfl⟩

#print axioms frameInput_address
#print axioms frameInput_chainId
#print axioms frameInput_participants
#print axioms frameInput_balance
#print axioms frameInput_value_zero
#print axioms frameInput_context

/-- Write a frame's storage journal to its account before child entry or
    after successful completion. The other accounts retain their records. -/
def commitFrame (w : TxWorld) (address : Nat) (out : State) : TxWorld :=
  let updated := { w.accounts address with storage := out.storage.current }
  { w with
    accounts := fun other => if other = address then updated else w.accounts other
    warmSlots := fun other key =>
      if other = address then out.storage.warm key else w.warmSlots other key
    refund := out.storage.refund }

/-- A result is not a transaction receipt or a block-state root. REVERT
    and exceptional halts deliberately return the unmodified pre-frame
    world and the interpreter's remaining gas. -/
inductive Outcome where
  | stopped (world : TxWorld) (gasRemaining : Nat)
  | returned (world : TxWorld) (gasRemaining offset length : Nat)
  | reverted (world : TxWorld) (gasRemaining offset length : Nat)
  | exceptional (world : TxWorld) (gasRemaining : Nat) (reason : Error)
  | unsupported (reason : Error)

def runAt (fuel : Nat) (world : TxWorld) (address gas : Nat)
    (readOnly : Bool := false) (profile : Profile := .shanghaiPlus) : Outcome :=
  match Frame.run fuel (frameInput world address gas readOnly profile) with
  | .stopped out => .stopped (commitFrame world address out) out.gas
  | .returned out offset length =>
      .returned (commitFrame world address out) out.gas offset length
  | .reverted out offset length =>
      .reverted world out.gas offset length
  | .exceptional out reason =>
      .exceptional world out.gas reason
  | .unsupported reason => .unsupported reason

/-- No account other than the executing account can be changed by
    committing a frame, regardless of its bytecode or storage updates. -/
theorem commitFrame_other_account (w : TxWorld) (address other : Nat)
    (out : State) (h : other ≠ address) :
    (commitFrame w address out).accounts other = w.accounts other := by
  simp [commitFrame, h]

/-- The current executing account cannot change its balance or nonce
    merely by running this storage-only frame. Value transfer is a
    distinct, not-yet-implemented operation. -/
theorem commitFrame_own_balance (w : TxWorld) (address : Nat)
    (out : State) :
    ((commitFrame w address out).accounts address).balance =
      (w.accounts address).balance := by
  simp [commitFrame]

theorem commitFrame_own_nonce (w : TxWorld) (address : Nat)
    (out : State) :
    ((commitFrame w address out).accounts address).nonce =
      (w.accounts address).nonce := by
  simp [commitFrame]

theorem commitFrame_own_code (w : TxWorld) (address : Nat)
    (out : State) :
    ((commitFrame w address out).accounts address).code =
      (w.accounts address).code := by
  simp [commitFrame]

/-- No number of intra-transaction writes can rewrite the original
    pre-transaction snapshot, even across different accounts. -/
theorem commitFrame_original (w : TxWorld) (address other key : Nat)
    (out : State) :
    (commitFrame w address out).original other key =
      w.original other key := rfl

theorem commitFrame_other_warmth (w : TxWorld) (address other key : Nat)
    (out : State) (h : other ≠ address) :
    (commitFrame w address out).warmSlots other key =
      w.warmSlots other key := by
  simp [commitFrame, h]

/-- Real Frame.run REVERT restores the *whole* world, not just the
    executing account; consequently the parent's already-committed
    account changes survive a failed child-like sequential frame. -/
theorem runAt_revert_world_unchanged (fuel : Nat) (w result : TxWorld)
    (address gas remaining offset length : Nat)
    (h : runAt fuel w address gas =
      .reverted result remaining offset length) :
    result = w := by
  cases hr : Frame.run fuel (frameInput w address gas) with
  | stopped s => simp [runAt, hr] at h
  | returned s off len => simp [runAt, hr] at h
  | reverted s off len =>
    have hc : Outcome.reverted w s.gas off len =
        Outcome.reverted result remaining offset length := by
      simpa [runAt, hr] using h
    injection hc with hw _ _ _
    exact hw.symm
  | exceptional s e => simp [runAt, hr] at h
  | unsupported e => simp [runAt, hr] at h

/-- Exceptional frame execution likewise preserves the entry world. -/
theorem runAt_exception_world_unchanged (fuel : Nat) (w result : TxWorld)
    (address gas remaining : Nat) (reason : Error)
    (h : runAt fuel w address gas =
      .exceptional result remaining reason) :
    result = w := by
  cases hr : Frame.run fuel (frameInput w address gas) with
  | stopped s => simp [runAt, hr] at h
  | returned s off len => simp [runAt, hr] at h
  | reverted s off len => simp [runAt, hr] at h
  | exceptional s e =>
    have hc : Outcome.exceptional w s.gas e =
        Outcome.exceptional result remaining reason := by
      simpa [runAt, hr] using h
    injection hc with hw _ _
    exact hw.symm
  | unsupported e => simp [runAt, hr] at h

#print axioms commitFrame_other_account
#print axioms commitFrame_own_balance
#print axioms commitFrame_own_nonce
#print axioms commitFrame_own_code
#print axioms commitFrame_original
#print axioms commitFrame_other_warmth
#print axioms runAt_revert_world_unchanged
#print axioms runAt_exception_world_unchanged

end EVMCleanroom.World
