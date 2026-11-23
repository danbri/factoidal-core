import EVMCleanroom.Call
import EVMCleanroom.ValueCall
import EVMCleanroom.Proofs
import EVMCleanroom.IdentityPrecompile

/-!
# World-aware execution of the EVM call family

CALL prices both memory windows before forwarding gas. A child reads its
input from the suspended caller's memory and executes through the same
world-aware dispatcher. On resumption the caller sees the full child output
and copies only the prefix that fits its output window.

Each caller journals its account before entering its child. The target
address is warmed in that caller's scope, before the child checkpoint and
before value transfer. A child failure restores the checkpoint, including
successful descendant effects. The top-level checkpoint has the same boundary.
CALLCODE and DELEGATECALL use the target's code with the caller's account
journal. STATICCALL uses the target's account journal in a read-only child.

An explicit continuation stack bounds nested execution by Ethereum's depth
limit. Simulation fuel counts dispatched instructions across all frames.
Exhaustion and unsupported instructions yield an indeterminate result.
-/

namespace EVMCleanroom.CallOpcode

open EVMCleanroom.World

inductive CallStep where
  | committed (world : TxWorld) (parent : State)
  | exceptional (reason : Error)
  | indeterminate (reason : Error)

/-- Check the resumed caller's stack and remaining gas through Core.commit,
    then refresh its account journal from the child outcome's world. -/
private def finishCall (parentAddress : Nat) (parent : State) (rest : List Word)
    (out : TxWorld) (remaining : Nat) (succeeded : Bool) : CallStep :=
  if remaining ≤ parent.gas then
    match commit parent (parent.pc + 1)
        (word (if succeeded then 1 else 0) :: rest)
        (parent.gas - remaining) with
    | .ok state =>
      .committed out
        { state with
          selfBalance := (out.accounts parentAddress).balance
          logsRev := out.logsRev
          storage := {
            current := (out.accounts parentAddress).storage
            original := parent.storage.original
            warm := out.warmSlots parentAddress
            refund := out.refund } }
    | .error e => .exceptional e
  else .indeterminate .unsupportedFork

/-- Projection.
    Says: continuation after a child outcome reads the caller's account
    state from the resulting world, while keeping transaction-original storage.
    Does not say: whether the child outcome itself commits or rolls back. -/
theorem finishCall_state_projection (parentAddress : Nat) (parent resumed : State)
    (rest : List Word) (out world : TxWorld) (remaining : Nat) (succeeded : Bool)
    (h : finishCall parentAddress parent rest out remaining succeeded =
      .committed world resumed) :
    resumed.selfBalance = (world.accounts parentAddress).balance ∧
    resumed.storage.current = (world.accounts parentAddress).storage ∧
    resumed.storage.original = parent.storage.original ∧
    resumed.storage.warm = world.warmSlots parentAddress ∧
    resumed.storage.refund = world.refund := by
  unfold finishCall at h
  split at h
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

/-- Kind: projection.
    Says: the resumed caller receives the selected child's resulting log journal.
    Does not say: that a later caller failure will keep those logs. -/
theorem finishCall_logs_projection (parentAddress : Nat) (parent resumed : State)
    (rest : List Word) (out world : TxWorld) (remaining : Nat) (succeeded : Bool)
    (h : finishCall parentAddress parent rest out remaining succeeded =
      .committed world resumed) : resumed.logsRev = world.logsRev := by
  unfold finishCall at h
  split at h
  · split at h <;> cases h
    rfl
  · cases h

/-- Preservation.
    Says: committing the resumed caller preserves the resulting world if no
    intervening instruction changes the caller's journal.
    Does not say: that an eventual caller REVERT retains child changes. -/
theorem finishCall_commit_preserves_world (parentAddress : Nat) (parent resumed : State)
    (rest : List Word) (out world : TxWorld) (remaining : Nat) (succeeded : Bool)
    (h : finishCall parentAddress parent rest out remaining succeeded =
      .committed world resumed) :
    commitFrame world parentAddress resumed = world := by
  obtain ⟨_, current, _, warm, refund⟩ :=
    finishCall_state_projection parentAddress parent resumed rest out world remaining succeeded h
  have logs := finishCall_logs_projection parentAddress parent resumed rest out world remaining succeeded h
  unfold commitFrame
  rw [current, warm, refund, logs]
  have accounts : (fun other => if other = parentAddress then
      { world.accounts parentAddress with storage := (world.accounts parentAddress).storage }
      else world.accounts other) = world.accounts := by
    funext other
    by_cases hOther : other = parentAddress
    · subst other
      simp
    · simp [hOther]
  have warmSlots : (fun other key => if other = parentAddress then
      world.warmSlots parentAddress key else world.warmSlots other key) = world.warmSlots := by
    funext other key
    by_cases hOther : other = parentAddress
    · subst other
      simp
    · simp [hOther]
  dsimp only
  rw [accounts, warmSlots]

/-- Unbounded offsets and sizes, so their sum cannot wrap modulo 2^256. -/
structure Windows where
  inputOffset : Nat
  inputSize : Nat
  outputOffset : Nat
  outputSize : Nat

/-- The maximum demand of the two ranges, before accounting for the
    caller's existing allocation. -/
def Windows.words (ranges : Windows) : Nat :=
  max (MemoryGas.requestedWords ranges.inputOffset ranges.inputSize)
    (MemoryGas.requestedWords ranges.outputOffset ranges.outputSize)

structure Budget where
  childGas : Nat
  reserve : Nat

/-- Both memory ranges are priced before the EIP-150 cap, including when
    funds or depth prevent the child from being entered. -/
def schedule (parent : State) (ranges : Windows) (requested value : Nat)
    (wasWarm isAlive : Bool) : Except Error Budget :=
  let expansion := MemoryGas.expansion parent.memory.words ranges.words
  if parent.gas < expansion then .error .outOfGas
  else
    let available := parent.gas - expansion
    if value = 0 then
      (CallGas.schedule available requested wasWarm).map fun b => ⟨b.forwarded, b.reserve⟩
    else
      (CallValue.schedule available requested wasWarm isAlive).map fun b => ⟨b.childGas, b.reserve⟩

/-- The terminal memory window is in `State.outputData`. The prior child
    buffer remains in `State.returnData`. The wrapper installs the entry
    world on REVERT or an exceptional halt. -/
inductive RawOutcome where
  | stopped (world : TxWorld) (parent : State)
  | returned (world : TxWorld) (parent : State)
  | reverted (parent : State)
  | exceptional (reason : Error)
  | indeterminate (reason : Error)

/-- Only designated INVALID (0xfe) is classified as definitely exceptional.
    Other unknown opcodes can be valid EVM instructions absent in this slice. -/
def stepError (e : Error) : RawOutcome :=
  match e with
  | .unsupportedFork | .stepLimit | .framePolicyViolation _
  | .resourceLimit | .incompleteState _ _ => .indeterminate e
  | .invalidOpcode b =>
      if b == 0xfe then .exceptional e else .indeterminate e
  | _ => .exceptional e

/-- Entry depth 0 allows child depths through 1024, as in EELS. -/
def maxDepth : Nat := 1024

/-- Only identity (0x04) is currently executable in the actual world-aware
    CALL family. All other reserved precompile addresses still refuse. -/
def unimplementedPrecompile (profile : Profile) (target : Nat) : Bool :=
  WorldCall.unsupportedPrecompile profile target && target != 4

/-- A local memory policy, not a fork rule or transaction-validity limit. -/
def maxIdentityCallBytes : Nat := 1_048_576

structure ActiveFrame where
  world : TxWorld
  address : Nat
  depth : Nat
  state : State

structure Continuation where
  address : Nat
  depth : Nat
  parent : State
  rest : List Word
  checkpoint : TxWorld
  budget : Budget
  ranges : Windows

inductive CallEntry where
  | entered (child : ActiveFrame) (continuation : Continuation)
  | failed (continuation : Continuation)

/-- Evaluate the CALL setup before suspending the caller. Account storage,
    slot warmth and refunds are journalled before the child even when both
    frames share the same address. -/
def beginCall (active : ActiveFrame) : Except Error CallEntry :=
  let parent := active.state
  match parent.stack.items with
  | requested :: targetWord :: value :: inputOffset :: inputSize ::
      outputOffset :: outputSize :: rest =>
    let target := targetWord.val % addressBound
    let ranges : Windows := ⟨inputOffset.val, inputSize.val, outputOffset.val, outputSize.val⟩
    if !active.world.hasAccount target then .error (.incompleteState target none)
    else
      let alive := value.val != 0 && CallValue.accountAlive (active.world.accounts target)
      match schedule parent ranges requested.val value.val (active.world.warmAddresses target) alive with
      | .error e => .error e
      | .ok budget =>
        if parent.readOnly && value.val != 0 then .error .writeProtection
        else
          let callerWorld := commitFrame active.world active.address parent
          let checkpoint := WorldCall.warmTarget callerWorld target
          let memory := parent.memory.expand ranges.words
          let continuation : Continuation :=
            ⟨active.address, active.depth, { parent with memory, returnData := {} }, rest, checkpoint, budget, ranges⟩
          if value.val > (callerWorld.accounts active.address).balance || active.depth ≥ maxDepth then
            .ok (.failed continuation)
          else if unimplementedPrecompile parent.profile target then .error .unsupportedFork
          else
            let transfer := if value.val = 0 then .ok checkpoint else
              (pay checkpoint active.address target value.val).mapError fun _ => .unsupportedFork
            transfer.map fun childWorld =>
              let child := { frameInput childWorld target budget.childGas parent.readOnly parent.profile with
                callData := ByteView.ofMemory memory ranges.inputOffset ranges.inputSize
                callValue := value.val
                txOrigin := parent.txOrigin
                callerAddress := active.address }
              .entered ⟨childWorld, target, active.depth + 1, child⟩ continuation
  | _ => .error .stackUnderflow

/-- The call opcodes that enter a child without transferring value. -/
inductive CallVariant where
  | callCode
  | delegateCall
  | staticCall
  deriving DecidableEq

def CallVariant.opcode : CallVariant → Nat
  | .callCode => 0xf2
  | .delegateCall => 0xf4
  | .staticCall => 0xfa

structure VariantOperands where
  requestedGas : Nat
  codeAddress : Nat
  stackValue : Nat
  ranges : Windows
  rest : List Word

private def decodeVariantWindows (requested target : Word) (value : Nat) :
    List Word → Option VariantOperands
  | inputOffset :: inputSize :: outputOffset :: outputSize :: rest =>
    some ⟨requested.val, target.val % addressBound, value,
      ⟨inputOffset.val, inputSize.val, outputOffset.val, outputSize.val⟩, rest⟩
  | _ => none

/-- Only CALLCODE consumes a value operand. DELEGATECALL's inherited
    value is context for the child, with no gas surcharge or funds check. -/
def decodeVariant (kind : CallVariant) (stack : List Word) : Option VariantOperands :=
  match kind with
  | .callCode =>
    match stack with
    | requested :: target :: value :: rest => decodeVariantWindows requested target value.val rest
    | _ => none
  | .delegateCall | .staticCall =>
    match stack with
    | requested :: target :: rest => decodeVariantWindows requested target 0 rest
    | _ => none

/-- Report an uncovered code account, or an uncovered execution account
    for variants that execute in the caller's account. -/
private def missingVariantAccount (active : ActiveFrame) (kind : CallVariant)
    (codeAddress : Nat) : Option Nat :=
  if !active.world.hasAccount codeAddress then some codeAddress
  else if kind ≠ .staticCall ∧ !active.world.hasAccount active.address then some active.address
  else none

private def variantFrame (active : ActiveFrame) (kind : CallVariant)
    (args : VariantOperands) (k : Continuation) : ActiveFrame :=
  let parent := active.state
  let address := if kind = .staticCall then args.codeAddress else active.address
  let readOnly := parent.readOnly || decide (kind = .staticCall)
  let caller := if kind = .delegateCall then parent.callerAddress else active.address
  let value := match kind with
    | .callCode => args.stackValue
    | .delegateCall => parent.callValue
    | .staticCall => 0
  let child := { frameInput k.checkpoint address k.budget.childGas readOnly parent.profile parent.txOrigin caller with
    code := (k.checkpoint.accounts args.codeAddress).code
    callData := ByteView.ofMemory k.parent.memory args.ranges.inputOffset args.ranges.inputSize
    callValue := value }
  ⟨k.checkpoint, address, active.depth + 1, child⟩

private def prepareVariant (active : ActiveFrame) (kind : CallVariant)
    (args : VariantOperands) (budget : Budget) : Except Error CallEntry :=
  let parent := active.state
  let checkpoint := WorldCall.warmTarget (commitFrame active.world active.address parent) args.codeAddress
  let memory := parent.memory.expand args.ranges.words
  let continuation : Continuation :=
    ⟨active.address, active.depth, { parent with memory, returnData := {} },
      args.rest, checkpoint, budget, args.ranges⟩
  if active.depth ≥ maxDepth ∨
      (args.stackValue ≠ 0 ∧ args.stackValue > (checkpoint.accounts active.address).balance) then
    .ok (.failed continuation)
  else if unimplementedPrecompile parent.profile args.codeAddress then .error .unsupportedFork
  else .ok (.entered (variantFrame active kind args continuation) continuation)

/-- CALLCODE, DELEGATECALL and STATICCALL share the CALL continuation.
    CALLCODE's explicit value incurs the surcharge and stipend even in a
    read-only parent. Its balance check uses the executing account and it
    never incurs the new-account surcharge. -/
def beginVariant (active : ActiveFrame) (kind : CallVariant) : Except Error CallEntry :=
  if active.state.profile = .preShanghai then .error .unsupportedFork
  else
    match decodeVariant kind active.state.stack.items with
    | none => .error .stackUnderflow
    | some args =>
      match missingVariantAccount active kind args.codeAddress with
      | some address => .error (.incompleteState address none)
      | none =>
        match schedule active.state args.ranges args.requestedGas args.stackValue
            (active.world.warmAddresses args.codeAddress) true with
        | .error e => .error e
        | .ok budget => prepareVariant active kind args budget

/-- The caller owns the entire last-child buffer, and only its fitting
    prefix replaces bytes in the already expanded output window. -/
def applyOutput (parent : State) (ranges : Windows) (data : ByteView) : State :=
  { parent with
    returnData := data
    memory := parent.memory.copyFrom data 0 ranges.outputOffset (min ranges.outputSize data.size) }

/-- Return unused allotted gas and resume the suspended caller through Core.commit. -/
def resumeCall (k : Continuation) (world : TxWorld) (gas : Nat)
    (data : ByteView) (success : Bool) : CallStep :=
  if gas ≤ k.budget.childGas then
    finishCall k.address (applyOutput k.parent k.ranges data) k.rest
      world (k.budget.reserve + gas) success
  else .indeterminate .unsupportedFork

/-- Successful child outcomes keep the child's world. Failed outcomes
    return the caller's checkpoint and REVERT still returns its bytes. -/
def resumeChild (k : Continuation) : RawOutcome → CallStep
  | .stopped world s => resumeCall k world s.gas {} true
  | .returned world s => resumeCall k world s.gas s.outputData true
  | .reverted s => resumeCall k k.checkpoint s.gas s.outputData false
  | .exceptional _ => resumeCall k k.checkpoint 0 {} false
  | .indeterminate reason => .indeterminate reason

/-- Before child entry, a soft failure returns all allotted gas and clears
    the last-child buffer. No child instruction is dispatched. -/
def resumeFailedCall (k : Continuation) : CallStep :=
  resumeCall k k.checkpoint k.budget.childGas {} false

private inductive Transition where
  | next (active : ActiveFrame)
  | enter (child : ActiveFrame) (continuation : Continuation)
  | terminal (raw : RawOutcome)

private def afterCall (k : Continuation) : CallStep → Transition
  | .committed world s => .next ⟨world, k.address, k.depth, s⟩
  | .exceptional e => .terminal (.exceptional e)
  | .indeterminate e => .terminal (.indeterminate e)

/-- The stack on the suspended caller retains the code target for every
    CALL-family variant (requested gas, target, then its other operands). -/
def Continuation.codeTarget (k : Continuation) : Nat :=
  match k.parent.stack.items with
  | _ :: target :: _ => target.val % addressBound
  | _ => addressBound

/-- Resolve an already budgeted precompile entry without running account code.
    Both the opcode dispatcher and the public single-CALL adapter use this
    resolver. Success keeps any value transfer, while out-of-gas restores the
    checkpoint. A local resource refusal remains indeterminate. -/
private def precompileStep (child : ActiveFrame) (k : Continuation) : Option CallStep :=
  if k.codeTarget == 4 then
    some (match IdentityPrecompile.executeView maxIdentityCallBytes k.budget.childGas
        child.state.callData with
      | .ok (data, remaining) => resumeCall k child.world remaining data true
      | .error .outOfGas => resumeCall k k.checkpoint 0 {} false
      | .error reason => .indeterminate reason)
  else none

/-- Ordinary children enter the continuation stack; precompiles resolve
    through the shared native precompile handler. -/
private def dispatchCall : Except Error CallEntry → Transition
  | .error e => .terminal (stepError e)
  | .ok (.entered child k) =>
      match precompileStep child k with
      | some result => afterCall k result
      | none => .enter child k
  | .ok (.failed k) => afterCall k (resumeFailedCall k)

/-- Actual dispatch delegates the complete identity byte window and child gas
    to our native Lean precompile, then resumes the same caller continuation. -/
theorem dispatchCall_identity_exact (child : ActiveFrame) (k : Continuation)
    (bytes : ByteView) (remaining : Nat)
    (hTarget : k.codeTarget = 4)
    (hResult : IdentityPrecompile.executeView maxIdentityCallBytes k.budget.childGas
      child.state.callData = .ok (bytes, remaining)) :
    dispatchCall (.ok (.entered child k)) =
      afterCall k (resumeCall k child.world remaining bytes true) := by
  simp [dispatchCall, precompileStep, hTarget, hResult]

/-- An admitted but underfunded identity child loses its forwarded gas and
    its value transfer, while the parent continuation retains the checkpoint. -/
theorem dispatchCall_identity_outOfGas (child : ActiveFrame) (k : Continuation)
    (hTarget : k.codeTarget = 4)
    (hResult : IdentityPrecompile.executeView maxIdentityCallBytes k.budget.childGas
      child.state.callData = .error .outOfGas) :
    dispatchCall (.ok (.entered child k)) =
      afterCall k (resumeCall k k.checkpoint 0 {} false) := by
  simp [dispatchCall, precompileStep, hTarget, hResult]

/-- Resource refusal is not an EVM failure bit or a completed receipt. -/
theorem dispatchCall_identity_resourceLimit (child : ActiveFrame) (k : Continuation)
    (hTarget : k.codeTarget = 4)
    (hResult : IdentityPrecompile.executeView maxIdentityCallBytes k.budget.childGas
      child.state.callData = .error .resourceLimit) :
    dispatchCall (.ok (.entered child k)) = .terminal (.indeterminate .resourceLimit) := by
  simp [dispatchCall, precompileStep, afterCall, hTarget, hResult]

/-- The only storage-reading opcodes admitted by Core use the top word as key. -/
private def missingStorage (active : ActiveFrame) (opcode : Nat) : Option Nat :=
  match active.world.witnessed with
  | none => none
  | some coverage =>
    let key := match active.state.stack.items with
      | key :: _ :: _ =>
        if opcode == 0x54 ||
            (opcode == 0x55 && !active.state.readOnly && active.state.gas > 2300) then some key.val
        else none
      | [key] => if opcode == 0x54 then some key.val else none
      | [] => none
    key.filter (fun slot => !coverage.slot active.address slot)

private def dispatch (active : ActiveFrame) : Transition :=
  let s := active.state
  if s.halted then .terminal (.stopped active.world s)
  else
    let opcode := byteAt s s.pc
    if opcode == 0xf1 then
      dispatchCall (beginCall active)
    else if opcode == 0xf2 then
      dispatchCall (beginVariant active .callCode)
    else if opcode == 0xf4 then
      dispatchCall (beginVariant active .delegateCall)
    else if opcode == 0xfa then
      dispatchCall (beginVariant active .staticCall)
    else if opcode == 0xf3 || opcode == 0xfd then
      match Frame.haltWithData s with
      | .error e => .terminal (stepError e)
      | .ok (terminal, _, _) =>
        if opcode == 0xfd then .terminal (.reverted terminal)
        else .terminal (.returned (commitFrame active.world active.address terminal) terminal)
    else
      match missingStorage active opcode with
      | some key => .terminal (.indeterminate (.incompleteState active.address (some key)))
      | none =>
        match step s with
        | .error e => .terminal (stepError e)
        | .ok next =>
          if next.halted then .terminal (.stopped (commitFrame active.world active.address next) next)
          else .next { active with state := next }

/-- The continuation stack is separate from the Lean call stack. One fuel
    unit is consumed per dispatch across the active frames, including implicit
    STOP at the end of code. -/
private def executeLoop : Nat → ActiveFrame → List Continuation → RawOutcome
  | 0, _, _ => .indeterminate .stepLimit
  | fuel + 1, active, callers =>
    match dispatch active with
    | .next next => executeLoop fuel next callers
    | .enter child k => executeLoop fuel child (k :: callers)
    | .terminal raw =>
      match callers with
      | [] => raw
      | k :: older =>
        match resumeChild k raw with
        | .committed world s => executeLoop fuel ⟨world, k.address, k.depth, s⟩ older
        | .indeterminate e => .indeterminate e
        -- A valid continuation removed at least six operands and only restores
        -- gas within its budget. Reject a malformed one without applying it.
        | .exceptional e => .indeterminate e

/-- Execute a frame and its nested calls at a supplied entry depth. -/
def executeAtDepth (fuel : Nat) (world : TxWorld) (address depth : Nat) (s : State) : RawOutcome :=
  executeLoop fuel ⟨world, address, depth, s⟩ []

/-- Execute a frame and all reached call-family opcodes using their shared world journal. -/
def execute (fuel : Nat) (world : TxWorld) (address : Nat) (s : State) : RawOutcome :=
  executeAtDepth fuel world address 0 s

/-- One CALL for clients that supply an already decoded parent state.
    The child runs in the same dispatcher as `execute`. -/
def callStep (fuel : Nat) (world : TxWorld) (parentAddress : Nat) (parent : State) : CallStep :=
  match beginCall ⟨world, parentAddress, 0, parent⟩ with
  | .ok (.entered child k) =>
      match precompileStep child k with
      | some result => result
      | none => resumeChild k (executeLoop fuel child [])
  | .ok (.failed k) => resumeFailedCall k
  | .error e =>
    match stepError e with
    | .indeterminate reason => .indeterminate reason
    | _ => .exceptional e

inductive Outcome where
  | stopped (world : TxWorld) (parent : State)
  | returned (world : TxWorld) (parent : State)
  | reverted (world : TxWorld) (parent : State)
  | exceptional (world : TxWorld) (parent : State) (reason : Error)
  | indeterminate (reason : Error)

/-- The parent entry world is the checkpoint: an unsuccessful parent
    undoes even earlier CHILD frames that had committed within the parent. -/
def settle (entryWorld : TxWorld) (initialParent : State)
    (raw : RawOutcome) : Outcome :=
  match raw with
  | .stopped world s => .stopped world s
  | .returned world s => .returned world s
  | .reverted s =>
      .reverted entryWorld { s with
        storage := initialParent.storage
        selfBalance := initialParent.selfBalance
        logsRev := initialParent.logsRev }
  | .exceptional e =>
      .exceptional entryWorld
        { initialParent with gas := 0, halted := true } e
  | .indeterminate e => .indeterminate e

def run (fuel : Nat) (world : TxWorld) (parentAddress gas : Nat) : Outcome :=
  let machine := frameInput world parentAddress gas
  settle world machine (execute fuel world parentAddress machine)

/-- Kind: correspondence.
    Says: a successful CALL schedule prices the maximum range demand before
    calculating the EIP-150 cap, with a stipend only for nonzero value.
    Does not say: the child executes or consumes all forwarded gas. -/
theorem schedule_exact (parent : State) (ranges : Windows) (requested value : Nat)
    (wasWarm isAlive : Bool) (budget : Budget)
    (h : schedule parent ranges requested value wasWarm isAlive = .ok budget) :
    let words := max (MemoryGas.requestedWords ranges.inputOffset ranges.inputSize)
      (MemoryGas.requestedWords ranges.outputOffset ranges.outputSize)
    let expandedGas := parent.gas - MemoryGas.expansion parent.memory.words words
    let overhead := if value = 0 then CallGas.accessCharge wasWarm
      else CallValue.extraCharge wasWarm isAlive
    let charged := min requested (CallGas.maxForwarded (expandedGas - overhead))
    budget.childGas = charged + (if value = 0 then 0 else CallValue.stipend) ∧
    budget.reserve = expandedGas - overhead - charged := by
  dsimp
  by_cases hMem : parent.gas < MemoryGas.expansion parent.memory.words ranges.words
  · simp [schedule, hMem] at h
  by_cases hValue : value = 0
  · simp only [schedule, hMem, if_false, hValue, if_true] at h
    unfold CallGas.schedule at h
    split at h
    · simp [Except.map] at h
      subst budget
      simp [Windows.words, hValue]
    · simp [Except.map] at h
  · simp only [schedule, hMem, if_false, hValue] at h
    unfold CallValue.schedule at h
    dsimp only at h
    split at h
    · simp [Except.map] at h
      subst budget
      simp [Windows.words, hValue]
    · simp [Except.map] at h

/-- Kind: correspondence.
    Says: an entered child receives the caller's input window from its
    suspended memory, the same static flag and profile, and one more depth.
    Its checkpoint includes the caller journal and the target warm-up.
    Does not say: every bytecode instruction executed in the child is supported. -/
theorem beginCall_entered_context (active child : ActiveFrame) (k : Continuation)
    (h : beginCall active = .ok (.entered child k)) :
    child.state.callData = ByteView.ofMemory k.parent.memory k.ranges.inputOffset k.ranges.inputSize ∧
    k.parent.memory = active.state.memory.expand k.ranges.words ∧
    child.state.readOnly = active.state.readOnly ∧ child.state.profile = active.state.profile ∧
    child.depth = active.depth + 1 ∧ child.depth ≤ maxDepth ∧
    k.checkpoint = WorldCall.warmTarget (commitFrame active.world active.address active.state) child.address ∧
    child.world.original = active.world.original ∧
    child.state.txOrigin = active.state.txOrigin ∧
    child.state.callerAddress = active.address := by
  unfold beginCall at h
  dsimp only at h
  split at h
  next requested targetWord value inputOffset inputSize outputOffset outputSize rest _hStack =>
    let target := targetWord.val % addressBound
    let ranges : Windows := ⟨inputOffset.val, inputSize.val, outputOffset.val, outputSize.val⟩
    let callerWorld := commitFrame active.world active.address active.state
    let checkpoint := WorldCall.warmTarget callerWorld target
    cases hKnown : active.world.hasAccount (targetWord.val % addressBound)
    · simp [hKnown] at h
    simp only [hKnown, Bool.not_true, Bool.false_eq_true, if_false] at h
    have hOriginal : checkpoint.original = active.world.original := by
      funext address slot
      exact WorldCall.warmTarget_original callerWorld target address slot
    cases hSchedule : schedule active.state ranges requested.val value.val
        (active.world.warmAddresses target)
        (value.val != 0 && CallValue.accountAlive (active.world.accounts target)) with
    | error e =>
      dsimp only [ranges, target] at hSchedule
      simp [hSchedule] at h
    | ok budget =>
      dsimp only [ranges, target] at hSchedule
      simp only [hSchedule] at h
      by_cases hStatic : (active.state.readOnly && value.val != 0) = true
      · simp [hStatic] at h
      simp only [hStatic] at h
      by_cases hDepth : maxDepth ≤ active.depth
      · simp [hDepth] at h
      by_cases hFunds : ((commitFrame active.world active.address active.state).accounts active.address).balance < value.val
      · simp [hFunds] at h
      simp only [hDepth, hFunds, decide_false, Bool.or_self, Bool.false_eq_true, if_false] at h
      by_cases hPrecompile : unimplementedPrecompile active.state.profile (targetWord.val % addressBound) = true
      · simp [hPrecompile] at h
      simp only [hPrecompile] at h
      have hChildDepth : active.depth + 1 ≤ maxDepth := by omega
      by_cases hValue : value.val = 0
      · simp only [hValue, if_true, Except.map] at h
        cases h
        exact ⟨rfl, rfl, rfl, rfl, rfl, hChildDepth, rfl, hOriginal, rfl, rfl⟩
      · simp only [hValue, if_false] at h
        cases hPay : pay checkpoint active.address target value.val with
        | error e =>
          dsimp only [checkpoint, callerWorld, target] at hPay
          simp [hPay, Except.mapError, Except.map] at h
        | ok transferred =>
          have hPay' := hPay
          dsimp only [checkpoint, callerWorld, target] at hPay'
          simp only [hPay', Except.mapError, Except.map] at h
          cases h
          have hTransferOriginal : transferred.original = checkpoint.original := by
            funext address slot
            exact pay_preserves_original hPay address slot
          exact ⟨rfl, rfl, rfl, rfl, rfl, hChildDepth, rfl, hTransferOriginal.trans hOriginal, rfl, rfl⟩
  next => contradiction

/-- Kind: invariant.
    Says: a continuation from an actually entered CALL includes adequate
    paid memory for every possible byte in its output window.
    Does not say: the child outputs as many bytes as the caller requested. -/
theorem beginCall_entered_output_paid (active child : ActiveFrame) (k : Continuation)
    (h : beginCall active = .ok (.entered child k)) :
    MemoryGas.requestedWords k.ranges.outputOffset k.ranges.outputSize ≤ k.parent.memory.words := by
  rw [(beginCall_entered_context active child k h).2.1]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

/-- Kind: correspondence.
    Says: each byte in an actually entered child's input window reads the
    corresponding byte in the immutable expanded caller memory.
    Does not say: the child will read each byte it receives. -/
theorem beginCall_entered_input_byte (active child : ActiveFrame) (k : Continuation)
    (h : beginCall active = .ok (.entered child k)) (index : Nat) (hIndex : index < k.ranges.inputSize) :
    child.state.callData.readByte index =
      (active.state.memory.expand k.ranges.words).readByte (k.ranges.inputOffset + index) := by
  obtain ⟨hInput, hMemory, _⟩ := beginCall_entered_context active child k h
  rw [hInput, hMemory]
  simp [ByteView.ofMemory, ByteView.readByte, hIndex]

/-- Kind: boundary.
    Says: the actual world-aware dispatch refuses an SLOAD with no
    witness for its key before invoking the storage-reading step.
    Does not say: who authenticated the supplied witness coverage. -/
theorem execute_missing_sload (fuel : Nat) (world : TxWorld) (address depth : Nat)
    (state : State) (coverage : World.WitnessCoverage) (key : Word) (rest : List Word)
    (hRunning : state.halted = false) (hOpcode : byteAt state state.pc = 0x54)
    (hStack : state.stack.items = key :: rest) (hCoverage : world.witnessed = some coverage)
    (hMissing : coverage.slot address key.val = false) :
    executeAtDepth (fuel + 1) world address depth state =
      .indeterminate (.incompleteState address (some key.val)) := by
  rw [executeAtDepth, executeLoop]
  cases rest <;> simp [dispatch, missingStorage, Option.filter, hRunning, hOpcode, hStack, hCoverage, hMissing]

/-- Kind: boundary.
    Says: the actual dispatcher refuses an eligible SSTORE when no
    witness covers the slot's original and current values.
    Does not say: that static writes or underflow read storage. -/
theorem execute_missing_sstore (fuel : Nat) (world : TxWorld) (address depth : Nat)
    (state : State) (coverage : World.WitnessCoverage) (key value : Word) (rest : List Word)
    (hRunning : state.halted = false) (hOpcode : byteAt state state.pc = 0x55)
    (hStack : state.stack.items = key :: value :: rest)
    (hMutable : state.readOnly = false) (hGas : 2300 < state.gas)
    (hCoverage : world.witnessed = some coverage) (hMissing : coverage.slot address key.val = false) :
    executeAtDepth (fuel + 1) world address depth state =
      .indeterminate (.incompleteState address (some key.val)) := by
  rw [executeAtDepth, executeLoop]
  simp [dispatch, missingStorage, Option.filter, hRunning, hOpcode, hStack, hMutable, hGas, hCoverage, hMissing]

/-- Kind: boundary.
    Says: a CALL without a target account witness refuses before scheduling
    from the target's balance or code.
    Does not say: the call could have completed if the witness were available. -/
theorem beginCall_missing_account (active : ActiveFrame) (request target value iOff iSize oOff oSize : Word)
    (rest : List Word) (hStack : active.state.stack.items =
      request :: target :: value :: iOff :: iSize :: oOff :: oSize :: rest)
    (hMissing : active.world.hasAccount (target.val % addressBound) = false) :
    beginCall active = .error (.incompleteState (target.val % addressBound) none) := by
  simp [beginCall, hStack, hMissing]

/-- Kind: projection.
    Says: completing the common window decoder preserves the supplied value.
    Does not say: the opcode obtains that value from the stack. -/
private theorem decodeVariantWindows_stackValue (requested target : Word) (value : Nat)
    (rest : List Word) (args : VariantOperands)
    (h : decodeVariantWindows requested target value rest = some args) : args.stackValue = value := by
  unfold decodeVariantWindows at h
  split at h
  · cases h
    rfl
  · cases h

/-- Kind: correspondence.
    Says: the decoder supplies zero to the value-pricing and funds checks
    for DELEGATECALL and STATICCALL, independent of the incoming message value.
    Does not say: DELEGATECALL executes with a zero CALLVALUE. -/
theorem decodeVariant_zero_stackValue (kind : CallVariant) (stack : List Word) (args : VariantOperands)
    (hKind : kind ≠ .callCode) (h : decodeVariant kind stack = some args) : args.stackValue = 0 := by
  cases kind with
  | callCode => exact (hKind rfl).elim
  | delegateCall | staticCall =>
    simp only [decodeVariant] at h
    split at h
    · exact decodeVariantWindows_stackValue _ _ _ _ _ h
    · cases h

/-- Kind: correspondence.
    Says: an entered child always has operands decoded from the actual
    caller stack for its opcode.
    Does not say: decoded operands alone suffice to enter the child. -/
theorem beginVariant_entered_operands (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (h : beginVariant active kind = .ok (.entered child k)) :
    ∃ args, decodeVariant kind active.state.stack.items = some args := by
  unfold beginVariant at h
  split at h
  · cases h
  · split at h
    · cases h
    next args hDecode => exact ⟨args, hDecode⟩

/-- Kind: correspondence.
    Says: entry is reached through decoded operands, an affordable budget,
    a committed and warmed checkpoint, and the permitted depth branch.
    Does not say: gas or depth suffice for subsequent child instructions. -/
private theorem beginVariant_entered_setup (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    ∃ budget, schedule active.state args.ranges args.requestedGas args.stackValue
      (active.world.warmAddresses args.codeAddress) true = .ok budget ∧
    k = ⟨active.address, active.depth,
      { active.state with memory := active.state.memory.expand args.ranges.words, returnData := {} },
      args.rest, WorldCall.warmTarget (commitFrame active.world active.address active.state) args.codeAddress,
      budget, args.ranges⟩ ∧
    child = variantFrame active kind args k ∧ active.depth < maxDepth := by
  simp only [beginVariant, hDecode] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      next budget hBudget =>
        unfold prepareVariant at h
        dsimp only at h
        split at h
        · cases h
        next hDepth =>
          split at h
          · cases h
          · cases h
            exact ⟨budget, hBudget, rfl, rfl, Nat.lt_of_not_ge (fun hMax => hDepth (.inl hMax))⟩

/-- Kind: correspondence.
    Says: each entered child executes the decoded target's code, while
    its ADDRESS and execution account follow the selected opcode.
    Does not say: the target's instructions all have semantics in this slice. -/
theorem beginVariant_entered_code (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    child.state.code = (active.world.accounts args.codeAddress).code ∧
    child.address = (if kind = .staticCall then args.codeAddress else active.address) ∧
    child.state.currentAddress = child.address := by
  obtain ⟨_, _, hK, hChild, _⟩ := beginVariant_entered_setup active child kind k args hDecode h
  rw [hChild]
  refine ⟨?_, rfl, rfl⟩
  rw [hK]
  change ((WorldCall.warmTarget (commitFrame active.world active.address active.state)
    args.codeAddress).accounts args.codeAddress).code = _
  unfold WorldCall.warmTarget
  split <;> by_cases hAddress : args.codeAddress = active.address <;> simp [commitFrame, hAddress]

/-- Kind: projection.
    Says: CALLCODE uses the explicit value, DELEGATECALL inherits the caller
    and value, and STATICCALL forces a read-only child with zero value.
    The original transaction origin and opcode profile are retained.
    Does not say: the caller or origin was authenticated. -/
theorem beginVariant_entered_context (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    child.state.callerAddress = (if kind = .delegateCall then active.state.callerAddress else active.address) ∧
    child.state.callValue = (match kind with
      | .callCode => args.stackValue
      | .delegateCall => active.state.callValue
      | .staticCall => 0) ∧
    child.state.readOnly = (active.state.readOnly || decide (kind = .staticCall)) ∧
    child.state.txOrigin = active.state.txOrigin ∧ child.state.profile = active.state.profile := by
  obtain ⟨_, _, _, hChild, _⟩ := beginVariant_entered_setup active child kind k args hDecode h
  subst child
  cases kind <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: projection.
    Says: the child uses the exact warmed checkpoint and its own execution
    account's storage, warmth and balance. Original slots retain the
    transaction-entry values, and block number and chain ID come from the world.
    Does not say: the world has authenticated account data or headers. -/
theorem beginVariant_entered_journal (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    child.world = k.checkpoint ∧
    k.checkpoint = WorldCall.warmTarget (commitFrame active.world active.address active.state) args.codeAddress ∧
    child.state.storage.current = (k.checkpoint.accounts child.address).storage ∧
    child.state.storage.warm = k.checkpoint.warmSlots child.address ∧
    child.state.storage.original = active.world.original child.address ∧
    child.state.selfBalance = (k.checkpoint.accounts child.address).balance ∧
    child.state.blockNumber = active.world.blockNumber ∧ child.state.chainId = active.world.chainId := by
  obtain ⟨_, _, hK, hChild, _⟩ := beginVariant_entered_setup active child kind k args hDecode h
  have hCheckpoint := congrArg Continuation.checkpoint hK
  rw [hChild]
  refine ⟨rfl, hCheckpoint, rfl, rfl, ?_, rfl, ?_, ?_⟩
  all_goals
    rw [hK]
    simp only [variantFrame, frameInput]
    unfold WorldCall.warmTarget
    split <;> rfl

/-- Kind: invariant.
    Says: entry for every new variant preserves the balance of every
    account, including CALLCODE's execution and code accounts.
    Does not say: descendants cannot transfer value through CALL. -/
theorem beginVariant_entered_no_transfer (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands) (address : Nat)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    (child.world.accounts address).balance = (active.world.accounts address).balance := by
  obtain ⟨hWorld, hCheckpoint, _⟩ := beginVariant_entered_journal active child kind k args hDecode h
  rw [hWorld, hCheckpoint]
  unfold WorldCall.warmTarget
  split <;> by_cases hAddress : address = active.address <;> simp [commitFrame, hAddress]

/-- Kind: invariant.
    Says: a child increases its parent's depth by one, within the depth
    limit, and the continuation retains the parent's depth.
    Does not say: how many dispatch units remain in the simulation. -/
theorem beginVariant_entered_depth (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    child.depth = active.depth + 1 ∧ child.depth ≤ maxDepth ∧ k.depth = active.depth := by
  obtain ⟨_, _, hK, hChild, hDepth⟩ := beginVariant_entered_setup active child kind k args hDecode h
  rw [hChild, hK]
  exact ⟨rfl, Nat.succ_le_of_lt hDepth, rfl⟩

/-- Kind: invariant.
    Says: an entered variant suspends the caller with expanded memory and
    an output window covered by that allocation, priced through CALL's schedule.
    Does not say: how much of the window a subsequent child writes. -/
theorem beginVariant_entered_output_paid (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    k.ranges = args.ranges ∧ k.parent.memory = active.state.memory.expand args.ranges.words ∧
    MemoryGas.requestedWords k.ranges.outputOffset k.ranges.outputSize ≤ k.parent.memory.words ∧
    schedule active.state k.ranges args.requestedGas args.stackValue
      (active.world.warmAddresses args.codeAddress) true = .ok k.budget := by
  obtain ⟨_, hBudget, hK, _, _⟩ := beginVariant_entered_setup active child kind k args hDecode h
  rw [hK]
  exact ⟨rfl, rfl, Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _), hBudget⟩

/-- Kind: correspondence.
    Says: every byte of an entered child's input is read from the matching
    position in the suspended caller's expanded memory.
    Does not say: the child reads every byte. -/
theorem beginVariant_entered_input_byte (active child : ActiveFrame) (kind : CallVariant)
    (k : Continuation) (args : VariantOperands) (index : Nat) (hIndex : index < args.ranges.inputSize)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (h : beginVariant active kind = .ok (.entered child k)) :
    child.state.callData.readByte index = (active.state.memory.expand args.ranges.words).readByte
      (args.ranges.inputOffset + index) := by
  obtain ⟨_, _, hK, hChild, _⟩ := beginVariant_entered_setup active child kind k args hDecode h
  rw [hChild, hK]
  simp [variantFrame, ByteView.ofMemory, ByteView.readByte, hIndex]

/-- Kind: boundary.
    Says: a missing code-account witness is reported at the decoded
    address, including for code executed in a different account.
    Does not say: supplying the witness suffices to enter a child. -/
theorem beginVariant_missing_code (active : ActiveFrame) (kind : CallVariant) (args : VariantOperands)
    (hProfile : active.state.profile ≠ .preShanghai)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (hMissing : active.world.hasAccount args.codeAddress = false) :
    beginVariant active kind = .error (.incompleteState args.codeAddress none) := by
  simp [beginVariant, hProfile, hDecode, missingVariantAccount, hMissing]

/-- Kind: boundary.
    Says: inherited execution context requires coverage of the executing
    account, even when the code account is covered.
    Does not say: the witness covers every accessed storage slot. -/
theorem beginVariant_missing_execution_account (active : ActiveFrame) (kind : CallVariant)
    (args : VariantOperands) (hKind : kind ≠ .staticCall)
    (hProfile : active.state.profile ≠ .preShanghai)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (hCode : active.world.hasAccount args.codeAddress = true)
    (hMissing : active.world.hasAccount active.address = false) :
    beginVariant active kind = .error (.incompleteState active.address none) := by
  simp [beginVariant, hProfile, hDecode, missingVariantAccount, hCode, hKind, hMissing]

/-- Kind: correspondence.
    Says: once 0xf1 enters a child, the next dispatch is the same world-aware
    interpreter using that child and the suspended caller on its stack.
    Does not say: all instructions reached in that child are supported. -/
private theorem executeLoop_enters_child (fuel : Nat) (active child : ActiveFrame)
    (callers : List Continuation) (k : Continuation) (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = 0xf1)
    (hEntry : beginCall active = .ok (.entered child k))
    (hOrdinary : k.codeTarget ≠ 4) :
    executeLoop (fuel + 1) active callers = executeLoop fuel child (k :: callers) := by
  rw [executeLoop]
  simp [dispatch, dispatchCall, precompileStep, hRunning, hOpcode, hEntry, hOrdinary]

/-- Kind: correspondence.
    Says: all three new opcode bytes enter the same continuation loop as CALL.
    Does not say: the supplied child is guaranteed to complete. -/
private theorem executeLoop_enters_variant (fuel : Nat) (active child : ActiveFrame)
    (callers : List Continuation) (k : Continuation) (kind : CallVariant)
    (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = kind.opcode)
    (hEntry : beginVariant active kind = .ok (.entered child k))
    (hOrdinary : k.codeTarget ≠ 4) :
    executeLoop (fuel + 1) active callers = executeLoop fuel child (k :: callers) := by
  rw [executeLoop]
  cases kind <;> simp [dispatch, dispatchCall, precompileStep, CallVariant.opcode, hRunning, hOpcode, hEntry,
    hOrdinary]

/-- Kind: boundary.
    Says: the public dispatcher propagates missing code coverage as an
    indeterminate result, without executing an empty child or returning success.
    Does not say: how the account witness was acquired. -/
theorem execute_missing_variant_code (fuel : Nat) (active : ActiveFrame) (kind : CallVariant)
    (args : VariantOperands) (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = kind.opcode)
    (hProfile : active.state.profile ≠ .preShanghai)
    (hDecode : decodeVariant kind active.state.stack.items = some args)
    (hMissing : active.world.hasAccount args.codeAddress = false) :
    executeAtDepth (fuel + 1) active.world active.address active.depth active.state =
      .indeterminate (.incompleteState args.codeAddress none) := by
  have hEntry := beginVariant_missing_code active kind args hProfile hDecode hMissing
  rcases active with ⟨world, address, depth, state⟩
  change state.halted = false at hRunning
  rw [executeAtDepth, executeLoop]
  cases kind <;> simp [dispatch, dispatchCall, stepError, CallVariant.opcode, hRunning, hOpcode, hEntry]

/-- Kind: correspondence.
    Says: the dispatcher continues a caller using the world and state
    supplied by the same child-result handler that implements rollback.
    Does not say: the remaining caller will complete successfully. -/
private theorem executeLoop_resumes_caller (fuel : Nat) (active : ActiveFrame)
    (callers : List Continuation) (k : Continuation) (raw : RawOutcome)
    (world : TxWorld) (state : State) (hTerminal : dispatch active = .terminal raw)
    (hResume : resumeChild k raw = .committed world state) :
    executeLoop (fuel + 1) active (k :: callers) =
      executeLoop fuel ⟨world, k.address, k.depth, state⟩ callers := by
  rw [executeLoop, hTerminal]
  simp only [hResume]

/-- Kind: boundary.
    Says: no remaining simulation fuel yields an indeterminate result even
    at a legal EVM call depth, separate from the CALL depth soft failure.
    Does not say: how much fuel is needed to complete the program. -/
theorem executeAtDepth_no_fuel (world : TxWorld) (address depth : Nat) (s : State) :
    executeAtDepth 0 world address depth s = .indeterminate .stepLimit := rfl

#print axioms dispatchCall_identity_exact
#print axioms dispatchCall_identity_outOfGas
#print axioms dispatchCall_identity_resourceLimit
#print axioms beginCall_entered_context
#print axioms beginCall_entered_output_paid
#print axioms beginCall_entered_input_byte
#print axioms execute_missing_sload
#print axioms execute_missing_sstore
#print axioms beginCall_missing_account
#print axioms decodeVariantWindows_stackValue
#print axioms decodeVariant_zero_stackValue
#print axioms beginVariant_entered_operands
#print axioms beginVariant_entered_setup
#print axioms beginVariant_entered_code
#print axioms beginVariant_entered_context
#print axioms beginVariant_entered_journal
#print axioms beginVariant_entered_no_transfer
#print axioms beginVariant_entered_depth
#print axioms beginVariant_entered_output_paid
#print axioms beginVariant_entered_input_byte
#print axioms beginVariant_missing_code
#print axioms beginVariant_missing_execution_account
#print axioms executeLoop_enters_child
#print axioms executeLoop_enters_variant
#print axioms execute_missing_variant_code
#print axioms executeLoop_resumes_caller
#print axioms executeAtDepth_no_fuel

/-- Kind: projection.
    Says: resuming a checked CALL keeps the supplied output memory and
    last-child buffer, installs the success flag, and restores the declared gas.
    Does not say: the child outcome qualifies to resume its caller. -/
private theorem finishCall_observations (address : Nat) (parent resumed : State)
    (rest : List Word) (world result : TxWorld) (gas : Nat) (success : Bool)
    (h : finishCall address parent rest world gas success = .committed result resumed) :
    result = world ∧ resumed.memory = parent.memory ∧ resumed.returnData = parent.returnData ∧
    resumed.gas = gas ∧ resumed.stack.items = word (if success then 1 else 0) :: rest := by
  unfold finishCall at h
  split at h
  next hGas =>
    split at h
    next _ hCommit =>
      cases h
      have hCost : parent.gas - gas ≤ parent.gas := Nat.sub_le _ _
      by_cases hStack : (word (if success then 1 else 0) :: rest).length ≤ 1024
      · simp only [commit, dif_pos hStack, dif_pos hCost] at hCommit
        cases hCommit
        exact ⟨rfl, rfl, rfl, Nat.sub_sub_self hGas, rfl⟩
      · simp only [commit, dif_neg hStack] at hCommit
        cases hCommit
    next => cases h
  next => cases h

/-- Kind: correspondence.
    Says: every resumed CALL sees the full child buffer, and updates memory
    only through the copy of the prefix that fits the paid output range.
    Does not say: whether the child returned, reverted, or ran exceptionally. -/
theorem resumeCall_observations (k : Continuation) (world result : TxWorld)
    (gas : Nat) (data : ByteView) (success : Bool) (resumed : State)
    (h : resumeCall k world gas data success = .committed result resumed) :
    result = world ∧ resumed.returnData = data ∧
    resumed.memory = k.parent.memory.copyFrom data 0 k.ranges.outputOffset
      (min k.ranges.outputSize data.size) ∧
    resumed.gas = k.budget.reserve + gas ∧
    resumed.stack.items = word (if success then 1 else 0) :: k.rest := by
  unfold resumeCall at h
  split at h
  · obtain ⟨hWorld, hMemory, hData, hGas, hStack⟩ :=
      finishCall_observations _ _ _ _ _ _ _ _ h
    exact ⟨hWorld, hData, hMemory, hGas, hStack⟩
  · cases h

/-- Kind: non-interference.
    Says: a resumed CALL leaves every byte outside the copied prefix alone,
    including the suffix of an output range longer than the child output.
    Does not say: an unpaid range can be read outside the bounds of memory. -/
theorem resumeCall_preserves_other_bytes (k : Continuation) (world result : TxWorld)
    (gas : Nat) (data : ByteView) (success : Bool) (resumed : State) (address : Nat)
    (h : resumeCall k world gas data success = .committed result resumed)
    (hOutside : address < k.ranges.outputOffset ∨
      k.ranges.outputOffset + min k.ranges.outputSize data.size ≤ address) :
    resumed.memory.readByte address = k.parent.memory.readByte address := by
  rw [(resumeCall_observations k world result gas data success resumed h).2.2.1]
  exact Memory.readByte_copyFrom_outside _ _ _ _ _ _ hOutside

/-- Kind: correspondence.
    Says: for any byte inside the copied prefix, a resumed CALL reads the
    corresponding child output byte from the paid output allocation.
    Does not say: an unaffordable CALL ever resumes with a child result. -/
theorem resumeCall_copies_prefix (k : Continuation) (world result : TxWorld)
    (gas : Nat) (data : ByteView) (success : Bool) (resumed : State) (index : Nat)
    (h : resumeCall k world gas data success = .committed result resumed)
    (hPaid : MemoryGas.requestedWords k.ranges.outputOffset k.ranges.outputSize ≤ k.parent.memory.words)
    (hIndex : index < min k.ranges.outputSize data.size) :
    resumed.memory.readByte (k.ranges.outputOffset + index) = data.readByte index := by
  rw [(resumeCall_observations k world result gas data success resumed h).2.2.1]
  have hLength : 0 < k.ranges.outputSize := by omega
  have hCover := MemoryGas.requestedWords_covers k.ranges.outputOffset k.ranges.outputSize hLength
  have hBound := Nat.mul_le_mul_left 32 hPaid
  have hAddress : k.ranges.outputOffset + index < 32 * k.parent.memory.words := by omega
  rw [Memory.readByte_copyFrom_inside _ _ _ _ _ _ hAddress (by omega) (by omega)]
  simp

/-- Kind: correspondence.
    Says: RETURN forwards the child's complete output buffer, and STOP
    clears the last-child buffer even after the child itself made calls.
    Does not say: output bytes beyond the parent's output window are copied. -/
theorem resumeChild_success (k : Continuation) (terminal resumed : State) (world result : TxWorld)
    (returns : Bool) (h : resumeChild k (if returns then .returned world terminal else .stopped world terminal) =
      .committed result resumed) :
    result = world ∧ resumed.returnData = (if returns then terminal.outputData else {}) ∧
    resumed.stack.items = word 1 :: k.rest := by
  cases returns <;> simp only [Bool.false_eq_true, if_false, if_true] at h ⊢
  all_goals
    obtain ⟨hWorld, hData, _, _, hStack⟩ := resumeCall_observations _ _ _ _ _ _ _ h
    exact ⟨hWorld, hData, hStack⟩

/-- Kind: checkpoint.
    Says: a reverting child restores the exact saved world, returns its
    complete output buffer, and pushes zero in the caller.
    Does not say: which reachable child program produces REVERT. -/
theorem resumeChild_revert (k : Continuation) (terminal resumed : State) (result : TxWorld)
    (h : resumeChild k (.reverted terminal) = .committed result resumed) :
    result = k.checkpoint ∧ resumed.returnData = terminal.outputData ∧
    resumed.stack.items = word 0 :: k.rest := by
  obtain ⟨hWorld, hData, _, _, hStack⟩ :=
    resumeCall_observations _ _ _ _ _ _ _ h
  exact ⟨hWorld, hData, hStack⟩

/-- Kind: checkpoint.
    Says: an exceptional child restores the exact saved world, clears the
    caller's last-child buffer, and refunds no child gas.
    Does not say: which reachable child program halts exceptionally. -/
theorem resumeChild_exception (k : Continuation) (e : Error) (resumed : State) (result : TxWorld)
    (h : resumeChild k (.exceptional e) = .committed result resumed) :
    result = k.checkpoint ∧ resumed.returnData.size = 0 ∧ resumed.gas = k.budget.reserve := by
  obtain ⟨hWorld, hData, _, hGas, _⟩ :=
    resumeCall_observations _ _ _ _ _ _ _ h
  exact ⟨hWorld, congrArg ByteView.size hData, hGas⟩

/-- Kind: boundary.
    Says: a depth or funds failure restores all allotted child gas and
    clears the last-child buffer while keeping the caller's warmed world.
    Does not say: when an input violates the depth or balance check. -/
theorem resumeFailedCall_observations (k : Continuation) (resumed : State) (result : TxWorld)
    (h : resumeFailedCall k = .committed result resumed) :
    result = k.checkpoint ∧ resumed.returnData.size = 0 ∧
    resumed.memory = k.parent.memory ∧ resumed.gas = k.budget.reserve + k.budget.childGas ∧
    resumed.stack.items = word 0 :: k.rest := by
  obtain ⟨hWorld, hData, hMemory, hGas, hStack⟩ :=
    resumeCall_observations _ _ _ _ _ _ _ h
  have hUnchanged : resumed.memory = k.parent.memory := by
    rw [hMemory]
    simp only [Nat.min_zero, Memory.copyFrom_zero]
  exact ⟨hWorld, congrArg ByteView.size hData, hUnchanged, hGas, hStack⟩

#print axioms schedule_exact
#print axioms finishCall_observations
#print axioms resumeCall_observations
#print axioms resumeCall_preserves_other_bytes
#print axioms resumeCall_copies_prefix
#print axioms resumeChild_success
#print axioms resumeChild_revert
#print axioms resumeChild_exception
#print axioms resumeFailedCall_observations

/-- Proven for ALL parent bytecode, ALL worlds, ALL execution fuel: the
    successful execution of a child never survives an eventual parent REVERT.
    This theorem concerns the executable checkpoint, not independent EELS
    semantic refinement. -/
theorem settle_parent_revert_atomic (entry : TxWorld) (initial : State)
    (raw : RawOutcome) (result : TxWorld) (terminal : State)
    (h : settle entry initial raw = .reverted result terminal) :
    result = entry := by
  cases raw <;> simp [settle] at h
  case reverted _ =>
    exact h.1.symm

/-- Exceptional parent execution likewise discards earlier child commits. -/
theorem settle_parent_exception_atomic (entry : TxWorld) (initial : State)
    (raw : RawOutcome) (result : TxWorld) (terminal : State)
    (reason : Error)
    (h : settle entry initial raw = .exceptional result terminal reason) :
    result = entry := by
  cases raw <;> simp [settle] at h
  case exceptional _ =>
    exact h.1.symm

/-- This is the public EXECUTABLE run entry point (not just a constructor
    lemma): any observed parent REVERT returns the precise original
    transaction world, even after one or more successful children. -/
theorem run_parent_revert_atomic (fuel : Nat) (entry result : TxWorld)
    (parentAddress gas : Nat) (terminal : State)
    (h : run fuel entry parentAddress gas = .reverted result terminal) :
    result = entry := by
  dsimp [run] at h
  exact settle_parent_revert_atomic entry
    (frameInput entry parentAddress gas)
    (execute fuel entry parentAddress (frameInput entry parentAddress gas))
    result terminal h

/-- Any exceptional public parent outcome similarly returns the entry world,
    rather than a child-mutated world. The gas is zeroed by settle. -/
theorem run_parent_exception_atomic (fuel : Nat) (entry result : TxWorld)
    (parentAddress gas : Nat) (terminal : State) (reason : Error)
    (h : run fuel entry parentAddress gas = .exceptional result terminal reason) :
    result = entry := by
  dsimp [run] at h
  exact settle_parent_exception_atomic entry
    (frameInput entry parentAddress gas)
    (execute fuel entry parentAddress (frameInput entry parentAddress gas))
    result terminal reason h

#print axioms settle_parent_revert_atomic
#print axioms settle_parent_exception_atomic
#print axioms run_parent_revert_atomic
#print axioms run_parent_exception_atomic
#print axioms finishCall_state_projection
#print axioms finishCall_logs_projection
#print axioms finishCall_commit_preserves_world

/-- Kind: executable correspondence.
    Says: the actual identity dispatcher derives unchanged bytes and exact
    remaining child gas from the input-size and gas inequalities.
    Does not say: an arbitrary continuation came from a valid parent CALL. -/
theorem dispatchCall_identity_admitted (child : ActiveFrame) (k : Continuation)
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : IdentityPrecompile.gasCost child.state.callData.size ≤ k.budget.childGas) :
    dispatchCall (.ok (.entered child k)) = afterCall k
      (resumeCall k child.world
        (k.budget.childGas - IdentityPrecompile.gasCost child.state.callData.size)
        child.state.callData true) := by
  exact dispatchCall_identity_exact child k _ _ hTarget
    (IdentityPrecompile.executeView_exact _ _ _ hSize hGas)

/-- Kind: executable gas boundary.
    Says: an admitted identity input with insufficient child gas restores
    the checkpoint, returns no bytes or child gas, and resumes with failure.
    Does not say: a resource-limit refusal is an EVM failure. -/
theorem dispatchCall_identity_underfunded (child : ActiveFrame) (k : Continuation)
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : k.budget.childGas < IdentityPrecompile.gasCost child.state.callData.size) :
    dispatchCall (.ok (.entered child k)) =
      afterCall k (resumeCall k k.checkpoint 0 {} false) := by
  exact dispatchCall_identity_outOfGas child k hTarget
    (IdentityPrecompile.executeView_underfunded _ _ _ hSize hGas)

/-- Kind: executable resource boundary.
    Says: exceeding the local identity input limit makes the actual
    dispatcher indeterminate before producing an EVM success or failure bit.
    Does not say: Ethereum has this local implementation limit. -/
theorem dispatchCall_identity_oversize (child : ActiveFrame) (k : Continuation)
    (hTarget : k.codeTarget = 4)
    (hSize : maxIdentityCallBytes < child.state.callData.size) :
    dispatchCall (.ok (.entered child k)) = .terminal (.indeterminate .resourceLimit) := by
  exact dispatchCall_identity_resourceLimit child k hTarget
    (IdentityPrecompile.executeView_oversize _ _ _ hSize)

/-- Kind: public adapter correspondence.
    Says: a successfully entered, funded identity CALL in the public
    single-CALL API executes the same byte-preserving precompile and gas charge.
    Does not say: the input world or transaction signature is authenticated. -/
theorem callStep_identity_admitted (fuel : Nat) (world : TxWorld) (address : Nat)
    (parent : State) (child : ActiveFrame) (k : Continuation)
    (hEntry : beginCall ⟨world, address, 0, parent⟩ = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : IdentityPrecompile.gasCost child.state.callData.size ≤ k.budget.childGas) :
    callStep fuel world address parent =
      resumeCall k child.world
        (k.budget.childGas - IdentityPrecompile.gasCost child.state.callData.size)
        child.state.callData true := by
  have hResult := IdentityPrecompile.executeView_exact _ _ _ hSize hGas
  simp [callStep, hEntry, precompileStep, hTarget, hResult]

/-- Kind: public adapter gas boundary.
    Says: insufficient identity gas in the public single-CALL API restores
    the caller checkpoint and returns the failure bit with zero child gas.
    Does not say: the entire parent transaction has failed. -/
theorem callStep_identity_underfunded (fuel : Nat) (world : TxWorld) (address : Nat)
    (parent : State) (child : ActiveFrame) (k : Continuation)
    (hEntry : beginCall ⟨world, address, 0, parent⟩ = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : k.budget.childGas < IdentityPrecompile.gasCost child.state.callData.size) :
    callStep fuel world address parent = resumeCall k k.checkpoint 0 {} false := by
  have hResult := IdentityPrecompile.executeView_underfunded _ _ _ hSize hGas
  simp [callStep, hEntry, precompileStep, hTarget, hResult]

/-- Kind: public adapter resource boundary.
    Says: the public single-CALL API preserves identity's local input-limit
    refusal as an indeterminate result, regardless of simulation fuel.
    Does not say: the input-size limit is an Ethereum validity rule. -/
theorem callStep_identity_oversize (fuel : Nat) (world : TxWorld) (address : Nat)
    (parent : State) (child : ActiveFrame) (k : Continuation)
    (hEntry : beginCall ⟨world, address, 0, parent⟩ = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : maxIdentityCallBytes < child.state.callData.size) :
    callStep fuel world address parent = .indeterminate .resourceLimit := by
  have hResult := IdentityPrecompile.executeView_oversize maxIdentityCallBytes k.budget.childGas
    child.state.callData hSize
  simp [callStep, hEntry, precompileStep, hTarget, hResult]

/-- Kind: observable public result.
    Says: a committed identity result exposes the complete input view,
    exact remaining gas, success bit and the child's resulting world.
    Does not say: a parent which later reverts retains that world. -/
theorem callStep_identity_observations (fuel : Nat) (world result : TxWorld)
    (address : Nat) (parent resumed : State) (child : ActiveFrame) (k : Continuation)
    (hEntry : beginCall ⟨world, address, 0, parent⟩ = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : IdentityPrecompile.gasCost child.state.callData.size ≤ k.budget.childGas)
    (hResult : callStep fuel world address parent = .committed result resumed) :
    result = child.world ∧ resumed.returnData = child.state.callData ∧
    resumed.gas = k.budget.reserve +
      (k.budget.childGas - IdentityPrecompile.gasCost child.state.callData.size) ∧
    resumed.stack.items = word 1 :: k.rest := by
  rw [callStep_identity_admitted fuel world address parent child k hEntry hTarget hSize hGas] at hResult
  obtain ⟨hWorld, hBytes, _, hRemaining, hStack⟩ := resumeCall_observations _ _ _ _ _ _ _ hResult
  exact ⟨hWorld, hBytes, hRemaining, hStack⟩

/-- Kind: end-to-end byte correspondence.
    Says: every byte copied by a successful public identity CALL equals the
    corresponding byte in the actual parent's expanded input-memory window.
    Does not say: bytes beyond the caller's output range are copied. -/
theorem callStep_identity_input_to_output (fuel : Nat) (world result : TxWorld)
    (address : Nat) (parent resumed : State) (child : ActiveFrame) (k : Continuation)
    (index : Nat)
    (hEntry : beginCall ⟨world, address, 0, parent⟩ = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : child.state.callData.size ≤ maxIdentityCallBytes)
    (hGas : IdentityPrecompile.gasCost child.state.callData.size ≤ k.budget.childGas)
    (hResult : callStep fuel world address parent = .committed result resumed)
    (hIndex : index < min k.ranges.outputSize k.ranges.inputSize) :
    resumed.memory.readByte (k.ranges.outputOffset + index) =
      (parent.memory.expand k.ranges.words).readByte (k.ranges.inputOffset + index) := by
  have hView := (beginCall_entered_context _ _ _ hEntry).1
  have hViewSize : child.state.callData.size = k.ranges.inputSize := by
    rw [hView]
    rfl
  rw [callStep_identity_admitted fuel world address parent child k hEntry hTarget hSize hGas] at hResult
  have hCopied := resumeCall_copies_prefix k child.world result _ child.state.callData true
    resumed index hResult (beginCall_entered_output_paid _ _ _ hEntry) (by simpa [hViewSize] using hIndex)
  rw [hCopied]
  exact beginCall_entered_input_byte _ _ _ hEntry index (Nat.lt_of_lt_of_le hIndex (Nat.min_le_right _ _))

/-- Kind: public opcode boundary.
    Says: after the real CALL opcode has entered an oversized identity
    input, one dispatcher step returns the local resource refusal.
    Does not say: other opcode paths have the same input limit. -/
theorem executeAtDepth_identity_oversize (fuel : Nat) (active child : ActiveFrame)
    (k : Continuation) (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = 0xf1)
    (hEntry : beginCall active = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : maxIdentityCallBytes < child.state.callData.size) :
    executeAtDepth (fuel + 1) active.world active.address active.depth active.state =
      .indeterminate .resourceLimit := by
  have hResult := IdentityPrecompile.executeView_oversize maxIdentityCallBytes k.budget.childGas
    child.state.callData hSize
  rw [executeAtDepth, executeLoop]
  simp [dispatch, dispatchCall, precompileStep, afterCall, hRunning, hOpcode, hEntry, hTarget, hResult]

/-- Kind: public opcode boundary.
    Says: CALLCODE, DELEGATECALL and STATICCALL each propagate identity's
    local input-limit refusal through the actual public dispatcher.
    Does not say: all their possible target precompiles are implemented. -/
theorem executeAtDepth_identity_variant_oversize (fuel : Nat) (active child : ActiveFrame)
    (k : Continuation) (kind : CallVariant) (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = kind.opcode)
    (hEntry : beginVariant active kind = .ok (.entered child k))
    (hTarget : k.codeTarget = 4)
    (hSize : maxIdentityCallBytes < child.state.callData.size) :
    executeAtDepth (fuel + 1) active.world active.address active.depth active.state =
      .indeterminate .resourceLimit := by
  have hResult := IdentityPrecompile.executeView_oversize maxIdentityCallBytes k.budget.childGas
    child.state.callData hSize
  rw [executeAtDepth, executeLoop]
  cases kind <;> simp [dispatch, dispatchCall, precompileStep, afterCall, CallVariant.opcode,
    hRunning, hOpcode, hEntry, hTarget, hResult]

#print axioms dispatchCall_identity_admitted
#print axioms dispatchCall_identity_underfunded
#print axioms dispatchCall_identity_oversize
#print axioms callStep_identity_admitted
#print axioms callStep_identity_underfunded
#print axioms callStep_identity_oversize
#print axioms callStep_identity_observations
#print axioms callStep_identity_input_to_output
#print axioms executeAtDepth_identity_oversize
#print axioms executeAtDepth_identity_variant_oversize

end EVMCleanroom.CallOpcode
