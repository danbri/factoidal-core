import EVMCleanroom.Call
import EVMCleanroom.ValueCall
import EVMCleanroom.Proofs

/-!
# World-aware execution of EVM CALL (0xf1)

CALL prices both memory windows before forwarding gas. A child reads its
input from the suspended caller's memory and executes through the same
world-aware dispatcher. On resumption the caller sees the full child output
and copies only the prefix that fits its output window.

Each caller journals its account before entering its child. The target
address is warmed in that caller's scope, before the child checkpoint and
before value transfer. A child failure restores the checkpoint, including
successful descendant effects. The top-level checkpoint has the same boundary.

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
  unfold commitFrame
  rw [current, warm, refund]
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
  | .unsupportedFork | .stepLimit | .framePolicyViolation _ => .indeterminate e
  | .invalidOpcode b =>
      if b == 0xfe then .exceptional e else .indeterminate e
  | _ => .exceptional e

/-- Entry depth 0 allows child depths through 1024, as in EELS. -/
def maxDepth : Nat := 1024

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
        else if WorldCall.unsupportedPrecompile parent.profile target then .error .unsupportedFork
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

private def dispatch (active : ActiveFrame) : Transition :=
  let s := active.state
  if s.halted then .terminal (.stopped active.world s)
  else
    let opcode := byteAt s s.pc
    if opcode == 0xf1 then
      match beginCall active with
      | .error e => .terminal (stepError e)
      | .ok (.entered child k) => .enter child k
      | .ok (.failed k) => afterCall k (resumeFailedCall k)
    else if opcode == 0xf3 || opcode == 0xfd then
      match Frame.haltWithData s with
      | .error e => .terminal (stepError e)
      | .ok (terminal, _, _) =>
        if opcode == 0xfd then .terminal (.reverted terminal)
        else .terminal (.returned (commitFrame active.world active.address terminal) terminal)
    else
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
        -- A valid continuation removed seven operands, and only restores
        -- gas within its budget. Reject a malformed one without applying it.
        | .exceptional e => .indeterminate e

/-- Execute a frame and its nested calls at a supplied entry depth. -/
def executeAtDepth (fuel : Nat) (world : TxWorld) (address depth : Nat) (s : State) : RawOutcome :=
  executeLoop fuel ⟨world, address, depth, s⟩ []

/-- Execute a frame and all reached CALLs using their shared world journal. -/
def execute (fuel : Nat) (world : TxWorld) (address : Nat) (s : State) : RawOutcome :=
  executeAtDepth fuel world address 0 s

/-- One CALL for clients that supply an already decoded parent state.
    The child runs in the same dispatcher as `execute`. -/
def callStep (fuel : Nat) (world : TxWorld) (parentAddress : Nat) (parent : State) : CallStep :=
  match beginCall ⟨world, parentAddress, 0, parent⟩ with
  | .ok (.entered child k) => resumeChild k (executeLoop fuel child [])
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
      .reverted entryWorld { s with storage := initialParent.storage, selfBalance := initialParent.selfBalance }
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
      by_cases hPrecompile : WorldCall.unsupportedPrecompile active.state.profile (targetWord.val % addressBound) = true
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

/-- Kind: correspondence.
    Says: once 0xf1 enters a child, the next dispatch is the same world-aware
    interpreter using that child and the suspended caller on its stack.
    Does not say: all instructions reached in that child are supported. -/
private theorem executeLoop_enters_child (fuel : Nat) (active child : ActiveFrame)
    (callers : List Continuation) (k : Continuation) (hRunning : active.state.halted = false)
    (hOpcode : byteAt active.state active.state.pc = 0xf1)
    (hEntry : beginCall active = .ok (.entered child k)) :
    executeLoop (fuel + 1) active callers = executeLoop fuel child (k :: callers) := by
  rw [executeLoop]
  simp [dispatch, hRunning, hOpcode, hEntry]

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

#print axioms beginCall_entered_context
#print axioms beginCall_entered_output_paid
#print axioms beginCall_entered_input_byte
#print axioms executeLoop_enters_child
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
#print axioms finishCall_commit_preserves_world

end EVMCleanroom.CallOpcode
