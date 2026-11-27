import EVMCleanroom.SignedTransaction
import EVMCleanroom.StateRoot
import EVMCleanroom.Precompiles.Secp256k1

/-!
# Official state-test cases through the Lean EVM

One case of an execution-spec-tests `state_test` fixture: a complete
pre-state, a block environment, the signed transaction bytes of one post
entry, and the published post-state root and logs hash. Lean decodes the
signed bytes, recovers the sender, executes the transaction with the
existing ordinary or blob runner, builds the post-state root and logs hash
and compares them with the published values. The host only moves bytes.

A state test's pre-state is the whole world: an address it does not list
is absent and a slot it does not list is zero. The runners require every
address and slot they reach to be in an explicit witness inventory; when
execution stops at an unlisted one, this module adds it (absent, or zero)
and runs the transaction again from the start. The final inventory is
therefore the set of reached accounts and slots, which is the domain of the
post-state. The number of such expansions is bounded (`maxExpansions`).

The verdict is `pass`, `fail` (a wrong answer: root, logs or validity
differ) or `unsupported` with a machine-readable reason naming what the
Lean EVM does not yet do. Nothing is skipped silently.
-/

namespace EVMCleanroom.StateTest

open CallTransaction

structure PreAccount where
  address : Nat
  balance : Nat
  nonce : Nat
  code : Array UInt8
  storage : List (Nat × Nat)

structure Env where
  coinbase : Nat
  gasLimit : Nat
  number : Nat
  timestamp : Nat
  baseFee : Nat
  prevRandao : Nat
  excessBlobGas : Option Nat
  chainId : Nat

structure Expected where
  hash : Array UInt8
  logs : Array UInt8
  exception : Option String

structure Case where
  fork : String
  env : Env
  pre : List PreAccount
  txBytes : Array UInt8
  expected : Expected

inductive Verdict where
  | pass
  | fail (reason : String)
  | unsupported (reason : String)
  deriving Repr, BEq

/-- What Lean decided about the transaction itself. -/
inductive Decision where
  | executed (status : Bool) (gasUsed : Nat)
  | rejected (reason : String)
  | unavailable (reason : String)

structure Report where
  verdict : Verdict
  decision : Decision
  stateRoot : Option (Array UInt8) := none
  logsHash : Option (Array UInt8) := none
  expansions : Nat := 0

/-! ## Opcode inventory for precise reasons -/

/-- Mnemonics of the opcodes defined from Cancun to Prague. -/
def opcodeName (op : Nat) : Option String :=
  match op with
  | 0x00 => "STOP" | 0x01 => "ADD" | 0x02 => "MUL" | 0x03 => "SUB" | 0x04 => "DIV"
  | 0x05 => "SDIV" | 0x06 => "MOD" | 0x07 => "SMOD" | 0x08 => "ADDMOD" | 0x09 => "MULMOD"
  | 0x0a => "EXP" | 0x0b => "SIGNEXTEND" | 0x10 => "LT" | 0x11 => "GT" | 0x12 => "SLT"
  | 0x13 => "SGT" | 0x14 => "EQ" | 0x15 => "ISZERO" | 0x16 => "AND" | 0x17 => "OR"
  | 0x18 => "XOR" | 0x19 => "NOT" | 0x1a => "BYTE" | 0x1b => "SHL" | 0x1c => "SHR"
  | 0x1d => "SAR" | 0x20 => "KECCAK256" | 0x30 => "ADDRESS" | 0x31 => "BALANCE"
  | 0x32 => "ORIGIN" | 0x33 => "CALLER" | 0x34 => "CALLVALUE" | 0x35 => "CALLDATALOAD"
  | 0x36 => "CALLDATASIZE" | 0x37 => "CALLDATACOPY" | 0x38 => "CODESIZE" | 0x39 => "CODECOPY"
  | 0x3a => "GASPRICE" | 0x3b => "EXTCODESIZE" | 0x3c => "EXTCODECOPY"
  | 0x3d => "RETURNDATASIZE" | 0x3e => "RETURNDATACOPY" | 0x3f => "EXTCODEHASH"
  | 0x40 => "BLOCKHASH" | 0x41 => "COINBASE" | 0x42 => "TIMESTAMP" | 0x43 => "NUMBER"
  | 0x44 => "PREVRANDAO" | 0x45 => "GASLIMIT" | 0x46 => "CHAINID" | 0x47 => "SELFBALANCE"
  | 0x48 => "BASEFEE" | 0x49 => "BLOBHASH" | 0x4a => "BLOBBASEFEE" | 0x50 => "POP"
  | 0x51 => "MLOAD" | 0x52 => "MSTORE" | 0x53 => "MSTORE8" | 0x54 => "SLOAD" | 0x55 => "SSTORE"
  | 0x56 => "JUMP" | 0x57 => "JUMPI" | 0x58 => "PC" | 0x59 => "MSIZE" | 0x5a => "GAS"
  | 0x5b => "JUMPDEST" | 0x5c => "TLOAD" | 0x5d => "TSTORE" | 0x5e => "MCOPY" | 0x5f => "PUSH0"
  | 0xa0 => "LOG0" | 0xa1 => "LOG1" | 0xa2 => "LOG2" | 0xa3 => "LOG3" | 0xa4 => "LOG4"
  | 0xf0 => "CREATE" | 0xf1 => "CALL" | 0xf2 => "CALLCODE" | 0xf3 => "RETURN"
  | 0xf4 => "DELEGATECALL" | 0xf5 => "CREATE2" | 0xfa => "STATICCALL" | 0xfd => "REVERT"
  | 0xfe => "INVALID" | 0xff => "SELFDESTRUCT"
  | _ =>
    if 0x60 ≤ op ∧ op ≤ 0x7f then some ("PUSH" ++ toString (op - 0x5f))
    else if 0x80 ≤ op ∧ op ≤ 0x8f then some ("DUP" ++ toString (op - 0x7f))
    else if 0x90 ≤ op ∧ op ≤ 0x9f then some ("SWAP" ++ toString (op - 0x8f))
    else none

private def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def byteHex (n : Nat) : String := String.ofList [hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- Hex of a precompile address (one or two bytes). -/
def precompileHex (n : Nat) : String := if n < 256 then byteHex n else byteHex (n / 256) ++ byteHex n

/-- A reason for an instruction the interpreter stopped at. -/
def opcodeReason (op : Nat) : String :=
  match opcodeName op with
  | some name => "missing-opcode:0x" ++ byteHex op ++ ":" ++ name
  | none => "undefined-opcode-unclassified:0x" ++ byteHex op

def errorReason : Error → String
  | .invalidOpcode op => opcodeReason op
  | .unsupportedFork => "unsupported-fork-feature"
  | .resourceLimit => "local-resource-limit"
  | .stepLimit => "local-step-limit"
  | .framePolicyViolation op => "frame-policy:" ++ opcodeReason op
  | .incompleteState _ _ => "witness-expansion-limit"
  | .stackUnderflow => "frame:stackUnderflow"
  | .stackOverflow => "frame:stackOverflow"
  | .outOfGas => "frame:outOfGas"
  | .returnDataOutOfBounds => "frame:returnDataOutOfBounds"
  | .invalidJump _ => "frame:invalidJump"
  | .alreadyHalted => "frame:alreadyHalted"
  | .writeProtection => "frame:writeProtection"

def unavailableReason : Unavailable → String
  | .frame e => errorReason e
  | .invalidWitness => "pre-state-unusable-account"
  | .unsupported why => why

/-! ## Inventory -/

def witnessOf (p : PreAccount) : WitnessAccount :=
  { address := p.address, present := true, balance := p.balance, nonce := p.nonce
    code := p.code, storage := p.storage.map fun (k, v) => { key := k, value := v } }

def absent (address : Nat) : WitnessAccount :=
  { address, present := false, balance := 0, nonce := 0, code := #[], storage := [] }

def ensureAccount (ws : List WitnessAccount) (address : Nat) : List WitnessAccount :=
  if ws.any (·.address == address) then ws else ws ++ [absent address]

/-- Add one zero slot to a listed account; `none` if the account is absent
    from the inventory or listed as absent (an absent account has no storage). -/
def ensureSlot (ws : List WitnessAccount) (address key : Nat) : Option (List WitnessAccount) :=
  if ws.any (fun w => w.address == address && w.present) then
    some (ws.map fun w =>
      if w.address == address && !(w.storage.any (·.key == key)) then
        { w with storage := w.storage ++ [{ key, value := 0 }] }
      else w)
  else none

/-! ## Transaction execution -/

def forkOf : String → Option Fork
  | "Shanghai" => some .shanghai
  | "Cancun" => some .cancun
  | "Prague" => some .prague
  | "Osaka" => some .osaka
  | _ => none

def blockOf (fork : Fork) (env : Env) : Except String BlockContext := do
  let blobFee ← match fork with
    | .shanghai => pure 0
    | .cancun | .prague | .osaka => match env.excessBlobGas with
      | none => throw "env-missing-excess-blob-gas"
      | some excess =>
        -- EIP-4844 and EIP-7691 update fractions.
        match HeaderRLP.boundedBlobFee excess (if fork = .cancun then 3338477 else 5007716) with
        | none => throw "blob-fee-local-resource-limit"
        | some fee => pure fee
  return { chainId := env.chainId, coinbase := env.coinbase, number := env.number
           timestamp := env.timestamp, gasLimit := env.gasLimit, gasUsedBefore := 0
           baseFee := env.baseFee, prevRandao := env.prevRandao, blobBaseFee := blobFee }

/-- Header fields read by the Cancun blob adapter, derived from the state
    test environment. Declared gas totals are the block maxima. -/
def blobHeader (env : Env) : HeaderRLP.Fields :=
  let f := StateRoot.beBytes
  #[#[], #[], f env.coinbase, #[], #[], #[], #[], #[], f env.number, f env.gasLimit,
    f env.gasLimit, f env.timestamp, #[], f env.prevRandao, #[], f env.baseFee, #[],
    f (6 * HeaderRLP.gasPerBlob), f (env.excessBlobGas.getD 0), #[], #[]]

/-- Result of one attempt with a fixed inventory. -/
inductive Attempt where
  | done (outcome : Outcome)
  | refusedBlob (r : BlobCall.Refusal)

def attempt (fork : Fork) (env : Env) (block : BlockContext) (fuel : Nat) (tx : Envelope)
    (blob : Option TransactionList.BlobFields) (ws : List WitnessAccount)
    (a : Keccak.Acceptance) : Attempt :=
  let request : Request := { fork, fuel, tx, block, witnesses := ws, keccakAcceptance := some a }
  match blob with
  | none => .done (CallTransaction.run request)
  | some fields =>
    let input : BlobCall.Input := {
      request, parent := #[], child := blobHeader env, hashes := fields.hashes
      blobCap := fields.maxFeePerBlobGas, priorBlobGas := 0 }
    match BlobCall.prepareWithFees input (block.baseFee, block.blobBaseFee) with
    | .error r => .refusedBlob r
    | .ok ready =>
      match BlobCall.execute ready env.gasLimit with
      | .refused r => .refusedBlob r
      | .transaction _ out => .done out

def maxExpansions : Nat := 512

/-- Each expansion also lists the next `expansionBatch - 1` addresses (or
    slot keys): tests often probe consecutive ones, and every listed extra is
    exactly what the complete pre-state says (absent, or zero), so it cannot
    change the outcome; empty accounts and zero slots leave the roots alone. -/
def expansionBatch : Nat := 16

/-- Add `address` and its successors as absent, staying within the
    runner's account limit. -/
def ensureAccounts (ws : List WitnessAccount) (address : Nat) : List WitnessAccount :=
  let extra := (List.range expansionBatch).map (address + ·)
  let extra := extra.filter (· < 2 ^ 160)
  if ws.length + expansionBatch ≤ CallTransaction.maxAccounts / 2 then extra.foldl ensureAccount ws
  else ensureAccount ws address

/-- Add `key` and its successors as zero slots, within the slot limits. -/
def ensureSlots (ws : List WitnessAccount) (address key : Nat) : Option (List WitnessAccount) := do
  let first ← ensureSlot ws address key
  let total := first.foldl (fun n w => n + w.storage.length) 0
  if total + expansionBatch ≤ 8192 then
    (List.range (expansionBatch - 1)).foldlM (fun acc i =>
      if key + i + 1 < 2 ^ 256 then ensureSlot acc address (key + i + 1) else some acc) first
  else pure first

/-- EIP-2537 precompile addresses, executable from Prague. -/
def blsAddress (address : Nat) : Bool := decide (0x0b ≤ address ∧ address ≤ 0x11)

/-- Precompile addresses this runner has no implementation for, beyond the
    Cancun set that the call dispatcher already refuses. -/
def laterPrecompile (fork : Fork) (address : Nat) : Bool :=
  match fork with
  | .prague => blsAddress address
  | .osaka => blsAddress address || address == 0x100
  | _ => false

/-- Forks with EIP-7702 delegations. -/
def hasDelegations (fork : Fork) : Bool := fork = .prague || fork = .osaka

/-- EIP-7702 delegation designator prefix 0xef0100. -/
def delegated (code : Array UInt8) : Bool :=
  code.size == 23 && code[0]? == some 0xef && code[1]? == some 0x01 && code[2]? == some 0x00

/-- Run with inventory expansion. Returns the final outcome and inventory. -/
def runExpanding (fork : Fork) (env : Env) (block : BlockContext) (fuel : Nat) (tx : Envelope)
    (blob : Option TransactionList.BlobFields) (a : Keccak.Acceptance) :
    Nat → Nat → List WitnessAccount → Attempt × List WitnessAccount × Nat
  | 0, used, ws => (.done (.indeterminate (.frame (.incompleteState 0 none))), ws, used)
  | budget + 1, used, ws =>
    match attempt fork env block fuel tx blob ws a with
    | .done (.indeterminate (.frame (.incompleteState address none))) =>
      if laterPrecompile fork address then
        (.done (.indeterminate (.unsupported ("missing-precompile:0x" ++ precompileHex address))), ws, used)
      else if ws.any (·.address == address) then
        (.done (.indeterminate (.unsupported "witness-domain-loop")), ws, used)
      else runExpanding fork env block fuel tx blob a budget (used + 1) (ensureAccounts ws address)
    | .done (.indeterminate (.frame (.incompleteState address (some key)))) =>
      match ensureSlots ws address key with
      | some next =>
        if next.length == ws.length && ws.any (fun w => w.address == address &&
            w.storage.any (·.key == key)) then
          (.done (.indeterminate (.unsupported "witness-domain-loop")), ws, used)
        else runExpanding fork env block fuel tx blob a budget (used + 1) next
      | none => (.done (.indeterminate (.unsupported "storage-of-absent-account")), ws, used)
    | other => (other, ws, used)

/-- Post-state of every inventoried account in the settled world. -/
def postAccounts (world : World.TxWorld) (ws : List WitnessAccount) : List StateRoot.AccountState :=
  ws.map fun w =>
    let acct := world.accounts w.address
    { address := w.address, nonce := acct.nonce, balance := acct.balance, code := acct.code
      storage := w.storage.map fun s => (s.key, acct.storage s.key) }

def preAccounts (pre : List PreAccount) : List StateRoot.AccountState :=
  pre.map fun p => { address := p.address, nonce := p.nonce, balance := p.balance
                     code := p.code, storage := p.storage }

def logsOf (logs : List LogEntry) : List StateRoot.Log :=
  logs.map fun l => { address := l.address, topics := l.topics.map (·.val)
                      data := (Array.range l.data.size).map l.data.readByte }

/-- Local instruction budget per case: the runner's own maximum. -/
def caseFuel : Nat := CallTransaction.maxFuel

/-- Compare a computed outcome with the published commitments. -/
def judge (c : Case) (decision : Decision) (root : Option (Array UInt8))
    (logs : Option (Array UInt8)) (expansions : Nat) : Report :=
  let report := fun v => { verdict := v, decision, stateRoot := root, logsHash := logs, expansions }
  match root, logs with
  | none, _ => report (.unsupported "state-root-local-resource-limit")
  | some r, some l =>
    match decision, c.expected.exception with
    | .executed _ _, some exc => report (.fail ("expected-exception-not-raised:" ++ exc))
    | .rejected why, none => report (.fail ("unexpected-rejection:" ++ why))
    | _, _ =>
      if r != c.expected.hash then report (.fail "state-root-mismatch")
      else if l != c.expected.logs then report (.fail "logs-hash-mismatch")
      else report .pass
  | some _, none => report (.unsupported "logs-unavailable")

def unsupportedReport (why : String) : Report :=
  { verdict := .unsupported why, decision := .unavailable why }

/-- An account with no nonce, balance or code. The witness runner has no
    profile for such a listed-but-empty account yet. -/
def PreAccount.empty (p : PreAccount) : Bool :=
  p.nonce == 0 && p.balance == 0 && p.code.isEmpty

def rejectedReport (a : Keccak.Acceptance) (c : Case) (why : String) : Report :=
  judge c (.rejected why) (StateRoot.stateRoot a (preAccounts c.pre))
    (some (StateRoot.logsHash a [])) 0

/-- Sender recovery on the shared Jacobian secp256k1 module, with the same
    EIP-2 scalar bounds as `SecpRecovery.signatureBounds`. Agreement with
    the affine `SignedTransaction.recover` is tested (the CI selftest runs
    both on the same fixture), not proved. -/
def fastRecover (a : Keccak.Acceptance) (d : SignedTransaction.Decoded) :
    Except SignedTransaction.Failure Nat :=
  let z := Keccak.experimentalDigestWord a (ByteView.ofArray d.signing)
  if !SecpRecovery.signatureBounds z d.parity d.r d.s then .error .invalidSignature
  else match Precompiles.Secp256k1.recover z d.parity d.r d.s with
    | none => .error .invalidSignature
    | some (x, y) =>
      .ok (Keccak.experimentalDigestWord a
        (ByteView.ofArray (SecpRecovery.fixed32 x ++ SecpRecovery.fixed32 y)) % 2 ^ 160)

/-- Evaluate one case with a given sender recovery. Every refusal names its reason. -/
def evaluateWith (a : Keccak.Acceptance)
    (recover : SignedTransaction.Decoded → Except SignedTransaction.Failure Nat) (c : Case) : Report :=
  match forkOf c.fork with
  | none => unsupportedReport ("fork-not-implemented:" ++ c.fork)
  | some fork =>
  if c.pre.any PreAccount.empty then unsupportedReport "pre-state-empty-account"
  else if hasDelegations fork && c.pre.any (fun p => delegated p.code) then
    unsupportedReport "eip7702-delegation-in-pre-state"
  else if c.pre.any (fun p => laterPrecompile fork p.address) then
    unsupportedReport "pre-state-account-at-unimplemented-precompile"
  else if !(decide ((c.pre.map (·.address)).Nodup)) then unsupportedReport "pre-state-duplicate-address"
  else match blockOf fork c.env with
  | .error why => unsupportedReport why
  | .ok block =>
  match SignedTransaction.decode c.txBytes with
  | .error .resourceLimit => unsupportedReport "tx-local-resource-limit"
  | .error (.unsupported why) =>
    let tag := (c.txBytes[0]?).getD 0
    unsupportedReport (if tag < 0x80 then "tx-type-not-implemented:" ++ toString tag.toNat else why)
  | .error .arithmeticRefusal => unsupportedReport "secp-arithmetic-refusal"
  | .error .invalidSignature => rejectedReport a c "invalid-signature"
  | .error (.malformed why) => rejectedReport a c ("signed-envelope:" ++ why)
  | .ok d =>
  if d.kind == 3 && fork != .cancun then unsupportedReport ("tx-type-3-not-implemented:" ++ c.fork)
  else
  match recover d with
  | .error .invalidSignature => rejectedReport a c "invalid-signature"
  | .error _ => unsupportedReport "secp-arithmetic-refusal"
  | .ok sender =>
  match d.to with
  | none => unsupportedReport "contract-creation-transaction"
  | some dest =>
    if laterPrecompile fork dest then
      unsupportedReport ("missing-precompile:0x" ++ precompileHex dest)
    else
    let tx : Envelope := {
      kind := d.kind, signedChainId := d.chain, sender, to := dest, nonce := d.nonce
      value := d.value, gasLimit := d.gasLimit, gasPriceCap := d.gasPriceCap
      priorityFeeCap := d.priorityFeeCap, data := d.data, accessList := d.accessList }
    let ws0 := [sender, dest, c.env.coinbase].foldl ensureAccount (c.pre.map witnessOf)
    let (out, ws, used) := runExpanding fork c.env block caseFuel tx d.blob a maxExpansions 0 ws0
    match out with
    | .refusedBlob (.rejected why) => rejectedReport a c why
    | .refusedBlob (.indeterminate why) => unsupportedReport ("blob:" ++ why)
    | .done (.rejected why) => rejectedReport a c why
    | .done (.indeterminate why) =>
      let reason := match why with
        | .frame .unsupportedFork =>
          if (1 ≤ dest ∧ dest ≤ 0x11) ∨ dest = 0x100 then "missing-precompile:0x" ++ precompileHex dest
          else unavailableReason why
        | _ => unavailableReason why
      { unsupportedReport reason with expansions := used }
    | .done (.executed result) =>
      judge c (.executed result.receiptStatus result.charge.used)
        (StateRoot.stateRoot a (postAccounts result.world ws))
        (some (StateRoot.logsHash a (logsOf result.logs))) used

/-- Evaluation with the affine reference recovery. -/
def evaluate (a : Keccak.Acceptance) (s : SecpRecovery.Acceptance) (c : Case) : Report :=
  evaluateWith a (SignedTransaction.recover a s) c

/-! ## Theorems -/

/-- Kind: classification.
    Says: a case for a fork without Lean transaction rules is reported as
    unsupported with that fork's name, never as a pass or a fail.
    Does not say: which forks will be added. -/
theorem evaluate_unknown_fork (a : Keccak.Acceptance) (s : SecpRecovery.Acceptance) (c : Case)
    (h : forkOf c.fork = none) :
    (evaluate a s c).verdict = .unsupported ("fork-not-implemented:" ++ c.fork) := by
  simp [evaluate, evaluateWith, h, unsupportedReport]

/-- Kind: soundness of the verdict.
    Says: `pass` is only given when the computed state root and logs hash
    both equal the published ones.
    Does not say: that the computation follows the specification. -/
theorem judge_pass_sound (c : Case) (d : Decision) (r l : Option (Array UInt8)) (n : Nat)
    (h : (judge c d r l n).verdict = .pass) :
    r = some c.expected.hash ∧ l = some c.expected.logs := by
  unfold judge at h
  split at h
  · simp at h
  · split at h <;> (try split at h) <;> (try split at h) <;> simp_all
  · simp at h

/-- Kind: soundness of the verdict.
    Says: a case whose published entry expects an exception cannot pass
    when Lean executed the transaction.
    Does not say: that Lean's rejection reason matches the expected one. -/
theorem judge_exception_executed (c : Case) (status : Bool) (gas : Nat) (exc : String)
    (r l : Array UInt8) (n : Nat) (h : c.expected.exception = some exc) :
    (judge c (.executed status gas) (some r) (some l) n).verdict =
      .fail ("expected-exception-not-raised:" ++ exc) := by
  simp [judge, h]

/-- Kind: inventory monotonicity.
    Says: adding an absent account never removes an inventoried account.
    Does not say: that the final inventory is minimal. -/
theorem ensureAccount_keeps (ws : List WitnessAccount) (address : Nat) (w : WitnessAccount)
    (h : w ∈ ws) : w ∈ ensureAccount ws address := by
  unfold ensureAccount; split <;> simp [h]

/-- Kind: resource bound.
    Says: a frame whose memory expansion fits within the local transaction
    gas cap `CallTransaction.maxGas` has at most 369,960 words (11.3 MiB).
    Does not say: how many frames are live at once (the call depth bounds it). -/
theorem memory_words_bounded (w : Nat) (h : MemoryGas.cost w ≤ CallTransaction.maxGas) :
    w ≤ 369960 := by
  apply Classical.byContradiction
  intro hw
  have hm : MemoryGas.cost 369961 ≤ MemoryGas.cost w := MemoryGas.cost_monotone (by omega)
  have hc : CallTransaction.maxGas < MemoryGas.cost 369961 := by
    unfold CallTransaction.maxGas MemoryGas.cost; decide
  omega

#print axioms memory_words_bounded
#print axioms evaluate_unknown_fork
#print axioms judge_pass_sound
#print axioms judge_exception_executed
#print axioms ensureAccount_keeps

end EVMCleanroom.StateTest
