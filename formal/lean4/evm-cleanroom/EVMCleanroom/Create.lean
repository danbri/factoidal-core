import EVMCleanroom.Call
import EVMCleanroom.ValueCall

/-!
# Contract creation rules shared by CREATE (0xf0) and CREATE2 (0xf5)

Pure rules, Shanghai through Osaka: the gas charged before anything else
(EIP-3860 initcode words, the CREATE2 hash words), the EIP-150 child gas, the
two address derivations, the EIP-684/EIP-7610 collision test, the world of a
new account (EIP-161 nonce, EIP-6780 created mark) and the code-deposit rules
(EIP-170 size, EIP-3541 first byte, 200 gas per byte).

Normative reference: ethereum/execution-specs, `forks/cancun`, `forks/prague`
and `forks/osaka`: `vm/instructions/system.py` (`create`, `create2`,
`generic_create`), `vm/interpreter.py` (`process_create_message`),
`utils/address.py` and `vm/gas.py` (`init_code_cost`). The three forks have
the same creation rules.

The world-aware dispatcher in `CallOpcode.lean` calls these functions; the
address derivations use the repository's experimental Keccak, which is not
proved equal to Keccak-256.
-/

namespace EVMCleanroom.Create

open EVMCleanroom.World

/-- EIP-170. -/
def maxCodeSize : Nat := 24576

/-- EIP-3860: twice the code-size limit. -/
def maxInitCodeSize : Nat := 2 * maxCodeSize

/-- The largest nonce (EIP-2681); a creator holding it cannot create. -/
def maxNonce : Nat := 2 ^ 64 - 1

/-- 32-byte words covering `size` bytes. -/
def dataWords (size : Nat) : Nat := (size + 31) / 32

/-- EIP-3860: 2 gas per initcode word. -/
def initCodeCost (size : Nat) : Nat := 2 * dataWords size

/-- Everything charged before the size, static and funds checks. CREATE2
    also pays 6 gas per word for hashing the initcode. -/
def charge (create2 : Bool) (oldWords offset size : Nat) : Nat :=
  32000 + MemoryGas.accessCost oldWords offset size + initCodeCost size +
    (if create2 then 6 * dataWords size else 0)

/-- EIP-150: all but one 64th of the remaining gas goes to the child. -/
def childGas (remaining : Nat) : Nat := remaining - remaining / 64

/-- `n` as exactly `width` big-endian bytes (higher bytes are dropped). -/
def fixedBytes (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ (width - 1 - i))

/-- Bytes in the shortest big-endian form of `n` (zero for `n = 0`). -/
def byteLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n / 8 + 1

/-- RLP of a scalar below 2^64: 0x80 for zero, the byte itself below 0x80,
    otherwise a short-string header and the shortest big-endian form. -/
def rlpScalar (n : Nat) : List UInt8 :=
  if n = 0 then [0x80]
  else if n < 0x80 then [UInt8.ofNat n]
  else UInt8.ofNat (0x80 + byteLength n) :: fixedBytes (byteLength n) n

/-- RLP of the list `[sender as 20 bytes, nonce]`, for a nonce below 2^64
    (the payload is then at most 30 bytes, so the list header is one byte). -/
def rlpSenderNonce (sender nonce : Nat) : List UInt8 :=
  let payload := 0x94 :: (fixedBytes 20 sender ++ rlpScalar nonce)
  UInt8.ofNat (0xc0 + payload.length) :: payload

def viewOfList (bytes : List UInt8) : ByteView := ByteView.ofArray bytes.toArray

/-- CREATE: the low 160 bits of the hash of `rlp([sender, nonce])`. -/
def createAddress (acceptance : Keccak.Acceptance) (sender nonce : Nat) : Nat :=
  Keccak.experimentalDigestWord acceptance (viewOfList (rlpSenderNonce sender nonce)) % addressBound

/-- 0xff, the sender (20 bytes), the salt (32) and the initcode hash (32). -/
def create2Preimage (sender salt initHash : Nat) : List UInt8 :=
  0xff :: (fixedBytes 20 sender ++ (fixedBytes 32 salt ++ fixedBytes 32 initHash))

/-- CREATE2 (EIP-1014): the low 160 bits of the hash of the preimage. -/
def create2Address (acceptance : Keccak.Acceptance) (sender salt : Nat) (initCode : ByteView) : Nat :=
  Keccak.experimentalDigestWord acceptance
    (viewOfList (create2Preimage sender salt (Keccak.experimentalDigestWord acceptance initCode))) % addressBound

/-- The new account's address: CREATE2 when a salt is given. -/
def address (acceptance : Keccak.Acceptance) (sender nonce : Nat) (salt : Option Nat)
    (initCode : ByteView) : Nat :=
  match salt with
  | none => createAddress acceptance sender nonce
  | some s => create2Address acceptance sender s initCode

/-- Copy a byte window into an array. Callers bound `data.size` first
    (49152 for initcode, 24576 for deployed code). -/
def materialize (data : ByteView) : Array UInt8 :=
  Array.ofFn (n := data.size) fun i => data.raw i.val

/-- EIP-684 and EIP-7610: the target already has code, a nonce or storage. -/
def collides (target : Account) : Bool :=
  target.nonce != 0 || target.code.size != 0 || target.hasStorage

/-- The creator's nonce rises by one before the child checkpoint. -/
def bumpNonce (w : TxWorld) (creator : Nat) : TxWorld :=
  putAccount w creator { w.accounts creator with nonce := (w.accounts creator).nonce + 1 }

/-- The new account at child entry: storage destroyed, marked as created in
    this transaction (EIP-6780; its original storage then reads as zero) and
    nonce incremented (EIP-161). Balance and (empty) code are kept. Witness
    coverage, if any, gains every slot of the new account, because its storage
    is empty by construction; a rolled-back creation restores the old coverage. -/
def prepare (w : TxWorld) (new : Nat) : TxWorld :=
  { w with
    accounts := fun a =>
      if a = new then
        { w.accounts new with nonce := (w.accounts new).nonce + 1, storage := fun _ => 0, hasStorage := false }
      else w.accounts a
    original := fun a => if a = new then fun _ => 0 else w.original a
    created := fun a => if a = new then true else w.created a
    -- In witness mode every slot of the new account is now known (zero).
    witnessed := w.witnessed.map fun coverage =>
      { coverage with slot := fun a key => if a = new then true else coverage.slot a key } }

/-- The child's entry world: the prepared account, then the endowment. -/
def enter (w : TxWorld) (creator new value : Nat) : Except TransferError TxWorld :=
  if value = 0 then .ok (prepare w new) else pay (prepare w new) creator new value

def setCode (w : TxWorld) (new : Nat) (code : Array UInt8) : TxWorld :=
  putAccount w new { w.accounts new with code := code }

/-- Code deposit after successful initcode: the code and the gas left, or
    `none` for a failure that is treated as an exceptional halt. The size
    bound is checked before any byte is read or copied. -/
def deposit (gas : Nat) (output : ByteView) : Option (Array UInt8 × Nat) :=
  if maxCodeSize < output.size then none
  else if output.size != 0 && output.readByte 0 == 0xEF then none
  else if gas < 200 * output.size then none
  else some (materialize output, gas - 200 * output.size)

/-- Kind: executable correspondence (gas schedule).
    Says: CREATE charges 32000, the memory expansion of the initcode window
    and 2 gas per initcode word.
    Does not say: that the creation is then entered. -/
theorem charge_create (oldWords offset size : Nat) :
    charge false oldWords offset size =
      32000 + MemoryGas.accessCost oldWords offset size + 2 * ((size + 31) / 32) := by
  simp [charge, initCodeCost, dataWords]

/-- Kind: executable correspondence (gas schedule).
    Says: CREATE2 charges what CREATE does plus 6 gas per initcode word.
    Does not say: that the creation is then entered. -/
theorem charge_create2 (oldWords offset size : Nat) :
    charge true oldWords offset size =
      32000 + MemoryGas.accessCost oldWords offset size + 2 * ((size + 31) / 32) + 6 * ((size + 31) / 32) := by
  simp [charge, initCodeCost, dataWords]

/-- Kind: bound (EIP-150).
    Says: the child receives at most the remaining gas, and the creator keeps
    exactly one 64th (rounded down).
    Does not say: how much of it the child uses. -/
theorem childGas_reserve (remaining : Nat) :
    childGas remaining ≤ remaining ∧ remaining - childGas remaining = remaining / 64 := by
  unfold childGas
  have := Nat.div_le_self remaining 64
  omega

/-- Kind: shape.
    Says: a fixed-width encoding has exactly the requested number of bytes.
    Does not say: that the number fits in that width. -/
theorem fixedBytes_length (width n : Nat) : (fixedBytes width n).length = width := by
  simp [fixedBytes]

/-- Kind: bound.
    Says: a scalar below 2^64 has a shortest form of at most 8 bytes.
    Does not say: anything about larger scalars. -/
theorem byteLength_le (n : Nat) (h : n < 2 ^ 64) : byteLength n ≤ 8 := by
  unfold byteLength
  split
  · omega
  next hn =>
    have := (Nat.log2_lt hn).2 h
    omega

/-- Kind: shape.
    Says: the scalar encoding of a nonce below 2^64 has 1 to 9 bytes.
    Does not say: that the encoding is injective. -/
theorem rlpScalar_length (n : Nat) (h : n < 2 ^ 64) :
    1 ≤ (rlpScalar n).length ∧ (rlpScalar n).length ≤ 9 := by
  have := byteLength_le n h
  unfold rlpScalar
  split
  · simp
  · split
    · simp
    · simp [fixedBytes_length]
      omega

/-- Kind: shape.
    Says: the CREATE preimage is a one-byte list header whose length field
    counts the rest, then 0x94 and the 20 sender bytes, then the nonce; for a
    nonce below 2^64 it has 23 to 31 bytes, so the short-list form is right.
    Does not say: that a decoder returns the sender and nonce, or that the
    encoding is injective (both are only tested). -/
theorem rlpSenderNonce_shape (sender nonce : Nat) (h : nonce < 2 ^ 64) :
    ∃ tail, rlpSenderNonce sender nonce =
        UInt8.ofNat (0xc0 + tail.length) :: tail ∧
      tail = 0x94 :: (fixedBytes 20 sender ++ rlpScalar nonce) ∧
      tail.length = 21 + (rlpScalar nonce).length ∧ tail.length ≤ 30 := by
  have := rlpScalar_length nonce h
  refine ⟨_, rfl, rfl, ?_, ?_⟩ <;> simp [fixedBytes_length] <;> omega

/-- Kind: shape (EIP-1014).
    Says: the CREATE2 preimage is 0xff, 20 sender bytes, 32 salt bytes and
    32 hash bytes: 85 bytes.
    Does not say: that the experimental hash of it is Keccak-256. -/
theorem create2Preimage_shape (sender salt initHash : Nat) :
    create2Preimage sender salt initHash =
      0xff :: (fixedBytes 20 sender ++ (fixedBytes 32 salt ++ fixedBytes 32 initHash)) ∧
    (create2Preimage sender salt initHash).length = 85 := by
  simp [create2Preimage, fixedBytes_length]

/-- Kind: bound.
    Says: every derived address is a 160-bit value.
    Does not say: that distinct inputs give distinct addresses. -/
theorem address_bound (acceptance : Keccak.Acceptance) (sender nonce : Nat) (salt : Option Nat)
    (initCode : ByteView) : address acceptance sender nonce salt initCode < addressBound := by
  have hPos : 0 < addressBound := by unfold addressBound; exact Nat.two_pow_pos 160
  unfold address
  split
  · exact Nat.mod_lt _ hPos
  · exact Nat.mod_lt _ hPos

/-- Kind: resource bound and correspondence.
    Says: a materialised window has the window's size and the window's bytes.
    Does not say: that the window is small; callers check the size first. -/
theorem materialize_bytes (data : ByteView) :
    (materialize data).size = data.size ∧
    ∀ i, i < data.size → (materialize data).getD i 0 = data.readByte i := by
  refine ⟨by simp [materialize], ?_⟩
  intro i hi
  simp [materialize, ByteView.readByte, hi, Array.getD_eq_getD_getElem?]

/-- Kind: executable correspondence (EIP-170).
    Says: an output longer than 24576 bytes fails the deposit, whatever the gas.
    Does not say: how the caller treats the failure. -/
theorem deposit_oversize (gas : Nat) (output : ByteView) (h : maxCodeSize < output.size) :
    deposit gas output = none := by
  simp [deposit, h]

/-- Kind: executable correspondence (EIP-3541).
    Says: a nonempty output starting with 0xEF fails the deposit.
    Does not say: anything about EOF containers. -/
theorem deposit_invalid_prefix (gas : Nat) (output : ByteView) (hSize : output.size ≠ 0)
    (hByte : output.readByte 0 = 0xEF) : deposit gas output = none := by
  simp [deposit, hSize, hByte]

/-- Kind: gas boundary.
    Says: fewer than 200 gas per output byte fails the deposit.
    Does not say: that the creator keeps the child's gas. -/
theorem deposit_outOfGas (gas : Nat) (output : ByteView) (h : gas < 200 * output.size) :
    deposit gas output = none := by
  unfold deposit
  split
  · rfl
  · split
    · rfl
    · simp

/-- Kind: executable correspondence.
    Says: every successful deposit passed all three rules, stores exactly the
    output bytes and charges exactly 200 gas per byte.
    Does not say: that the initcode succeeded. -/
theorem deposit_success (gas : Nat) (output : ByteView) (code : Array UInt8) (remaining : Nat)
    (h : deposit gas output = some (code, remaining)) :
    output.size ≤ maxCodeSize ∧ (output.size = 0 ∨ output.readByte 0 ≠ 0xEF) ∧
    200 * output.size ≤ gas ∧ remaining = gas - 200 * output.size ∧ code = materialize output := by
  unfold deposit at h
  split at h
  · cases h
  next hSize =>
    split at h
    · cases h
    next hPrefix =>
      split at h
      · cases h
      next hGas =>
        cases h
        refine ⟨by omega, ?_, by omega, rfl, rfl⟩
        by_cases hZero : output.size = 0
        · exact .inl hZero
        · right
          intro hByte
          simp [hZero, hByte] at hPrefix

/-- Kind: boundary.
    Says: empty output always deposits: empty code at no cost.
    Does not say: that the account is otherwise unchanged. -/
theorem deposit_empty (gas : Nat) (output : ByteView) (h : output.size = 0) :
    deposit gas output = some (materialize output, gas) := by
  simp [deposit, h, maxCodeSize]

/-- Kind: world effect.
    Says: the nonce bump adds one to the creator's nonce and changes nothing
    else: not its balance, code or storage, and no other account.
    Does not say: that the nonce stays below 2^64 (the caller checks first). -/
theorem bumpNonce_accounts (w : TxWorld) (creator other : Nat) :
    (bumpNonce w creator).accounts other =
      if other = creator then { w.accounts creator with nonce := (w.accounts creator).nonce + 1 }
      else w.accounts other := by
  simp [bumpNonce, putAccount]

/-- Kind: world effect.
    Says: the bump leaves warmth, original storage, transient storage, the
    created marks, logs and refund as they were.
    Does not say: anything about later child effects. -/
theorem bumpNonce_journal (w : TxWorld) (creator : Nat) :
    (bumpNonce w creator).warmAddresses = w.warmAddresses ∧
    (bumpNonce w creator).warmSlots = w.warmSlots ∧
    (bumpNonce w creator).original = w.original ∧
    (bumpNonce w creator).transient = w.transient ∧
    (bumpNonce w creator).created = w.created ∧
    (bumpNonce w creator).logsRev = w.logsRev ∧
    (bumpNonce w creator).refund = w.refund := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: world effect (EIP-161, EIP-6780).
    Says: the prepared account is marked created, has its nonce incremented,
    empty storage and zero original storage, and keeps its balance and code;
    every other account, mark and original value is unchanged.
    Does not say: that the target was free of a collision. -/
theorem prepare_new (w : TxWorld) (new : Nat) :
    (prepare w new).created new = true ∧
    ((prepare w new).accounts new).nonce = (w.accounts new).nonce + 1 ∧
    ((prepare w new).accounts new).balance = (w.accounts new).balance ∧
    ((prepare w new).accounts new).code = (w.accounts new).code ∧
    (∀ key, ((prepare w new).accounts new).storage key = 0) ∧
    (∀ key, (prepare w new).original new key = 0) ∧
    (∀ other, other ≠ new → (prepare w new).accounts other = w.accounts other ∧
      (prepare w new).created other = w.created other ∧
      (prepare w new).original other = w.original other) := by
  refine ⟨by simp [prepare], by simp [prepare], by simp [prepare], by simp [prepare],
    by simp [prepare], by simp [prepare], ?_⟩
  intro other h
  simp [prepare, h]

/-- Kind: world effect.
    Says: setting the code changes only the code of the new account and keeps
    every created mark.
    Does not say: that the code passed the deposit rules. -/
theorem setCode_effect (w : TxWorld) (new : Nat) (code : Array UInt8) :
    ((setCode w new code).accounts new).code = code ∧
    ((setCode w new code).accounts new).nonce = (w.accounts new).nonce ∧
    ((setCode w new code).accounts new).balance = (w.accounts new).balance ∧
    ((setCode w new code).accounts new).storage = (w.accounts new).storage ∧
    (setCode w new code).created = w.created ∧
    (∀ other, other ≠ new → (setCode w new code).accounts other = w.accounts other) := by
  refine ⟨by simp [setCode, putAccount], by simp [setCode, putAccount], by simp [setCode, putAccount],
    by simp [setCode, putAccount], rfl, ?_⟩
  intro other h
  simp [setCode, putAccount, h]

/-- Kind: executable correspondence (EIP-684, EIP-7610).
    Says: a target collides exactly when it has a nonzero nonce, nonempty
    code, or storage according to the host's statement.
    Does not say: that the host's storage statement is authenticated. -/
theorem collides_iff (target : Account) :
    collides target = true ↔ target.nonce ≠ 0 ∨ target.code.size ≠ 0 ∨ target.hasStorage = true := by
  simp [collides, or_assoc]

#print axioms charge_create
#print axioms charge_create2
#print axioms childGas_reserve
#print axioms fixedBytes_length
#print axioms byteLength_le
#print axioms rlpScalar_length
#print axioms rlpSenderNonce_shape
#print axioms create2Preimage_shape
#print axioms address_bound
#print axioms materialize_bytes
#print axioms deposit_oversize
#print axioms deposit_invalid_prefix
#print axioms deposit_outOfGas
#print axioms deposit_success
#print axioms deposit_empty
#print axioms bumpNonce_accounts
#print axioms bumpNonce_journal
#print axioms prepare_new
#print axioms setCode_effect
#print axioms collides_iff

end EVMCleanroom.Create
