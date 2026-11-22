import EVMCleanroom.Memory
import EVMCleanroom.Storage
/-!
# Independently written, small-step EVM executable model

A deliberately limited proof-development seed, not a mainnet EVM.
Specification references: Ethereum Yellow Paper §9; Ethereum execution-specs.
Fork-sensitive instructions are admitted only for supported profiles.
No code was copied from an Ethereum client or other EVM formalization.
-/

namespace EVMCleanroom

/-- EVM words are residues modulo 2^256, represented as bounded naturals. -/
def modulus : Nat := 2 ^ 256

structure Word where
  val : Nat
  isLt : val < modulus
  deriving DecidableEq, Repr

/-- Arithmetic wraps to 256 bits. -/
def word (n : Nat) : Word :=
  ⟨n % modulus, Nat.mod_lt _ (by decide)⟩

def Word.add (a b : Word) : Word := word (a.val + b.val)
def Word.mul (a b : Word) : Word := word (a.val * b.val)
def Word.sub (a b : Word) : Word := word (a.val + modulus - b.val)
def Word.div (a b : Word) : Word := word (a.val / b.val)

/-- EVM MOD: unsigned remainder, with a zero result for a zero divisor. -/
def Word.modulo (a b : Word) : Word :=
  if b.val = 0 then word 0 else word (a.val % b.val)

/-- Bounded square-and-multiply, visiting at most 256 exponent bits.
    The recursive fuel decreases on every iteration, and zero bits terminate
    early. Intermediate products are reduced before the next iteration. -/
private def powModBits : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, accumulator => accumulator
  | fuel + 1, base, exponent, accumulator =>
      if exponent == 0 then accumulator
      else
        let nextAccumulator :=
          if exponent % 2 == 1 then (accumulator * base) % modulus else accumulator
        let nextBase := (base * base) % modulus
        powModBits fuel nextBase (exponent / 2) nextAccumulator

/-- EVM EXP: bounded 256-bit exponentiation modulo 2^256.
    No intermediate mathematical power or exponent-sized allocation occurs. -/
def Word.powMod (base exponent : Word) : Word :=
  word (powModBits 256 base.val exponent.val 1)

/-- EIP-160 EXP byte metering: exponent zero has no exponent-byte charge. -/
def expByteCount (exponent : Word) : Nat :=
  if exponent.val == 0 then 0 else Nat.log2 exponent.val / 8 + 1

def expGas (exponent : Word) : Nat := 10 + 50 * expByteCount exponent

/-- Zero divisors must not expose Lean's Nat.mod zero-divisor convention. -/
theorem Word.modulo_zero (a : Word) : a.modulo (word 0) = word 0 := by
  rfl

/-- EVM defines zero exponent as one, including the case zero to zero. -/
theorem Word.powMod_zero (base : Word) : base.powMod (word 0) = word 1 := by
  rfl

/-- EXP zero exponent costs ten gas on post-EIP-160 forks. -/
theorem expGas_zero : expGas (word 0) = 10 := by
  rfl

/-- Absolute magnitude of the signed two's-complement interpretation. -/
def Word.signedMagnitude (a : Word) : Nat :=
  if a.val < 2 ^ 255 then a.val else modulus - a.val

/-- EVM SDIV truncates towards zero. Signs apply to the mathematical
    magnitude before reduction to the word domain; a zero divisor gives 0.
    In particular (-2^255)/(-1) wraps back to -2^255. -/
def Word.signedDivide (a b : Word) : Word :=
  if b.val = 0 then word 0
  else
    let q := a.signedMagnitude / b.signedMagnitude
    if decide (a.val < 2 ^ 255) == decide (b.val < 2 ^ 255) then word q
    else word (modulus - q)

/-- EVM SMOD uses the dividend's sign, unlike Euclidean Int.mod.
    A zero divisor or an exact multiple yields zero. -/
def Word.signedMod (a b : Word) : Word :=
  if b.val = 0 then word 0
  else
    let r := a.signedMagnitude % b.signedMagnitude
    if a.val < 2 ^ 255 then word r else word (modulus - r)

/-- EVM SIGNEXTEND (0x0b): index counts bytes from the least-significant
    end. Retain the low index+1 bytes and replicate their highest bit.
    The guard stops a full-width index becoming an exponent or allocation. -/
def Word.signExtend (index value : Word) : Word :=
  if index.val < 32 then
    let keep := 2 ^ (8 * (index.val + 1))
    let low := value.val % keep
    if low < keep / 2 then word low
    else word (low + modulus - keep)
  else value

/-- Kind: executable helper boundary.
    Says: any SIGNEXTEND byte index >= 32 preserves the original 256-bit word.
    Does not say: the lower byte indexes have been refined against EELS. -/
theorem Word.signExtend_large (index value : Word) (h : ¬ index.val < 32) :
    index.signExtend value = value := by
  simp [Word.signExtend, h]

/-- Kind: executable helper boundary.
    Says: SDIV never divides by zero and returns the EVM zero word.
    Does not say: SDIV matches every fork-specific context. -/
theorem Word.signedDivide_zero (a : Word) :
    a.signedDivide (word 0) = word 0 := by
  rfl

/-- Kind: executable helper boundary.
    Says: SMOD never divides by zero and returns the EVM zero word.
    Does not say: arbitrary signed division is independently specified. -/
theorem Word.signedMod_zero (a : Word) :
    a.signedMod (word 0) = word 0 := by
  rfl

/-- ADDMOD computes the full mathematical sum before reducing, not an
    intermediate 256-bit wrapped addition. A zero modulus yields zero. -/
def Word.addMod (a b m : Word) : Word :=
  if m.val = 0 then word 0 else word ((a.val + b.val) % m.val)

/-- MULMOD likewise uses the full mathematical product before reducing. -/
def Word.mulMod (a b m : Word) : Word :=
  if m.val = 0 then word 0 else word ((a.val * b.val) % m.val)

def Word.ofBool (b : Bool) : Word := if b then word 1 else word 0
def Word.lt (a b : Word) : Word := Word.ofBool (decide (a.val < b.val))
def Word.gt (a b : Word) : Word := Word.ofBool (decide (b.val < a.val))

/-- Bit 255 is the sign bit of a 256-bit two's-complement word. -/
def signBit : Nat := 2 ^ 255

/-- Signed ordering by sign and unsigned value within the same sign class. -/
def Word.signedLt (a b : Word) : Word :=
  if a.val < signBit then
    Word.ofBool (decide (b.val < signBit ∧ a.val < b.val))
  else
    Word.ofBool (decide (b.val < signBit ∨ a.val < b.val))

/-- SGT is signed greater-than; reverse signed less-than arguments, not word signs. -/
def Word.signedGt (a b : Word) : Word := b.signedLt a

/-- Executable SGT has precisely reversed SLT operand semantics for every word. -/
theorem Word.signedGt_dual (a b : Word) : a.signedGt b = b.signedLt a := rfl

def Word.eq (a b : Word) : Word := Word.ofBool (a.val == b.val)
def Word.isZero (a : Word) : Word := Word.ofBool (a.val == 0)
def Word.bitAnd (a b : Word) : Word := word (Nat.land a.val b.val)
/-- Unsigned EVM bitwise OR over 256-bit words. -/
def Word.bitOr (a b : Word) : Word := word (Nat.lor a.val b.val)
def Word.bitXor (a b : Word) : Word := word (Nat.xor a.val b.val)
def Word.bitNot (a : Word) : Word := word (modulus - 1 - a.val)

/-- BYTE uses a big-endian index over the 32 bytes of the value. -/
def Word.byte (index value : Word) : Word :=
  if index.val < 32 then word ((value.val >>> (8 * (31 - index.val))) % 256)
  else word 0

/-- EIP-145 logical shifts test the full shift operand before shifting. -/
def Word.shiftLeft (shift value : Word) : Word :=
  if shift.val < 256 then word (value.val <<< shift.val) else word 0

def Word.shiftRight (shift value : Word) : Word :=
  if shift.val < 256 then word (value.val >>> shift.val) else word 0

/-- EIP-145 SAR. For a negative value retain the high sign bits; avoid a
    shift by a full-width EVM operand by checking the 256-bit bound first. -/
def Word.shiftArithmetic (shift value : Word) : Word :=
  if value.val < signBit then
    if shift.val < 256 then word (value.val >>> shift.val) else word 0
  else if shift.val < 256 then
    word ((value.val >>> shift.val) + modulus - (modulus >>> shift.val))
  else word (modulus - 1)

/-- Kind: executable helper boundary.
    Says: shifts >= 256 of a nonnegative EVM word yield zero.
    Does not say: the opcode is available on pre-Istanbul forks. -/
theorem Word.shiftArithmetic_large_nonnegative (shift value : Word)
    (hShift : ¬ shift.val < 256) (hSign : value.val < signBit) :
    shift.shiftArithmetic value = word 0 := by
  simp [Word.shiftArithmetic, hShift, hSign]

/-- Kind: executable helper boundary.
    Says: shifts >= 256 of a negative EVM word yield all ones.
    Does not say: this accounts for 256-bit fork activation rules. -/
theorem Word.shiftArithmetic_large_negative (shift value : Word)
    (hShift : ¬ shift.val < 256) (hSign : ¬ value.val < signBit) :
    shift.shiftArithmetic value = word (modulus - 1) := by
  simp [Word.shiftArithmetic, hShift, hSign]

/-- EIP-7939: leading zero bits in a 256-bit EVM word.
    Zero has 256 leading zero bits; otherwise bit length is log2(x)+1.
    No narrowing to a machine word is permitted. -/
def Word.leadingZeros (a : Word) : Nat :=
  if a.val == 0 then 256 else 255 - Nat.log2 a.val

/-- The CLZ result always fits in the EVM 256-bit word domain. -/
theorem Word.leadingZeros_le (a : Word) : a.leadingZeros ≤ 256 := by
  unfold Word.leadingZeros
  split <;> omega

/-- The exceptional all-zero operand produces 256, not 255. -/
theorem Word.leadingZeros_zero : (word 0).leadingZeros = 256 := by decide

inductive Error where
  | stackUnderflow
  | stackOverflow
  | outOfGas
  | returnDataOutOfBounds
  | invalidOpcode (opcode : Nat)
  | invalidJump (destination : Nat)
  | alreadyHalted
  | writeProtection
  | unsupportedFork
  | framePolicyViolation (opcode : Nat)
  | stepLimit
  deriving Repr, DecidableEq

/-- The bounds check is part of the constructor, not an assumed theorem. -/
structure Stack where
  items : List Word
  bounded : items.length ≤ 1024

def Stack.empty : Stack := ⟨[], by decide⟩

/-- Opcode-dispatch profiles, NOT complete fork execution environments.
    "shanghaiPlus" is the pre-Osaka legacy subset used by the existing
    tests, NOT a claim that later opcodes/gas rules are present. "osaka"
    enables EIP-7939 CLZ but does not claim full Fusaka/Osaka support. -/
inductive Profile where
  | preShanghai
  | shanghaiPlus
  | osaka
  deriving DecidableEq, Repr

/-- Machine-local state only. No accounts, persistent storage, external calls,
    precompiles or transaction context is modeled in this first slice. -/
structure State where
  code : Array UInt8
  pc : Nat := 0
  stack : Stack := Stack.empty
  gas : Nat
  halted : Bool := false
  profile : Profile := .shanghaiPlus
  memory : Memory := Memory.empty
  storage : Storage := Storage.empty
  /-- Host-populated frame context, not independently authenticated account state. -/
  currentAddress : Nat := 0
  /-- Externally supplied transaction origin (not authenticated here). -/
  txOrigin : Nat := 0
  /-- Chain identifier provided by the surrounding execution environment.
      It is not derived from or authenticated against a transaction here. -/
  chainId : Nat := 0
  /-- Immediate caller, set at each CALL entry. -/
  callerAddress : Nat := 0
  callValue : Nat := 0
  selfBalance : Nat := 0
  readOnly : Bool := false
  callData : ByteView := {}
  /-- Full output of the most recent call in this frame. -/
  returnData : ByteView := {}
  /-- This frame's own RETURN or REVERT payload. -/
  outputData : ByteView := {}

/-- An instruction plan describes effects without committing state changes.
    The dispatcher must produce one of these; all success passes through
    'commit'. This separation makes whole-step safety proofs compositional. -/
structure Plan where
  nextPC : Nat
  stack : List Word
  gasCost : Nat
  halt : Bool
  nextMemory : Option Memory := none
  nextStorage : Option Storage := none

private def prepared (nextPC : Nat) (xs : List Word) (cost : Nat)
    (halt : Bool := false) (nextMemory : Option Memory := none)
    (nextStorage : Option Storage := none) : Except Error Plan :=
  .ok ⟨nextPC, xs, cost, halt, nextMemory, nextStorage⟩

/-- A single controlled state transition. Invariant: every successful
    transition has a bounded stack and charges gas before mutation. -/
def commit (s : State) (nextPC : Nat) (xs : List Word) (cost : Nat)
    (halt : Bool := false) (nextMemory : Option Memory := none)
    (nextStorage : Option Storage := none) : Except Error State :=
  if hb : xs.length ≤ 1024 then
    if hg : cost ≤ s.gas then
      let nextStack : Stack := ⟨xs, hb⟩
      let s1 : State := { s with pc := nextPC }
      let s2 : State := { s1 with stack := nextStack }
      let s3 : State := { s2 with gas := s.gas - cost }
      let s4 : State := { s3 with halted := halt }
      let m : Memory := nextMemory.getD s.memory
      let planned : Storage := nextStorage.getD s.storage
      -- No opcode may alter transaction-original storage. Static frames can
      -- warm slots but cannot change current storage or the refund counter.
      let st : Storage := {
        planned with
        original := s.storage.original
        current := if s.readOnly then s.storage.current else planned.current
        refund := if s.readOnly then s.storage.refund else planned.refund
      }
      .ok { s4 with memory := m, storage := st }
    else .error .outOfGas
  else .error .stackOverflow

/-- Missing bytes in a PUSH immediate are treated as zero. Beyond-code
    instruction fetch likewise behaves as STOP. -/
def byteAt (s : State) (position : Nat) : Nat :=
  (s.code.getD position 0).toNat

def pushData (s : State) (n : Nat) : Word :=
  (List.range n).foldl
    (fun accumulated i => word (accumulated.val * 256 + byteAt s (s.pc + 1 + i)))
    (word 0)

/-- Accumulate big-endian bytes with a natural-number cursor and zero padding. -/
def loadCallDataLoop (data : ByteView) (offset acc : Nat) : Nat → Nat
  | 0 => acc
  | remaining + 1 =>
    loadCallDataLoop data (offset + 1) (acc * 256 + (data.readByte offset).toNat) remaining

/-- CALLDATALOAD reads exactly 32 bytes, even for a full-width offset. -/
def loadCallDataWord (data : ByteView) (offset : Nat) : Word :=
  word (loadCallDataLoop data offset 0 32)

/-- Byte width of the instruction starting addr pc, including PUSH
    immediates. The width is always addr least one. -/
def opcodeWidth (code : Array UInt8) (pc : Nat) : Nat :=
  let opcode := (code.getD pc 0).toNat
  if 0x60 ≤ opcode ∧ opcode ≤ 0x7f then 1 + (opcode - 0x5f)
  else 1

/-- Executable decoder for JUMPDEST recognition. The next candidate
    program counter advances over PUSH immediate data as an indivisible
    instruction. Fuel bounds scanning even on malformed or empty code. -/
def scanJumpdest (code : Array UInt8) (target : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | pc, remaining + 1 =>
    if pc ≥ code.size then false
    else if pc == target then (code.getD pc 0).toNat == 0x5b
    else scanJumpdest code target (pc + opcodeWidth code pc) remaining

/-- Valid JUMPDESTs are opcode boundaries, *not* 0x5b bytes embedded
    inside PUSH immediates. -/
def validJumpdest (code : Array UInt8) (target : Nat) : Bool :=
  scanJumpdest code target 0 (code.size + 1)

private def binary (s : State) (op : Word → Word → Word) (cost : Nat) : Except Error Plan :=
  match s.stack.items with
  | a :: b :: rest => prepared (s.pc + 1) (op a b :: rest) cost
  | _ => .error .stackUnderflow

/-- Three stack operands in pop order; no state is committed here. -/
private def ternary (s : State) (op : Word → Word → Word → Word)
    (cost : Nat) : Except Error Plan :=
  match s.stack.items with
  | a :: b :: m :: rest => prepared (s.pc + 1) (op a b m :: rest) cost
  | _ => .error .stackUnderflow

/-- EXP has a value-dependent charge. This model only admits the EIP-160
    pricing present on Shanghai and later profiles. The coarse preShanghai
    profile cannot select the historical EIP-160 activation boundary. -/
private def expStep (s : State) : Except Error Plan :=
  if s.profile = .preShanghai then .error .unsupportedFork
  else match s.stack.items with
  | base :: exponent :: rest =>
    prepared (s.pc + 1) (base.powMod exponent :: rest) (expGas exponent)
  | _ => .error .stackUnderflow

private def unary (s : State) (op : Word → Word) (cost : Nat) : Except Error Plan :=
  match s.stack.items with
  | value :: rest => prepared (s.pc + 1) (op value :: rest) cost
  | [] => .error .stackUnderflow

private def logicalShift (s : State) (op : Word → Word → Word) : Except Error Plan :=
  if s.profile = .preShanghai then .error .unsupportedFork else binary s op 3

/-- All COPY sources are bounded views. RETURNDATACOPY checks that the
    full source range fits after checking gas, as in EELS. -/
private def copyBytes (s : State) (data : ByteView) (checkBounds : Bool := false) : Except Error Plan :=
  match s.stack.items with
  | dest :: source :: length :: rest =>
    let gas := MemoryGas.copyCost s.memory.words dest.val length.val
    if s.gas < gas then .error .outOfGas
    else if checkBounds && decide (data.size < source.val + length.val) then
      .error .returnDataOutOfBounds
    else
      let requested := MemoryGas.requestedWords dest.val length.val
      let memory := (s.memory.expand requested).copyFrom data source.val dest.val length.val
      prepared (s.pc + 1) rest gas false (some memory)
  | _ => .error .stackUnderflow

private def pop (s : State) : Except Error Plan :=
  match s.stack.items with
  | _ :: rest => prepared (s.pc + 1) rest 2
  | [] => .error .stackUnderflow

private def dup (s : State) (n : Nat) : Except Error Plan :=
  match s.stack.items[n - 1]? with
  | none => .error .stackUnderflow
  | some x => prepared (s.pc + 1) (x :: s.stack.items) 3

private def swap (s : State) (n : Nat) : Except Error Plan :=
  match s.stack.items with
  | [] => .error .stackUnderflow
  | top :: rest =>
    match rest[n - 1]? with
    | none => .error .stackUnderflow
    | some other => prepared (s.pc + 1) (other :: rest.set (n - 1) top) 3

private def jump (s : State) : Except Error Plan :=
  match s.stack.items with
  | dest :: rest =>
    if validJumpdest s.code dest.val then prepared dest.val rest 8
    else .error (.invalidJump dest.val)
  | [] => .error .stackUnderflow

private def jumpi (s : State) : Except Error Plan :=
  match s.stack.items with
  | dest :: condition :: rest =>
    if condition.val == 0 then prepared (s.pc + 1) rest 10
    else if validJumpdest s.code dest.val then prepared dest.val rest 10
    else .error (.invalidJump dest.val)
  | _ => .error .stackUnderflow

/-- MLOAD: read 32 big-endian bytes, charging for previously unallocated words. -/
private def mload (s : State) : Except Error Plan :=
  match s.stack.items with
  | addr :: rest =>
    let requested := MemoryGas.requestedWords addr.val 32
    let expanded := s.memory.expand requested
    let value := word (expanded.readWord addr.val)
    let gas := 3 + MemoryGas.expansion s.memory.words requested
    prepared (s.pc + 1) (value :: rest) gas false (some expanded)
  | [] => .error .stackUnderflow

/-- MSTORE: store a 256-bit value in 32 big-endian bytes. -/
private def mstore (s : State) : Except Error Plan :=
  match s.stack.items with
  | addr :: value :: rest =>
    let requested := MemoryGas.requestedWords addr.val 32
    let expanded := s.memory.expand requested
    let written := expanded.writeWord addr.val value.val
    let gas := 3 + MemoryGas.expansion s.memory.words requested
    prepared (s.pc + 1) rest gas false (some written)
  | _ => .error .stackUnderflow

/-- MSTORE8: store only the low eight bits of the value. -/
private def mstore8 (s : State) : Except Error Plan :=
  match s.stack.items with
  | addr :: value :: rest =>
    let requested := MemoryGas.requestedWords addr.val 1
    let expanded := s.memory.expand requested
    let written := expanded.writeByte addr.val (UInt8.ofNat (value.val % 256))
    let gas := 3 + MemoryGas.expansion s.memory.words requested
    prepared (s.pc + 1) rest gas false (some written)
  | _ => .error .stackUnderflow

/-- EIP-2929 warm/cold SLOAD. A failed gas check cannot warm the slot. -/
private def sload (s : State) : Except Error Plan :=
  if s.profile = .preShanghai then .error .unsupportedFork
  else match s.stack.items with
  | key :: rest =>
    let price := s.storage.readCost key.val
    let next := s.storage.touch key.val
    prepared (s.pc + 1) (word (s.storage.current key.val) :: rest)
      price false none (some next)
  | [] => .error .stackUnderflow

/-- EIP-2200 + 2929 + 3529 SSTORE for one account in a transaction.
    Static frames cannot write and <=2300 gas cannot execute SSTORE.
    The original value must be the value at the *start of the transaction*.
    Refund deltas can be negative; the transaction-level cap is not here. -/
private def sstore (s : State) : Except Error Plan :=
  if s.profile = .preShanghai then .error .unsupportedFork
  else match s.stack.items with
  | key :: value :: rest =>
    if s.readOnly then .error .writeProtection
    else if s.gas ≤ 2300 then .error .outOfGas
    else
      let price := s.storage.storeCharge key.val value.val
      let next := s.storage.store key.val value.val price.refundDelta
      prepared (s.pc + 1) rest price.gas false none (some next)
  | _ => .error .stackUnderflow

/-- Partial instruction set. Unsupported instructions are errors, not NOPs.
    Gas costs here are those of the explicitly supported opcodes. -/
def planStep (s : State) : Except Error Plan :=
  if s.halted then .error .alreadyHalted
  else
    let op := byteAt s s.pc
    match op with
    | 0x00 => prepared (s.pc + 1) s.stack.items 0 true  -- STOP
    | 0x01 => binary s Word.add 3                      -- ADD
    | 0x02 => binary s Word.mul 5                      -- MUL
    | 0x03 => binary s Word.sub 3                      -- SUB
    | 0x04 => binary s Word.div 5                      -- DIV
    | 0x05 => binary s Word.signedDivide 5             -- SDIV
    | 0x06 => binary s Word.modulo 5                   -- MOD
    | 0x07 => binary s Word.signedMod 5                -- SMOD
    | 0x08 => ternary s Word.addMod 8                  -- ADDMOD
    | 0x09 => ternary s Word.mulMod 8                  -- MULMOD
    | 0x0a => expStep s                                -- EXP (EIP-160 price)
    | 0x0b => binary s Word.signExtend 5              -- SIGNEXTEND
    | 0x10 => binary s Word.lt 3                       -- LT
    | 0x11 => binary s Word.gt 3                       -- GT
    | 0x12 => binary s Word.signedLt 3                 -- SLT
    | 0x13 => binary s Word.signedGt 3                 -- SGT
    | 0x14 => binary s Word.eq 3                       -- EQ
    | 0x15 => unary s Word.isZero 3                     -- ISZERO
    | 0x16 => binary s Word.bitAnd 3                   -- AND
    | 0x17 => binary s Word.bitOr 3                    -- OR
    | 0x18 => binary s Word.bitXor 3                   -- XOR
    | 0x19 => unary s Word.bitNot 3                     -- NOT
    | 0x1a => binary s Word.byte 3                     -- BYTE
    | 0x1b => logicalShift s Word.shiftLeft            -- SHL
    | 0x1c => logicalShift s Word.shiftRight           -- SHR
    | 0x1d => logicalShift s Word.shiftArithmetic      -- SAR (EIP-145)
    | 0x1e =>                                           -- EIP-7939 CLZ (Osaka)
      if s.profile = .osaka then
        unary s (fun value => word value.leadingZeros) 5
      else .error .unsupportedFork
    | 0x30 => prepared (s.pc + 1) (word s.currentAddress :: s.stack.items) 2 -- ADDRESS
    | 0x32 => prepared (s.pc + 1) (word s.txOrigin :: s.stack.items) 2 -- ORIGIN
    | 0x33 => prepared (s.pc + 1) (word s.callerAddress :: s.stack.items) 2 -- CALLER
    | 0x34 => prepared (s.pc + 1) (word s.callValue :: s.stack.items) 2 -- CALLVALUE
    | 0x35 => unary s (fun offset => loadCallDataWord s.callData offset.val) 3 -- CALLDATALOAD
    | 0x36 => prepared (s.pc + 1) (word s.callData.size :: s.stack.items) 2 -- CALLDATASIZE
    | 0x37 => copyBytes s s.callData -- CALLDATACOPY
    | 0x38 => prepared (s.pc + 1) (word s.code.size :: s.stack.items) 2 -- CODESIZE
    | 0x39 => copyBytes s (ByteView.ofArray s.code) -- CODECOPY
    | 0x3d => -- RETURNDATASIZE (EIP-211)
      if s.profile = .preShanghai then .error .unsupportedFork
      else prepared (s.pc + 1) (word s.returnData.size :: s.stack.items) 2
    | 0x3e => -- RETURNDATACOPY (EIP-211)
      if s.profile = .preShanghai then .error .unsupportedFork
      else copyBytes s s.returnData true
    | 0x46 => -- CHAINID (EIP-1344; Istanbul and later)
      -- preShanghai spans both sides of Istanbul: refuse to claim either.
      if s.profile = .preShanghai then .error .unsupportedFork
      else prepared (s.pc + 1) (word s.chainId :: s.stack.items) 2
    | 0x47 =>                                           -- SELFBALANCE (Istanbul+)
      if s.profile = .preShanghai then .error .unsupportedFork
      else prepared (s.pc + 1) (word s.selfBalance :: s.stack.items) 5
    | 0x50 => pop s                                    -- POP
    | 0x51 => mload s                                  -- MLOAD
    | 0x52 => mstore s                                 -- MSTORE
    | 0x53 => mstore8 s                                -- MSTORE8
    | 0x54 => sload s                                  -- SLOAD
    | 0x55 => sstore s                                 -- SSTORE
    | 0x56 => jump s                                   -- JUMP
    | 0x57 => jumpi s                                  -- JUMPI
    | 0x58 => prepared (s.pc + 1) (word s.pc :: s.stack.items) 2
    | 0x59 => prepared (s.pc + 1) (word (32 * s.memory.words) :: s.stack.items) 2 -- MSIZE
    | 0x5a =>
      if 2 ≤ s.gas then
        prepared (s.pc + 1) (word (s.gas - 2) :: s.stack.items) 2
      else .error .outOfGas
    | 0x5b => prepared (s.pc + 1) s.stack.items 1        -- JUMPDEST
    | 0x5f =>
      if s.profile != .preShanghai then
        prepared (s.pc + 1) (word 0 :: s.stack.items) 2
      else .error (.invalidOpcode op)
    | _ =>
      if 0x60 ≤ op ∧ op ≤ 0x7f then
        let n := op - 0x5f
        prepared (s.pc + 1 + n) (pushData s n :: s.stack.items) 3
      else if 0x80 ≤ op ∧ op ≤ 0x8f then dup s (op - 0x7f)
      else if 0x90 ≤ op ∧ op ≤ 0x9f then swap s (op - 0x8f)
      else .error (.invalidOpcode op)

/-- The sole path to successful state mutation. The preparatory dispatcher has
    no authority to change code or gas; commit enforces the stack bound and
    charges the declared gas cost. -/
def step (s : State) : Except Error State :=
  match planStep s with
  | .error e => .error e
  | .ok p => commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage

/-- Kind: dispatcher correspondence.
    Says: CALLDATALOAD replaces the top stack item through the loader and
    requests a three-gas commit.
    Does not say: a frame with insufficient gas can commit. -/
theorem step_callDataLoad (s : State) (offset : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x35)
    (hStack : s.stack.items = offset :: rest) :
    step s = commit s (s.pc + 1) (loadCallDataWord s.callData offset.val :: rest) 3 := by
  simp [step, planStep, hRun, hOp, unary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: CALLDATASIZE pushes the input length and requests a two-gas commit.
    Does not say: a frame with a full stack can commit. -/
theorem step_callDataSize (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x36) :
    step s = commit s (s.pc + 1) (word s.callData.size :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, prepared]

/-- Kind: dispatcher correspondence.
    Says: funded CALLDATACOPY pops destination, source and length and commits
    the priced memory overlay using frame input bytes.
    Does not say: calldata is modified by the copy. -/
theorem step_callDataCopy (s : State) (dest source length : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x37)
    (hStack : s.stack.items = dest :: source :: length :: rest)
    (hGas : MemoryGas.copyCost s.memory.words dest.val length.val ≤ s.gas) :
    step s = commit s (s.pc + 1) rest (MemoryGas.copyCost s.memory.words dest.val length.val)
      false (some ((s.memory.expand (MemoryGas.requestedWords dest.val length.val)).copyFrom
        s.callData source.val dest.val length.val)) := by
  simp [step, planStep, hRun, hOp, copyBytes, hStack, Nat.not_lt_of_ge hGas, prepared]

/-- Kind: dispatcher correspondence.
    Says: CODESIZE pushes the current code array's length for two gas.
    Does not say: a frame with a full stack can commit. -/
theorem step_codeSize (s : State) (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x38) :
    step s = commit s (s.pc + 1) (word s.code.size :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, prepared]

/-- Kind: dispatcher correspondence.
    Says: funded CODECOPY pops destination, source and length and commits
    the priced memory overlay using the current code bytes.
    Does not say: reads beyond code length fail. -/
theorem step_codeCopy (s : State) (dest source length : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x39)
    (hStack : s.stack.items = dest :: source :: length :: rest)
    (hGas : MemoryGas.copyCost s.memory.words dest.val length.val ≤ s.gas) :
    step s = commit s (s.pc + 1) rest (MemoryGas.copyCost s.memory.words dest.val length.val)
      false (some ((s.memory.expand (MemoryGas.requestedWords dest.val length.val)).copyFrom
        (ByteView.ofArray s.code) source.val dest.val length.val)) := by
  simp [step, planStep, hRun, hOp, copyBytes, hStack, Nat.not_lt_of_ge hGas, prepared]

/-- Kind: dispatcher correspondence.
    Says: on an admitted profile RETURNDATASIZE pushes the current buffer size for two gas.
    Does not say: this opcode updates the return buffer. -/
theorem step_returnDataSize (s : State) (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x3d)
    (hProfile : s.profile ≠ .preShanghai) :
    step s = commit s (s.pc + 1) (word s.returnData.size :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, hProfile, prepared]

/-- Kind: dispatcher correspondence.
    Says: a funded, in-bounds RETURNDATACOPY on an admitted profile commits
    a priced memory overlay from the last call's return buffer.
    Does not say: the underlying call succeeded. -/
theorem step_returnDataCopy (s : State) (dest source length : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x3e) (hProfile : s.profile ≠ .preShanghai)
    (hStack : s.stack.items = dest :: source :: length :: rest)
    (hGas : MemoryGas.copyCost s.memory.words dest.val length.val ≤ s.gas)
    (hBounds : source.val + length.val ≤ s.returnData.size) :
    step s = commit s (s.pc + 1) rest (MemoryGas.copyCost s.memory.words dest.val length.val)
      false (some ((s.memory.expand (MemoryGas.requestedWords dest.val length.val)).copyFrom
        s.returnData source.val dest.val length.val)) := by
  simp [step, planStep, hRun, hOp, hProfile, copyBytes, hStack,
    Nat.not_lt_of_ge hGas, Nat.not_lt_of_ge hBounds, prepared]

/-- Kind: boundary.
    Says: a funded RETURNDATACOPY on an admitted profile with source end
    past the buffer fails, including a zero-length read starting past the end.
    Does not say: bounds failure takes precedence over insufficient gas. -/
theorem step_returnDataCopy_outOfBounds (s : State) (dest source length : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x3e) (hProfile : s.profile ≠ .preShanghai)
    (hStack : s.stack.items = dest :: source :: length :: rest)
    (hGas : MemoryGas.copyCost s.memory.words dest.val length.val ≤ s.gas)
    (hBounds : s.returnData.size < source.val + length.val) :
    step s = .error .returnDataOutOfBounds := by
  simp [step, planStep, hRun, hOp, hProfile, copyBytes, hStack, Nat.not_lt_of_ge hGas, hBounds]

/-- Kind: dispatcher correspondence.
    Says: SLT replaces the top two stack words in pop order and requests a
    three-gas commit.
    Does not say: insufficient gas can execute the comparison. -/
theorem step_slt (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x12)
    (hStack : s.stack.items = a :: b :: rest) :
    step s = commit s (s.pc + 1) (a.signedLt b :: rest) 3 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: SGT pops its left then right signed operand, and commits the
    reversed-SLT helper with the correct three-gas cost.
    Does not say: a transaction, fork schedule or external oracle is proved. -/
theorem step_sgt (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x13)
    (hStack : s.stack.items = a :: b :: rest) :
    step s = commit s (s.pc + 1) (a.signedGt b :: rest) 3 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: MOD pops the numerator before the divisor, and charges five gas.
    Does not say: the whole fork schedule is modelled. -/
theorem step_mod (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x06)
    (hStack : s.stack.items = a :: b :: rest) :
    step s = commit s (s.pc + 1) (a.modulo b :: rest) 5 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: post-EIP-160 EXP uses the actual bounded exponentiation helper,
    exponent-dependent pricing and shared gas-checked commit path.
    Does not say: the helper's general mathematical refinement is proved. -/
theorem step_exp (s : State) (base exponent : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x0a)
    (hProfile : s.profile ≠ .preShanghai)
    (hStack : s.stack.items = base :: exponent :: rest) :
    step s = commit s (s.pc + 1) (base.powMod exponent :: rest)
      (expGas exponent) := by
  simp [step, planStep, hRun, hOp, expStep, hProfile, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: SDIV pops signed numerator then denominator and requests five gas.
    Does not say: the source-level helper is normatively proved equivalent. -/
theorem step_sdiv (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x05)
    (hStack : s.stack.items = a :: b :: rest) :
    step s = commit s (s.pc + 1) (a.signedDivide b :: rest) 5 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: SMOD pops signed dividend then divisor and requests five gas.
    Does not say: it supplies a whole transaction gas model. -/
theorem step_smod (s : State) (a b : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x07)
    (hStack : s.stack.items = a :: b :: rest) :
    step s = commit s (s.pc + 1) (a.signedMod b :: rest) 5 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: SAR requests three gas and uses the signed shift helper on
    admitted pre-Osaka profiles; preShanghai remains explicitly refused.
    Does not say: the coarse profile models the historical Istanbul boundary. -/
theorem step_sar (s : State) (shift value : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x1d)
    (hProfile : s.profile ≠ .preShanghai)
    (hStack : s.stack.items = shift :: value :: rest) :
    step s = commit s (s.pc + 1) (shift.shiftArithmetic value :: rest) 3 := by
  simp [step, planStep, hRun, hOp, logicalShift, hProfile, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: SIGNEXTEND pops byte index then value and requests five gas through
    the actual Core.step to commit path.
    Does not say: the whole EVM transaction is conformant. -/
theorem step_signExtend (s : State) (index value : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x0b)
    (hStack : s.stack.items = index :: value :: rest) :
    step s = commit s (s.pc + 1) (index.signExtend value :: rest) 5 := by
  simp [step, planStep, hRun, hOp, binary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: ADDMOD uses three words in EVM pop order and charges eight gas
    through the common commit path, without early 256-bit addition wrap. -/
theorem step_addMod (s : State) (a b m : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x08)
    (hStack : s.stack.items = a :: b :: m :: rest) :
    step s = commit s (s.pc + 1) (a.addMod b m :: rest) 8 := by
  simp [step, planStep, hRun, hOp, ternary, hStack, prepared]

/-- Kind: dispatcher correspondence.
    Says: MULMOD uses three words in EVM pop order and charges eight gas
    through the common commit path, without early 256-bit product wrap. -/
theorem step_mulMod (s : State) (a b m : Word) (rest : List Word)
    (hRun : s.halted = false) (hOp : byteAt s s.pc = 0x09)
    (hStack : s.stack.items = a :: b :: m :: rest) :
    step s = commit s (s.pc + 1) (a.mulMod b m :: rest) 8 := by
  simp [step, planStep, hRun, hOp, ternary, hStack, prepared]

/-- Kind: dispatcher boundary.
    Says: SLT faults on stacks with fewer than two operands.
    Does not say: a valid stack is sufficient to execute SLT. -/
theorem step_slt_underflow (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x12) (hStack : s.stack.items.length < 2) :
    step s = .error .stackUnderflow := by
  cases hs : s.stack.items with
  | nil => simp [step, planStep, hRun, hOp, binary, hs]
  | cons a tail =>
    cases tail with
    | nil => simp [step, planStep, hRun, hOp, binary, hs]
    | cons b rest =>
      simp only [hs, List.length_cons] at hStack
      have hMin : 2 ≤ rest.length + 1 + 1 := Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
      exact (Nat.not_lt_of_ge hMin hStack).elim

/-- EIP-1344 CHAINID executes through the actual gas-checked dispatcher.
    This proves propagation of the supplied context, not its authenticity. -/
theorem step_chainId (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x46) (hProfile : s.profile ≠ .preShanghai) :
    step s = commit s (s.pc + 1) (word s.chainId :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, hProfile, prepared]

/-- The coarse older profile cannot claim EIP-1344 availability. -/
theorem step_chainId_unknown_fork (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x46) (hProfile : s.profile = .preShanghai) :
    step s = .error .unsupportedFork := by
  simp [step, planStep, hRun, hOp, hProfile]

#print axioms step_chainId
#print axioms step_chainId_unknown_fork

/-- ORIGIN reads the supplied transaction-origin field through actual Core.step.
    Authentication of that context is a separate obligation. -/
theorem step_origin (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x32) :
    step s = commit s (s.pc + 1) (word s.txOrigin :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, prepared]

/-- CALLER reads the immediate caller through actual Core.step. -/
theorem step_caller (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x33) :
    step s = commit s (s.pc + 1) (word s.callerAddress :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, prepared]

/-- Kind: dispatcher correspondence.
    Says: CALLVALUE in the zero-value context pushes zero and requests a
    two-gas commit.
    Does not say: the caller or value of a remote call has been authenticated. -/
theorem step_callValue_zero (s : State) (hRun : s.halted = false)
    (hOp : byteAt s s.pc = 0x34) (hValue : s.callValue = 0) :
    step s = commit s (s.pc + 1) (word 0 :: s.stack.items) 2 := by
  simp [step, planStep, hRun, hOp, hValue, prepared]

/-- Fuel-limited execution, terminating on STOP, error or exhausted fuel.
    Exceptional errors are reported; their outer transaction-level gas and
    rollback effects have not yet been formalized. -/
def run : Nat → State → Except Error State
  | 0, _ => .error .stepLimit
  | fuel + 1, s =>
    if s.halted then .ok s
    else
      match step s with
      | .error e => .error e
      | .ok next =>
        if next.halted then .ok next else run fuel next

-- Normative EIP-7939 boundary examples; the differential harness also
-- runs full-width EVM words on a separately maintained Osaka runtime.
#guard (word 0).leadingZeros == 256
#guard (word 1).leadingZeros == 255
#guard (word 2).leadingZeros == 254
#guard (word (2 ^ 255)).leadingZeros == 0
#guard (word (2 ^ 254)).leadingZeros == 1
#guard (word (2 ^ 256 - 1)).leadingZeros == 0

#print axioms Word.modulo_zero
#print axioms Word.powMod_zero
#print axioms expGas_zero
#print axioms step_mod
#print axioms step_exp
#print axioms Word.leadingZeros_le
#print axioms Word.leadingZeros_zero
#print axioms step_origin
#print axioms step_caller
#print axioms step_callDataLoad
#print axioms step_callDataSize
#print axioms step_callDataCopy
#print axioms step_codeSize
#print axioms step_codeCopy
#print axioms step_returnDataSize
#print axioms step_returnDataCopy
#print axioms step_returnDataCopy_outOfBounds
#print axioms step_slt
#print axioms Word.signedGt_dual
#print axioms step_sgt
#print axioms Word.signExtend_large
#print axioms step_signExtend
#print axioms Word.signedDivide_zero
#print axioms Word.signedMod_zero
#print axioms Word.shiftArithmetic_large_nonnegative
#print axioms Word.shiftArithmetic_large_negative
#print axioms step_sdiv
#print axioms step_smod
#print axioms step_sar
#print axioms step_addMod
#print axioms step_mulMod
#print axioms step_slt_underflow
#print axioms step_callValue_zero

end EVMCleanroom
