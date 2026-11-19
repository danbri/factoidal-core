import Std
/-!
# Independently written, small-step EVM executable model

A deliberately limited proof-development seed, not a mainnet EVM.
Specification references: Ethereum Yellow Paper §9; Ethereum execution-specs.
Only a fork-insensitive opcode subset plus Shanghai's PUSH0 is admitted.
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

inductive Error where
  | stackUnderflow
  | stackOverflow
  | outOfGas
  | invalidOpcode (opcode : Nat)
  | invalidJump (destination : Nat)
  | alreadyHalted
  | stepLimit
  deriving Repr, DecidableEq

/-- The bounds check is part of the constructor, not an assumed theorem. -/
structure Stack where
  items : List Word
  bounded : items.length ≤ 1024

def Stack.empty : Stack := ⟨[], by decide⟩

/-- Profile captures only the PUSH0 fork boundary; other fork-dependent
    opcodes and gas rules are deliberately unsupported. -/
inductive Profile where
  | preShanghai
  | shanghaiPlus
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

/-- An instruction plan describes effects without committing state changes.
    The dispatcher must produce one of these; all success passes through
    'commit'. This separation makes whole-step safety proofs compositional. -/
structure Plan where
  nextPC : Nat
  stack : List Word
  gasCost : Nat
  halt : Bool
  deriving Repr

private def prepared (nextPC : Nat) (xs : List Word) (cost : Nat)
    (halt : Bool := false) : Except Error Plan :=
  .ok ⟨nextPC, xs, cost, halt⟩

/-- A single controlled state transition. Invariant: every successful
    transition has a bounded stack and charges gas before mutation. -/
def commit (s : State) (nextPC : Nat) (xs : List Word) (cost : Nat)
    (halt : Bool := false) : Except Error State :=
  if hb : xs.length ≤ 1024 then
    if hg : cost ≤ s.gas then
      let nextStack : Stack := ⟨xs, hb⟩
      let s1 : State := { s with pc := nextPC }
      let s2 : State := { s1 with stack := nextStack }
      let s3 : State := { s2 with gas := s.gas - cost }
      .ok { s3 with halted := halt }
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

/-- Byte width of the instruction starting at pc, including PUSH
    immediates. The width is always at least one. -/
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
    | 0x50 => pop s                                    -- POP
    | 0x56 => jump s                                   -- JUMP
    | 0x57 => jumpi s                                  -- JUMPI
    | 0x58 => prepared (s.pc + 1) (word s.pc :: s.stack.items) 2
    | 0x5a =>
      if 2 ≤ s.gas then
        prepared (s.pc + 1) (word (s.gas - 2) :: s.stack.items) 2
      else .error .outOfGas
    | 0x5b => prepared (s.pc + 1) s.stack.items 1        -- JUMPDEST
    | 0x5f =>
      if s.profile = .shanghaiPlus then
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
  | .ok p => commit s p.nextPC p.stack p.gasCost p.halt

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
      | .ok next => run fuel next

end EVMCleanroom
