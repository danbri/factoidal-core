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

/-- A single controlled state transition. Invariant: every successful
    transition has a bounded stack and charges gas before mutation. -/
def commit (s : State) (nextPC : Nat) (xs : List Word) (cost : Nat)
    (halt : Bool := false) : Except Error State :=
  if hb : xs.length ≤ 1024 then
    if hg : cost ≤ s.gas then
      let nextStack : Stack := ⟨xs, hb⟩
      .ok { s with pc := nextPC, stack := nextStack,
          gas := s.gas - cost, halted := halt }
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

/-- Valid JUMPDESTs are opcode bytes, *not* 0x5b bytes embedded inside
    PUSH immediates. Fuel is bounded by bytecode length. -/
def validJumpdest (code : Array UInt8) (target : Nat) : Bool :=
  let rec scan (pc fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | remaining + 1 =>
      if pc ≥ code.size then false
      else
        let opcode := (code.getD pc 0).toNat
        if pc == target then opcode == 0x5b
        else if 0x60 ≤ opcode ∧ opcode ≤ 0x7f then
          scan (pc + 1 + (opcode - 0x5f)) remaining
        else scan (pc + 1) remaining
  scan 0 (code.size + 1)

private def binary (s : State) (op : Word → Word → Word) (cost : Nat) : Except Error State :=
  match s.stack.items with
  | a :: b :: rest => commit s (s.pc + 1) (op a b :: rest) cost
  | _ => .error .stackUnderflow

private def pop (s : State) : Except Error State :=
  match s.stack.items with
  | _ :: rest => commit s (s.pc + 1) rest 2
  | [] => .error .stackUnderflow

private def dup (s : State) (n : Nat) : Except Error State :=
  match s.stack.items[n - 1]? with
  | none => .error .stackUnderflow
  | some x => commit s (s.pc + 1) (x :: s.stack.items) 3

private def swap (s : State) (n : Nat) : Except Error State :=
  match s.stack.items with
  | [] => .error .stackUnderflow
  | top :: rest =>
    match rest[n - 1]? with
    | none => .error .stackUnderflow
    | some other => commit s (s.pc + 1) (other :: rest.set (n - 1) top) 3

private def jump (s : State) : Except Error State :=
  match s.stack.items with
  | dest :: rest =>
    if validJumpdest s.code dest.val then commit s dest.val rest 8
    else .error (.invalidJump dest.val)
  | [] => .error .stackUnderflow

private def jumpi (s : State) : Except Error State :=
  match s.stack.items with
  | dest :: condition :: rest =>
    if condition.val == 0 then commit s (s.pc + 1) rest 10
    else if validJumpdest s.code dest.val then commit s dest.val rest 10
    else .error (.invalidJump dest.val)
  | _ => .error .stackUnderflow

/-- Partial instruction set. Unsupported instructions are errors, not NOPs.
    Gas costs here are those of the explicitly supported opcodes. -/
def step (s : State) : Except Error State :=
  if s.halted then .error .alreadyHalted
  else
    let op := byteAt s s.pc
    match op with
    | 0x00 => commit s (s.pc + 1) s.stack.items 0 true  -- STOP
    | 0x01 => binary s Word.add 3                      -- ADD
    | 0x02 => binary s Word.mul 5                      -- MUL
    | 0x03 => binary s Word.sub 3                      -- SUB
    | 0x04 => binary s Word.div 5                      -- DIV
    | 0x50 => pop s                                    -- POP
    | 0x56 => jump s                                   -- JUMP
    | 0x57 => jumpi s                                  -- JUMPI
    | 0x58 => commit s (s.pc + 1) (word s.pc :: s.stack.items) 2
    | 0x5a =>
      if 2 ≤ s.gas then
        commit s (s.pc + 1) (word (s.gas - 2) :: s.stack.items) 2
      else .error .outOfGas
    | 0x5b => commit s (s.pc + 1) s.stack.items 1        -- JUMPDEST
    | 0x5f =>
      if s.profile = .shanghaiPlus then
        commit s (s.pc + 1) (word 0 :: s.stack.items) 2
      else .error (.invalidOpcode op)
    | _ =>
      if 0x60 ≤ op ∧ op ≤ 0x7f then
        let n := op - 0x5f
        commit s (s.pc + 1 + n) (pushData s n :: s.stack.items) 3
      else if 0x80 ≤ op ∧ op ≤ 0x8f then dup s (op - 0x7f)
      else if 0x90 ≤ op ∧ op ≤ 0x9f then swap s (op - 0x8f)
      else .error (.invalidOpcode op)

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
