import L4Factoidal.Paralliverse.WGSL.Surface

/-! # A bounded WGSL loop with a captured bound and a terminal storage assignment

Every expression in the limit guard, for-header, loop body and final store is
parsed from the source. The execution model reads two immutable bindings and
records stores to a third binding in execution order. -/

namespace L4Factoidal.Paralliverse.WGSL.ScanSurface

open Surface

structure Store where
  destination : BufferName
  address : Expr
  value : Expr

structure Code where
  initialCarry : Expr
  snapshot : Expr
  guardLeft : Expr
  guardRight : Expr
  initialIndex : Expr
  testLeft : Expr
  testRight : Expr
  increment : Expr
  store : Store
  updateCarry : Expr
  terminal : Store

structure Module where
  first : Binding
  second : Binding
  third : Binding
  sizeX : Nat
  sizeY : Nat
  sizeZ : Nat
  code : Code

private def expr := expressionWith localName

private def storeStmt : Parser Store := fun ts => do
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect ["["] ts
  let (i, ts) ← expr ts
  let ts ← expect ["]", "="] ts
  let (v, ts) ← expr ts
  return (⟨name, i, v⟩, ← expect [";"] ts)

private def code : Parser Code := fun ts => do
  let ts ← expect ["var", "pv_l0", ":", "u32", "="] ts
  let (initialCarry, ts) ← expr ts
  let ts ← expect [";", "let", "pv_bound", ":", "u32", "="] ts
  let (snapshot, ts) ← expr ts
  let ts ← expect [";", "if", "("] ts
  let (guardLeft, ts) ← expr ts
  let ts ← expect [">"] ts
  let (guardRight, ts) ← expr ts
  let ts ← expect [")", "{", "return", ";", "}", "for", "(", "var", "pv_i", ":", "u32", "="] ts
  let (initialIndex, ts) ← expr ts
  let ts ← expect [";"] ts
  let (testLeft, ts) ← expr ts
  let ts ← expect ["<"] ts
  let (testRight, ts) ← expr ts
  let ts ← expect [";", "pv_i", "="] ts
  let (increment, ts) ← expr ts
  let ts ← expect [")", "{"] ts
  let (store, ts) ← storeStmt ts
  let ts ← expect ["pv_l0", "="] ts
  let (updateCarry, ts) ← expr ts
  let ts ← expect [";", "}"] ts
  let (terminal, ts) ← storeStmt ts
  return (⟨initialCarry, snapshot, guardLeft, guardRight, initialIndex, testLeft,
    testRight, increment, store, updateCarry, terminal⟩, ts)

def parseShader (bytes : ByteArray) : Option Module := do
  if bytes.size > 2048 then return ← none
  let (a, ts) ← binding (lex bytes)
  let (b, ts) ← binding ts
  let (c, ts) ← binding ts
  if !(distinct a b && distinct a c && distinct b c) then return ← none
  let ((x, y, z), ts) ← entry ts
  let (body, ts) ← code ts
  let ts ← expect ["}"] ts
  if ts.isEmpty then return ⟨a, b, c, x, y, z, body⟩ else none

structure Frame where
  carry : UInt32
  bound : UInt32
  index : UInt32
  dst : Array UInt32
  writes : Array Write

structure Outcome where
  dst : Array UInt32
  writes : List Write
  returnedEarly : Bool

def Module.lookup (m : Module) (name : BufferName) : Option Binding :=
  if m.first.name == name then some m.first
  else if m.second.name == name then some m.second
  else if m.third.name == name then some m.third
  else none

def eval (m : Module) (packet aux : Array UInt32) (s : Frame) : Expr → Option UInt32 :=
  evalWith (fun name addr => do
    let d ← m.lookup name
    if d.group != 0 || d.mode != .read then none
    else if d.slot == 0 then packet[addr.toNat]?
    else if d.slot == 1 then aux[addr.toNat]?
    else none) 0 (fun
      | .word0 => some s.carry
      | .bound => some s.bound
      | .index => some s.index
      | .word1 => none)

def write (m : Module) (packet aux : Array UInt32) (op : Store) (s : Frame) : Option Frame := do
  let d ← m.lookup op.destination
  if d.group != 0 || d.slot != 2 || d.mode != .readWrite then return ← none
  let i ← eval m packet aux s op.address
  let v ← eval m packet aux s op.value
  if h : i.toNat < s.dst.size then
    return {s with dst := s.dst.set i.toNat v h, writes := s.writes.push ⟨d.group, d.slot, i, v⟩}
  else none

def running (m : Module) (packet aux : Array UInt32) (s : Frame) : Option Bool := do
  let a ← eval m packet aux s m.code.testLeft
  let b ← eval m packet aux s m.code.testRight
  return decide (a < b)

def step (m : Module) (packet aux : Array UInt32) (s : Frame) : Option Frame := do
  let s ← write m packet aux m.code.store s
  let carry ← eval m packet aux s m.code.updateCarry
  let s := {s with carry}
  let index ← eval m packet aux s m.code.increment
  return {s with index}

/-- Check the parsed condition even at zero budget. A loop that would execute
another iteration there has no successful result in this bounded semantics. -/
def loop (m : Module) (packet aux : Array UInt32) : Nat → Frame → Option Frame
  | 0, s => do if (← running m packet aux s) then none else return s
  | k + 1, s => do
    if (← running m packet aux s) then
      let next ← step m packet aux s
      loop m packet aux k next
    else return s

def run (m : Module) (packet aux prior : Array UInt32) : Option Outcome := do
  let s : Frame := ⟨0, 0, 0, prior, #[]⟩
  let carry ← eval m packet aux s m.code.initialCarry
  let s := {s with carry}
  let bound ← eval m packet aux s m.code.snapshot
  let s := {s with bound}
  let a ← eval m packet aux s m.code.guardLeft
  let b ← eval m packet aux s m.code.guardRight
  if a > b then return ⟨s.dst, s.writes.toList, true⟩
  let index ← eval m packet aux s m.code.initialIndex
  let s ← loop m packet aux (min bound.toNat 128) {s with index}
  let s ← write m packet aux m.code.terminal s
  return ⟨s.dst, s.writes.toList, false⟩

def runText (bytes : ByteArray) (packet aux prior : Array UInt32) : Option Outcome := do
  let m ← parseShader bytes
  run m packet aux prior

end L4Factoidal.Paralliverse.WGSL.ScanSurface
