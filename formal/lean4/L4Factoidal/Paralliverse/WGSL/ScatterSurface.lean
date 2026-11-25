import L4Factoidal.Paralliverse.WGSL.ScanSurface

/-! # WGSL surface semantics for a guarded storage-copy loop

Each assignment, guard, loop operand and storage reference is read from the
source. The only shared reads are from the separately bound packet and offsets.
The third binding is written by the parsed store; its chronological trace
contains the actual words and addresses. -/

namespace L4Factoidal.Paralliverse.WGSL.ScatterSurface

open Surface

structure Code where
  laneLeft : Expr
  laneRight : Expr
  initial0 : Expr
  initial1 : Expr
  assign0 : Expr
  assign1 : Expr
  snapshot : Expr
  limitLeft : Expr
  limitRight : Expr
  initialIndex : Expr
  testLeft : Expr
  testRight : Expr
  increment : Expr
  store : ScanSurface.Store

structure Module where
  first : Binding
  second : Binding
  third : Binding
  sizeX : Nat
  sizeY : Nat
  sizeZ : Nat
  code : Code

private def expr := expressionWith localName

private def code : Parser Code := fun ts => do
  let ts ← expect ["if", "("] ts
  let (laneLeft, ts) ← expr ts
  let ts ← expect ["<"] ts
  let (laneRight, ts) ← expr ts
  let ts ← expect [")", "{", "var", "pv_l0", ":", "u32", "="] ts
  let (initial0, ts) ← expr ts
  let ts ← expect [";", "var", "pv_l1", ":", "u32", "="] ts
  let (initial1, ts) ← expr ts
  let ts ← expect [";", "pv_l0", "="] ts
  let (assign0, ts) ← expr ts
  let ts ← expect [";", "pv_l1", "="] ts
  let (assign1, ts) ← expr ts
  let ts ← expect [";", "let", "pv_bound", ":", "u32", "="] ts
  let (snapshot, ts) ← expr ts
  let ts ← expect [";", "if", "("] ts
  let (limitLeft, ts) ← expr ts
  let ts ← expect [">"] ts
  let (limitRight, ts) ← expr ts
  let ts ← expect [")", "{", "return", ";", "}", "for", "(", "var", "pv_i", ":", "u32", "="] ts
  let (initialIndex, ts) ← expr ts
  let ts ← expect [";"] ts
  let (testLeft, ts) ← expr ts
  let ts ← expect ["<"] ts
  let (testRight, ts) ← expr ts
  let ts ← expect [";", "pv_i", "="] ts
  let (increment, ts) ← expr ts
  let ts ← expect [")", "{"] ts
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect ["["] ts
  let (address, ts) ← expr ts
  let ts ← expect ["]", "="] ts
  let (value, ts) ← expr ts
  let ts ← expect [";", "}", "}"] ts
  return (⟨laneLeft, laneRight, initial0, initial1, assign0, assign1, snapshot, limitLeft, limitRight,
    initialIndex, testLeft, testRight, increment, ⟨name, address, value⟩⟩, ts)

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

structure Registers where
  word0 : UInt32
  word1 : UInt32
  bound : UInt32
  index : UInt32

structure Storage where
  dst : Array UInt32
  writes : Array Write

def Module.lookup (m : Module) (name : BufferName) : Option Binding :=
  if m.first.name == name then some m.first
  else if m.second.name == name then some m.second
  else if m.third.name == name then some m.third
  else none

def eval (m : Module) (packet offsets : Array UInt32) (gid : UInt32) (r : Registers) : Expr → Option UInt32 :=
  evalWith (fun name addr => do
    let d ← m.lookup name
    if d.group != 0 || d.mode != .read then none
    else if d.slot == 0 then packet[addr.toNat]?
    else if d.slot == 1 then offsets[addr.toNat]?
    else none) gid (fun
      | .word0 => some r.word0
      | .word1 => some r.word1
      | .bound => some r.bound
      | .index => some r.index)

def write (m : Module) (packet offsets : Array UInt32) (gid : UInt32) (r : Registers) (s : Storage) :
    Option Storage := do
  let op := m.code.store
  let d ← m.lookup op.destination
  if d.group != 0 || d.slot != 2 || d.mode != .readWrite then return ← none
  let addr ← eval m packet offsets gid r op.address
  let word ← eval m packet offsets gid r op.value
  if h : addr.toNat < s.dst.size then
    return ⟨s.dst.set addr.toNat word h, s.writes.push ⟨d.group, d.slot, addr, word⟩⟩
  else none

def running (m : Module) (packet offsets : Array UInt32) (gid : UInt32) (r : Registers) : Option Bool := do
  let a ← eval m packet offsets gid r m.code.testLeft
  let b ← eval m packet offsets gid r m.code.testRight
  return decide (a < b)

def loop (m : Module) (packet offsets : Array UInt32) (gid : UInt32) : Nat → Registers → Storage → Option Storage
  | 0, r, s => do if (← running m packet offsets gid r) then none else return s
  | k + 1, r, s => do
    if (← running m packet offsets gid r) then
      let next ← write m packet offsets gid r s
      let index ← eval m packet offsets gid r m.code.increment
      loop m packet offsets gid k {r with index} next
    else return s

def active (m : Module) (packet offsets prior : Array UInt32) (gid : UInt32) : Option ScanSurface.Outcome := do
  let r : Registers := ⟨0, 0, 0, 0⟩
  let a ← eval m packet offsets gid r m.code.initial0
  let r := {r with word0 := a}
  let b ← eval m packet offsets gid r m.code.initial1
  let r := {r with word1 := b}
  let a ← eval m packet offsets gid r m.code.assign0
  let r := {r with word0 := a}
  let b ← eval m packet offsets gid r m.code.assign1
  let r := {r with word1 := b}
  let bound ← eval m packet offsets gid r m.code.snapshot
  let r := {r with bound}
  let a ← eval m packet offsets gid r m.code.limitLeft
  let b ← eval m packet offsets gid r m.code.limitRight
  if a > b then return ⟨prior, [], true⟩
  let index ← eval m packet offsets gid r m.code.initialIndex
  let s ← loop m packet offsets gid (min bound.toNat 1024) {r with index} ⟨prior, #[]⟩
  return ⟨s.dst, s.writes.toList, false⟩

def run (m : Module) (packet offsets prior : Array UInt32) (gid : UInt32) : Option ScanSurface.Outcome := do
  let r : Registers := ⟨0, 0, 0, 0⟩
  let a ← eval m packet offsets gid r m.code.laneLeft
  let b ← eval m packet offsets gid r m.code.laneRight
  if a < b then active m packet offsets prior gid else return ⟨prior, [], false⟩

def runText (bytes : ByteArray) (packet offsets prior : Array UInt32) (gid : UInt32) : Option ScanSurface.Outcome := do
  let m ← parseShader bytes
  run m packet offsets prior gid

end L4Factoidal.Paralliverse.WGSL.ScatterSurface
