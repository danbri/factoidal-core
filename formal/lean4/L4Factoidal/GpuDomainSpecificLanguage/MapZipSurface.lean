import L4Factoidal.Paralliverse.WGSL.Surface
import L4Factoidal.GpuDomainSpecificLanguage.MapZipShader

/-!
# Concrete WGSL syntax and execution for the PVGraph map/zip kernel

The parser consumes the complete byte string. It reads four storage declarations,
the compute entry and workgroup dimensions, a guarded block, and at most eight
if/else-if stores. It does not identify a program by its hash or assign an opcode
directly to shader text: addresses, conditions and arithmetic are parsed into
expressions and executed below. Expression depth is four and source is at most
4,096 bytes. Unsupported syntax or an executed out-of-bounds access returns none.

The refinement is restricted to the exact `MapZipShader.source` bytes required
by the shipping validator. The shared lexer splits punctuation and drops white
space, so this parser alone is not an arbitrary-WGSL validity checker (for
example, it does not distinguish `==` from `= =`). No theorem or runtime
certificate extends the claim to those other parser-accepted strings.

This is a concrete fragment of WGSL, not a theorem about a browser's WGSL
compiler or device. Larger kernels remain tracked in
https://github.com/danbri/factoidal-core/issues/707.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipSurface

open L4Factoidal.Paralliverse.WGSL
open Surface (Token Tokens Parser takeToken expect)

inductive Name where
  | a | b | outWords | config
  deriving DecidableEq, Repr

structure Binding where
  group : Nat
  slot : Nat
  writable : Bool
  name : Name
  deriving DecidableEq, Repr

inductive Expr where
  | literal (value : UInt32)
  | gidX
  | load (name : Name) (address : Expr)
  | add (left right : Expr)
  | mul (left right : Expr)
  | xor (left right : Expr)
  deriving DecidableEq, Repr

structure Arm where
  left : Expr
  right : Expr
  destination : Name
  address : Expr
  value : Expr
  deriving DecidableEq, Repr

structure Module where
  bindings : List Binding
  sizeX : Nat
  sizeY : Nat
  sizeZ : Nat
  left : Expr
  right : Expr
  arms : List Arm
  deriving DecidableEq, Repr

private def spelling (s : String) : Token := s.toUTF8.data.toList

private def natural (token : Token) : Option Nat := do
  let first :: rest := token | none
  if first == 48 && !rest.isEmpty then none
  else token.foldlM (fun value b =>
    if b < 48 || 57 < b then none
    else
      let next := value * 10 + (b.toNat - 48)
      if next < UInt32.size then some next else none) 0

private def number : Parser Nat := fun ts => do
  let (t, rest) ← takeToken ts
  return (← natural t, rest)

private def wordLiteral (t : Token) : Option UInt32 := do
  let suffix :: digits := t.reverse | none
  if suffix == 117 then return UInt32.ofNat (← natural digits.reverse)
  else none

private def bufferName (t : Token) : Option Name :=
  if t == spelling "a" then some .a
  else if t == spelling "b" then some .b
  else if t == spelling "outWords" then some .outWords
  else if t == spelling "config" then some .config
  else none

private def binding : Parser Binding := fun ts => do
  let ts ← expect ["@", "group", "("] ts
  let (group, ts) ← number ts
  let ts ← expect [")", "@", "binding", "("] ts
  let (slot, ts) ← number ts
  let ts ← expect [")", "var", "<", "storage", ","] ts
  let (mode, ts) ← takeToken ts
  let writable ← if mode == spelling "read" then some false
    else if mode == spelling "read_write" then some true else none
  let ts ← expect [">"] ts
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect [":", "array", "<", "u32", ">", ";"] ts
  return (⟨group, slot, writable, name⟩, ts)

private def fourLayers {α : Type} (layer : α → α) (bottom : α) : α :=
  layer (layer (layer (layer bottom)))

private def exprLayer (sub : Parser Expr) : Parser Expr := fun ts => do
  let (t, ts) ← takeToken ts
  if t == spelling "(" then
    let (a, ts) ← sub ts
    let (op, ts) ← takeToken ts
    let (b, ts) ← sub ts
    let ts ← expect [")"] ts
    if op == spelling "+" then return (.add a b, ts)
    else if op == spelling "*" then return (.mul a b, ts)
    else if op == spelling "^" then return (.xor a b, ts)
    else none
  else if t == spelling "pv_gid" then return (.gidX, ← expect [".", "x"] ts)
  else if let some name := bufferName t then
    let ts ← expect ["["] ts
    let (i, ts) ← sub ts
    return (.load name i, ← expect ["]"] ts)
  else return (.literal (← wordLiteral t), ts)

def expression : Parser Expr := fourLayers exprLayer (fun _ => none)

private def arm : Parser Arm := fun ts => do
  let ts ← expect ["if", "("] ts
  let (a, ts) ← expression ts
  let ts ← expect ["=", "="] ts
  let (b, ts) ← expression ts
  let ts ← expect [")", "{"] ts
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect ["["] ts
  let (i, ts) ← expression ts
  let ts ← expect ["]", "="] ts
  let (v, ts) ← expression ts
  let ts ← expect [";", "}"] ts
  return (⟨a, b, name, i, v⟩, ts)

private def arms : Nat → Parser (List Arm)
  | 0 => fun _ => none
  | fuel + 1 => fun ts => do
      let (a, ts) ← arm ts
      match ts with
      | next :: rest =>
          if next == spelling "else" then
            let (as, ts) ← arms fuel rest
            return (a :: as, ts)
          else return ([a], ts)
      | [] => return ([a], ts)

private def distinct (a b : Binding) : Bool :=
  a.name != b.name && (a.group != b.group || a.slot != b.slot)

/-- Parse every source byte; the numeric and syntax limits return none. -/
def parseShader (bytes : ByteArray) : Option Module := do
  if bytes.size > 4096 then return ← none
  let (a, ts) ← binding (Surface.lex bytes)
  let (b, ts) ← binding ts
  let (c, ts) ← binding ts
  let (d, ts) ← binding ts
  if !(distinct a b && distinct a c && distinct a d &&
      distinct b c && distinct b d && distinct c d) then return ← none
  let ((x,y,z), ts) ← Surface.entry ts
  let ts ← expect ["if", "("] ts
  let (left, ts) ← expression ts
  let ts ← expect ["<"] ts
  let (right, ts) ← expression ts
  let ts ← expect [")", "{"] ts
  let (body, ts) ← arms 8 ts
  let ts ← expect ["}", "}"] ts
  if ts.isEmpty then return ⟨[a,b,c,d],x,y,z,left,right,body⟩ else none

def Module.lookup (m : Module) (name : Name) : Option Binding :=
  m.bindings.find? (fun decl => decl.name == name)

/-- Read-only storage bound at the three actual PVGraph input/config slots. -/
structure Inputs where
  a : Array UInt32
  b : Array UInt32
  config : Array UInt32

private def readAt (m : Module) (inputs : Inputs) (name : Name) (address : UInt32) :
    Option UInt32 := do
  let decl ← m.lookup name
  if decl.group != 0 || decl.writable then none
  else if decl.slot == 0 then inputs.a[address.toNat]?
  else if decl.slot == 1 then inputs.b[address.toNat]?
  else if decl.slot == 3 then inputs.config[address.toNat]?
  else none

private def evalLayer (read : Name → UInt32 → Option UInt32) (gid : UInt32)
    (sub : Expr → Option UInt32) : Expr → Option UInt32
  | .literal n => some n
  | .gidX => some gid
  | .load name address => do read name (← sub address)
  | .add a b => do return (← sub a) + (← sub b)
  | .mul a b => do return (← sub a) * (← sub b)
  | .xor a b => do return (← sub a) ^^^ (← sub b)

/-- Wrapping-u32 expression semantics, with checked storage reads. -/
def eval (m : Module) (inputs : Inputs) (gid : UInt32) : Expr → Option UInt32 :=
  fourLayers (evalLayer (readAt m inputs) gid) (fun _ => none)

private def runArms (m : Module) (inputs : Inputs) (prior : Array UInt32) (gid : UInt32) :
    List Arm → Option Surface.Outcome
  | [] => some ⟨prior,[]⟩
  | arm :: rest => do
      let left ← eval m inputs gid arm.left
      let right ← eval m inputs gid arm.right
      if left == right then
        let dest ← m.lookup arm.destination
        if dest.group != 0 || dest.slot != 2 || !dest.writable then none
        else
          let address ← eval m inputs gid arm.address
          let value ← eval m inputs gid arm.value
          if h : address.toNat < prior.size then
            some ⟨prior.set address.toNat value h, [⟨dest.group,dest.slot,address,value⟩]⟩
          else none
      else runArms m inputs prior gid rest

/-- Execute the parsed outer guard, opcode comparisons and selected store.
    The destination is a distinct allocation; host correspondence is external. -/
def run (m : Module) (inputs : Inputs) (prior : Array UInt32) (gid : UInt32) :
    Option Surface.Outcome := do
  let left ← eval m inputs gid m.left
  let right ← eval m inputs gid m.right
  if left < right then runArms m inputs prior gid m.arms
  else some ⟨prior,[]⟩

def runText (bytes : ByteArray) (inputs : Inputs) (prior : Array UInt32) (gid : UInt32) :
    Option Surface.Outcome := do
  let m ← parseShader bytes
  run m inputs prior gid

end L4Factoidal.GpuDomainSpecificLanguage.MapZipSurface
