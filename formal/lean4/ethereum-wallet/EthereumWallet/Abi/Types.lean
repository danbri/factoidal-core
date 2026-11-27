import EthereumWallet.Abi.Bytes

/-!
# Solidity ABI types and values

`AbiType` is the type grammar of the Solidity contract ABI: `uint<M>`,
`int<M>`, `address`, `bool`, `bytes<M>`, `bytes`, `string`, `T[]`, `T[k]` and
tuples. `fixed`/`ufixed` and `function` are not accepted yet (the parser
refuses them). `AbiValue` is untyped: `AbiType.check` says when a value has a
type.

Every function here recurses on the type, so the recursion depth is the
nesting depth of the type, which the public entry points bound by
`maxTypeDepth`.
-/

namespace EthereumWallet.Abi

inductive AbiType where
  | uint (bits : Nat)
  | int (bits : Nat)
  | address
  | bool
  | fixedBytes (n : Nat)
  | bytes
  | string
  | array (elem : AbiType)
  | fixedArray (elem : AbiType) (len : Nat)
  | tuple (fields : List AbiType)

instance : Inhabited AbiType := ⟨.bool⟩

inductive AbiValue where
  | uint (n : Nat)
  | int (i : Int)
  | address (a : Nat)
  | bool (b : Bool)
  /-- `bytes<M>`, `bytes` and `string` (the UTF-8 bytes, not validated here). -/
  | bytes (b : List UInt8)
  /-- Arrays and tuples. -/
  | seq (vs : List AbiValue)

instance : Inhabited AbiValue := ⟨.bool false⟩

/-- Nesting bound for types taken from outside (signatures, typed data). -/
def maxTypeDepth : Nat := 32

mutual
/-- Dynamic types are encoded out of line, behind an offset. -/
def AbiType.isDynamic : AbiType → Bool
  | .bytes => true
  | .string => true
  | .array _ => true
  | .fixedArray t _ => t.isDynamic
  | .tuple ts => anyDynamic ts
  | _ => false
def anyDynamic : List AbiType → Bool
  | [] => false
  | t :: ts => t.isDynamic || anyDynamic ts
end

mutual
/-- Bytes a value of this type takes in its parent's head: 32 for a dynamic
    type (the offset), the whole encoding for a static one. -/
def AbiType.headSize : AbiType → Nat
  | .fixedArray t n => if t.isDynamic then 32 else n * t.headSize
  | .tuple ts => if anyDynamic ts then 32 else headSizeL ts
  | _ => 32
def headSizeL : List AbiType → Nat
  | [] => 0
  | t :: ts => t.headSize + headSizeL ts
end

mutual
/-- Widths in range, and no zero-size element anywhere: no empty tuple and no
    `T[0]`. A well-formed type has a head of at least 32 bytes, which is what
    lets a decoder bound an array count by the data that is left. -/
def AbiType.wf : AbiType → Bool
  | .uint b => decide (8 ≤ b ∧ b ≤ 256 ∧ b % 8 = 0)
  | .int b => decide (8 ≤ b ∧ b ≤ 256 ∧ b % 8 = 0)
  | .fixedBytes n => decide (1 ≤ n ∧ n ≤ 32)
  | .array t => t.wf
  | .fixedArray t n => decide (1 ≤ n) && t.wf
  | .tuple ts => !ts.isEmpty && wfL ts
  | _ => true
def wfL : List AbiType → Bool
  | [] => true
  | t :: ts => t.wf && wfL ts
end

mutual
def AbiType.depth : AbiType → Nat
  | .array t => t.depth + 1
  | .fixedArray t _ => t.depth + 1
  | .tuple ts => depthL ts + 1
  | _ => 0
def depthL : List AbiType → Nat
  | [] => 0
  | t :: ts => max t.depth (depthL ts)
end

mutual
/-- The canonical type string used in signatures. -/
def AbiType.canonical : AbiType → String
  | .uint b => "uint" ++ toString b
  | .int b => "int" ++ toString b
  | .address => "address"
  | .bool => "bool"
  | .fixedBytes n => "bytes" ++ toString n
  | .bytes => "bytes"
  | .string => "string"
  | .array t => t.canonical ++ "[]"
  | .fixedArray t n => t.canonical ++ "[" ++ toString n ++ "]"
  | .tuple ts => "(" ++ canonicalL ts ++ ")"
def canonicalL : List AbiType → String
  | [] => ""
  | t :: ts =>
    match ts with
    | [] => t.canonical
    | _ :: _ => t.canonical ++ "," ++ canonicalL ts
end

/-- Two's-complement range of `int<bits>`. -/
def intInRange (bits : Nat) : Int → Bool
  | .ofNat n => decide (n < 2 ^ (bits - 1))
  | .negSucc n => decide (n < 2 ^ (bits - 1))

def intToWord : Int → Nat
  | .ofNat n => n
  | .negSucc n => two256 - (n + 1)

def wordToInt (w : Nat) : Int :=
  if w < two255 then Int.ofNat w else Int.negSucc (two256 - w - 1)

mutual
/-- `t.check v`: the value `v` has type `t`. -/
def AbiType.check : AbiType → AbiValue → Bool
  | .uint bits, v => match v with | .uint n => decide (n < 2 ^ bits) | _ => false
  | .int bits, v => match v with | .int i => intInRange bits i | _ => false
  | .address, v => match v with | .address a => decide (a < 2 ^ 160) | _ => false
  | .bool, v => match v with | .bool _ => true | _ => false
  | .fixedBytes k, v => match v with | .bytes b => decide (b.length = k) | _ => false
  | .bytes, v => match v with | .bytes _ => true | _ => false
  | .string, v => match v with | .bytes _ => true | _ => false
  | .array t, v => match v with | .seq vs => vs.all (fun x => t.check x) | _ => false
  | .fixedArray t n, v =>
    match v with
    | .seq vs => decide (vs.length = n) && vs.all (fun x => t.check x)
    | _ => false
  | .tuple ts, v => match v with | .seq vs => checkL ts vs | _ => false
def checkL : List AbiType → List AbiValue → Bool
  | [], vs => vs.isEmpty
  | t :: ts, vs =>
    match vs with
    | v :: vs' => t.check v && checkL ts vs'
    | [] => false
end

end EthereumWallet.Abi
