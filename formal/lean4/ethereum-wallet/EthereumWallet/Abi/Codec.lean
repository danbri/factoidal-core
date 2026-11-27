import EthereumWallet.Abi.Types

/-!
# Solidity ABI encoding and single-pass decoding

`AbiType.enc` is the encoding of the Solidity ABI specification, written as
lists. `AbiType.decodeAt` reads a value of a given type at a position in an
untrusted byte array:

* every read is range-checked first (`readWord`, and the explicit size tests);
* an array count is refused unless that many element heads fit in the data
  that is left, before anything is allocated for it;
* a dynamic value's offset must be exactly where the canonical encoding puts
  it (the end of the previous tail), so no byte is decoded twice and two
  offsets cannot share or overlap a tail;
* bits outside a value's width and nonzero padding are refused;
* a width over 256 bits or over 32 bytes is refused before it is used as a size.

The loop over fields (`runFields`) is tail-recursive. The decoder recurses
only through the type, so its depth is the type's nesting depth.
-/

namespace EthereumWallet.Abi

/-! ## Encoding -/

/-- Sum of the head sizes of a sequence of fields `(dynamic?, encoding)`. -/
def headTotal (fs : List (Bool × List UInt8)) : Nat :=
  fs.foldl (fun a f => a + (if f.1 then 32 else f.2.length)) 0

def headsLoop : List (Bool × List UInt8) → Nat → List (List UInt8) → List (List UInt8)
  | [], _, acc => acc.reverse
  | f :: fs, cur, acc =>
    if f.1 then headsLoop fs (cur + f.2.length) (word cur :: acc)
    else headsLoop fs cur (f.2 :: acc)

/-- Heads of a sequence: a static field's encoding, a dynamic field's offset.
    `cur` is the offset of the next tail. -/
def heads (fs : List (Bool × List UInt8)) (cur : Nat) : List UInt8 :=
  (headsLoop fs cur []).flatten

/-- Tails of a sequence: the encodings of its dynamic fields, in order. -/
def tails (fs : List (Bool × List UInt8)) : List UInt8 :=
  (fs.filterMap fun f => if f.1 then some f.2 else none).flatten

/-- `enc(X) = head(X1) ... head(Xk) tail(X1) ... tail(Xk)`. -/
def encSeq (fs : List (Bool × List UInt8)) : List UInt8 :=
  heads fs (headTotal fs) ++ tails fs

/-- `bytes` and `string`: length, content, zero padding to a word. -/
def encBytes (b : List UInt8) : List UInt8 :=
  word b.length ++ b ++ List.replicate (padLen b.length) 0

mutual
/-- The ABI encoding of `v` at type `t`. Defined (as the empty list) on
    ill-typed input; the theorems are about values with `t.check v`. -/
def AbiType.enc : AbiType → AbiValue → List UInt8
  | .uint _, v => match v with | .uint n => word n | _ => []
  | .int _, v => match v with | .int i => word (intToWord i) | _ => []
  | .address, v => match v with | .address a => word a | _ => []
  | .bool, v => match v with | .bool b => word (if b then 1 else 0) | _ => []
  | .fixedBytes k, v => match v with | .bytes b => b ++ List.replicate (32 - k) 0 | _ => []
  | .bytes, v => match v with | .bytes b => encBytes b | _ => []
  | .string, v => match v with | .bytes b => encBytes b | _ => []
  | .array t, v =>
    match v with
    | .seq vs => word vs.length ++ encSeq (vs.map fun x => (t.isDynamic, t.enc x))
    | _ => []
  | .fixedArray t _, v =>
    match v with
    | .seq vs => encSeq (vs.map fun x => (t.isDynamic, t.enc x))
    | _ => []
  | .tuple ts, v => match v with | .seq vs => encSeq (encL ts vs) | _ => []
def encL : List AbiType → List AbiValue → List (Bool × List UInt8)
  | [], _ => []
  | t :: ts, vs =>
    match vs with
    | v :: vs' => (t.isDynamic, t.enc v) :: encL ts vs'
    | [] => []
end

/-! ## Decoding -/

/-- A field decoder: whether the field is dynamic, and how to read it at a position.
    A read returns the value and the number of bytes its encoding takes. -/
structure FieldDec where
  dyn : Bool
  run : Nat → Except Err (AbiValue × Nat)

/-- Decode the fields of a sequence whose encoding starts at `base`. `hp` is the
    position of the next head and `cur` the position of the next tail, both
    relative to `base`. A dynamic field's offset must equal `cur`. -/
def runFields (d : ByteArray) (base : Nat) :
    List FieldDec → Nat → Nat → List AbiValue → Except Err (List AbiValue × Nat)
  | [], _, cur, acc => .ok (acc.reverse, cur)
  | f :: fs, hp, cur, acc =>
    if f.dyn then
      match readWord d (base + hp) with
      | .error e => .error e
      | .ok o =>
        if o = cur then
          match f.run (base + cur) with
          | .error e => .error e
          | .ok r => runFields d base fs (hp + 32) (cur + r.2) (r.1 :: acc)
        else .error .badOffset
    else
      match f.run (base + hp) with
      | .error e => .error e
      | .ok r => runFields d base fs (hp + r.2) cur (r.1 :: acc)

def decBytes (d : ByteArray) (p : Nat) : Except Err (AbiValue × Nat) :=
  match readWord d p with
  | .error e => .error e
  | .ok n =>
    if n ≤ d.size - (p + 32) then
      if p + 32 + n + padLen n ≤ d.size then
        if allZero d (p + 32 + n) (padLen n) then
          .ok (.bytes (takeBytes d (p + 32) n), 32 + n + padLen n)
        else .error .dirtyPadding
      else .error .outOfBounds
    else .error .lengthOutOfBounds

/-- The count check made before an array's elements are decoded: every element
    has a nonzero head, and `n` heads fit in the `rem` bytes that are left. -/
def countOk (headSize n rem : Nat) : Bool :=
  decide (0 < headSize ∧ n * headSize ≤ rem)

mutual
def AbiType.decodeAt : AbiType → ByteArray → Nat → Except Err (AbiValue × Nat)
  | .uint bits, d, p =>
    match readWord d p with
    | .error e => .error e
    | .ok w =>
      if bits ≤ 256 then
        if w < 2 ^ bits then .ok (.uint w, 32) else .error .dirtyPadding
      else .error .badType
  | .int bits, d, p =>
    match readWord d p with
    | .error e => .error e
    | .ok w =>
      if bits ≤ 256 then
        if intInRange bits (wordToInt w) then .ok (.int (wordToInt w), 32)
        else .error .dirtyPadding
      else .error .badType
  | .address, d, p =>
    match readWord d p with
    | .error e => .error e
    | .ok w => if w < 2 ^ 160 then .ok (.address w, 32) else .error .dirtyPadding
  | .bool, d, p =>
    match readWord d p with
    | .error e => .error e
    | .ok w =>
      if w = 0 then .ok (.bool false, 32)
      else if w = 1 then .ok (.bool true, 32)
      else .error .dirtyPadding
  | .fixedBytes k, d, p =>
    if k ≤ 32 then
      if p + 32 ≤ d.size then
        if allZero d (p + k) (32 - k) then .ok (.bytes (takeBytes d p k), 32)
        else .error .dirtyPadding
      else .error .outOfBounds
    else .error .badType
  | .bytes, d, p => decBytes d p
  | .string, d, p => decBytes d p
  | .array t, d, p =>
    match readWord d p with
    | .error e => .error e
    | .ok n =>
      if countOk t.headSize n (d.size - (p + 32)) then
        match runFields d (p + 32) (List.replicate n ⟨t.isDynamic, t.decodeAt d⟩) 0
            (n * t.headSize) [] with
        | .error e => .error e
        | .ok r => .ok (.seq r.1, 32 + r.2)
      else .error .lengthOutOfBounds
  | .fixedArray t n, d, p =>
    if countOk t.headSize n (d.size - p) then
      match runFields d p (List.replicate n ⟨t.isDynamic, t.decodeAt d⟩) 0 (n * t.headSize) [] with
      | .error e => .error e
      | .ok r => .ok (.seq r.1, r.2)
    else .error .lengthOutOfBounds
  | .tuple ts, d, p =>
    match runFields d p (fieldDecs ts d) 0 (headSizeL ts) [] with
    | .error e => .error e
    | .ok r => .ok (.seq r.1, r.2)
def fieldDecs : List AbiType → ByteArray → List FieldDec
  | [], _ => []
  | t :: ts, d => ⟨t.isDynamic, t.decodeAt d⟩ :: fieldDecs ts d
end

/-! ## Argument lists (the top level of calldata, return data and event data) -/

/-- The encoding of an argument list: the tuple of the arguments. -/
def encodeArgs (ts : List AbiType) (vs : List AbiValue) : List UInt8 :=
  encSeq (encL ts vs)

end EthereumWallet.Abi
