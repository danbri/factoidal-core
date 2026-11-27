import Beacon.Preset
import L4Factoidal.Crypto.SHA2

/-!
# SSZ codecs and hash tree roots for the beacon chain containers

A `Codec α` carries the SSZ serialisation, deserialisation and
`hash_tree_root` of one type, parameterised by the preset (vector lengths
and list limits differ between `minimal` and `mainnet`). Hashing is the
repository's pure Lean SHA-256. Written from the SSZ specification
(`ssz/simple-serialize.md` and `ssz/merkle-proofs.md` of consensus-specs
v1.6.1); no other implementation is consulted.

The `ssz_container` command declares a structure and its codec from one
field list, at compile time only.
-/

namespace Beacon

@[inline] def sha (b : ByteArray) : ByteArray := L4Factoidal.Crypto.sha256 b

def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

def zero32 : ByteArray := zeroBytes 32

/-- `n` as `width` little-endian bytes (reduced modulo `256 ^ width`). -/
def natLE (n width : Nat) : ByteArray :=
  (List.range width).foldl (fun acc i => acc.push (UInt8.ofNat (n / 256 ^ i % 256))) (ByteArray.emptyWithCapacity width)

/-- Little-endian value of `width` bytes at `pos`; missing bytes read as zero. -/
def leNat (b : ByteArray) (pos width : Nat) : Nat :=
  (List.range width).foldl (fun acc i => acc + (b.get! (pos + i)).toNat * 256 ^ i) 0

def padTo32 (b : ByteArray) : ByteArray :=
  if b.size % 32 == 0 then b else b ++ zeroBytes (32 - b.size % 32)

def mkZeroHashes : Nat → ByteArray → Array ByteArray → Array ByteArray
  | 0, _, acc => acc
  | n + 1, h, acc => mkZeroHashes n (sha (h ++ h)) (acc.push h)

/-- `zeroHashes[d]` is the root of a depth-`d` tree of zero chunks. -/
def zeroHashes : Array ByteArray := mkZeroHashes 65 zero32 #[]

def log2ceilGo : Nat → Nat → Nat → Nat → Nat
  | 0, d, _, _ => d
  | fuel + 1, d, pow, n => if pow ≥ n then d else log2ceilGo fuel (d + 1) (pow * 2) n

/-- Smallest `d ≤ 64` with `2 ^ d ≥ n`. -/
def log2ceil (n : Nat) : Nat := log2ceilGo 64 0 1 n

/-- Hash adjacent pairs of 32-byte chunks; an unpaired last chunk is paired
    with the zero subtree root of this depth. -/
def hashLayer (layer : ByteArray) (d : Nat) : ByteArray := Id.run do
  let n := layer.size / 32
  let mut out := ByteArray.emptyWithCapacity (((n + 1) / 2) * 32)
  for i in [0:(n + 1) / 2] do
    if 64 * i + 64 ≤ layer.size then
      out := out ++ sha (layer.extract (64 * i) (64 * i + 64))
    else
      out := out ++ sha (layer.extract (64 * i) (64 * i + 32) ++ zeroHashes[d]!)
  return out

def merkleizeLoop (depth : Nat) : Nat → ByteArray → ByteArray
  | 0, layer => layer
  | fuel + 1, layer => merkleizeLoop depth fuel (hashLayer layer (depth - (fuel + 1)))

/-- Merkle root of `chunks` (a multiple of 32 bytes) in a tree with room
    for `limit` chunks, padded with zero chunks. -/
def merkleize (chunks : ByteArray) (limit : Nat) : ByteArray :=
  let depth := log2ceil limit
  if chunks.size == 0 then zeroHashes[depth]!
  else merkleizeLoop depth depth chunks

def mixInLength (root : ByteArray) (len : Nat) : ByteArray :=
  sha (root ++ natLE len 32)

structure Codec (α : Type) where
  /-- Serialised size when the type is fixed-size. -/
  fixedSize : Preset → Option Nat
  /-- Basic types are packed into chunks inside lists and vectors. -/
  basic : Bool := false
  encode : Preset → α → ByteArray
  decode : Preset → ByteArray → Except String α
  root : Preset → α → ByteArray

namespace Codec

def u64 : Codec Nat where
  fixedSize _ := some 8
  basic := true
  encode _ n := natLE n 8
  decode _ b := if b.size = 8 then .ok (leNat b 0 8) else .error "uint64: width"
  root _ n := natLE n 8 ++ zeroBytes 24

def u256 : Codec Nat where
  fixedSize _ := some 32
  basic := true
  encode _ n := natLE n 32
  decode _ b := if b.size = 32 then .ok (leNat b 0 32) else .error "uint256: width"
  root _ n := natLE n 32

def bool : Codec Bool where
  fixedSize _ := some 1
  basic := true
  encode _ v := ⟨#[if v then 1 else 0]⟩
  decode _ b :=
    if b.size ≠ 1 then .error "boolean: width"
    else if b.get! 0 == 0 then .ok false
    else if b.get! 0 == 1 then .ok true
    else .error "boolean: value"
  root _ v := natLE (if v then 1 else 0) 32

/-- `ByteVector[n]` (also `Bytes4`, `Bytes20`, `Bytes32`, `Bytes48`, `Bytes96`). -/
def bytesN (n : Nat) : Codec ByteArray where
  fixedSize _ := some n
  encode _ b := b
  decode _ b := if b.size = n then .ok b else .error s!"bytes{n}: width {b.size}"
  root _ b := merkleize (padTo32 b) ((n + 31) / 32)

def bytes32 : Codec ByteArray := bytesN 32

/-- `ByteList[limit]`, also the layout of `List[uint8, limit]`. -/
def byteList (limit : Preset → Nat) : Codec ByteArray where
  fixedSize _ := none
  encode _ b := b
  decode p b := if b.size ≤ limit p then .ok b else .error "byte list: over limit"
  root p b := mixInLength (merkleize (padTo32 b) ((limit p + 31) / 32)) b.size

def concatMap {α : Type} (f : α → ByteArray) (xs : Array α) : ByteArray :=
  xs.foldl (fun acc x => acc ++ f x) ByteArray.empty

/-- Serialise a homogeneous sequence: concatenation for fixed-size
    elements, else an offset table followed by the elements. -/
def encodeSeq {α : Type} (c : Codec α) (p : Preset) (xs : Array α) : ByteArray :=
  match c.fixedSize p with
  | some _ => concatMap (c.encode p) xs
  | none =>
    let parts := xs.map (c.encode p)
    let (table, _) := parts.foldl
      (fun (acc : ByteArray × Nat) part => (acc.1 ++ natLE acc.2 4, acc.2 + part.size))
      (ByteArray.empty, 4 * xs.size)
    parts.foldl (· ++ ·) table

def decodeFixedSeq {α : Type} (c : Codec α) (p : Preset) (size : Nat) (b : ByteArray) :
    Except String (Array α) :=
  if size = 0 then .error "sequence: zero-size element"
  else if b.size % size ≠ 0 then .error "sequence: ragged length"
  else (Array.range (b.size / size)).mapM fun i => c.decode p (b.extract (i * size) (i * size + size))

def decodeVarSeq {α : Type} (c : Codec α) (p : Preset) (b : ByteArray) :
    Except String (Array α) :=
  if b.size = 0 then .ok #[]
  else if b.size < 4 then .error "sequence: truncated offsets"
  else
    let first := leNat b 0 4
    if first % 4 ≠ 0 || first = 0 || first > b.size then .error "sequence: bad first offset"
    else
      let count := first / 4
      (Array.range count).mapM fun i =>
        let lo := leNat b (4 * i) 4
        let hi := if i + 1 < count then leNat b (4 * i + 4) 4 else b.size
        if lo > hi || hi > b.size then .error "sequence: bad offset"
        else c.decode p (b.extract lo hi)

def decodeSeq {α : Type} (c : Codec α) (p : Preset) (b : ByteArray) : Except String (Array α) :=
  match c.fixedSize p with
  | some size => decodeFixedSeq c p size b
  | none => decodeVarSeq c p b

/-- Root of the element sequence before any length mix-in. -/
def seqRoot {α : Type} (c : Codec α) (p : Preset) (xs : Array α) (capacity : Nat) : ByteArray :=
  if c.basic then
    let size := (c.fixedSize p).getD 1
    merkleize (padTo32 (concatMap (c.encode p) xs)) ((capacity * size + 31) / 32)
  else merkleize (concatMap (c.root p) xs) capacity

def vec {α : Type} (c : Codec α) (len : Preset → Nat) : Codec (Array α) where
  fixedSize p := (c.fixedSize p).map (· * len p)
  encode p xs := encodeSeq c p xs
  decode p b := do
    let xs ← decodeSeq c p b
    if xs.size = len p then pure xs else throw "vector: wrong length"
  root p xs := seqRoot c p xs (len p)

def list {α : Type} (c : Codec α) (limit : Preset → Nat) : Codec (Array α) where
  fixedSize _ := none
  encode p xs := encodeSeq c p xs
  decode p b := do
    let xs ← decodeSeq c p b
    if xs.size ≤ limit p then pure xs else throw "list: over limit"
  root p xs := mixInLength (seqRoot c p xs (limit p)) xs.size

def packBits (bits : Array Bool) (byteCount : Nat) : ByteArray :=
  (Array.range byteCount).foldl
    (fun acc i =>
      acc.push (UInt8.ofNat ((List.range 8).foldl
        (fun v j => if bits.getD (8 * i + j) false then v + 2 ^ j else v) 0)))
    (ByteArray.emptyWithCapacity byteCount)

def unpackBits (b : ByteArray) (count : Nat) : Array Bool :=
  (Array.range count).map fun i => (b.get! (i / 8)).toNat / 2 ^ (i % 8) % 2 == 1

def bitvector (len : Preset → Nat) : Codec (Array Bool) where
  fixedSize p := some ((len p + 7) / 8)
  encode p bits := packBits bits ((len p + 7) / 8)
  decode p b :=
    let n := len p
    if b.size ≠ (n + 7) / 8 then .error "bitvector: width"
    else
      let bits := unpackBits b n
      if packBits bits b.size == b then .ok bits else .error "bitvector: stray high bits"
  root p bits := merkleize (padTo32 (packBits bits ((len p + 7) / 8))) ((len p + 255) / 256)

/-- Position of the highest set bit of a non-zero byte. -/
def highBit (v : Nat) : Nat := (List.range 8).foldl (fun acc j => if v / 2 ^ j % 2 == 1 then j else acc) 0

def bitlist (limit : Preset → Nat) : Codec (Array Bool) where
  fixedSize _ := none
  encode _ bits := packBits (bits.push true) (bits.size / 8 + 1)
  decode p b :=
    if b.size = 0 then .error "bitlist: empty"
    else
      let last := (b.get! (b.size - 1)).toNat
      if last = 0 then .error "bitlist: missing delimiter"
      else
        let count := 8 * (b.size - 1) + highBit last
        if count > limit p then .error "bitlist: over limit" else .ok (unpackBits b count)
  root p bits :=
    mixInLength (merkleize (padTo32 (packBits bits ((bits.size + 7) / 8))) ((limit p + 255) / 256)) bits.size

/-! Container helpers used by `ssz_container`. -/

def containerFixed (sizes : List (Option Nat)) : Option Nat :=
  sizes.foldl (fun acc s => match acc, s with
    | some a, some b => some (a + b)
    | _, _ => none) (some 0)

def containerEncode (parts : List (Option Nat × ByteArray)) : ByteArray :=
  let fixedLen := parts.foldl (fun acc part => acc + (match part.1 with | some _ => part.2.size | none => 4)) 0
  let (head, tail) := parts.foldl
    (fun (acc : ByteArray × ByteArray) part =>
      match part.1 with
      | some _ => (acc.1 ++ part.2, acc.2)
      | none => (acc.1 ++ natLE (fixedLen + acc.2.size) 4, acc.2 ++ part.2))
    (ByteArray.empty, ByteArray.empty)
  head ++ tail

/-- Positions of the fields of a container inside `b`: fixed fields in
    place, variable fields between consecutive offsets. Offsets must start
    at the end of the fixed part, never decrease, and stay inside `b`. -/
def containerSplit (sizes : List (Option Nat)) (b : ByteArray) : Except String (Array ByteArray) := do
  let fixedLen := sizes.foldl (fun acc s => acc + s.getD 4) 0
  if b.size < fixedLen then throw "container: shorter than fixed part"
  -- First pass: the start offset of each variable field.
  let (_, offsets) := sizes.foldl
    (fun (acc : Nat × Array Nat) s =>
      match s with
      | some n => (acc.1 + n, acc.2)
      | none => (acc.1 + 4, acc.2.push (leNat b acc.1 4)))
    (0, #[])
  if offsets.size = 0 then
    if b.size ≠ fixedLen then throw "container: trailing bytes"
  else
    if offsets[0]! ≠ fixedLen then throw "container: first offset"
  let bounds := offsets.push b.size
  for i in [0:offsets.size] do
    if bounds[i]! > bounds[i + 1]! then throw "container: offsets out of order"
  let (_, _, parts) := sizes.foldl
    (fun (acc : Nat × Nat × Array ByteArray) s =>
      match s with
      | some n => (acc.1 + n, acc.2.1, acc.2.2.push (b.extract acc.1 (acc.1 + n)))
      | none => (acc.1 + 4, acc.2.1 + 1, acc.2.2.push (b.extract bounds[acc.2.1]! bounds[acc.2.1 + 1]!)))
    (0, 0, #[])
  return parts

def containerRoot (roots : List ByteArray) : ByteArray :=
  merkleize (roots.foldl (· ++ ·) ByteArray.empty) roots.length

end Codec

open Lean in
/-- `ssz_container Name where field : Type := codec, ...` declares the
    structure `Name` and `Name.codec : Codec Name`. -/
macro "ssz_container " name:ident " where " fields:(ident " : " term " := " term),+ : command => do
  let fs := fields.getElems
  let names : Array (TSyntax `ident) := fs.map fun f => ⟨f.raw[0]⟩
  let types : Array (TSyntax `term) := fs.map fun f => ⟨f.raw[2]⟩
  let codecs : Array (TSyntax `term) := fs.map fun f => ⟨f.raw[4]⟩
  let projs : Array (TSyntax `ident) := names.map fun f => mkIdent (name.getId ++ f.getId)
  let codecName := mkIdent (name.getId ++ `codec)
  let ctor := mkIdent (name.getId ++ `mk)
  let mut body ← `((pure $ctor : Except String _))
  let mut fixeds : Array (TSyntax `term) := #[]
  let mut encs : Array (TSyntax `term) := #[]
  let mut roots : Array (TSyntax `term) := #[]
  for i in [0:names.size] do
    let idx := Syntax.mkNumLit (toString i)
    let c := codecs[i]!
    let t := types[i]!
    let proj := projs[i]!
    body ← `($body <*> (Beacon.Codec.decode ($c : Beacon.Codec $t) p (parts[$idx]!)))
    fixeds := fixeds.push (← `(Beacon.Codec.fixedSize ($c : Beacon.Codec $t) p))
    encs := encs.push (← `((Beacon.Codec.fixedSize ($c : Beacon.Codec $t) p, Beacon.Codec.encode ($c : Beacon.Codec $t) p ($proj x))))
    roots := roots.push (← `(Beacon.Codec.root ($c : Beacon.Codec $t) p ($proj x)))
  `(structure $name where
      $[$names:ident : $types]*
      deriving Inhabited, BEq
    def $codecName : Beacon.Codec $name where
      fixedSize := fun p => Beacon.Codec.containerFixed [$fixeds,*]
      encode := fun p x => Beacon.Codec.containerEncode [$encs,*]
      decode := fun p b => (Beacon.Codec.containerSplit [$fixeds,*] b) >>= fun parts => $body
      root := fun p x => Beacon.Codec.containerRoot [$roots,*])

end Beacon
