/-
L4Factoidal.EXPath.Binary.Octets — the octet-level operations of the
EXPath Binary Module 4.0, as total functions on octet lists.

Spec: EXPath Binary Module 4.0 (https://qt4cg.org/specifications/expath-binary-40/Overview.html,
qtspecs commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c, files
`specifications/expath-binary/src/{binary-functions,function-catalog}.xml`).

A binary value is a list of octets (`List Nat`, each below 256), the
representation `L4Factoidal.XSD.Val.bin` uses for `xs:hexBinary` and
`xs:base64Binary`. The functions here have no error cases; the bounds
checks and the error codes of the specification are in
`EXPath.Binary.Lib`, which calls these only with arguments in range.
The theorems are in `EXPath.Binary.Theorems`.

Bit numbering (§ bin:is-bit-set): bit 0 is the most significant bit of
the first octet. Shifts and rotations treat the value as one
big-endian number of `8 * length` bits (§ bin:shift, "big-endian
treatment").
-/
namespace L4Factoidal.EXPath.Binary

/-! ## Octets and numbers -/

/-- The number that octets denote, most significant octet first. A
left fold (one frame for any length). -/
def beValue (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- The `n` low-order octets of `v`, most significant first: the
big-endian representation of `v mod 256^n`. -/
def packBE : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => packBE n (v / 256) ++ [v % 256]

/-- `packBE` with an accumulator, the form that runs (one frame for any
size); `packBE_eq_packBEAcc` proves it equal to `packBE`. -/
def packBEAcc : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, v, acc => packBEAcc n (v / 256) (v % 256 :: acc)

/-- Two's complement of an integer in `n` octets: `v mod 256^n`. -/
def twosComplement (n : Nat) (v : Int) : Nat := (v % ((256 : Int) ^ n)).toNat

/-- Read `n` octets as a signed two's-complement number. -/
def signedOf (n : Nat) (u : Nat) : Int :=
  if n > 0 && u ≥ 256 ^ n / 2 then (u : Int) - (256 : Int) ^ n else u

/-! ## Slices -/

/-- `bin:part` without its checks: `size` octets from `off`. -/
def part (bs : List Nat) (off size : Nat) : List Nat := (bs.drop off).take size

/-- `bin:insert-before` without its checks. -/
def insertBefore (bs : List Nat) (off : Nat) (extra : List Nat) : List Nat :=
  bs.take off ++ extra ++ bs.drop off

/-- The first position at or after `off` where `pat` occurs. A loop
with a counter (one frame for any length). -/
def findFrom (bs pat : List Nat) (off : Nat) : Option Nat :=
  let rec go (rest : List Nat) (i : Nat) : Option Nat :=
    if pat.isPrefixOf rest then some i
    else match rest with
      | [] => none
      | _ :: r => go r (i + 1)
  go (bs.drop off) off

/-! ## Bitwise operations -/

def octetOr (a b : Nat) : Nat := a ||| b
def octetAnd (a b : Nat) : Nat := a &&& b
def octetXor (a b : Nat) : Nat := a ^^^ b
def octetNot (a : Nat) : Nat := 255 - a

/-- `bin:shift`: shift the bits of the value `by` places to the left
(negative: to the right), keeping the length. -/
def shiftBits (bs : List Nat) (by_ : Int) : List Nat :=
  let n := bs.length
  let v := beValue bs
  let r := if by_ ≥ 0 then (v <<< by_.toNat) % (2 ^ (8 * n)) else v >>> (-by_).toNat
  packBEAcc n r []

/-- `bin:rotate`: rotate cyclically, modulo the bit length. -/
def rotateBits (bs : List Nat) (by_ : Int) : List Nat :=
  let n := bs.length
  let w := 8 * n
  if w == 0 then bs else
  let k := (by_ % (w : Int)).toNat
  if k == 0 then bs else
  let v := beValue bs
  let r := ((v <<< k) ||| (v >>> (w - k))) % (2 ^ w)
  packBEAcc n r []

/-- Whether bit `i` (0 = most significant of the first octet) is set. -/
def bitSet (bs : List Nat) (i : Nat) : Bool :=
  (bs.getD (i / 8) 0 >>> (7 - i % 8)) % 2 == 1

/-- Set (`b` true) or clear bit `i`. -/
def setBit (bs : List Nat) (i : Nat) (b : Bool) : List Nat :=
  let mask := 1 <<< (7 - i % 8)
  bs.modify (i / 8) (fun o => if b then o ||| mask else o &&& (255 - mask))

/-- The number of one bits in an octet. -/
def popcount8 (o : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc + (o >>> k) % 2) 0

def countBits (bs : List Nat) : Nat := bs.foldl (fun acc o => acc + popcount8 o) 0

/-! ## Numeric constructors (bin:hex, bin:bin, bin:octal) -/

def isStripped (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '_'

/-- The value of a hexadecimal digit. -/
def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Octets from an even number of hexadecimal digits. -/
def hexPairs : List Nat → List Nat
  | a :: b :: r => (a * 16 + b) :: hexPairs r
  | _ => []

/-- `bin:hex` on a string: strip, pad to even length, read pairs;
`none` for a character that is not a hexadecimal digit. -/
def ofHex (s : String) : Option (List Nat) := do
  let ds ← (s.toList.filter (! isStripped ·)).mapM hexDigit?
  let ds := if ds.length % 2 == 1 then 0 :: ds else ds
  pure (hexPairs ds)

/-- Octets from groups of 8 binary digits (most significant first). -/
def bitGroups (ds : List Nat) : List Nat :=
  let rec go (rest : List Nat) (acc : Array Nat) (fuel : Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if rest.isEmpty then acc
      else go (rest.drop 8) (acc.push ((rest.take 8).foldl (fun a d => a * 2 + d) 0)) f
  (go ds #[] (ds.length / 8 + 1)).toList

/-- `bin:bin` on a list of binary digits: pad on the left to a multiple
of 8, then read groups of 8. -/
def ofBits (ds : List Nat) : List Nat :=
  let pad := (8 - ds.length % 8) % 8
  bitGroups (List.replicate pad 0 ++ ds)

def bitDigit? (c : Char) : Option Nat :=
  if c == '0' then some 0 else if c == '1' then some 1 else none

def ofBin (s : String) : Option (List Nat) := do
  let ds ← (s.toList.filter (! isStripped ·)).mapM bitDigit?
  pure (ofBits ds)

def octDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '7' then some (c.toNat - 48) else none

/-- `bin:octal`: each digit becomes three bits; at most two leading
zero bits are removed; the result is read as by `bin:bin`. -/
def ofOctal (s : String) : Option (List Nat) := do
  let ds ← (s.toList.filter (! isStripped ·)).mapM octDigit?
  let bits := ds.flatMap (fun d => [d / 4, d / 2 % 2, d % 2])
  let bits := match bits with
    | 0 :: 0 :: r => r
    | 0 :: r => r
    | r => r
  pure (ofBits bits)

/-! ## Octet order -/

/-- `true` for least-significant-first (`least-significant-first`,
`little-endian`, `LE`). -/
def isLittle (order : String) : Bool :=
  order == "least-significant-first" || order == "little-endian" || order == "LE"

def orderBytes (little : Bool) (bs : List Nat) : List Nat := if little then bs.reverse else bs

#guard packBE 2 0x1234 == [0x12, 0x34]
#guard packBEAcc 2 0x1234 [] == [0x12, 0x34]
#guard beValue [0x12, 0x34] == 0x1234
#guard twosComplement 2 (-1) == 0xFFFF
#guard signedOf 2 0xFFFF == -1
#guard shiftBits [0x80, 0x01] 1 == [0x00, 0x02]
#guard shiftBits [0x80, 0x01] (-1) == [0x40, 0x00]
#guard rotateBits [0x80, 0x01] 1 == [0x00, 0x03]
#guard bitSet [0x80] 0 && !bitSet [0x80] 1
#guard setBit [0x00] 7 true == [0x01]
#guard countBits [0xFF, 0x01] == 9
#guard ofHex "1_2 3" == some [0x01, 0x23]
#guard ofBin "1101000111010101" == some [0xD1, 0xD5]
#guard ofOctal "0" == some [0]
#guard ofOctal "155" == some [0x6D]
#guard ofOctal "355" == some [0xED]
#guard ofOctal "555" == some [0x01, 0x6D]
#guard ofOctal "0155" == some [0x00, 0x6D]
#guard ofOctal "177 177 177 177" == some [0x03, 0xF9, 0xFC, 0xFE, 0x7F]
#guard findFrom [1, 2, 3, 2, 3] [2, 3] 2 == some 3

end L4Factoidal.EXPath.Binary
