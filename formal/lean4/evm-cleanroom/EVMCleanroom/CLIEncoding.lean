import EVMCleanroom.Core

/-! Shared hex encoders and EVM error labels for the native entry points. -/

namespace EVMCleanroom.CLI

private def nibble (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 65 + 10)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10)
  else none

private def decodePairs : List Char → Array UInt8 → Except String (Array UInt8)
  | [], acc => .ok acc
  | [_], _ => .error "odd-length hex bytecode"
  | hi :: lo :: rest, acc =>
    match nibble hi, nibble lo with
    | some a, some b =>
      decodePairs rest (acc.push (UInt8.ofNat (16 * a + b)))
    | _, _ => .error "invalid hex bytecode"

def parseBytecode (s : String) : Except String (Array UInt8) :=
  match s.toList with
  | '0' :: 'x' :: cs => decodePairs cs #[]
  | '0' :: 'X' :: cs => decodePairs cs #[]
  | cs => decodePairs cs #[]

def errorCode : EVMCleanroom.Error → String
  | .stackUnderflow => "stackUnderflow"
  | .stackOverflow => "stackOverflow"
  | .outOfGas => "outOfGas"
  | .invalidOpcode _ => "invalidOpcode"
  | .invalidJump _ => "invalidJump"
  | .alreadyHalted => "alreadyHalted"
  | .writeProtection => "writeProtection"
  | .returnDataOutOfBounds => "returnDataOutOfBounds"
  | .resourceLimit => "resourceLimit"
  | .incompleteState _ _ => "incompleteState"
  | .unsupportedFork => "unsupportedFork"
  | .framePolicyViolation _ => "framePolicyViolation"
  | .stepLimit => "stepLimit"
  | .missingBlockHash _ => "missingBlockHash"
  | .addressCollision => "addressCollision"
  | .invalidContractPrefix => "invalidContractPrefix"

def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

def exactViewHex (data : ByteView) : String := Id.run do
  let mut chars := ByteArray.emptyWithCapacity (2 * data.size)
  for index in [:data.size] do
    let byte := (data.readByte index).toNat
    chars := chars.push (UInt8.ofNat (hexDigit (byte / 16)).toNat)
    chars := chars.push (UInt8.ofNat (hexDigit (byte % 16)).toNat)
  return String.fromUTF8! chars

def hexBytes (bs : Array UInt8) : String :=
  String.ofList ((bs.toList).flatMap (fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]))

end EVMCleanroom.CLI
