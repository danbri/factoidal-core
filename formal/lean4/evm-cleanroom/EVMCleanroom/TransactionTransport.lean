import Std

/-!
# Resource checks before transaction JSON parsing

The native CLIs bound input files before calling this module. This additional
linear scan bounds nesting and numeric work before the standard JSON parser
can recurse or construct a large power of ten. It is a resource admission
check, not a replacement JSON parser; grammar and schema checks still follow.
-/
namespace EVMCleanroom.TransactionTransport

def maxDepth : Nat := 64
def maxNumberBytes : Nat := 96
def maxExponent : Nat := 78

structure ScanState where
  depth : Nat := 0
  quoted : Bool := false
  escaped : Bool := false
  numberBytes : Nat := 0
  exponentMode : Bool := false
  exponent : Nat := 0
  deriving Repr, BEq

def digit (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

def numericByte (byte : UInt8) : Bool :=
  digit byte || byte == 46 || byte == 69 || byte == 101 || byte == 43 || byte == 45

/-- Start or end structural/string/token state after a number delimiter.
    Mismatched closing delimiters remain the JSON parser's grammar error. -/
def structural (state : ScanState) (byte : UInt8) : Except String ScanState :=
  let state := { state with numberBytes := 0, exponentMode := false, exponent := 0 }
  if byte == 34 then .ok { state with quoted := true, escaped := false }
  else if byte == 91 || byte == 123 then
    if state.depth ≥ maxDepth then .error "json-nesting-limit"
    else .ok { state with depth := state.depth + 1 }
  else if byte == 93 || byte == 125 then .ok { state with depth := state.depth - 1 }
  else if digit byte || byte == 45 then .ok { state with numberBytes := 1 }
  else .ok state

/-- One bounded lexical step. Quotes and escapes prevent string bytes from
    being counted as structure or numbers. Numeric spelling remains the
    standard parser's decision after these size/magnitude checks pass. -/
def step (state : ScanState) (byte : UInt8) : Except String ScanState :=
  if state.quoted then
    if state.escaped then .ok { state with escaped := false }
    else if byte == 92 then .ok { state with escaped := true }
    else if byte == 34 then .ok { state with quoted := false }
    else .ok state
  else if state.numberBytes != 0 && numericByte byte then
    let numberBytes := state.numberBytes + 1
    let exponent := if state.exponentMode && digit byte then
        state.exponent * 10 + (byte.toNat - 48)
      else state.exponent
    if numberBytes > maxNumberBytes then .error "json-number-token-limit"
    else if exponent > maxExponent then .error "json-exponent-limit"
    else .ok { state with
      numberBytes := numberBytes
      exponent := exponent
      exponentMode := state.exponentMode || byte == 69 || byte == 101 }
  else structural state byte

/-- Errors are retained through the remaining finite input without further
    token work. No source list or recursive syntax tree is allocated here. -/
def feed (result : Except String ScanState) (byte : UInt8) : Except String ScanState :=
  match result with
  | .error reason => .error reason
  | .ok state => step state byte

def scan (bytes : ByteArray) : Except String ScanState :=
  bytes.foldl feed (.ok {})

def check (text : String) : Except String Unit :=
  match scan text.toUTF8 with
  | .error reason => .error reason
  | .ok _ => .ok ()

/-- The parser continuation is selected only after the lexical check passes.
    The native codec supplies Lean.Json.parse; this generic function makes
    the refusal boundary explicit in the executable definition and proofs. -/
def parseWith {α : Type} (parser : String → Except String α) (text : String) : Except String α :=
  match check text with
  | .error reason => .error reason
  | .ok () => parser text

end EVMCleanroom.TransactionTransport
