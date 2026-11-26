import EVMCleanroom.TransactionTransport
import Lean.Data.Json.Parser

/-!
# Unambiguous JSON transport for authenticated witnesses

The existing lexical resource guard runs before this scan and the standard JSON
parser. The scan records member names per object, decoding their quoted spelling
with that same standard parser, so escaped aliases cannot replace a prior field.
It does not interpret Ethereum data. The schema-specific callers still reject
unknown fields, and the legacy decoded transaction mode retains its old parser.
-/
namespace EVMCleanroom.WitnessJSON

open Lean (Json)

def maxInputBytes : Nat := 16777216
def maxMemberBytes : Nat := 256
def maxObjectMembers : Nat := 256

private inductive Container where
  | object (names : List String)
  | array

private structure State where
  stack : List Container := []
  quoted : Bool := false
  escaped : Bool := false
  quoteStart : Nat := 0
  lastQuoted : Option (Nat × Nat) := none

private def memberName (bytes : ByteArray) (start stop : Nat) : Except String String := do
  if stop - start > maxMemberBytes then throw "json-member-name-limit"
  let raw ← match String.fromUTF8? (bytes.extract start stop) with
    | none => throw "invalid UTF-8 object member"
    | some value => pure value
  (← Json.parse raw).getStr?

private def step (bytes : ByteArray) (pos : Nat) (state : State) : Except String State := do
  let byte := (bytes[pos]?).getD 0
  if state.quoted then
    if state.escaped then return { state with escaped := false }
    else if byte == 92 then return { state with escaped := true }
    else if byte == 34 then
      return { state with quoted := false, lastQuoted := some (state.quoteStart, pos + 1) }
    else return state
  else if byte == 34 then
    return { state with quoted := true, escaped := false, quoteStart := pos, lastQuoted := none }
  else if byte == 123 || byte == 91 then
    if state.stack.length ≥ TransactionTransport.maxDepth then throw "json-nesting-limit"
    let container := if byte == 123 then Container.object [] else Container.array
    return { state with stack := container :: state.stack, lastQuoted := none }
  else if byte == 125 || byte == 93 then
    match byte.toNat, state.stack with
    | 125, .object _ :: rest => return { state with stack := rest, lastQuoted := none }
    | 93, .array :: rest => return { state with stack := rest, lastQuoted := none }
    | _, _ => throw "mismatched JSON container"
  else if byte == 58 then
    match state.lastQuoted, state.stack with
    | some (start, stop), .object names :: rest =>
      let key ← memberName bytes start stop
      if names.contains key then throw ("duplicate JSON field: " ++ key)
      if names.length ≥ maxObjectMembers then throw "json-object-member-limit"
      return { state with stack := .object (key :: names) :: rest, lastQuoted := none }
    | _, _ => throw "expected JSON object member"
  else if byte == 32 || byte == 9 || byte == 10 || byte == 13 then return state
  else return { state with lastQuoted := none }

private def scan (bytes : ByteArray) : Nat → Nat → State → Except String Unit
  | 0, _, _ => .ok ()
  | fuel + 1, pos, state =>
    match step bytes pos state with
    | .error reason => .error reason
    | .ok next => scan bytes fuel (pos + 1) next

/-- Member comparisons are per object and use decoded names. Work per object
and name is bounded before the standard parser constructs the JSON value. -/
def checkMembers (text : String) : Except String Unit :=
  let bytes := text.toUTF8
  scan bytes bytes.size 0 {}

/-- Strict proof-mode transport. The ordinary JSON parser still decides grammar
after the byte, nesting, numeric-work and duplicate-member guards succeed. -/
def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > maxInputBytes then throw "witness-json-byte-limit"
  TransactionTransport.check text
  checkMembers text
  Json.parse text

end EVMCleanroom.WitnessJSON
