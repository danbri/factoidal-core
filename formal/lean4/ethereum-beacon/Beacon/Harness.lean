import Beacon.Types
import Beacon.Snappy

/-!
# Test-vector harness support

File reading, the small subset of YAML used by the vectors' metadata, hex,
result records and summary statistics. Test tooling only.
-/

namespace Beacon.Harness
open Beacon

inductive Status where
  | pass | fail | unsupported
  deriving BEq, Repr

structure CaseResult where
  name : String
  status : Status
  detail : String := ""
  /-- 0 optional, 1 required, 2 must be off (the vectors' `bls_setting`). -/
  blsSetting : Nat := 0
  /-- Whether signatures were really checked while running this case. -/
  blsVerified : Bool := false
  micros : Nat := 0

def hexDigit (c : UInt8) : Option UInt8 :=
  if 48 ≤ c && c ≤ 57 then some (c - 48)
  else if 97 ≤ c && c ≤ 102 then some (c - 87)
  else if 65 ≤ c && c ≤ 70 then some (c - 55)
  else none

/-- Decode the hex digits found in `s` after an optional `0x`; other
    characters (quotes, spaces) are skipped. -/
def hexBytes (s : String) : ByteArray := Id.run do
  let raw := s.toUTF8
  let mut digits : Array UInt8 := #[]
  let mut i := 0
  -- skip up to and including "0x"
  for j in [0:raw.size] do
    if j + 1 < raw.size && raw[j]! == 48 && raw[j + 1]! == 120 then
      i := j + 2
      break
  for j in [i:raw.size] do
    match hexDigit raw[j]! with
    | some d => digits := digits.push d
    | none => pure ()
  let mut out := ByteArray.emptyWithCapacity (digits.size / 2)
  for j in [0:digits.size / 2] do
    out := out.push (digits[2 * j]! * 16 + digits[2 * j + 1]!)
  return out

def toHex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := Char.ofNat (if n < 10 then 48 + n.toNat else 87 + n.toNat)
  b.foldl (fun acc x => (acc.push (digit (x / 16))).push (digit (x % 16))) ""

/-- Value of `key: <digits>` in a flow or block YAML mapping. -/
def yamlNat (text key : String) : Option Nat :=
  match text.splitOn (key ++ ":") with
  | _ :: rest :: _ =>
    let digits := (rest.toList.dropWhile (· == ' ')).takeWhile Char.isDigit
    if digits.isEmpty then none else some (digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)
  | _ => none

def yamlBool (text key : String) : Option Bool :=
  match text.splitOn (key ++ ":") with
  | _ :: rest :: _ =>
    let word := String.ofList ((rest.toList.dropWhile (· == ' ')).takeWhile Char.isAlpha)
    if word == "true" then some true else if word == "false" then some false else none
  | _ => none

def firstNat (text : String) : Option Nat :=
  let digits := (text.toList.dropWhile (fun c => !c.isDigit)).takeWhile Char.isDigit
  if digits.isEmpty then none else some (digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0)

def readSnappy (path : System.FilePath) : IO ByteArray := do
  let raw ← IO.FS.readBinFile path
  match Snappy.decompress raw with
  | .ok b => pure b
  | .error e => throw (IO.userError s!"{path}: {e}")

def readOptional (path : System.FilePath) : IO (Option ByteArray) := do
  if ← path.pathExists then some <$> readSnappy path else pure none

def readText (path : System.FilePath) : IO String := do
  if ← path.pathExists then IO.FS.readFile path else pure ""

def sortedDir (path : System.FilePath) : IO (Array String) := do
  if !(← path.isDir) then return #[]
  let entries ← path.readDir
  return (entries.map (·.fileName)).qsort (· < ·)

/-- Nearest-rank percentile of a sorted array. -/
def percentile (sorted : Array Nat) (q : Nat) : Nat :=
  if sorted.size = 0 then 0 else sorted[min (sorted.size - 1) ((sorted.size * q + 99) / 100 - 1)]!

def jsonString (s : String) : String :=
  "\"" ++ s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 32 then acc ++ " " else acc.push c) "" ++ "\""

end Beacon.Harness
