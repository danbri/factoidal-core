import EVMCleanroom.StateTest
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

/-!
`evm-state-test`: reads published execution-spec-tests `state_test`
fixture files and prints one JSON line per (test, fork, post entry) with
the Lean verdict. The fixture JSON is read here as data; every decision
(decoding, sender recovery, execution, roots and the comparison) is made by
`StateTest.evaluate`.

Local limits: a fixture file above `maxFileBytes` is reported as not
executed, with its reason. Duplicate JSON member names are not detected by
the standard parser; fixture files are pinned by SHA-256 in CI.
-/

namespace EVMCleanroom.StateTestCLI

open Lean (Json)
open StateTest

def maxFileBytes : Nat := 96 * 1024 * 1024

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def strip (s : String) : Except String String :=
  if s.startsWith "0x" || s.startsWith "0X" then .ok (s.drop 2).toString
  else .error ("expected 0x-prefixed hex: " ++ (s.take 20).toString)

def hexNat (s : String) : Except String Nat := do
  let body ← strip s
  if body.length > 64 then throw "hex integer wider than 256 bits"
  body.foldl (fun acc c => do
    let n ← acc
    match hexVal c with
    | some d => pure (n * 16 + d)
    | none => throw "bad hex digit") (pure 0)

def hexBytes (s : String) : Except String (Array UInt8) := do
  let body ← strip s
  let cs := body.toList.toArray
  if cs.size % 2 = 1 then throw "odd hex length"
  let mut out : Array UInt8 := Array.mkEmpty (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexVal (cs.getD (2 * i) '0'), hexVal (cs.getD (2 * i + 1) '0') with
    | some h, some l => out := out.push (UInt8.ofNat (h * 16 + l))
    | _, _ => throw "bad hex digit"
  return out

private def strField (j : Json) (name : String) : Except String String := do
  (← j.getObjVal? name).getStr?

private def natField (j : Json) (name : String) : Except String Nat := do
  hexNat (← strField j name)

private def optNatField (j : Json) (name : String) : Except String (Option Nat) :=
  match j.getObjVal? name with
  | .ok (.str s) => some <$> hexNat s
  | _ => pure none

private def members (j : Json) : Except String (List (String × Json)) := do
  return (← j.getObj?).toList

def parsePre (j : Json) : Except String (List PreAccount) := do
  (← members j).mapM fun (addr, acct) => do
    let storage ← match acct.getObjVal? "storage" with
      | .ok s => (← members s).mapM fun (k, v) => do
          return (← hexNat k, ← hexNat (← v.getStr?))
      | .error _ => pure []
    return { address := ← hexNat addr, balance := ← natField acct "balance"
             nonce := ← natField acct "nonce", code := ← hexBytes (← strField acct "code")
             storage }

def parseEnv (j : Json) (chainId : Nat) : Except String Env := do
  let randao ← match ← optNatField j "currentRandom" with
    | some r => pure r
    | none => natField j "currentDifficulty"
  return { coinbase := ← natField j "currentCoinbase", gasLimit := ← natField j "currentGasLimit"
           number := ← natField j "currentNumber", timestamp := ← natField j "currentTimestamp"
           baseFee := (← optNatField j "currentBaseFee").getD 0, prevRandao := randao
           excessBlobGas := ← optNatField j "currentExcessBlobGas", chainId }

private def esc (s : String) : Json := .str s

private def hexOf (b : Array UInt8) : String :=
  "0x" ++ String.join (b.toList.map fun x => byteHex x.toNat)

structure Line where
  file : String
  id : String
  fork : String
  index : Nat
  indexes : Json
  verdict : String
  reason : Option String
  extra : List (String × Json) := []

def Line.json (l : Line) : Json :=
  Json.mkObj ([("file", esc l.file), ("id", esc l.id), ("fork", esc l.fork),
    ("index", (l.index : Nat)), ("indexes", l.indexes), ("verdict", esc l.verdict)] ++
    (match l.reason with | some r => [("reason", esc r)] | none => []) ++ l.extra)

private def decisionFields : Decision → List (String × Json)
  | .executed status gas => [("decision", esc "executed"),
      ("receiptStatus", ((if status then 1 else 0 : Nat) : Json)), ("gasUsed", esc (toString gas))]
  | .rejected why => [("decision", esc "rejected"), ("decisionReason", esc why)]
  | .unavailable _ => [("decision", esc "unavailable")]

def reportLine (file id fork : String) (index : Nat) (indexes : Json) (expected : Expected)
    (r : Report) (nanos : Nat) : Line :=
  let (verdict, reason) := match r.verdict with
    | .pass => ("pass", none)
    | .fail why => ("fail", some why)
    | .unsupported why => ("unsupported", some why)
  { file, id, fork, index, indexes, verdict, reason
    extra := decisionFields r.decision ++
      (match r.stateRoot with | some h => [("stateRoot", esc (hexOf h))] | none => []) ++
      [("expectedRoot", esc (hexOf expected.hash)), ("expansions", (r.expansions : Json)),
       ("nanos", (nanos : Json))] ++
      (match expected.exception with | some e => [("expectException", esc e)] | none => []) }

def notExecuted (file id fork : String) (index : Nat) (indexes : Json) (why : String) : Line :=
  { file, id, fork, index, indexes, verdict := "not-executed", reason := some why }

/-- Run every post entry of one test. -/
def runTest (a : Keccak.Acceptance) (s : SecpRecovery.Acceptance) (affine : Bool) (forks : List String)
    (file id : String) (test : Json) : IO Unit := do
  let posts ← match test.getObjVal? "post" >>= members with
    | .ok p => pure p
    | .error why => IO.println (notExecuted file id "?" 0 .null ("fixture-shape:" ++ why)).json.compress; return
  let chainId := match test.getObjVal? "config" >>= (·.getObjVal? "chainid") >>= (·.getStr?) >>= hexNat with
    | .ok n => n
    | .error _ => 1
  let setup : Except String (Env × List PreAccount) := do
    return (← parseEnv (← test.getObjVal? "env") chainId, ← parsePre (← test.getObjVal? "pre"))
  for (fork, entries) in posts do
    let list := match entries.getArr? with | .ok xs => xs | .error _ => #[]
    for h : i in [0:list.size] do
      let entry := list[i]
      let indexes := (entry.getObjVal? "indexes").toOption.getD .null
      if !forks.isEmpty && !forks.contains fork then
        IO.println (notExecuted file id fork i indexes "fork-not-selected").json.compress
        continue
      let parsed : Except String Case := do
        let (env, pre) ← setup
        let exception := match entry.getObjVal? "expectException" with
          | .ok (.str e) => some e
          | _ => none
        return { fork, env, pre, txBytes := ← hexBytes (← strField entry "txbytes")
                 expected := { hash := ← hexBytes (← strField entry "hash")
                               logs := ← hexBytes (← strField entry "logs"), exception } }
      match parsed with
      | .error why =>
        IO.println (notExecuted file id fork i indexes ("fixture-shape:" ++ why)).json.compress
      | .ok c =>
        let t0 ← IO.monoNanosNow
        -- The case depends on the clock reading so the pure evaluation
        -- cannot be moved before it; the branch is never taken in practice.
        let c := if t0 == 0 then { c with fork := "" } else c
        let r := if affine then evaluate a s c else evaluateWith a (fastRecover a) c
        let tag := match r.verdict with | .pass => 0 | .fail _ => 1 | .unsupported _ => 2
        -- Reading the clock depends on the verdict, so evaluation happens first.
        let t1 ← if tag == 3 then pure t0 else IO.monoNanosNow
        IO.println (reportLine file id fork i indexes c.expected r (t1 - t0)).json.compress

def runFile (a : Keccak.Acceptance) (s : SecpRecovery.Acceptance) (affine : Bool) (forks : List String)
    (path : String) : IO Unit := do
  let fail := fun (why : String) =>
    IO.println (notExecuted path "*" "*" 0 .null why).json.compress
  try
    let size := (← System.FilePath.metadata path).byteSize.toNat
    if size > maxFileBytes then fail "fixture-file-over-local-limit"; return
    let text ← IO.FS.readFile path
    match Json.parse text with
    | .error why => fail ("fixture-json:" ++ why)
    | .ok j =>
      match members j with
      | .error why => fail ("fixture-shape:" ++ why)
      | .ok tests =>
        for (id, test) in tests do
          runTest a s affine forks path id test
  catch e => fail ("fixture-io:" ++ toString e)

def splitForks (s : String) : List String :=
  (s.splitOn ",").filter (· ≠ "")

def usage : String :=
  "usage: evm-state-test --dangerously-enable-unverified-keccak " ++
  "--dangerously-enable-unverified-secp256k1 [--affine-secp256k1] [--forks F1,F2] (--list LISTFILE | FILE...)"

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | "--dangerously-enable-unverified-keccak" :: "--dangerously-enable-unverified-secp256k1" :: rest =>
    let (affine, rest) := match rest with
      | "--affine-secp256k1" :: more => (true, more)
      | more => (false, more)
    let (forks, rest) := match rest with
      | "--forks" :: fs :: more => (splitForks fs, more)
      | more => ([], more)
    let files ← match rest with
      | ["--list", listFile] => do
        let lines ← IO.FS.lines listFile
        pure (lines.toList.filter (· ≠ ""))
      | fs => pure fs
    if files.isEmpty then IO.eprintln usage; return 2
    for f in files do
      runFile Keccak.dangerouslyAcceptUnverified SecpRecovery.dangerouslyAcceptUnverified affine forks f
    return 0
  | _ => IO.eprintln usage; return 2

end EVMCleanroom.StateTestCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.StateTestCLI.cliMain args
