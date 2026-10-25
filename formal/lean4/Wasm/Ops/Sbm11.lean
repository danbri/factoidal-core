/-
Wasm.Ops.Sbm11 — SPARQL over an SBM11 generation in the wasm module
(https://github.com/danbri/factoidal/issues/1009 KR1; stage 1 of
https://github.com/danbri/factoidal/issues/1007).

  sbm11Open(source)
    -> {"ok":true,"handle":"sbm11-1","generation":G,"terms":N,"artifacts":K,"bytesRead":B}
  sbm11Query(handle, sparql [, optionsJson])
    -> {"ok":true,"path":"path=ids"|"path=reference ...","rows":N,
        "format":"srj"|"ntriples","bytesRead":B,"reads":R,"result":"..."}
    through l4_call_blob_io: "resultBytes":N in place of "result", and the
    result bytes as the out region
  sbm11Close(handle)
    -> {"ok":true}

`source` is the string the host resolves (`Wasm/HostRead.lean`): a directory
for Node and the native CLI, an OPFS directory name in a browser worker. It
names a generation directory, or a collection root whose `CURRENT` file names
one (`G` is then that name, else `""`). Every
byte of the generation comes through the host's positioned read; nothing is
copied in whole. `optionsJson` is an object with the optional members `base`
(the base IRI of the query), `sparql12` (the SPARQL 1.2 grammar) and
`reference` (run the reference evaluator also for the id fragment, the oracle
of the tests).

`result` is SPARQL 1.1 Query Results JSON for SELECT and ASK, and N-Triples
lines for CONSTRUCT and DESCRIBE: the bytes `l4sbm11 query` writes for the
same query on the same generation.

The engine: `L4Factoidal.Storage.Sbm11.HostSession`. The handle table is the
only state of this module (the rule of `Wasm/Ops/Handles.lean`).
-/
import Std.Data.HashMap
import Wasm.HostRead
import Wasm.Ops.Support
import Wasm.Ops.Clock
import L4Factoidal.SPARQL.Parser

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.HostSession

/-- The most SBM11 handles open at once. -/
def maxSbm11Handles : Nat := 8

initialize sbm11HandleCounter : IO.Ref Nat ← IO.mkRef 0
initialize sbm11HandleTable : IO.Ref (Std.HashMap String Session) ← IO.mkRef ∅

private def ioMessage (e : IO.Error) : String := toString e

/-- `sbm11Open(source)`. -/
def sbm11Open (source : String) : IO String := do
  let table ← sbm11HandleTable.get
  if table.size ≥ maxSbm11Handles then
    return errJson s!"sbm11Open: {table.size} handles are open (at most {maxSbm11Handles}); close one with sbm11Close"
  try
    let (host, genName) ← resolveHost (hostOf source)
    let ss ← openSession host
    let n ← sbm11HandleCounter.modifyGet fun c => (c + 1, c + 1)
    let h := s!"sbm11-{n}"
    sbm11HandleTable.modify (·.insert h ss)
    return okWith
      [ ("handle", .string h)
      , ("generation", .string genName)
      , ("terms", .number (toString ss.dictHdr.termCount))
      , ("artifacts", .number (toString ss.manifest.artifacts.length))
      , ("bytesRead", .number (toString (← ss.bytesRead.get))) ]
  catch e => return errJson s!"sbm11Open: {ioMessage e}"

private structure QueryOpts where
  base : Option String := none
  sparql12 : Bool := false
  reference : Bool := false

private def queryOpts (optionsJson : String) : Except String QueryOpts := do
  if optionsJson.trimAscii.isEmpty then return {}
  match parseJson optionsJson with
  | .error e => throw s!"optionsJson: {toString e}"
  | .ok (.object members) =>
    let mut o : QueryOpts := {}
    for (k, v) in members do
      match k, v with
      | "base", .string s => o := { o with base := some s }
      | "base", .null => pure ()
      | "sparql12", .bool b => o := { o with sparql12 := b }
      | "reference", .bool b => o := { o with reference := b }
      | k, _ => throw s!"optionsJson: member {k} is not base (string), sparql12 or reference (boolean)"
    return o
  | .ok _ => throw "optionsJson must be a JSON object"

/-- Run `sbm11Query`: the envelope fields (without the result) and the
    result bytes, or an error message. -/
def sbm11Run (h sparql optionsJson : String) : IO (Except String (List (String × Json) × ByteArray)) := do
  match (← sbm11HandleTable.get)[h]? with
  | none => return .error s!"sbm11Query: no open SBM11 handle {h}"
  | some held =>
  match queryOpts optionsJson with
  | .error e => return .error s!"sbm11Query: {e}"
  | .ok o =>
  match parseSparql sparql o.base (if o.sparql12 then .v12 else .v11) with
  | .error e => return .error s!"sbm11Query: SPARQL parse error at {e.pos}: {e.msg}"
  | .ok q =>
  -- the query runs on references of its own (`Session.localize`: the held
  -- session is reachable from the handle table, a global)
  let ss ← held.localize
  let b0 ← ss.bytesRead.get
  let r0 ← ss.reads.get
  let out ← IO.mkRef (ByteArray.emptyWithCapacity 4096)
  try
    let clockEnv ← emptyEnvNow
    let outcome ← runOne ss clockEnv q (fun b => out.modify (· ++ b)) o.reference
    held.keep ss
    let format := match q.form with
      | .select _ | .ask => "srj"
      | _ => "ntriples"
    return .ok
      ([ ("path", .string outcome.path)
       , ("rows", .number (toString outcome.rows))
       , ("format", .string format)
       , ("bytesRead", .number (toString ((← ss.bytesRead.get) - b0)))
       , ("reads", .number (toString ((← ss.reads.get) - r0))) ], ← out.get)
  catch e => return .error s!"sbm11Query: {ioMessage e}"

/-- `sbm11Query(handle, sparql, optionsJson)` through `callIO`: the result as
    the member `result` of the envelope. -/
def sbm11Query (h sparql optionsJson : String) : IO String := do
  match ← sbm11Run h sparql optionsJson with
  | .error e => return errJson e
  | .ok (fields, bytes) => return okWith (fields ++ [("result", .string (String.fromUTF8! bytes))])

/-- `sbm11Query(handle, sparql, optionsJson)` through `callBlobIO`: the result
    bytes as the out region, not in the envelope. A large answer is then not
    escaped into a JSON string and parsed again (olympics q20: 18.8 MB). -/
def sbm11QueryBlob (h sparql optionsJson : String) : IO (String × ByteArray) := do
  match ← sbm11Run h sparql optionsJson with
  | .error e => return (errJson e, ByteArray.empty)
  | .ok (fields, bytes) => return (okWith (fields ++ [("resultBytes", .number (toString bytes.size))]), bytes)

/-- `sbm11Close(handle)`. -/
def sbm11Close (h : String) : IO String := do
  if (← sbm11HandleTable.get).contains h then
    sbm11HandleTable.modify (·.erase h)
    return okWith []
  return errJson s!"sbm11Close: no open SBM11 handle {h}"

/-- The op names of this module, served by `callIO` only. -/
def sbm11OpNames : List String := ["sbm11Open", "sbm11Query", "sbm11Close"]

end L4Wasm.Ops
