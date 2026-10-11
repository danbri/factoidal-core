/- Native, read-only JSONL session over one admitted IBK3 generation.
Each request is a JSON string containing SELECT or ASK. The first response
announces the pinned snapshot; subsequent responses are SRJ or error objects.
There are no storage reads after readiness and no automatic refresh. -/
import Harness.IndexedBlockV3Materialize
import Harness.ShardMerkleMaterialize
import Harness.GenerationPointer
import L4Factoidal.SPARQL.PreparedSnapshot
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import Std.Time

namespace Harness.SnapshotSession

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.JSON
open L4Factoidal.SPARQL.PreparedSnapshot
open L4Factoidal.Storage.ShardManifest
open Harness.GenerationPointer Harness.IndexedBlockV3Materialize

private def admission (root : System.FilePath) :
    IO (Snapshot × Counters × System.FilePath × Bool) := do
  let directory ← resolveStoreDirectory root
  let bytes ← IO.FS.readBinFile (directory / "manifest.sbm2")
  let some manifest := decode? bytes
    | throw (IO.userError "malformed SBM2 manifest")
  if isIbk4Layout manifest.layout || manifest.version == 7 || manifest.version == 8 ||
      manifest.version == 9 || !rangeCommitted manifest || !isIbk3Layout manifest.layout then
    throw (IO.userError "snapshot session requires an IBK3 range-committed manifest")
  if manifest.version >= 5 && !(← (root / currentName).pathExists) then
    throw (IO.userError "SBM5 and later require an activated collection root (CURRENT)")
  let some delta ← Harness.ShardMerkleMaterialize.readDefaultDelta? directory
    | throw (IO.userError "malformed DLOG sidecar")
  let some (base, counters) ← materializeEntries directory manifest.entries
    | throw (IO.userError "malformed or unavailable committed artifact")
  let hasDelta := !deltaResolvedIsEmpty delta
  let graph := if hasDelta then
    (Harness.ShardMerkleMaterialize.readOpsOfDelta base delta).search patternBoundAll
    else base
  return (prepare graph, counters, directory, hasDelta)

private def errorResponse (code message : String) : String :=
  (Json.object [("error", .string code), ("message", .string message)]).toString

private def response (snapshot : Snapshot) (env : EvalEnv) (line : String) : String :=
  match parseJson line with
  | .error _ => errorResponse "invalid-request" "expected one JSON string containing SPARQL"
  | .ok (.string text) =>
      match parseSparql text with
      | .error error => errorResponse "invalid-query" s!"at {error.pos}: {error.msg}"
      | .ok query =>
          match query.form with
          | .select _ | .ask =>
              match run snapshot query env with
              | .ok result => result.toSrjFast
              | .error message => errorResponse "evaluation-failed" message
          | _ => errorResponse "unsupported-form" "snapshot sessions support SELECT and ASK only"
  | .ok _ => errorResponse "invalid-request" "expected one JSON string containing SPARQL"

private def serve (snapshot : Snapshot) : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  while true do
    let line ← input.getLine
    if line.isEmpty then break
    let now ← Std.Time.Timestamp.now
    let timestamp := (Std.Time.DateTime.ofTimestampWithZone now .UTC).toISO8601String
    let env : EvalEnv := { now := some timestamp }
    output.putStrLn (response snapshot env line)
    output.flush

def main (args : List String) : IO UInt32 := do
  match args with
  | [directory] =>
      try
        let (snapshot, counters, resolved, hasDelta) ← admission (System.FilePath.mk directory)
        let output ← IO.getStdout
        output.putStrLn (Json.object [
          ("ready", .bool true), ("mode", .string "ibk3-full-snapshot"),
          ("resolved-directory", .string resolved.toString),
          ("triples", .number (toString snapshot.graph.length)),
          ("delta", .bool hasDelta), ("admissions", .number "1"), ("index-builds", .number "1"),
          ("hash-index-builds", .number "1"), ("subject-order-index-builds", .number "1"),
          ("logical-read-bytes", .number (toString counters.requestedBytes)),
          ("fetched-bytes", .number (toString counters.fetchedBytes))]).toString
        output.flush
        serve snapshot
        return 0
      catch error =>
        IO.eprintln s!"l4block-snapshot-session rejected: {error}"
        return 1
  | _ =>
      IO.eprintln "usage: l4block-snapshot-session COLLECTION-ROOT < queries.jsonl"
      return 2

end Harness.SnapshotSession

def main (args : List String) : IO UInt32 := Harness.SnapshotSession.main args
