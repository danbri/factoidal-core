/-
Wasm.Ops.Sbm11 — SPARQL over an SBM11 store through the host's storage medium
(https://github.com/danbri/factoidal/issues/1009 KR1; the medium interface is
https://github.com/danbri/factoidal/issues/1010 KR1).

  sbm11Open(root)
    -> {"ok":true,"handle":"sbm11-1","generation":"…","quads":N,"terms":N,
        "artifacts":N,"deltaBatches":N,"deltaEntries":N,"deltaTorn":B,
        "openBytes":N}
  sbm11Query(handle, sparql [, optionsJson])
    optionsJson: {"base":"<IRI>","version":"1.1"|"1.2"} (both optional)
    -> SELECT, ASK: {"ok":true,"form":"select"|"ask","path":"ids"|"reference",
                     "detail":"…","rows":N,"blockBytes":N,"prmBytes":N,
                     "mediumBytes":N,"results":<SPARQL 1.1 Query Results JSON>}
       CONSTRUCT, DESCRIBE: the same members with "ntriples":"<N-Triples>"
       in place of "results"
  sbm11Close(handle) -> {"ok":true}

`root` names a store to the host (Node: a directory; it may be a collection
root whose `CURRENT` names the generation directory). The open and every read
go through `L4Wasm.hostMedium root` (`Wasm/MediumHost.lean`): the host answers
byte ranges of named objects and nothing else.

The ops are thin: `QuerySession.openMedium` opens the generation (manifest,
file lengths, GDX1 header, delta-log replay), `QuerySession.runOne` runs the
query on one thread (the id path, or the reference fallback over the quads the
planner guard selects), the function the native `l4sbm11 query` calls with
`--threads 1` (`Harness/Sbm11Query.lean`'s `runOne` calls
`QuerySession.runOneWith`). NOW() is read once per query
(`Wasm/Ops/Clock.lean`). The handle table is the only state of this module.

The reads are exact byte ranges within the manifest's length of each file (the
`--verify none` reads of the native command); no Merkle proof is checked in
this op. What the host returns is the named IO assumption
`MediumReadsWritten` (stage `sbm11Medium`, `L4Factoidal/Dataflow/Instances.lean`).
-/
import L4Factoidal.Storage.Sbm11.QuerySession
import Wasm.MediumHost
import Wasm.Ops.Support
import Wasm.Ops.ErrorModel
import Wasm.Ops.Clock
import L4Factoidal.JSON.Parser
import Std.Data.HashMap

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11

/-- An open SBM11 store: the host's root, the generation directory its
`CURRENT` names (`""`: the root is the generation), the session, and the count
of bytes read from the medium since the open. -/
structure Sbm11Handle where
  root : String
  generation : String
  core : QuerySession.Core
  mediumBytes : IO.Ref Nat

/-- Handle ids already issued (`sbm11-1`, `sbm11-2`, …); never reused. -/
initialize sbm11Counter : IO.Ref Nat ← IO.mkRef 0

/-- The open SBM11 stores, keyed by handle. -/
initialize sbm11Table : IO.Ref (Std.HashMap String Sbm11Handle) ← IO.mkRef ∅

private def num (n : Nat) : Json := .number (toString n)

/-- The error for a handle that is not open. -/
def sbm11MissingHandle (h : String) : IO String := do
  let issued ← sbm11Counter.get
  let wasIssued := h.startsWith "sbm11-" &&
    match (String.ofList (h.toList.drop 6)).toNat? with
    | some n => 1 ≤ n && n ≤ issued
    | none => false
  if wasIssued then
    pure (errCoded "handle.disposed" s!"SBM11 store handle {h} was closed; a closed handle cannot be used again")
  else pure (errCoded "handle.unknown" s!"unknown SBM11 store handle: {h}")

/-- `sbm11Open(root)`: open the store `root` names through the host medium. -/
def sbm11Open (root : String) : IO String := do
  if root.isEmpty then return errJson "sbm11Open: the store root is empty"
  let counter ← IO.mkRef 0
  match ← (QuerySession.openMedium (L4Wasm.hostMedium root) counter).toBaseIO with
  | .error e => return errJson s!"sbm11Open: {e}"
  | .ok (core, generation) =>
    let openBytes ← counter.get
    let n ← sbm11Counter.modifyGet fun n => (n + 1, n + 1)
    let h := s!"sbm11-{n}"
    sbm11Table.modify (·.insert h { root, generation, core, mediumBytes := counter })
    return okWith
      [ ("handle", .string h), ("generation", .string generation)
      , ("quads", num core.manifest.quads), ("terms", num core.manifest.terms)
      , ("artifacts", num core.manifest.artifacts.length)
      , ("deltaBatches", num core.deltaBatches), ("deltaEntries", num core.deltaOps)
      , ("deltaTorn", .bool core.deltaTorn), ("openBytes", num openBytes) ]

/-- The options of `sbm11Query`: the base IRI and the SPARQL grammar. -/
def sbm11QueryOptions (optionsJson : String) : Except String (Option String × SparqlVersion) :=
  if optionsJson.isEmpty then .ok (none, .v11)
  else
    match parseJson optionsJson with
    | .ok (.object fields) =>
      let base := match fields.lookup "base" with
        | some (.string b) => if b.isEmpty then none else some b
        | _ => none
      match fields.lookup "version" with
      | none | some (.string "1.1") => .ok (base, .v11)
      | some (.string "1.2") => .ok (base, .v12)
      | some _ => .error "sbm11Query: version must be \"1.1\" or \"1.2\""
    | .ok _ => .error "sbm11Query: options must be a JSON object"
    | .error e => .error s!"sbm11Query: options: {toString e}"

/-- `sbm11Query(handle, sparql, optionsJson)`. -/
def sbm11Query (h sparql : String) (optionsJson : String := "") : IO String := do
  match (← sbm11Table.get)[h]? with
  | none => sbm11MissingHandle h
  | some hd =>
    match sbm11QueryOptions optionsJson with
    | .error e => return errJson e
    | .ok (base, version) =>
    match QuerySession.parse? sparql base version with
    | .error e => return errCoded "query.parse" e
    | .ok q =>
      let c := hd.core
      c.frameBytes.set 0
      c.prmBytes.set 0
      let m0 ← hd.mediumBytes.get
      let buf ← IO.mkRef ByteArray.empty
      let clockEnv ← emptyEnvNow
      match ← (QuerySession.runOne c clockEnv q (fun b => buf.modify (· ++ b))).toBaseIO with
      | .error e => return errJson s!"sbm11Query: {e}"
      | .ok out =>
        let text := String.fromUTF8? (← buf.get) |>.getD ""
        let (form, isGraph) := match q.form with
          | .select _ => ("select", false)
          | .ask => ("ask", false)
          | .construct _ => ("construct", true)
          | .describe _ => ("describe", true)
        let fields : List (String × Json) :=
          [ ("form", .string form)
          , ("path", .string (if out.path == "path=ids" then "ids" else "reference"))
          , ("detail", .string out.path), ("rows", num out.rows)
          , ("blockBytes", num (← c.frameBytes.get)), ("prmBytes", num (← c.prmBytes.get))
          , ("mediumBytes", num ((← hd.mediumBytes.get) - m0)) ]
        if isGraph then return okWith (fields ++ [("ntriples", .string text)])
        if text.isEmpty then return errJson "sbm11Query: the query wrote no answer"
        return "{\"ok\":true," ++ jsonMembers fields ++ ",\"results\":" ++ text ++ "}"

/-- `sbm11Close(handle)`. -/
def sbm11Close (h : String) : IO String := do
  if (← sbm11Table.get).contains h then
    sbm11Table.modify (·.erase h)
    return okWith []
  sbm11MissingHandle h

end L4Wasm.Ops
