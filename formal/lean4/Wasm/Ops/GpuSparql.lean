import Wasm.Ops.Handles
import L4Factoidal.Dataflow.GpuSparqlStage
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoin

/-!
# Suspended, mixed CPU/WebGPU SPARQL queries

The session owns the dataset, query, environment and continuation. The host
only executes Lean-emitted numeric plans and returns their buffers. A failed
device resumes the existing indexed Lean operation. Query restarts for async
extension functions retain the original dataset and NOW() snapshot.

Readbacks are phase- and session-bound; capacity is checked before expansion.
The numerical index-join refinement and physical device behaviour are explicit
obligations, not new logical axioms or a second SPARQL evaluator in JavaScript.
-/
namespace L4Wasm.Ops.GpuSparql

open Lean L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Dataflow
open L4Factoidal.GpuDomainSpecificLanguage

private def error (message : String) : String :=
  (Json.mkObj [("ok", toJson false), ("error", toJson message)]).compress

private def fieldString (j : Json) (key fallback : String) : Except String String :=
  match j.getObjVal? key with
  | .error _ => .ok fallback
  | .ok .null => .ok fallback
  | .ok value => value.getStr?

private def boundedNat (j : Json) (key : String) (fallback max : Nat) : Except String Nat := do
  match j.getObjVal? key with
  | .error _ => pure fallback
  | .ok .null => pure fallback
  | .ok value =>
    let n ← value.getNat?
    if n > max then throw s!"{key} exceeds {max}"
    pure n

private inductive Pending where
  | ranges (prepared : IndexedJoin.Prepared)
  | pairs (prepared : IndexedJoin.Prepared) (counted : IndexedJoin.Counted)

private structure Session where
  query : Query
  dataset : Dataset
  env : EvalEnv
  config : GpuQuery.Config
  backend : StoreDataset.DatasetBackend
  useGpu : Bool
  referenceCpu : Bool
  output : Option String
  requiredGpu : Bool
  plan : GpuQuery.Plan Answer
  pending : Option Pending := none
  request : Nat := 0
  gpuJoins : Nat := 0
  cpuFallbacks : Nat := 0
  deviceChecked : Bool := false
  automaticGpuAllowed : Bool := true
  device : Json := .null
  trace : Array Json := #[]

private def startPlan (s : Session) : GpuQuery.Plan Answer :=
  let input : EvalInput :=
    { env := s.env, ds := s.dataset,
      backend := if s.referenceCpu then none else some s.backend, query := s.query }
  if s.useGpu then gpuSparqlPlan
      { s.config with available := s.config.available && (s.requiredGpu || s.automaticGpuAllowed) } input
  else .done (shippedEvaluator.run input)

private initialize sessions : IO.Ref (Std.HashMap String Session) ← IO.mkRef {}
private initialize counter : IO.Ref Nat ← IO.mkRef 0

private def execution (s : Session) : Json := Json.mkObj [
  ("backend", toJson (if s.gpuJoins == 0 then "cpu" else "mixed-cpu-webgpu")),
  ("selection", toJson (if s.useGpu then "indexed-estimate-and-actual-cardinality" else "cpu-preflight")),
  ("minimumInputRows", toJson s.config.minLeftRows),
  ("maximumPairs", toJson s.config.maxOutputPairs),
  ("automaticGpuAllowed", toJson s.automaticGpuAllowed),
  ("device", s.device),
  ("gpuJoins", toJson s.gpuJoins), ("cpuFallbacks", toJson s.cpuFallbacks),
  ("joins", Json.arr s.trace)]

private def record (s : Session) (job : GpuQuery.Job) (backend reason : String)
    (pairs : Nat := 0) : Session :=
  { s with trace := s.trace.push (Json.mkObj [
      ("label", toJson job.label), ("backend", toJson backend),
      ("leftRows", toJson job.left.size), ("rightRows", toJson job.right.size),
      ("pairs", toJson pairs), ("reason", toJson reason)]) }

private def reply (id : String) (s : Session) (members : List (String × Json)) : IO String := do
  sessions.modify (·.insert id s)
  pure (Json.mkObj ([("ok", toJson true), ("session", toJson id),
    ("requestId", toJson s.request)] ++ members)).compress

private def finish (id : String) (s : Session) (answer : Answer) : IO String := do
  if s.requiredGpu && s.gpuJoins == 0 then
    return error "query execution 'gpu' required an observed GPU join; this query has no eligible join"
  let rendered : Except String String := match s.output with
    | none => .ok (queryAnswerEnvelope s.query answer
        (datasetWarningMembers (datasetWarnings s.query.dataset s.dataset)))
    | some output => do
      let text ← renderQueryAnswer output answer
      pure (Json.mkObj [("ok", toJson true), ("text", toJson text)]).compress
  match rendered with
  | .error reason => pure (error reason)
  | .ok rendered =>
    match Json.parse rendered with
    | .error reason => pure (error reason)
    | .ok answer => reply id s [("state", toJson "done"), ("answer", answer),
        ("execution", execution s)]

private def emitJob (id : String) (s : Session) (phase : String)
    (plan bindings : Json) : IO String :=
  reply id s [("state", toJson "gpu"), ("phase", toJson phase),
    ("plan", plan), ("bindings", bindings)]

/-- Device facts are observations supplied by the host. Placement policy
stays in Lean. Known software adapters have no automatic acceleration claim;
explicit required-GPU execution remains available for testing them. -/
private def softwareDevice (device : Json) : Bool :=
  let text := ["vendor", "device", "description"].map fun key =>
    ((device.getObjVal? key >>= Json.getStr?).toOption).getD ""
  let description := (String.intercalate " " text).toLower
  ((device.getObjVal? "isFallbackAdapter" >>= Json.getBool?).toOption).getD false ||
    ["swiftshader", "llvmpipe", "lavapipe", "software"].any
      (fun marker => (description.splitOn marker).length > 1)

#guard softwareDevice (Json.mkObj [("description", toJson "SwiftShader Device (Subzero)")])
#guard softwareDevice (Json.mkObj [("isFallbackAdapter", toJson true)])
#guard !softwareDevice (Json.mkObj [("vendor", toJson "Example hardware vendor")])

/-- Fuel bounds failed admissions and the number of device jobs in a session.
It never bounds a SPARQL answer or silently returns a partial result. -/
private def advance (fuel : Nat) (id : String) (s : Session) : IO String := do
  match s.plan with
  | .done answer => finish id s answer
  | .dispatch job resume =>
    match fuel with
    | 0 =>
      if s.requiredGpu then pure (error "SPARQL GPU session exceeded 256 join requests")
      else
        let answer := s.plan.cpu
        finish id { s with plan := .done answer, pending := none, cpuFallbacks := s.cpuFallbacks + 1 } answer
    | fuel + 1 =>
      if s.trace.size ≥ 256 then
        if s.requiredGpu then return error "SPARQL GPU session exceeded 256 join requests"
        let answer := s.plan.cpu
        return ← finish id { s with plan := .done answer, pending := none, cpuFallbacks := s.cpuFallbacks + 1 } answer
      if !s.deviceChecked then
        return ← reply id { s with request := s.request + 1 }
          [("state", toJson "device")]
      match IndexedJoin.prepare? job.left job.right >>= fun p =>
          IndexedJoin.phase1Plan? p >>= fun plan => .ok (p, plan) with
      | .ok (prepared, plan) =>
        let s := { s with pending := some (.ranges prepared), request := s.request + 1 }
        emitJob id s "ranges" plan (IndexedJoin.phase1Bindings prepared)
      | .error reason =>
        if s.requiredGpu then return error reason
        let s := record s job "cpu" reason
        advance fuel id { s with plan := resume none, pending := none, cpuFallbacks := s.cpuFallbacks + 1 }

private def resumeFailure (id : String) (s : Session) (reason : String) : IO String := do
  if s.requiredGpu then return error reason
  match s.plan with
  | .done _ => pure (error "GPU session has already finished")
  | .dispatch job resume =>
    let s := record s job "cpu" reason
    if !s.deviceChecked then
      let answer := s.plan.cpu
      return ← finish id { s with plan := .done answer, pending := none, automaticGpuAllowed := false, cpuFallbacks := s.cpuFallbacks + 1 } answer
    advance 256 id { s with plan := resume none, pending := none, cpuFallbacks := s.cpuFallbacks + 1 }

def begin (handle sparql options : String) : IO String := do
  if options.utf8ByteSize > 65536 then return error "GPU query options exceed 64 KiB"
  let .ok opts := Json.parse (if options.isEmpty then "{}" else options)
    | return error "GPU query options must be a JSON object"
  match opts with
  | .obj _ => pure ()
  | _ => return error "GPU query options must be a JSON object"
  let .ok mode := fieldString opts "execution" "auto" | return error "invalid execution option"
  let mode := mode.toLower
  if mode != "auto" && mode != "cpu" && mode != "gpu" then
    return error "execution must be auto, cpu or gpu"
  if (← sessions.get).size ≥ 32 then
    if mode == "gpu" then return error "at most 32 live GPU query sessions"
    return (Json.mkObj [("ok", toJson true), ("state", toJson "cpu"),
      ("reason", toJson "GPU session capacity; use the ordinary CPU query entry")]).compress
  let .ok minRows := boundedNat opts "gpuMinRows" (if mode == "gpu" then 1 else 1024) 1000000
    | return error "gpuMinRows must be an integer from 0 to 1000000"
  let .ok maxPairs := boundedNat opts "gpuMaxPairs" 1000000 2097120
    | return error "gpuMaxPairs must be an integer from 0 to 2097120"
  let .ok entail := fieldString opts "entail" "none" | return error "invalid entail option"
  let .ok version := fieldString opts "version" "1.1" | return error "invalid version option"
  if version != "1.1" && version != "1.2" then return error "version must be 1.1 or 1.2"
  let output := (opts.getObjVal? "output" >>= Json.getStr?).toOption
  let referenceCpu := (entail != "none" && entail != "") || output.isSome
  let available := ((opts.getObjVal? "available" >>= Json.getBool?).toOption).getD false
  if mode == "gpu" && !available then return error "WebGPU is unavailable for required GPU query execution"
  let table ← handleTable.get
  let some od := table[handle]? | return ← missingHandle handle
  let ds ← match closeDefaultGraph entail od.ds with
    | .error reason => return error reason
    | .ok ds => pure ds
  let q ← match parseSparql sparql none (if version == "1.2" then .v12 else .v11) with
    | .error reason => return (attachCode
        (if version == "1.2" then "datasetQuery12" else "datasetQuery") [handle, sparql]
        (error s!"SPARQL parse error: {fmtParseError reason}"))
    | .ok q => pure q
  let ext ← extSnapshot
  let services ← serviceSnapshot
  let now ← nowDateTime
  let env : EvalEnv :=
    { base := q.base, ext := extFnsWith ext, dataset := some ds, services, now := some now }
  if let some failure := q.serviceFailure env ds then return error failure.message
  let config : GpuQuery.Config :=
    { available := available && mode != "cpu", minLeftRows := minRows, minRightRows := minRows,
      maxInputRows := 1000000, maxOutputPairs := maxPairs }
  let backend := if entail == "none" || entail == "" then od.backendThunk.get.backend
    else (LawfulDataset.ofDataset ds).backend
  let useGpu := mode == "gpu" || GpuQuery.worthwhile config backend q
  let n ← counter.get
  counter.set (n + 1)
  let id := s!"sparql-gpu-{n}"
  let input : EvalInput := {env, ds, backend := if referenceCpu then none else some backend, query := q}
  let plan := if useGpu then gpuSparqlPlan config input else .done (shippedEvaluator.run input)
  let s : Session :=
    { query := q, dataset := ds, env, config, backend, useGpu, referenceCpu, output,
      requiredGpu := mode == "gpu", plan }
  sessions.modify (·.insert id s)
  let result ← advance 256 id s
  -- Errors before the host learns the session id must not leak a slot.
  if (Json.parse result >>= fun j => j.getObjVal? "ok" >>= Json.getBool?).toOption == some false then
    sessions.modify (·.erase id)
  pure result

def step (id response : String) : IO String := do
  let some s := (← sessions.get)[id]? | return error "unknown GPU query session"
  if response.utf8ByteSize > 67108864 then return error "GPU query reply exceeds 64 MiB"
  let .ok raw := Json.parse response | return error "malformed GPU query response"
  let .ok request := raw.getObjVal? "requestId" >>= Json.getNat?
    | return error "GPU query response has no requestId"
  if request != s.request then return error "stale or cross-phase GPU query response"
  if let .ok reason := raw.getObjVal? "error" >>= Json.getStr? then
    return ← resumeFailure id s reason
  if let .ok device := raw.getObjVal? "device" then
    if s.deviceChecked then return error "GPU query device was already admitted"
    if device.compress.utf8ByteSize > 4096 then return error "GPU device facts exceed 4 KiB"
    match device with
    | .obj _ => pure ()
    | _ => return error "GPU device facts must be a JSON object"
    let .dispatch job _ := s.plan | return error "GPU query is already complete"
    let software := softwareDevice device
    let s := { s with deviceChecked := true, automaticGpuAllowed := !software, device }
    if software && !s.requiredGpu then
      let s := record s job "cpu" "known software WebGPU adapter; automatic execution uses CPU"
      let answer := s.plan.cpu
      return ← finish id { s with plan := .done answer, pending := none, cpuFallbacks := s.cpuFallbacks + 1 } answer
    return ← advance 256 id s
  if !s.deviceChecked then return error "GPU query device capabilities have not been admitted"
  let .ok outputs := raw.getObjVal? "outputs" | return error "GPU query response has no outputs"
  let .dispatch job resume := s.plan | return error "GPU query is already complete"
  match s.pending with
  | none => pure (error "GPU query has no pending request")
  | some (.ranges prepared) =>
    match IndexedJoin.acceptRanges? prepared outputs with
    | .error reason => resumeFailure id s reason
    | .ok counted =>
      if counted.total > job.maxPairs then
        return ← resumeFailure id s "GPU join output exceeds configured pair limit before allocation"
      if counted.total == 0 then
        match IndexedJoin.acceptPairs? prepared counted (Json.mkObj [("pairs", toJson ([] : List Nat))]) with
        | .error reason => return ← resumeFailure id s reason
        | .ok pairs =>
          let s := record s job "gpu" "validated empty join" 0
          return ← advance 256 id { s with plan := resume (some pairs), pending := none, gpuJoins := s.gpuJoins + 1 }
      match IndexedJoin.phase2Plan? counted with
      | .error reason => resumeFailure id s reason
      | .ok plan =>
        let s := { s with pending := some (.pairs prepared counted), request := s.request + 1 }
        emitJob id s "pairs" plan (IndexedJoin.phase2Bindings counted)
  | some (.pairs prepared counted) =>
    match IndexedJoin.acceptPairs? prepared counted outputs with
    | .error reason => resumeFailure id s reason
    | .ok pairs =>
      let s := record s job "gpu" "validated indexed join" counted.total
      advance 256 id { s with plan := resume (some pairs), pending := none, gpuJoins := s.gpuJoins + 1 }

def restart (id : String) : IO String := do
  let some s := (← sessions.get)[id]? | return error "unknown GPU query session"
  match s.plan with
  | .dispatch _ _ => return error "cannot restart a GPU query with an outstanding request"
  | .done _ => pure ()
  if s.pending.isSome then return error "cannot restart a GPU query with an outstanding request"
  if let some failure := s.query.serviceFailure s.env s.dataset then return error failure.message
  advance 256 id { s with plan := startPlan s, gpuJoins := 0, cpuFallbacks := 0, trace := #[] }

def close (id : String) : IO String := do
  sessions.modify (·.erase id)
  pure "{\"ok\":true}"

end L4Wasm.Ops.GpuSparql

namespace L4Wasm.Ops
def datasetQueryGpuBegin := GpuSparql.begin
def datasetQueryGpuStep := GpuSparql.step
def datasetQueryGpuRestart := GpuSparql.restart
def datasetQueryGpuClose := GpuSparql.close
end L4Wasm.Ops
