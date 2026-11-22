import L4Factoidal.SPARQL.GsslCertifiedFastPath
import L4Factoidal.SPARQL.GsslSnapshotLease
import L4Factoidal.Dataflow.Stage

/-!
# Hybrid SPARQL placement: CPU, GPU, persistent index and effectful services

The SPARQL planner may choose backends independently for *pure* BGP
subplans. The choice never changes the indexed evaluator's semantics:
GPU/storage candidates require exact-query/active-graph certificates;
unsupported or uncertified paths use the existing CPU evaluator.

REST and MCP endpoints are effectful service boundaries, not generic
GPU nodes. The host provides their external data; Dataflow.IOStage
records a named semantic obligation. This module does not purport to
verify a remote server or perform network calls.
-/

namespace L4Factoidal.SPARQL.PvGraphHybridPlacement

open L4Factoidal.RDF
open L4Factoidal.Dataflow

inductive LocalBackend where
  | leanIndexed
  | gpu
  | persistentStore
  deriving DecidableEq, Repr, Inhabited

structure Capabilities where
  gpuAvailable : Bool := false
  persistentStoreAvailable : Bool := false

structure Estimates where
  comparisonPairs : Nat := 0
  indexedRows : Nat := 0

/-- Advisory policy only. An accelerator must still pass admission,
    capacity, snapshot-lease and backend-correctness gates. -/
def choose (caps : Capabilities) (estimate : Estimates)
    (bgp : Bgp) : LocalBackend :=
  if caps.gpuAvailable && GsslFastPath.supports bgp &&
      decide (estimate.comparisonPairs >= 1024) then .gpu
  else if caps.persistentStoreAvailable &&
      decide (estimate.indexedRows >= 4096) then .persistentStore
  else .leanIndexed

/-- No candidate from a different BGP or different active RDF graph can
    inhabit this type: both appear in the candidate type indices. -/
def run (backend : LocalBackend) (bgp : Bgp) (active : RDF.Graph)
    (candidate : Option (GsslCertifiedFastPath.CertifiedCandidate bgp active)) :
    SolutionSeq :=
  match backend with
  | .leanIndexed => evalBgpIdx bgp active
  | .gpu | .persistentStore =>
      GsslCertifiedFastPath.resolve bgp active candidate

/-- CPU, GPU and persisted-index choices preserve SPARQL binding order,
    multiplicity and full RDF term payload, once admitted. -/
theorem run_eq_indexed (backend : LocalBackend)
    (bgp : Bgp) (active : RDF.Graph)
    (candidate : Option (GsslCertifiedFastPath.CertifiedCandidate bgp active)) :
    run backend bgp active candidate = evalBgpIdx bgp active := by
  cases backend with
  | leanIndexed => rfl
  | gpu => exact GsslCertifiedFastPath.resolve_eq_indexed bgp active candidate
  | persistentStore => exact GsslCertifiedFastPath.resolve_eq_indexed bgp active candidate

/-- The heuristic can change without invalidating the semantics theorem. -/
theorem chosen_eq_indexed (caps : Capabilities) (est : Estimates)
    (bgp : Bgp) (active : RDF.Graph)
    (candidate : Option (GsslCertifiedFastPath.CertifiedCandidate bgp active)) :
    run (choose caps est bgp) bgp active candidate =
      evalBgpIdx bgp active :=
  run_eq_indexed _ _ _ _

/-- The host must establish the active graph's snapshot identity and
    validate it again before accepting an asynchronous GPU or persisted
    candidate. A stale result, even one once certified, uses the CPU path. -/
def runWithLease (backend : LocalBackend)
    (bgp : Bgp) (active : RDF.Graph)
    (expected : GsslSnapshotLease.Lease)
    (offered : Option (GsslSnapshotLease.Lease ×
      GsslCertifiedFastPath.CertifiedCandidate bgp active)) :
    SolutionSeq :=
  match backend with
  | .leanIndexed => evalBgpIdx bgp active
  | .gpu | .persistentStore =>
      GsslSnapshotLease.resolveGuarded bgp active expected offered

theorem runWithLease_eq_indexed (backend : LocalBackend)
    (bgp : Bgp) (active : RDF.Graph)
    (expected : GsslSnapshotLease.Lease)
    (offered : Option (GsslSnapshotLease.Lease ×
      GsslCertifiedFastPath.CertifiedCandidate bgp active)) :
    runWithLease backend bgp active expected offered =
      evalBgpIdx bgp active := by
  cases backend with
  | leanIndexed => rfl
  | gpu =>
      exact GsslSnapshotLease.resolveGuarded_eq_indexed
        bgp active expected offered
  | persistentStore =>
      exact GsslSnapshotLease.resolveGuarded_eq_indexed
        bgp active expected offered

inductive RemoteProtocol where
  | sparqlService | restHttp | mcpTool
  deriving Repr, DecidableEq

structure RemoteRequest where
  protocol : RemoteProtocol
  endpoint : String
  requestId : String
  sourceSnapshot : String
  inputBindings : SolutionSeq

/-- The original Dataflow IO mechanism explicitly names the obligation
    on a REST/MCP/SERVICE adapter. Only a realized IOStage may be composed
    with a proved application-level Stage. -/
def remoteIO (meaning : RemoteRequest → SolutionSeq → Prop) :
    IOStage String RemoteRequest SolutionSeq :=
  { assumption := meaning }

/-- Composition does not assume REST or MCP requests are pure or
    schedule-independent. The caller must supply the host realization. -/
def serviceStage (meaning : RemoteRequest → SolutionSeq → Prop)
    (ioRun : RemoteRequest → Except String SolutionSeq)
    (validated : (remoteIO meaning).Realised ioRun) :
    Stage String RemoteRequest SolutionSeq :=
  (remoteIO meaning).toStage ioRun validated

theorem serviceStage_contract (meaning : RemoteRequest → SolutionSeq → Prop)
    (ioRun : RemoteRequest → Except String SolutionSeq)
    (validated : (remoteIO meaning).Realised ioRun) :
    (serviceStage meaning ioRun validated).contract = meaning := rfl

#guard choose {} {} [] == .leanIndexed
#guard choose {gpuAvailable:=true,persistentStoreAvailable:=true}
  {comparisonPairs:=100000,indexedRows:=100000} [] == .persistentStore

#print axioms runWithLease_eq_indexed
#print axioms run_eq_indexed
#print axioms chosen_eq_indexed
#print axioms serviceStage_contract

end L4Factoidal.SPARQL.PvGraphHybridPlacement
