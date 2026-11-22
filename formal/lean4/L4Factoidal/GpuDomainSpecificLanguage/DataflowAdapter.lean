import Lean.Data.Json
import L4Factoidal.Dataflow.Stage
import L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath

/-!
# PVGraph as a contracted component of Factoidal Dataflow

Dataflow.Stage has the *application-level* contract (documents, RDF,
SPARQL, stores, stages). PVGraph is a *computation within a stage*.
This module connects them without identifying PVGraph with RDF.Graph
or replacing the existing Dataflow.Graph.

A physical GPU implementation would be an IO boundary whose realization
must satisfy the same reference-output contract. Merely returning bytes
from a device does not discharge that obligation.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.DataflowAdapter

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.Dataflow

structure Request where
  pvgraph : Json
  bindings : Json

/-- The interface promise, including the existing Lean reference's errors:
    a successfully returned value is exactly the reference result. -/
def ExactResult (request : Request) (result : Json) : Prop :=
  GraphEvaluate.evaluate? request.pvgraph request.bindings = .ok result

/-- PVGraph's reference evaluator is a real, proof-carrying Dataflow.Stage. -/
def referenceStage : Stage String Request Json where
  run request := GraphEvaluate.evaluate? request.pvgraph request.bindings
  contract := ExactResult
  sound := by
    intro request result h
    exact h

/-- An eligible GPU kernel *model* can be a Dataflow.Stage without changing
    the contract seen by callers of the original Dataflow API. -/
def modeledFastStage : Stage String Request Json where
  run request :=
    GraphEvaluate.evaluateWith? GpuFastPath.modelOrCpu request.pvgraph request.bindings
  contract := ExactResult
  sound := by
    intro request result h
    rw [GpuFastPath.pvgraph_model_eq_reference] at h
    exact h

/-- The two stages return exactly the same output or error for every request. -/
theorem modeledFastStage_run_eq (request : Request) :
    modeledFastStage.run request = referenceStage.run request :=
  GpuFastPath.pvgraph_model_eq_reference request.pvgraph request.bindings

/-- A physical WebGPU run is a Dataflow IOStage, *not* a proved
    pure Stage. Its named assumption states exactly the observational
    obligation on the host runtime and device. -/
def webGpu : IOStage String Request Json :=
  { assumption := ExactResult }

/-- Promote an actual GPU host implementation to Stage only when a
    concrete realisation of the IOStage assumption has been supplied. -/
def stageOfVerifiedDevice (run : Request → Except String Json)
    (sound : webGpu.Realised run) : Stage String Request Json :=
  webGpu.toStage run sound

/-- The Dataflow framework preserves the device contract under its explicit
    realisation premise. This is not a theorem about WebGPU hardware. -/
theorem stageOfVerifiedDevice_contract (run : Request → Except String Json)
    (h : webGpu.Realised run) :
    (stageOfVerifiedDevice run h).contract = ExactResult := rfl

#print axioms modeledFastStage_run_eq
#print axioms stageOfVerifiedDevice_contract

end L4Factoidal.GpuDomainSpecificLanguage.DataflowAdapter
