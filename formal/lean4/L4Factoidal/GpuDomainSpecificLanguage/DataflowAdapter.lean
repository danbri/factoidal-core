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

/-- GPU readback is a host boundary; its correctness must be established
    independently before promoting it to a contract-preserving Stage. -/
def DeviceResultCorrect (request : Request) (result : Json) : Prop :=
  ExactResult request result

/-- A future device implementation can be admitted into Dataflow.Stage only
    by supplying its actual run function and the contract proof. -/
def stageOfVerifiedDevice (run : Request → Except String Json)
    (sound : ∀ request output, run request = .ok output →
      DeviceResultCorrect request output) : Stage String Request Json :=
  { run, contract := ExactResult, sound }

#print axioms modeledFastStage_run_eq

end L4Factoidal.GpuDomainSpecificLanguage.DataflowAdapter
