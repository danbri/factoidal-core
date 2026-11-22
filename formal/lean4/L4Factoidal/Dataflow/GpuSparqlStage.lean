import L4Factoidal.SPARQL.GpuQuery

/-!
# The shipping mixed CPU/WebGPU SPARQL stage

The browser runner invokes the resumable Wasm query entry. The physical
boundary remains an IOStage: neither a driver nor emitted WGSL is a Lean
proof. Its one numeric device obligation is named below. Under that
obligation, the actual continuation evaluator refines the reference answer
for every mixture of accepted GPU replies and indexed CPU fallbacks.
-/
namespace L4Factoidal.Dataflow

open SPARQL

/-- Exact ordered UInt64 candidate-pair replies, or an explicit CPU refusal.
This includes the sorted-index lowering and host/device readback boundary. -/
def GpuSparqlDeviceLaw (device : GpuQuery.Job → Option GpuQuery.Pairs) : Prop :=
  ∀ (job : GpuQuery.Job), GpuQuery.Job.ReplyValid job (device job)

def GpuSparqlContract (input : EvalInput) (answer : Answer) : Prop :=
  answer = referenceAnswer input

/-- The same plan used by Wasm.Ops.GpuSparql; the host advances it one
constructor at a time, retaining the input snapshot in the Lean session. -/
def gpuSparqlPlan (cfg : GpuQuery.Config) (input : EvalInput) : GpuQuery.Plan Answer :=
  GpuQuery.begin cfg input.env input.ds input.query

def gpuSparqlStage : IOStage String EvalInput Answer :=
  { assumption := GpuSparqlContract }

/-- Kind: conditional implementation refinement.
Says: the actual plan returns the reference answer under the numeric device
law, including arbitrary CPU refusals. Does not say: emitted GPU code or a
particular device has been proved to satisfy that law. -/
theorem gpuSparqlPlan_sound (cfg : GpuQuery.Config) (input : EvalInput)
    (device : GpuQuery.Job → Option GpuQuery.Pairs) (hd : GpuSparqlDeviceLaw device) :
    GpuSparqlContract input ((gpuSparqlPlan cfg input).run device) := by
  exact GpuQuery.Plan.run_eq _ _ (GpuQuery.begin_sound cfg input.env input.ds input.query) device hd

#print axioms gpuSparqlPlan_sound

end L4Factoidal.Dataflow
