import L4Factoidal.Dataflow.GpuSparqlStage
import L4Factoidal.GpuDomainSpecificLanguage.IndexedJoinCorrectness

/-!
# Untrusted device replies refine the shipping SPARQL stage

The complete numerical device law follows from the actual Lean readback
validators. A device may return arbitrary buffers, including corrupt data;
the validators either reconstruct the exact ordered join or refuse it and
the continuation uses its CPU path. No GPU-fidelity premise is required.

The remaining IO boundary concerns delivery of the session's actual request
and response buffers to those functions, not the mathematical join algorithm.
-/
namespace L4Factoidal.Dataflow

open SPARQL
open GpuDomainSpecificLanguage

/-- The actual successful numeric decoder establishes the SPARQL job law.
    The equality is of the full ordered list, including all multiplicities. -/
theorem acceptedGpuSparqlReply_valid (job : GpuQuery.Job) (p : IndexedJoin.Prepared)
    (c : IndexedJoin.Counted) (rangeReply pairReply : Lean.Json) (answer : GpuQuery.Pairs)
    (hp : IndexedJoin.prepare? job.left job.right = .ok p)
    (hr : IndexedJoin.acceptRanges? p rangeReply = .ok c)
    (ha : IndexedJoin.acceptPairs? p c pairReply = .ok answer) :
    GpuQuery.Job.ReplyValid job (some answer) := by
  exact IndexedJoin.accepted_join_eq_reference job.left job.right p c
    rangeReply pairReply answer hp hr ha

/-- The same numerical acceptance path used by the suspended Wasm session.
    The session retains prepared and counted values between the two replies;
    this pure adapter composes those steps for the semantic statement. -/
def checkedGpuSparqlReply? (job : GpuQuery.Job) (rangeReply pairReply : Lean.Json) :
    Except String GpuQuery.Pairs := do
  let p ← IndexedJoin.prepare? job.left job.right
  let c ← IndexedJoin.acceptRanges? p rangeReply
  if c.total > job.maxPairs then
    .error "GPU join output exceeds configured pair limit before allocation"
  else IndexedJoin.acceptPairs? p c pairReply

/-- A missing response or any failed admission resumes the existing CPU
    operation. Device buffers are never accepted on trust. -/
def checkedGpuSparqlDeviceReply (job : GpuQuery.Job)
    (reply : Option (Lean.Json × Lean.Json)) : Option GpuQuery.Pairs :=
  reply.bind (fun r => (checkedGpuSparqlReply? job r.1 r.2).toOption)

theorem checkedGpuSparqlReply_sound (job : GpuQuery.Job) (rangeReply pairReply : Lean.Json)
    (answer : GpuQuery.Pairs)
    (h : checkedGpuSparqlReply? job rangeReply pairReply = .ok answer) :
    GpuQuery.Job.ReplyValid job (some answer) := by
  unfold checkedGpuSparqlReply? at h
  cases hp : IndexedJoin.prepare? job.left job.right with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    simp only [hp, bind, Except.bind] at h
    cases hr : IndexedJoin.acceptRanges? p rangeReply with
    | error e => simp [hr] at h
    | ok c =>
      simp only [hr] at h
      split at h
      · contradiction
      · exact acceptedGpuSparqlReply_valid job p c rangeReply pairReply answer hp hr h

/-- Kind: unconditional parser refinement.
    Says: every raw reply, including arbitrary corrupted GPU bytes, satisfies
    the numeric continuation law after the actual validators run.
    Does not say: a device will be available or return a successful result. -/
theorem checkedGpuSparqlDeviceReply_valid (job : GpuQuery.Job)
    (reply : Option (Lean.Json × Lean.Json)) :
    GpuQuery.Job.ReplyValid job (checkedGpuSparqlDeviceReply job reply) := by
  cases reply with
  | none => trivial
  | some r =>
    rcases r with ⟨rangeReply,pairReply⟩
    cases h : checkedGpuSparqlReply? job rangeReply pairReply with
    | error e => simp [checkedGpuSparqlDeviceReply, h, Except.toOption, GpuQuery.Job.ReplyValid]
    | ok answer =>
      simpa only [checkedGpuSparqlDeviceReply, Option.bind_some, h, Except.toOption] using
        checkedGpuSparqlReply_sound job rangeReply pairReply answer h

/-- Kind: complete checked implementation refinement.
    Says: arbitrary raw device replies, checked by the production acceptance
    functions, give exactly the reference SPARQL answer for the shipping
    mixed plan. No numeric-device correctness premise is needed.
    Does not say: the host/session transport has been verified in Lean. -/
theorem checkedGpuSparqlPlan_sound (cfg : GpuQuery.Config) (input : EvalInput)
    (device : GpuQuery.Job → Option (Lean.Json × Lean.Json)) :
    GpuSparqlContract input
      ((gpuSparqlPlan cfg input).run (fun job => checkedGpuSparqlDeviceReply job (device job))) := by
  exact gpuSparqlPlan_sound cfg input _ (fun job => checkedGpuSparqlDeviceReply_valid job (device job))

#print axioms acceptedGpuSparqlReply_valid
#print axioms checkedGpuSparqlDeviceReply_valid
#print axioms checkedGpuSparqlPlan_sound

end L4Factoidal.Dataflow
