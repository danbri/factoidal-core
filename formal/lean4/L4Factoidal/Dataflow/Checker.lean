/-
L4Factoidal.Dataflow.Checker — the interface type of a proof checker
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, kind CHECKER).

A checker maps an FPP0 bundle to the claim it accepts. `CheckProfile` names
what acceptance means:

* `foundational`: `CheckContract`. The accepted claim is the bundle's
  conclusion and an `rdfDerivable gd ad t` claim is derivable (`DerivesFull`,
  in some blank-node scope) from the merge of the graph artifacts;
* `rdfs D`: `RdfsCheckContract D`. Accepted with the RDFS profile axiom set,
  the claim is RDFS-entailed (`RdfsEntails`, in some scope) by the merge of the
  graph artifacts (`checkBundle_rdfsEntails`).

`SoundChecker` holds a profile, a `run`, and `sound`: every accepted claim
satisfies the profile. There is no named assumption: both shipped checkers are
proved. The hash functions are not assumed either (`profileAxiomsOk` compares
graph values).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.PhaseE

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.FPP0

/-- What acceptance means. -/
inductive CheckProfile where
  | foundational
  | rdfs (D : List WfIri)

/-- The claim holds of the bundle, in the profile. -/
def CheckProfile.Holds : CheckProfile → Bundle → Claim → Prop
  | .foundational => CheckContract
  | .rdfs D => RdfsCheckContract D

/-- **A proof checker, with "accept implies the claim" as a field.** -/
structure SoundChecker where
  profile : CheckProfile
  run : Bundle → Except String Claim
  sound : ∀ b c, run b = .ok c → profile.Holds b c

namespace SoundChecker

def toStage (k : SoundChecker) : Stage String Bundle Claim :=
  { run := k.run, contract := k.profile.Holds, sound := k.sound }

end SoundChecker

/-- The kernel checker (`checkBundle`, foundational bundles only). -/
def foundationalChecker : SoundChecker where
  profile := .foundational
  run := proofCheckStage.run
  sound := proofCheckStage.sound

/-- The kernel checker with the RDFS profile axiom set. -/
def rdfsChecker (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) : SoundChecker where
  profile := .rdfs D
  run := (proofCheckRdfsStage D cmps hcmps).run
  sound := (proofCheckRdfsStage D cmps hcmps).sound

/-- **Accept implies the claim.** An RDFS-profile acceptance of an
`rdfDerivable` claim gives RDFS entailment from the merge of the graph
artifacts. -/
theorem rdfsChecker_accept (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c)
    {b : Bundle} {c : Claim} (h : (rdfsChecker D cmps hcmps).run b = .ok c)
    {gd ad : String} {t : Triple} (hc : c = Claim.rdfDerivable gd ad t) :
    ∃ s : Scope, RdfsEntails (fun x => x ∈ D) (mergeOf b.artifacts.toList gd) [t.scoped s] :=
  ((rdfsChecker D cmps hcmps).sound b c h).2 gd ad t hc

#print axioms foundationalChecker
#print axioms rdfsChecker
#print axioms rdfsChecker_accept

end L4Factoidal.Dataflow
