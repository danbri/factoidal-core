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
  graph artifacts (`checkBundle_rdfsEntails`);
* `rdfsGraph D`: `GraphCheckContract D`. The bundle is a `GraphBundle`
  (`Dataflow/GraphClaim.lean`, https://github.com/danbri/factoidal/issues/1002)
  and the claim is a description, a graph: accepted, the sources RDFS-entail
  the description (`checkGraphRun_sound`).

`CheckProfile β γ` is indexed by the bundle type `β` and the claim type `γ`:
the FPP0 profiles check `Bundle → Claim`, the graph profile checks
`GraphBundle → GraphClaim`.

`SoundChecker β γ` holds a profile, a `run`, and `sound`: every accepted claim
satisfies the profile. There is no named assumption: the three shipped
checkers are proved. The hash functions are not assumed either (`profileAxiomsOk` compares
graph values).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.PhaseE
import L4Factoidal.Dataflow.GraphClaim

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.FPP0

/-- What acceptance means. -/
inductive CheckProfile : Type → Type → Type 1 where
  | foundational : CheckProfile Bundle Claim
  | rdfs (D : List WfIri) : CheckProfile Bundle Claim
  | rdfsGraph (D : List WfIri) : CheckProfile GraphBundle GraphClaim

/-- The claim holds of the bundle, in the profile. -/
def CheckProfile.Holds : {β γ : Type} → CheckProfile β γ → β → γ → Prop
  | _, _, .foundational => CheckContract
  | _, _, .rdfs D => RdfsCheckContract D
  | _, _, .rdfsGraph D => GraphCheckContract D

/-- **A proof checker, with "accept implies the claim" as a field.** -/
structure SoundChecker (β γ : Type) where
  profile : CheckProfile β γ
  run : β → Except String γ
  sound : ∀ b c, run b = .ok c → profile.Holds b c

namespace SoundChecker

def toStage {β γ : Type} (k : SoundChecker β γ) : Stage String β γ :=
  { run := k.run, contract := k.profile.Holds, sound := k.sound }

end SoundChecker

/-- The kernel checker (`checkBundle`, foundational bundles only). -/
def foundationalChecker : SoundChecker Bundle Claim where
  profile := .foundational
  run := proofCheckStage.run
  sound := proofCheckStage.sound

/-- The kernel checker with the RDFS profile axiom set. -/
def rdfsChecker (D cmps : List WfIri) (hcmps : ∀ c ∈ cmps, IsRdfMemberIri c) :
    SoundChecker Bundle Claim where
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

/-- **The graph checker** (https://github.com/danbri/factoidal/issues/1002):
a `GraphBundle` is accepted when its RDFS derivation checks and every triple
of the description has its instance, under the one mapping of the bundle, as
the conclusion of a cited step. The axiom set is computed by the checker. -/
def rdfsGraphChecker (D : List WfIri) : SoundChecker GraphBundle GraphClaim where
  profile := .rdfsGraph D
  run := checkGraphRun D
  sound := checkGraphRun_sound D

/-- **Accept implies the description.** The sources of the bundle RDFS-entail
its description (RDF 1.1 Semantics section 9.2). -/
theorem rdfsGraphChecker_accept (D : List WfIri) {b : GraphBundle} {c : GraphClaim}
    (h : (rdfsGraphChecker D).run b = .ok c) :
    RdfsEntails (fun x => x ∈ D) b.sources b.description := by
  obtain ⟨hs, hd, he⟩ := (rdfsGraphChecker D).sound b c h
  rw [hs, hd] at he
  exact he

#print axioms foundationalChecker
#print axioms rdfsChecker
#print axioms rdfsChecker_accept
#print axioms rdfsGraphChecker
#print axioms rdfsGraphChecker_accept

end L4Factoidal.Dataflow
