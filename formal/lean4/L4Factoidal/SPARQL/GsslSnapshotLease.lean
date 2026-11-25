import L4Factoidal.SPARQL.GsslCertifiedFastPath
import L4Factoidal.Storage.Sbm11.TermId

/-!
# GSSL: request/snapshot admission of a certified accelerator reply

A physical GPU reply can arrive late, after the active graph, request,
SBM11 generation or codebook has changed. A reply must be refused unless
its ORIGINAL dispatch identity agrees with the one still current.

The equality guard below is a pure proof of *no cross-request selection*.
The host must create the lease from an authentic snapshot and compute
the actual content fingerprints; a string claimed by an untrusted device
is not evidence of provenance.

Even after a lease matches, the candidate must carry the existing
CertifiedCandidate indexed by the exact BGP and RDF graph. Raw GPU
readback cannot construct this proof merely by sending an assertion.
Device, compiler, transport and host trust are outside this model.
-/
namespace L4Factoidal.SPARQL.GsslSnapshotLease

open L4Factoidal.RDF
open L4Factoidal.SPARQL

inductive Layout where
  | direct64Lanes
  | dense32Snapshot
  deriving DecidableEq, Repr

/-- An equality-comparable, immutable request identity. The content hashes
    are opaque here, not proved cryptographic functions. A generation
    number alone is insufficient when multiple datasets or dictionaries
    coexist. Note the explicit separation between GraphId and TermId. -/
structure Lease where
  sourceId : String
  generation : String
  graphId : L4Factoidal.Storage.Sbm11.GraphId
  graphDigest : String
  codebookDigest : String
  queryDigest : String
  requestNumber : Nat
  layout : Layout
  deriving DecidableEq, Repr

/-- A missing, stale, cross-query, cross-graph, cross-generation or
    cross-layout reply yields no candidate. -/
def fresh? (expected : Lease) : Option (Lease × α) → Option α
  | none => none
  | some (actual, candidate) =>
      if actual == expected then some candidate else none

theorem fresh_accept (expected : Lease) (candidate : α) :
    fresh? expected (some (expected, candidate)) = some candidate := by
  simp [fresh?]

theorem stale_refused (expected actual : Lease) (candidate : α)
    (stale : actual ≠ expected) :
    fresh? expected (some (actual, candidate)) = none := by
  simp [fresh?, beq_iff_eq, stale]

theorem missing_refused (expected : Lease) :
    fresh? expected (none : Option (Lease × α)) = none := by
  rfl

/-- A logical API: only an evidence-carrying answer for this precise
    BGP and graph can bypass the CPU result. Lease equality additionally
    prevents reuse across unrelated in-flight requests. -/
def resolveGuarded (bgp : Bgp) (graph : Graph)
    (expected : Lease)
    (offered : Option (Lease ×
      GsslCertifiedFastPath.CertifiedCandidate bgp graph)) : SolutionSeq :=
  GsslCertifiedFastPath.resolve bgp graph (fresh? expected offered)

/-- The semantic result is the actual indexed evaluator whenever the
    offered answer has a genuine Lean correctness certificate. -/
theorem resolveGuarded_eq_indexed (bgp : Bgp) (graph : Graph)
    (expected : Lease)
    (offered : Option (Lease ×
      GsslCertifiedFastPath.CertifiedCandidate bgp graph)) :
    resolveGuarded bgp graph expected offered = evalBgpIdx bgp graph :=
  GsslCertifiedFastPath.resolve_eq_indexed bgp graph (fresh? expected offered)

/-- A stale reply unconditionally takes the CPU fallback branch, even
    if an old proof certificate existed for the same BGP and graph. -/
theorem stale_fallback (bgp : Bgp) (graph : Graph)
    (expected actual : Lease)
    (certificate : GsslCertifiedFastPath.CertifiedCandidate bgp graph)
    (stale : actual ≠ expected) :
    resolveGuarded bgp graph expected (some (actual, certificate)) =
      evalBgpIdx bgp graph := by
  unfold resolveGuarded
  rw [stale_refused expected actual certificate stale]
  cases h : GsslFastPath.supports bgp <;>
    simp [GsslCertifiedFastPath.resolve, h]

private def exampleLease : Lease :=
  { sourceId := "fixture"
    generation := "g1"
    graphId := L4Factoidal.Storage.Sbm11.GraphId.default
    graphDigest := "graph-digest-a"
    codebookDigest := "codebook-digest-a"
    queryDigest := "query-a"
    requestNumber := 1
    layout := .direct64Lanes }

#guard fresh? exampleLease (some (exampleLease, 12)) == some 12
#guard fresh? exampleLease (some ({exampleLease with requestNumber := 2}, 12)) == none
#guard fresh? exampleLease (some ({exampleLease with layout := .dense32Snapshot}, 12)) == none
#guard fresh? exampleLease (some ({exampleLease with generation := "g2"}, 12)) == none
#guard fresh? exampleLease (some ({exampleLease with graphDigest := "changed"}, 12)) == none

#print axioms fresh_accept
#print axioms stale_refused
#print axioms missing_refused
#print axioms resolveGuarded_eq_indexed
#print axioms stale_fallback

end L4Factoidal.SPARQL.GsslSnapshotLease
