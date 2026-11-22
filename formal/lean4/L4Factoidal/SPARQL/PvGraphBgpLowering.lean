import L4Factoidal.SPARQL.GsslEncodedBgpRefinement
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
# Restricted BGP lowering to the real, versioned PVGraph

For ?person <knows> ?colleague . ?colleague <works> <object>,
the source RDF graph is read using the existing Factoidal SPARQL
selection code. Join keys are represented by a finite, checked UInt32
codebook, but the solution Binding payloads remain original RDF Terms.

Each potential left/right pair occupies a slot, left-major then
right-major. The generic PVGraph u32.zip.xor operator computes word
differences; zero denotes a matching key. Stable reconstruction
retains the original RDF binding payload, preserving order and
multiplicity. This profile is quadratic and capacity-bounded: it is
a correctness bridge, not evidence of a competitive GPU join.

The abstract XOR/model and RDF-to-BGP theorems below are universal.
A separately admitted *actual serialized PVGraph* is exercised by
the executable guard. Universal serialized-evaluator/WGSL/device
refinement is not claimed by this module.
-/

namespace L4Factoidal.SPARQL.PvGraphBgpLowering

open Lean
open L4Factoidal.RDF
open L4Factoidal.SPARQL.GsslEncodedBgpRefinement
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

/-- One comparison lane; the payload never crosses into the GPU. -/
structure Comparison where
  binding : Binding
  leftWord : UInt32
  rightWord : UInt32

/-- Left-major/right-major Cartesian slot order, including every
    occurrence. No deduplication or sorting is performed here. -/
def comparisons (code : Term → UInt32)
    (left : List (RdfTermCodebook.Key × Binding))
    (right : List (RdfTermCodebook.Key × Unit)) : List Comparison :=
  left.flatMap fun l =>
    right.map fun r => ⟨l.2, code l.1.term, code r.1.term⟩

def leftWords (ps : List Comparison) : List UInt32 :=
  ps.map Comparison.leftWord

def rightWords (ps : List Comparison) : List UInt32 :=
  ps.map Comparison.rightWord

def differences (ps : List Comparison) : List UInt32 :=
  ps.map (fun p => p.leftWord ^^^ p.rightWord)

/-- Stable, occurrence-preserving decoder in the original RDF space. -/
def matches : List Comparison → SolutionSeq
  | [] => []
  | p :: ps =>
      if p.leftWord == p.rightWord then p.binding :: matches ps
      else matches ps

/-- Decode *exactly* the expected output count; a truncated or extra GPU
    buffer cannot silently become a valid answer. -/
def reconstruct : List Comparison → List UInt32 → Option SolutionSeq
  | [], [] => some []
  | p :: ps, d :: ds =>
      (reconstruct ps ds).map fun tail =>
        if d == 0 then p.binding :: tail else tail
  | _, _ => none

/-- UInt32 XOR is zero precisely when both 32-bit words are identical.
    There is no narrowing to JavaScript Number in this proof. -/
theorem word_xor_zero_iff (a b : UInt32) :
    ((a ^^^ b) == (0 : UInt32)) = (a == b) := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      simp [UInt32.xor, BitVec.xor_eq_zero_iff]

/-- For every list of comparison lanes the exact XOR output reconstructs
    the same ordered bag of RDF bindings as direct integer equality. -/
theorem reconstruct_differences (ps : List Comparison) :
    reconstruct ps (differences ps) = some (matches ps) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      simp only [differences, List.map_cons, reconstruct, ih, Option.map_some]
      simp only [matches]
      rw [word_xor_zero_iff]
      split <;> rfl

/-- Empty and nonempty lane lists have equal left/right input lengths. -/
theorem paired_lengths (ps : List Comparison) :
    (leftWords ps).length = (rightWords ps).length := by
  simp [leftWords, rightWords]

private theorem zipPairWords (ps : List Comparison) :
    List.zipWith (· ^^^ ·) (leftWords ps) (rightWords ps) = differences ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      simp [leftWords, rightWords, differences, ih]

/-- The *existing* generic Lean PVGraph primitive computes the exact
    comparison lanes, not a separately invented RDF-specific operation. -/
theorem pvgraph_zipXor_matches_model (ps : List Comparison) :
    GraphWords.execute .zipXor
      [.buffer (leftWords ps), .buffer (rightWords ps)] none =
      .ok (.buffer (differences ps)) := by
  simp only [GraphWords.execute, paired_lengths, BEq.beq]
  exact congrArg (fun xs => Except.ok (GraphWords.Value.buffer xs))
    (zipPairWords ps)

/-- Each right-side match produces exactly the original left binding.
    Right multiplicity is preserved, as is left-major/right-major order. -/
private theorem row_matches (code : Term → UInt32)
    (left : RdfTermCodebook.Key × Binding)
    (right : List (RdfTermCodebook.Key × Unit)) :
    matches (right.map fun r =>
      (⟨left.2, code left.1.term, code r.1.term⟩ : Comparison)) =
    (EncodedJoin.rowMatches (code left.1.term, left.2)
      (right.map fun r => (code r.1.term, r.2))).map Prod.fst := by
  induction right with
  | nil => rfl
  | cons r rest ih =>
      simp only [List.map_cons, matches, EncodedJoin.rowMatches,
        List.filterMap_cons, List.map_cons]
      cases h : code left.1.term == code r.1.term <;> simp [h, ih]

private theorem matches_append (a b : List Comparison) :
    matches (a ++ b) = matches a ++ matches b := by
  induction a with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.cons_append, matches]
      split <;> simp [ih]

/-- The stable mask decoder has the same ordered bag as the generic
    equality-encoded join, including duplicate right-hand matches. -/
theorem matches_eq_encodedJoin (code : Term → UInt32)
    (left : List (RdfTermCodebook.Key × Binding))
    (right : List (RdfTermCodebook.Key × Unit)) :
    matches (comparisons code left right) =
    (EncodedJoin.joinRows
      (left.map fun l => (code l.1.term, l.2))
      (right.map fun r => (code r.1.term, r.2))).map Prod.fst := by
  induction left with
  | nil => rfl
  | cons l rest ih =>
      simp only [comparisons, List.flatMap_cons, List.map_cons]
      rw [matches_append, row_matches, ih]
      rfl

/-- Source-level RDF→word-comparison→RDF round-trip, for any active
    RDF graph and a codebook passing the exact finite equality check.
    This is list equality, stronger than set or bag equality. -/
theorem reconstructed_eq_indexed (code : Term → UInt32)
    (person colleague : VarName) (knows works object : WfIri)
    (active : Graph) (different : person ≠ colleague)
    (checked : RdfTermCodebook.check code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differences (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some (evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩] active) := by
  rw [reconstruct_differences, matches_eq_encodedJoin]
  exact congrArg some
    (encodedJoin_eq_evalBgpIdx code person colleague knows works object
      active different checked)

/-- The same proof against the *active graph* argument of
    GraphPattern.evalIn: named graphs are not silently unioned into the
    default graph. -/
theorem reconstructed_eq_evalIn (dataset : Dataset) (active : Graph)
    (code : Term → UInt32)
    (person colleague : VarName) (knows works object : WfIri)
    (different : person ≠ colleague)
    (checked : RdfTermCodebook.check code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differences (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some ((GraphPattern.bgp [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩]).evalIn dataset active) := by
  simpa only [GraphPattern.evalIn] using
    reconstructed_eq_indexed code person colleague knows works object
      active different checked

/-- Selection by GRAPH <iri> uses only that named graph, and has
    the same complete ordered answer as the original SPARQL evaluator. -/
theorem reconstructed_eq_namedGraph (dataset : Dataset) (name : WfIri)
    (active : Graph)
    (found : dataset.lookupNamedIri name.val = some active)
    (code : Term → UInt32)
    (person colleague : VarName) (knows works object : WfIri)
    (different : person ≠ colleague)
    (checked : RdfTermCodebook.check code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differences (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some ((GraphPattern.graph (.iri name)
      (.bgp [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩])).evalIn
      dataset dataset.default) := by
  simpa only [GraphPattern.evalIn, found] using
    reconstructed_eq_indexed code person colleague knows works object
      active different checked

/-- The precise PVGraph document whose one operator computes XOR
    differences on two equal-length word buffers. -/
def pvgraph : Json := build do
  let left ← input "leftWords"
  let right ← input "rightWords"
  let diff ← zipXor left right (some "compare")
  output "differences" diff (some "answer")

def inputBindings (ps : List Comparison) : Json :=
  Json.mkObj [("leftWords", toJson ((leftWords ps).map UInt32.toNat)),
    ("rightWords", toJson ((rightWords ps).map UInt32.toNat))]

def expectedOutput (ps : List Comparison) : Json :=
  Json.mkObj [("differences", toJson ((differences ps).map UInt32.toNat))]

#guard (PVGraph.admit? pvgraph).isOk

-- Actual serialized Lean PVGraph evaluator, not a proxy graph.
private def sample : List Comparison :=
  [⟨[], 0, 0⟩, ⟨[], 1, 2⟩, ⟨[], 4294967295, 4294967295⟩]

#guard (match PVGraph.evaluate? pvgraph (inputBindings sample) with
  | .ok answer => answer.compress == (expectedOutput sample).compress
  | .error _ => false)
#guard (reconstruct sample [0,0]).isNone

#print axioms word_xor_zero_iff
#print axioms reconstruct_differences
#print axioms pvgraph_zipXor_matches_model
#print axioms matches_eq_encodedJoin
#print axioms reconstructed_eq_indexed
#print axioms reconstructed_eq_evalIn
#print axioms reconstructed_eq_namedGraph

end L4Factoidal.SPARQL.PvGraphBgpLowering
