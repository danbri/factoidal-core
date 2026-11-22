import L4Factoidal.SPARQL.GsslEncodedBgpRefinement
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder
import L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes
import L4Factoidal.GpuDomainSpecificLanguage.GpuFastPath

/-!
# A restricted RDF BGP lowered to the actual Lean PVGraph evaluator

The identifier model is *UInt64*, as in Shardborough/SBM11.
WGSL receives two u32 words per term. The two halves are compared by
the same generic PVGraph u32.zip.xor operator, and a stable CPU
reconstruction step retains the original RDF Binding payloads.
No RDF identity is replaced with JS numbers or a u32-only codebook.

For ?person <knows> ?colleague . ?colleague <works> <object>, the
existing SPARQL evaluator selects from the *active* RDF graph.
Join comparisons occupy left-major/right-major slots, preserving the
exact multiplicity of duplicate solutions and the solution order.

This quadratic fragment is an assurance milestone, not a fast general
SPARQL join. It assumes a finite equality-checked codebook and proves
the pure model. It does NOT prove GPU WGSL, host I/O, or device fidelity.
-/

namespace L4Factoidal.SPARQL.PvGraphBgpLowering

set_option linter.unusedSimpArgs false

open Lean
open L4Factoidal.RDF
open L4Factoidal.SPARQL.GsslEncodedBgpRefinement
open L4Factoidal.SPARQL.GsslBgpRefinement
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

/-- A comparison slot uses the standard 64-bit term identifiers.
    The Binding payload remains a real RDF solution mapping. -/
structure Comparison where
  binding : Binding
  leftId : UInt64
  rightId : UInt64

/-- Exact finite comparison admission; this does not assert that an
    arbitrary 64-bit codebook is injective over *all* possible RDF terms. -/
def checkCode64 (code : RDF.Term → UInt64)
    (left : List (RdfTermCodebook.Key × Binding))
    (right : List (RdfTermCodebook.Key × Unit)) : Bool :=
  EncodedJoin.checkAgreement
    (fun k : RdfTermCodebook.Key => code k.term) left right

def comparisons (code : RDF.Term → UInt64)
    (left : List (RdfTermCodebook.Key × Binding))
    (right : List (RdfTermCodebook.Key × Unit)) : List Comparison :=
  left.flatMap fun l =>
    right.map fun r => ⟨l.2, code l.1.term, code r.1.term⟩

def leftLow (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.leftId).lo
def leftHigh (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.leftId).hi
def rightLow (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.rightId).lo
def rightHigh (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.rightId).hi

def differenceLow (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.leftId).lo ^^^ (split p.rightId).lo
def differenceHigh (ps : List Comparison) : List UInt32 :=
  ps.map fun p => (split p.leftId).hi ^^^ (split p.rightId).hi

/-- Plain RDF binding list in the original, stable join order. -/
def matchingBindings : List Comparison → SolutionSeq
  | [] => []
  | p :: ps => if p.leftId == p.rightId
      then p.binding :: matchingBindings ps
      else matchingBindings ps

/-- No partial, truncated or extra WebGPU readback can decode as success. -/
def reconstruct : List Comparison → List UInt32 → List UInt32 → Option SolutionSeq
  | [], [], [] => some []
  | p :: ps, dl :: dls, dh :: dhs =>
      (reconstruct ps dls dhs).map fun tail =>
        if dl == 0 && dh == 0 then p.binding :: tail else tail
  | _, _, _ => none

/-- A fixed-width XOR is zero precisely for equal words. -/
theorem word_xor_zero_iff (a b : UInt32) :
    ((a ^^^ b) == (0 : UInt32)) = (a == b) := by
  have hx : (a ^^^ b = (0 : UInt32)) ↔ (a = b) := by
    cases a with
    | ofBitVec x =>
        cases b with
        | ofBitVec y =>
            simp [UInt32.xor, BitVec.xor_eq_zero_iff]
  cases h1 : ((a ^^^ b) == (0 : UInt32)) <;>
    cases h2 : (a == b) <;> simp_all [beq_iff_eq, hx]

/-- Two 32-bit XOR masks recover the equality of the original 64-bit IDs. -/
theorem both_masks_zero_iff (a b : UInt64) :
    (((split a).lo ^^^ (split b).lo == 0) &&
     ((split a).hi ^^^ (split b).hi == 0)) = (a == b) := by
  rw [word_xor_zero_iff, word_xor_zero_iff]
  have encode_pair :
      (((split a).lo == (split b).lo) &&
       ((split a).hi == (split b).hi)) = ((split a) == (split b)) := by
    cases ha : split a with
    | mk alo ahi =>
      cases hb : split b with
      | mk blo bhi =>
        change (alo == blo && ahi == bhi) =
          ((⟨alo,ahi⟩ : Lanes) == ⟨blo,bhi⟩)
        by_cases h1 : alo = blo <;> by_cases h2 : ahi = bhi <;>
          simp_all [beq_iff_eq]
  rw [encode_pair]
  exact split_beq_eq a b

/-- XOR outputs preserve complete comparison-slot count. -/
theorem pairedLow (ps : List Comparison) :
    (leftLow ps).length = (rightLow ps).length := by
  simp [leftLow, rightLow]
theorem pairedHigh (ps : List Comparison) :
    (leftHigh ps).length = (rightHigh ps).length := by
  simp [leftHigh, rightHigh]

private theorem zipLow (ps : List Comparison) :
    List.zipWith (· ^^^ ·) (leftLow ps) (rightLow ps) = differenceLow ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      change ((split p.leftId).lo ^^^ (split p.rightId).lo) ::
        List.zipWith (· ^^^ ·) (leftLow rest) (rightLow rest) =
        ((split p.leftId).lo ^^^ (split p.rightId).lo) :: differenceLow rest
      rw [ih]

private theorem zipHigh (ps : List Comparison) :
    List.zipWith (· ^^^ ·) (leftHigh ps) (rightHigh ps) = differenceHigh ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      change ((split p.leftId).hi ^^^ (split p.rightId).hi) ::
        List.zipWith (· ^^^ ·) (leftHigh rest) (rightHigh rest) =
        ((split p.leftId).hi ^^^ (split p.rightId).hi) :: differenceHigh rest
      rw [ih]

/-- Both operations are the existing generic PVGraph primitive,
    with no RDF-specific arithmetic implementation. -/
theorem pvgraph_low_eq (ps : List Comparison) :
    GraphWords.execute .zipXor
      [.buffer (leftLow ps), .buffer (rightLow ps)] none =
    .ok (.buffer (differenceLow ps)) := by
  have h := GpuFastPath.KernelCall_correct
    (.zipXor (leftLow ps) (rightLow ps) (pairedLow ps))
  change GraphWords.execute .zipXor
    [.buffer (leftLow ps), .buffer (rightLow ps)] none =
      .ok (.buffer (List.zipWith (· ^^^ ·) (leftLow ps) (rightLow ps))) at h
  rw [zipLow] at h
  exact h

theorem pvgraph_high_eq (ps : List Comparison) :
    GraphWords.execute .zipXor
      [.buffer (leftHigh ps), .buffer (rightHigh ps)] none =
    .ok (.buffer (differenceHigh ps)) := by
  have h := GpuFastPath.KernelCall_correct
    (.zipXor (leftHigh ps) (rightHigh ps) (pairedHigh ps))
  change GraphWords.execute .zipXor
    [.buffer (leftHigh ps), .buffer (rightHigh ps)] none =
      .ok (.buffer (List.zipWith (· ^^^ ·) (leftHigh ps) (rightHigh ps))) at h
  rw [zipHigh] at h
  exact h

/-- For all comparison slots, the complete pair of u32 GPU-model
    output buffers reconstructs the exact original RDF bindings. -/
theorem reconstruct_differences (ps : List Comparison) :
    reconstruct ps (differenceLow ps) (differenceHigh ps) =
      some (matchingBindings ps) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      change (reconstruct rest (differenceLow rest) (differenceHigh rest)).map
        (fun tail =>
          if ((split p.leftId).lo ^^^ (split p.rightId).lo == 0) &&
             ((split p.leftId).hi ^^^ (split p.rightId).hi == 0)
          then p.binding :: tail else tail) =
        some (matchingBindings (p :: rest))
      rw [both_masks_zero_iff, ih]
      simp only [matchingBindings]
      cases h : (p.leftId == p.rightId) <;> rfl

private theorem matching_append (a b : List Comparison) :
    matchingBindings (a ++ b) = matchingBindings a ++ matchingBindings b := by
  induction a with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.cons_append, matchingBindings]
      split <;> simp [ih]

private theorem row_matching (code : RDF.Term → UInt64)
    (left : RdfTermCodebook.Key × Binding)
    (right : List (RdfTermCodebook.Key × Unit)) :
    matchingBindings
      (right.map fun r =>
        (⟨left.2, code left.1.term, code r.1.term⟩ : Comparison)) =
    (EncodedJoin.rowMatches (code left.1.term, left.2)
      (right.map fun r => (code r.1.term, r.2))).map Prod.fst := by
  induction right with
  | nil => rfl
  | cons r rest ih =>
      change
        (if code left.1.term == code r.1.term then
          left.2 :: matchingBindings (rest.map fun t =>
            (⟨left.2, code left.1.term, code t.1.term⟩ : Comparison))
         else matchingBindings (rest.map fun t =>
            (⟨left.2, code left.1.term, code t.1.term⟩ : Comparison))) =
        (EncodedJoin.rowMatches (code left.1.term, left.2)
          ((code r.1.term,r.2) :: (rest.map fun t =>
            (code t.1.term,t.2)))).map Prod.fst
      simp only [EncodedJoin.rowMatches, List.filterMap_cons]
      cases hc : (code left.1.term == code r.1.term) with
      | false =>
          simpa [hc] using ih
      | true =>
          simpa [hc] using congrArg (List.cons left.2) ih

/-- Exact ordered and multiplicity-preserving reconstruction from
    equality-comparison slot order. -/
theorem matching_eq_encodedJoin64 (code : RDF.Term → UInt64)
    (left : List (RdfTermCodebook.Key × Binding))
    (right : List (RdfTermCodebook.Key × Unit)) :
    matchingBindings (comparisons code left right) =
    (EncodedJoin.joinRows
      (left.map fun l => (code l.1.term, l.2))
      (right.map fun r => (code r.1.term, r.2))).map Prod.fst := by
  induction left with
  | nil => rfl
  | cons l rest ih =>
      change matchingBindings
        ((right.map fun r =>
          (⟨l.2, code l.1.term, code r.1.term⟩ : Comparison)) ++
            comparisons code rest right) =
        (EncodedJoin.joinRows
          ((l :: rest).map fun l => (code l.1.term,l.2))
          (right.map fun r => (code r.1.term,r.2))).map Prod.fst
      rw [matching_append, row_matching, ih]
      simp [EncodedJoin.joinRows, List.map_append]

/-- A checked finite UInt64 dictionary preserves actual RDF.Term.eqb
    comparison semantics and all ordered solution occurrences. -/
theorem encodedJoin64_eq_indexed (code : RDF.Term → UInt64)
    (person colleague : VarName) (knows works object : WfIri)
    (active : RDF.Graph) (different : person ≠ colleague)
    (checked : checkCode64 code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    (EncodedJoin.joinRows
      ((leftRows person colleague knows active).map fun l =>
        (code l.1.term,l.2))
      ((rightRows works object active).map fun r =>
        (code r.1.term,r.2))).map Prod.fst =
    evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩] active := by
  calc
    _ = rdfJoin person colleague knows works object active := by
      unfold rdfJoin
      exact congrArg (List.map Prod.fst)
        (EncodedJoin.joinRows_encode_checked
          (fun k : RdfTermCodebook.Key => code k.term)
          (leftRows person colleague knows active)
          (rightRows works object active) checked)
    _ = relationalPlan person colleague knows works object active :=
      rdfJoin_eq_relationalPlan person colleague knows works object active
    _ = evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩] active :=
      relationalPlan_eq_evalBgpIdx person colleague knows works object active different

/-- Pure UInt64→two-u32-lanes→RDF correctness, list equality stronger
    than bag equality: order and duplicates remain identical. -/
theorem reconstructed_eq_indexed (code : RDF.Term → UInt64)
    (person colleague : VarName) (knows works object : WfIri)
    (active : RDF.Graph) (different : person ≠ colleague)
    (checked : checkCode64 code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differenceLow (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active)))
      (differenceHigh (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some (evalBgpIdx [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩] active) := by
  rw [reconstruct_differences, matching_eq_encodedJoin64]
  exact congrArg some
    (encodedJoin64_eq_indexed code person colleague knows works object
      active different checked)

/-- Active graph is supplied explicitly; named graphs are not
    accidentally substituted for the default RDF graph. -/
theorem reconstructed_eq_evalIn (dataset : RDF.Dataset) (active : RDF.Graph)
    (code : RDF.Term → UInt64)
    (person colleague : VarName) (knows works object : WfIri)
    (different : person ≠ colleague)
    (checked : checkCode64 code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differenceLow (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active)))
      (differenceHigh (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some ((GraphPattern.bgp [⟨.var person, .iri knows, .var colleague⟩,
      ⟨.var colleague, .iri works, .iri object⟩]).evalIn dataset active) := by
  simpa only [GraphPattern.evalIn] using
    reconstructed_eq_indexed code person colleague knows works object
      active different checked

/-- GRAPH <iri> resolves exactly one named graph in the dataset. -/
theorem reconstructed_eq_namedGraph (dataset : RDF.Dataset) (name : WfIri)
    (active : RDF.Graph)
    (found : dataset.lookupNamedIri name.val = some active)
    (code : RDF.Term → UInt64)
    (person colleague : VarName) (knows works object : WfIri)
    (different : person ≠ colleague)
    (checked : checkCode64 code
      (leftRows person colleague knows active)
      (rightRows works object active) = true) :
    reconstruct
      (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))
      (differenceLow (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active)))
      (differenceHigh (comparisons code
        (leftRows person colleague knows active)
        (rightRows works object active))) =
    some ((GraphPattern.graph (.iri name)
      (.bgp [⟨.var person, .iri knows, .var colleague⟩,
        ⟨.var colleague, .iri works, .iri object⟩])).evalIn
      dataset dataset.default) := by
  simpa only [GraphPattern.evalIn, found] using
    reconstructed_eq_indexed code person colleague knows works object
      active different checked

/-- One genuine serialized PVGraph with two generic XOR operators,
    four input buffers and two output buffers. -/
def pvgraph : Json := build do
  let ll ← input "leftLow"
  let lr ← input "rightLow"
  let hl ← input "leftHigh"
  let hr ← input "rightHigh"
  let dlo ← zipXor ll lr (some "compareLow")
  let dhi ← zipXor hl hr (some "compareHigh")
  output "differenceLow" dlo (some "outLow")
  output "differenceHigh" dhi (some "outHigh")

def inputBindings (ps : List Comparison) : Json :=
  Json.mkObj [("leftLow", toJson ((leftLow ps).map UInt32.toNat)),
    ("rightLow", toJson ((rightLow ps).map UInt32.toNat)),
    ("leftHigh", toJson ((leftHigh ps).map UInt32.toNat)),
    ("rightHigh", toJson ((rightHigh ps).map UInt32.toNat))]

def expectedOutput (ps : List Comparison) : Json :=
  Json.mkObj [("differenceLow", toJson ((differenceLow ps).map UInt32.toNat)),
    ("differenceHigh", toJson ((differenceHigh ps).map UInt32.toNat))]

#guard (PVGraph.admit? pvgraph).isOk

private def sample : List Comparison :=
  [⟨[], 0x2000000000000001, 0x9000000000000001⟩,
   ⟨[], 0x2000000000000001, 0x2000000000000001⟩,
   ⟨[], 0x9000000000000001, 0x9000000000000001⟩]

#guard (match PVGraph.evaluate? pvgraph (inputBindings sample) with
  | .ok answer => answer.compress == (expectedOutput sample).compress
  | .error _ => false)
#guard (reconstruct sample [0,0] [0]).isNone

#print axioms word_xor_zero_iff
#print axioms both_masks_zero_iff
#print axioms reconstruct_differences
#print axioms pvgraph_low_eq
#print axioms pvgraph_high_eq
#print axioms matching_eq_encodedJoin64
#print axioms encodedJoin64_eq_indexed
#print axioms reconstructed_eq_indexed
#print axioms reconstructed_eq_evalIn
#print axioms reconstructed_eq_namedGraph

end L4Factoidal.SPARQL.PvGraphBgpLowering
