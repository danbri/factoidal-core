/-
L4Factoidal.SPARQLRL.OwlRlDiff — the differential check between the
SPARQL-RL OWL 2 RL rule set (`SPARQLRL/OwlRl.lean`) and the Lean OWL 2 RL
closure (`OWL/RLClosureIndexed.lean`).
Requested on https://github.com/danbri/factoidal-core/pull/163.

## The two Lean closures

The Lean closure of `OWL/RLClosure.lean` runs the table rows AND fourteen
`[ext]` rows that no table has (differentFrom synthesis, inverse-property
flips, the XSD axioms, comprehension witnesses, owl:sameAs inside triple
terms, cls-hs1 and cls-hs2, and the premise-free RDF-Based axioms). So the
check has two references:

* `tableClosure`: the indexed naive loop of `RLClosureIndexed`
  (`stepI`/`closureI`) with only the table rows — the same row functions
  (`eqRefSForS` .. `scmUniForS`, 54 of them), and as premise-free triples
  cls-thing, cls-nothing1 and prp-ap (`vocabAnnotationPropertyAxioms`). The
  SPARQL-RL rules of `owlRlCommon` must give the same set of triples.
* `OWL.RL.indexedClosureSN`: the closure that the OWL probe and the library
  use. The difference to it is reported, not required to be empty.

The clash rows are compared the same way: `tableClashRows` is
`OWL.RL.clashRowsS` without `prpFpLitAtS` (a composition of prp-fp with the
datatype rows dt-diff and eq-diff1; decision 5 of `OwlRl.lean`).

## The comparison

Sets of triples, by exact term identity: the inference graph of the rule
set less its helper triples, against the closure less the input graph.
-/
import L4Factoidal.SPARQLRL.OwlRl
import L4Factoidal.OWL.RLClosureIndexed

namespace L4Factoidal.SPARQLRL.OwlRl

open L4Factoidal.RDF
open L4Factoidal.OWL.RL

/-- The table rows of `conclusionsListS`, in its order (54 functions). -/
def tableRowsS (s : Store) (d : Triple) : List (List Triple) :=
  [ eqRefSForS s d, eqRefPForS s d, eqRefOForS s d,
    eqSymForS s d, eqTransForS s d,
    eqRepSForS s d, eqRepPForS s d, eqRepOForS s d,
    prpDomForS s d, prpRngForS s d, prpFpForS s d, prpIfpForS s d,
    prpSympForS s d, prpTrpForS s d, prpSpo1ForS s d, prpSpo2ForS s d,
    prpEqp1ForS s d, prpEqp2ForS s d, prpInv1ForS s d, prpInv2ForS s d,
    prpKeyForS s d,
    clsInt1ForS s d, clsInt2ForS s d, clsUniForS s d,
    clsSvf1ForS s d, clsSvf2ForS s d, clsAvfForS s d,
    clsHv1ForS s d, clsHv2ForS s d,
    clsMaxc2ForS s d, clsOoForS s d,
    caxScoForS s d, caxEqc1ForS s d, caxEqc2ForS s d,
    scmClsForS s d, scmScoForS s d, scmEqc1ForS s d, scmEqc2ForS s d,
    scmSpoForS s d, scmEqp1ForS s d, scmEqp2ForS s d,
    scmDom1ForS s d, scmDom2ForS s d, scmRng1ForS s d, scmRng2ForS s d,
    scmOpForS s d, scmDpForS s d,
    scmSvf1ForS s d, scmSvf2ForS s d, scmAvf1ForS s d, scmAvf2ForS s d,
    scmHvForS s d,
    scmIntForS s d, scmUniForS s d ]

/-- cls-thing, cls-nothing1 and prp-ap. -/
def tableAxioms : List Triple :=
  [⟨Subject.iri owlThing, rdfType, Term.iri owlClass⟩,
   ⟨Subject.iri owlNothing, rdfType, Term.iri owlClass⟩] ++
  vocabAnnotationPropertyAxioms

/-- One round of the table rows over the index (`stepI` with the table
rows only). -/
def tableStepI (i : Index) : Index :=
  let s := Store.ofIndex i
  i.insertAll (tableAxioms ++ s.graph.flatMap (fun d => (tableRowsS s d).flatten))

/-- The fuel loop, with `closureI`'s stopping rule. -/
def tableClosureI (i : Index) : Nat → Index
  | 0 => i
  | n + 1 =>
      let i' := tableStepI i
      if i'.all.size = i.all.size then i else tableClosureI i' n

/-- The table-rows closure of `g`, at the fuel bound of `closureFix`. -/
def tableClosure (g : Graph) : Graph :=
  (tableClosureI (Index.ofGraph g) (closureFuelBound g)).toGraph

/-- The table ids of `clashRowsS` (its order), less prp-fp-lit. -/
def tableClashIds : List String :=
  [ "eq-diff1", "prp-irp", "prp-asyp", "prp-pdw", "prp-npa1", "prp-npa2",
    "cls-nothing2", "cls-com", "cls-maxc1", "cls-maxqc1", "cls-maxqc2",
    "cax-dw", "cax-adc", "eq-diff2", "eq-diff3", "prp-adp" ]

/-- The table clash rows that fire on a closed graph, by table id. -/
def tableClashes (g : Graph) : List String :=
  let s := Store.ofIndex (Index.ofGraph g)
  let fired : List Bool := tableClashIds.zipIdx.map fun (_, k) =>
    g.any (fun d => ((clashRowsS s d).getD k false))
  (tableClashIds.zip fired).filterMap fun (id, b) => if b then some id else none

/-- The closure less the input, as a set of triples (no repetition). -/
def newTriples (g cl : Graph) : List Triple :=
  let base : Std.HashSet Triple := g.foldl (fun s t => s.insert t) {}
  (cl.foldl (fun (seen, out) t =>
    if base.contains t || seen.contains t then (seen, out) else (seen.insert t, out.push t))
    (({} : Std.HashSet Triple), (#[] : Array Triple))).2.toList

/-- `a \ b` as sets. -/
def setMinus (a b : List Triple) : List Triple :=
  let bs : Std.HashSet Triple := b.foldl (fun s t => s.insert t) {}
  a.filter (fun t => !bs.contains t)

/-- The result of one comparison. `onlyRules` are triples the rule set
derives and the reference does not; `onlyLean` the converse. -/
structure Diff where
  onlyRules : List Triple := []
  onlyLean : List Triple := []
  rulesClash : List String := []
  leanClash : List String := []
  ruleCount : Nat := 0
  leanCount : Nat := 0

def Diff.agrees (d : Diff) : Bool :=
  d.onlyRules.isEmpty && d.onlyLean.isEmpty &&
  d.rulesClash.all d.leanClash.contains && d.leanClash.all d.rulesClash.contains

/-- Compare the rule set `rs` over `g` with the reference closure `ref g`.
An error of `RuleSet.infer` is returned as an error. -/
def compareWith (rs : RuleSet) (ref : Graph → Graph) (g : Graph) : Except String Diff := do
  let (ent, cl) ← run rs g
  let rules := newTriples g ent
  let refCl := ref g
  let lean := newTriples g refCl
  return { onlyRules := setMinus rules lean, onlyLean := setMinus lean rules,
           rulesClash := cl, leanClash := tableClashes refCl,
           ruleCount := rules.length, leanCount := lean.length }

/-- The differential that must agree: `owlRlCommon` against the table rows. -/
def compareTable (g : Graph) : Except String Diff := compareWith owlRlCommon tableClosure g

/-- `owlRl` (all rows) against the library closure. -/
def compareLibrary (g : Graph) : Except String Diff :=
  compareWith owlRl (fun g => indexedClosureSN g (closureFuelBound g)) g

/-- `true` when the comparison ran and agrees. -/
def agreesTable (g : Graph) : Bool :=
  match compareTable g with
  | .ok d => d.agrees
  | .error _ => false

end L4Factoidal.SPARQLRL.OwlRl
