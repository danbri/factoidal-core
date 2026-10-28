/-
L4Factoidal.DataCube.Normalize — the normalization algorithm of the RDF Data
Cube Recommendation (16 January 2014), section 10.1.

Section 10.1 defines normalization by two SPARQL 1.1 Update requests, applied
in turn to a dataset whose default graph is the cube: phase 1 (type and
property closure) and phase 2 (push down attachment levels). It says the
notation "does not imply that the transformation must be implemented this
way". This module has both forms:

* `normalizeSparql`: the two vendored update requests (`Queries.lean`), run
  by this tree's SPARQL 1.1 Update evaluator (`SPARQL/Update.lean`);
* `normalize`: the same operations written as graph functions, one function
  per INSERT operation, applied in the order of the request.

`NormalizeTheorems.lean` proves that every triple that phase 1 adds is
derivable by the RDF 1.1 Semantics section 9.2 rules (rdfs2, rdfs3, rdfs7)
from the cube and the declarations of the Data Cube vocabulary, as the
Recommendation says ("These closure operations are implied by the RDFS
semantics of the Data Cube vocabulary"). The agreement of `normalize` with
`normalizeSparql` is checked by `tests/datacube/run.sh` on every fixture.
Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.DataCube.Vocabulary
import L4Factoidal.DataCube.Queries
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.DataCube.QB2014

open L4Factoidal.RDF
open L4Factoidal.RDFS (rdfType)

/-! ## Graph access -/

/-- The objects of `s p ?o` in `g`. -/
def objectsOf (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  g.filterMap fun t => if t.s == s && t.p == p then some t.o else none

/-- The triples of `g` with predicate `p`. -/
def withPredicate (g : Graph) (p : WfIri) : List Triple :=
  g.filter fun t => t.p == p

/-- `s p o` is in `g`. -/
def holds (g : Graph) (s : Subject) (p : WfIri) (o : Term) : Bool :=
  g.any fun t => t.s == s && t.p == p && t.o == o

/-- `x rdf:type c` for a term `x` usable as a subject. -/
def typeTriple? (x : Term) (c : WfIri) : List Triple :=
  match x.toSubject? with
  | some s => [⟨s, rdfType, .iri c⟩]
  | none => []

/-- Append the triples of `new` that are not already in `g`, in order. -/
def addNew (g : Graph) (new : List Triple) : Graph :=
  new.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) g

/-! ## Phase 1: type and property closure (six INSERT operations) -/

/-- `INSERT { ?o rdf:type qb:Observation } WHERE { [] qb:observation ?o }`. -/
def p1ObservationOf (g : Graph) : List Triple :=
  (withPredicate g qbObservationP).flatMap fun t => typeTriple? t.o qbObservation

/-- `INSERT { ?o rdf:type qb:Observation . ?ds rdf:type qb:DataSet }
WHERE { ?o qb:dataSet ?ds }`. -/
def p1DataSetOf (g : Graph) : List Triple :=
  (withPredicate g qbDataSetP).flatMap fun t =>
    ⟨t.s, rdfType, .iri qbObservation⟩ :: typeTriple? t.o qbDataSet

/-- `INSERT { ?s rdf:type qb:Slice } WHERE { [] qb:slice ?s }`. -/
def p1SliceOf (g : Graph) : List Triple :=
  (withPredicate g qbSliceP).flatMap fun t => typeTriple? t.o qbSlice

/-- `INSERT { ?cs qb:componentProperty ?p . ?p rdf:type C } WHERE { ?cs P ?p }`
for `P` one of `qb:dimension`, `qb:measure`, `qb:attribute` and `C` its class. -/
def p1ComponentOf (g : Graph) (p : WfIri) (c : WfIri) : List Triple :=
  (withPredicate g p).flatMap fun t =>
    ⟨t.s, qbComponentProperty, t.o⟩ :: typeTriple? t.o c

/-- The six operations of phase 1, in the order of the request; each one reads
the graph that the operations before it wrote. -/
def phase1Ops : List (Graph → List Triple) :=
  [p1ObservationOf, p1DataSetOf, p1SliceOf,
   fun g => p1ComponentOf g qbDimension qbDimensionProperty,
   fun g => p1ComponentOf g qbMeasure qbMeasureProperty,
   fun g => p1ComponentOf g qbAttribute qbAttributeProperty]

/-! ## Phase 2: push down attachment levels (three INSERT operations) -/

/-- The component specifications of the structure of `dataset`
(`?dataset qb:structure [qb:component ?spec]`). -/
def specsOf (g : Graph) (dataset : Subject) : List Term :=
  (objectsOf g dataset qbStructure).flatMap fun dsd =>
    match dsd.toSubject? with
    | some d => objectsOf g d qbComponent
    | none => []

/-- The data sets of `g`: subjects of `qb:structure`. -/
def dataSetSubjects (g : Graph) : List Subject :=
  (withPredicate g qbStructure).map (·.s)

/-- The component properties `?comp` of `spec`, IRIs only (`?comp` is used in
predicate position). -/
def specComponents (g : Graph) (spec : Term) : List WfIri :=
  match spec.toSubject? with
  | some s => (objectsOf g s qbComponentProperty).filterMap fun
      | .iri i => some i
      | _ => none
  | none => []

/-- Dataset attachments: for a component attached at `qb:DataSet`, copy the
data set's values to each of its observations. -/
def p2DataSetOf (g : Graph) : List Triple :=
  (dataSetSubjects g).flatMap fun ds =>
    (specsOf g ds).flatMap fun spec =>
      match spec.toSubject? with
      | none => []
      | some sp =>
        if holds g sp qbComponentAttachment (.iri qbDataSet) then
          (specComponents g spec).flatMap fun comp =>
            (objectsOf g ds comp).flatMap fun v =>
              (withPredicate g qbDataSetP).filterMap fun t =>
                if t.o == ds.toTerm then some ⟨t.s, comp, v⟩ else none
        else []

/-- The slice pushdown shared by the second and third operations: for each
selected component, copy the slice's values to each observation of the slice. -/
def p2SliceWith (g : Graph) (select : Subject → WfIri → Bool) : List Triple :=
  (dataSetSubjects g).flatMap fun ds =>
    (specsOf g ds).flatMap fun spec =>
      match spec.toSubject? with
      | none => []
      | some sp =>
        (specComponents g spec).flatMap fun comp =>
          if select sp comp then
            (objectsOf g ds qbSliceP).flatMap fun sl =>
              match sl.toSubject? with
              | none => []
              | some sls =>
                (objectsOf g sls comp).flatMap fun v =>
                  (objectsOf g sls qbObservationP).filterMap fun o =>
                    o.toSubject?.map fun os => ⟨os, comp, v⟩
          else []

/-- Slice attachments (components attached at `qb:Slice`). -/
def p2SliceOf (g : Graph) : List Triple :=
  p2SliceWith g fun sp _ => holds g sp qbComponentAttachment (.iri qbSlice)

/-- Dimension values on slices (components typed `qb:DimensionProperty`). -/
def p2DimensionOf (g : Graph) : List Triple :=
  p2SliceWith g fun _ comp => holds g (.iri comp) rdfType (.iri qbDimensionProperty)

def phase2Ops : List (Graph → List Triple) := [p2DataSetOf, p2SliceOf, p2DimensionOf]

/-! ## The algorithm -/

/-- Apply update operations in order, each to the result of the one before. -/
def applyOps (g : Graph) (ops : List (Graph → List Triple)) : Graph :=
  ops.foldl (fun acc op => addNew acc (op acc)) g

def phase1 (g : Graph) : Graph := applyOps g phase1Ops
def phase2 (g : Graph) : Graph := applyOps g phase2Ops

/-- Section 10.1: phase 1, then phase 2. -/
def normalize (g : Graph) : Graph := phase2 (phase1 g)

/-! ## The same algorithm through the SPARQL 1.1 Update evaluator -/

/-- Run one vendored update request on the default graph `g`. -/
def runUpdateText (text : String) (g : Graph) : Except String Graph :=
  match SPARQL.parseSparqlUpdate text with
  | .error e => .error s!"update parse error: {repr e}"
  | .ok u =>
    match SPARQL.applyUpdate { default := g, named := [] } u with
    | .error e => .error s!"update error: {e}"
    | .ok ds => .ok ds.default

/-- Section 10.1 run by the SPARQL 1.1 Update evaluator. -/
def normalizeSparql (g : Graph) : Except String Graph := do
  let g1 ← runUpdateText normalizePhase1Text g
  runUpdateText normalizePhase2Text g1

/-- Two graphs have the same triples (as sets). -/
def sameTriples (a b : Graph) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

end L4Factoidal.DataCube.QB2014
