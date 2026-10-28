/-
L4Factoidal.DataCube.Constraints — the integrity constraints IC-0 to IC-21 of
the RDF Data Cube Recommendation (16 January 2014), section 11.1.

Section 11.1 gives each constraint as prose and, for IC-1 to IC-21, as a SPARQL
1.1 ASK query (IC-19: two queries; IC-20, IC-21: a query template instantiated
once for each IRI that an instantiation SELECT query finds). An ASK query that
returns true on a graph means that the graph violates the constraint. The
Recommendation says implementations "are free to use alternative query
formulations or alternative implementation techniques to perform equivalent
checks". This module has both:

* `checkSparql`: the vendored queries (`Queries.lean`), parsed and evaluated by
  this tree's SPARQL 1.1 engine (`SPARQL/Parser.lean`, `SPARQL/Query.lean`);
* `checkDirect`: one graph function per constraint, written from the query.

`tests/datacube/run.sh` runs both on every fixture and fails when they
disagree. The direct functions compare RDF terms by term equality; the queries
of IC-1, IC-2, IC-9, IC-12 and IC-16 use the SPARQL `=` and `!=` operators,
which compare literals by value. The fixtures use IRIs where those operators
apply, so the two agree there. A theorem that the two agree on every graph is
not stated yet: https://github.com/danbri/factoidal/issues/1165.

IC-0 (datatype consistency: the graph is consistent under D-entailment with a
datatype map that holds every datatype the graph uses) has no query. It is
`ic0Violated`, which reuses the D-entailment inconsistency test of
`RDF/Entailment.lean` (`hasIllFormedLiteral`, RDF 1.1 Semantics section 7.1).

Two properties of the Recommendation's queries that this module keeps as
written:

* The IC-20 and IC-21 templates do not join `?list` with the code list that
  has `$p` as its parent-child property. Each instantiated template checks
  every hierarchical code list against the one property `$p`.
* IC-17 counts rows (`COUNT(?obs2)`, `COUNT(?m)`), so a measure that two
  component specifications declare is counted twice.

One query is not used as written. The IC-17 query of the Recommendation ends
`HAVING (?count != ?numMeasures)`, where `?count` is the alias of a SELECT
expression. SPARQL 1.1 Query section 18.2.4.1 applies the HAVING filter to the
result of the aggregation before section 18.2.4.4 extends the solutions with
the SELECT expressions, so `?count` is unbound in the HAVING expression, the
expression is an error, and the query is false on every graph. `checkSparql`
evaluates `ic17Sparql11Text` (tests/datacube/local/ic-17-sparql11.rq), the
same query with `HAVING (COUNT(?obs2) != ?numMeasures)`, which is the check
that the prose of IC-17 states. `ic17Verbatim` evaluates the query as written;
`l4datacube` reports a STALE result (a failure) if it is ever true on a
fixture. Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.DataCube.Normalize
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.RDF.Entailment

namespace L4Factoidal.DataCube.QB2014

open L4Factoidal.RDF
open L4Factoidal.RDFS (rdfType rdfsRange)

/-! ## The constraint names -/

/-- The constraints this module checks, in the order of section 11.1. -/
def constraintNames : List String :=
  (List.range 22).map fun n => s!"IC-{n}"

/-! ## The SPARQL formulation -/

/-- Evaluate a vendored ASK query (with the section 11.1 prefix bindings). -/
def askText (g : Graph) (text : String) : Except String Bool :=
  match SPARQL.parseSparql (prefixesText ++ text) with
  | .error e => .error s!"query parse error: {repr e}"
  | .ok q => .ok (SPARQL.evalAsk SPARQL.emptyEnv { default := g, named := [] } q)

/-- The IRIs bound to `?p` by an instantiation SELECT query. -/
def selectIris (g : Graph) (text : String) : Except String (List String) :=
  match SPARQL.parseSparql (prefixesText ++ text) with
  | .error e => .error s!"query parse error: {repr e}"
  | .ok q =>
    let rows := (SPARQL.evalSelect SPARQL.emptyEnv { default := g, named := [] } q).2
    .ok ((rows.filterMap fun mu => match SPARQL.Binding.lookup "p" mu with
      | some (.iri i) => some i.val
      | _ => none).eraseDups)

/-- Section 11.1, IC-20 and IC-21: "the template is then instantiated by
replacing the string `$p` by the IRI found by the instantiation query". -/
def instantiate (template iri : String) : String :=
  template.replace "$p" iri

/-- A template constraint: violated when one of its instances is. -/
def templateViolated (g : Graph) (inst template : String) : Except String Bool := do
  let ps ← selectIris g inst
  ps.foldlM (fun acc p => if acc then pure true else askText g (instantiate template p)) false

/-- IC-0 by its definition (no query): some literal that the graph mentions is
ill-typed for its own datatype, D being the datatypes of the graph's literals. -/
def ic0Violated (g : Graph) : Bool :=
  let used := (mentionedLiterals g).map (·.datatype)
  hasIllFormedLiteral used.eraseDups g

/-- The verdict of every constraint by the Recommendation's queries:
`true` means violated. -/
def checkSparql (g : Graph) : List (String × Except String Bool) :=
  let fixed := fixedQueryTexts.map fun (n, text) => (n, askText g text)
  let get (n : String) : Except String Bool :=
    if n == "IC-17" then askText g ic17Sparql11Text else
    match fixed.find? (·.1 == n) with
    | some (_, r) => r
    | none => .error s!"no query {n}"
  let ic19 : Except String Bool := do
    let a ← get "IC-19A"
    let b ← get "IC-19B"
    pure (a || b)
  [("IC-0", .ok (ic0Violated g))] ++
  ((List.range 18).map fun k => (s!"IC-{k + 1}", get s!"IC-{k + 1}")) ++
  [("IC-19", ic19),
   ("IC-20", templateViolated g ic20InstantiationText ic20TemplateText),
   ("IC-21", templateViolated g ic21InstantiationText ic21TemplateText)]

/-- The IC-17 query of the Recommendation as written (see the module
comment: false on every graph under SPARQL 1.1). -/
def ic17Verbatim (g : Graph) : Except String Bool :=
  match fixedQueryTexts.find? (·.1 == "IC-17") with
  | some (_, text) => askText g text
  | none => .error "no query IC-17"

/-! ## The direct formulation -/

/-- `x rdf:type c`. -/
def typed (g : Graph) (x : Term) (c : WfIri) : Bool :=
  match x.toSubject? with
  | some s => holds g s rdfType (.iri c)
  | none => false

/-- The subjects typed `c`. -/
def instancesOf (g : Graph) (c : WfIri) : List Subject :=
  (withPredicate g rdfType).filterMap fun t =>
    if t.o == .iri c then some t.s else none

/-- `objectsOf` from a term (nothing from a literal or a triple term). -/
def objs (g : Graph) (x : Term) (p : WfIri) : List Term :=
  match x.toSubject? with
  | some s => objectsOf g s p
  | none => []

/-- The objects of a sequence path `p1/p2/…` from `x`, with the multiplicity
of the join that SPARQL 1.1 section 18.4 makes of it. -/
def pathObjs (g : Graph) (x : Term) (ps : List WfIri) : List Term :=
  ps.foldl (fun xs p => xs.flatMap fun y => objs g y p) [x]

/-- `?x ?p []` for a term `?p`: false when `?p` is not an IRI (no triple has
such a predicate). -/
def hasValue (g : Graph) (x : Term) (p : Term) : Bool :=
  match p with
  | .iri i => !(objs g x i).isEmpty
  | _ => false

/-- The nodes reachable from `starts` by zero or more `p` links (or inverse
`p` links when `inverse`), a breadth-first loop bounded by the number of
triples plus one. -/
def reachStar (g : Graph) (p : WfIri) (inverse : Bool) (starts : List Term) : List Term :=
  let step (x : Term) : List Term :=
    if inverse then
      (withPredicate g p).filterMap fun t => if t.o == x then some t.s.toTerm else none
    else objs g x p
  let rec go : Nat → List Term → List Term → List Term
    | 0, seen, _ => seen
    | _ + 1, seen, [] => seen
    | n + 1, seen, x :: rest =>
      let new := (step x).filter fun y => !seen.contains y
      go n (seen ++ new.eraseDups) (rest ++ new.eraseDups)
  go ((g.length + 1) * (g.length + 1)) starts.eraseDups starts.eraseDups

/-- The nodes reachable by one or more `p` links. -/
def reachPlus (g : Graph) (p : WfIri) (start : Term) : List Term :=
  reachStar g p false (objs g start p)

/-- Literal `"b"^^xsd:boolean`. -/
def boolLit (b : Bool) : Term :=
  if b then .literal ⟨⟨"true", xsdBoolean, none, none⟩, rfl⟩
  else .literal ⟨⟨"false", xsdBoolean, none, none⟩, rfl⟩

/-- "has not exactly one value" (IC-1, IC-2, IC-9). -/
def notExactlyOne (vs : List Term) : Bool := vs.eraseDups.length != 1

def ic1 (g : Graph) : Bool :=
  (instancesOf g qbObservation).any fun o => notExactlyOne (objectsOf g o qbDataSetP)

def ic2 (g : Graph) : Bool :=
  (instancesOf g qbDataSet).any fun d => notExactlyOne (objectsOf g d qbStructure)

def ic3 (g : Graph) : Bool :=
  (instancesOf g qbDataStructureDefinition).any fun d =>
    !((pathObjs g d.toTerm [qbComponent, qbComponentProperty]).any
        fun m => typed g m qbMeasureProperty)

def ic4 (g : Graph) : Bool :=
  (instancesOf g qbDimensionProperty).any fun d => (objectsOf g d rdfsRange).isEmpty

def ic5 (g : Graph) : Bool :=
  (instancesOf g qbDimensionProperty).any fun d =>
    holds g d rdfsRange (.iri skosConcept) && (objectsOf g d qbCodeList).isEmpty

def ic6 (g : Graph) : Bool :=
  (withPredicate g qbComponent).any fun t =>
    let spec := t.o
    (objs g spec qbComponentRequired).contains (boolLit false) &&
    (objs g spec qbComponentProperty).any fun c => !typed g c qbAttributeProperty

def ic7 (g : Graph) : Bool :=
  (instancesOf g qbSliceKey).any fun k =>
    !((withPredicate g qbSliceKeyP).any fun t =>
        t.o == k.toTerm && typed g t.s.toTerm qbDataStructureDefinition)

def ic8 (g : Graph) : Bool :=
  (instancesOf g qbSliceKey).any fun k =>
    (objectsOf g k qbComponentProperty).any fun prop =>
      (withPredicate g qbSliceKeyP).any fun t =>
        t.o == k.toTerm &&
        !((objectsOf g t.s qbComponent).any fun c =>
            (objs g c qbComponentProperty).contains prop)

def ic9 (g : Graph) : Bool :=
  (instancesOf g qbSlice).any fun s => notExactlyOne (objectsOf g s qbSliceStructure)

def ic10 (g : Graph) : Bool :=
  (withPredicate g qbSliceStructure).any fun t =>
    (objs g t.o qbComponentProperty).any fun dim => !hasValue g t.s.toTerm dim

/-- The observations: subjects of `qb:dataSet`. -/
def observationTerms (g : Graph) : List Term :=
  ((withPredicate g qbDataSetP).map (·.s.toTerm)).eraseDups

/-- `?obs qb:dataSet/qb:structure/qb:component/qb:componentProperty ?dim`. -/
def obsComponents (g : Graph) (obs : Term) : List Term :=
  pathObjs g obs [qbDataSetP, qbStructure, qbComponent, qbComponentProperty]

def ic11 (g : Graph) : Bool :=
  (observationTerms g).any fun obs =>
    (obsComponents g obs).any fun dim =>
      typed g dim qbDimensionProperty && !hasValue g obs dim

/-- The dimensions of a data set (`qb:structure/qb:component/qb:componentProperty`,
typed `qb:DimensionProperty`), IRIs only. -/
def dataSetDimensions (g : Graph) (ds : Term) : List WfIri :=
  (pathObjs g ds [qbStructure, qbComponent, qbComponentProperty]).filterMap fun
    | .iri i => if typed g (.iri i) qbDimensionProperty then some i else none
    | _ => none

def ic12 (g : Graph) : Bool :=
  (withPredicate g qbDataSetP).any fun t1 =>
    (withPredicate g qbDataSetP).any fun t2 =>
      t1.o == t2.o && t1.s != t2.s &&
      let rows := (dataSetDimensions g t1.o).flatMap fun d =>
        (objectsOf g t1.s d).flatMap fun v1 =>
          (objectsOf g t2.s d).map fun v2 => v1 == v2
      !rows.isEmpty && rows.all id

def ic13 (g : Graph) : Bool :=
  (observationTerms g).any fun obs =>
    (pathObjs g obs [qbDataSetP, qbStructure, qbComponent]).any fun comp =>
      (objs g comp qbComponentRequired).contains (boolLit true) &&
      (objs g comp qbComponentProperty).any fun attr => !hasValue g obs attr

/-- The DSD uses the measure dimension. -/
def usesMeasureType (g : Graph) (dsd : Term) : Bool :=
  (pathObjs g dsd [qbComponent, qbComponentProperty]).contains (.iri qbMeasureType)

def ic14 (g : Graph) : Bool :=
  (observationTerms g).any fun obs =>
    (pathObjs g obs [qbDataSetP, qbStructure]).any fun dsd =>
      !usesMeasureType g dsd &&
      (pathObjs g dsd [qbComponent, qbComponentProperty]).any fun m =>
        typed g m qbMeasureProperty && !hasValue g obs m

def ic15 (g : Graph) : Bool :=
  (observationTerms g).any fun obs =>
    (pathObjs g obs [qbDataSetP, qbStructure]).any fun dsd =>
      usesMeasureType g dsd &&
      (objs g obs qbMeasureType).any fun m => !hasValue g obs m

/-- The predicates of the triples whose subject is `x`. -/
def predicatesOf (g : Graph) (x : Term) : List WfIri :=
  match x.toSubject? with
  | some s => (g.filter (·.s == s)).map (·.p)
  | none => []

def ic16 (g : Graph) : Bool :=
  (observationTerms g).any fun obs =>
    (pathObjs g obs [qbDataSetP, qbStructure]).any fun dsd =>
      usesMeasureType g dsd &&
      (objs g obs qbMeasureType).any fun m =>
        (predicatesOf g obs).any fun om =>
          (pathObjs g dsd [qbComponent, qbComponentProperty]).contains (.iri om) &&
          typed g (.iri om) qbMeasureProperty && Term.iri om != m

/-- IC-17's inner sub-select: the number of measure rows of a DSD. -/
def measureCount (g : Graph) (dsd : Term) : Nat :=
  ((pathObjs g dsd [qbComponent, qbComponentProperty]).filter
    fun m => typed g m qbMeasureProperty).length

/-- IC-17's FILTER NOT EXISTS: some non-measure dimension has different values
on the two observations. -/
def differOnDimension (g : Graph) (dsd o1 o2 : Term) : Bool :=
  (pathObjs g dsd [qbComponent, qbComponentProperty]).any fun dim =>
    dim != .iri qbMeasureType && typed g dim qbDimensionProperty &&
    match dim with
    | .iri d => (objs g o1 d).any fun v1 => (objs g o2 d).any fun v2 => v1 != v2
    | _ => false

def ic17 (g : Graph) : Bool :=
  let dsds := ((withPredicate g qbComponent).map (·.s.toTerm)).eraseDups
  -- One row of the outer pattern per (obs1, dsd, dataset, m1, obs2, m2).
  let keys : List (Term × Nat) := (observationTerms g).flatMap fun o1 =>
    (pathObjs g o1 [qbDataSetP, qbStructure]).flatMap fun dsd =>
      if dsds.contains dsd && measureCount g dsd > 0 then
        (objs g o1 qbDataSetP).flatMap fun ds =>
          (objs g o1 qbMeasureType).flatMap fun _ =>
            (withPredicate g qbDataSetP).flatMap fun t2 =>
              if t2.o == ds then
                (objs g t2.s.toTerm qbMeasureType).filterMap fun _ =>
                  if differOnDimension g dsd o1 t2.s.toTerm then none
                  else some (o1, measureCount g dsd)
              else []
      else []
  keys.eraseDups.any fun k => (keys.filter (· == k)).length != k.2

def ic18 (g : Graph) : Bool :=
  (withPredicate g qbSliceP).any fun t =>
    (objs g t.o qbObservationP).any fun obs =>
      !(objs g obs qbDataSetP).contains t.s.toTerm

/-- IC-19 to IC-21 share this pattern: an observation's value `?v` of a
dimension `?dim` with code list `?list` of class `cls`. -/
def codedValues (g : Graph) (cls : WfIri) : List (Term × Term) :=
  (observationTerms g).flatMap fun obs =>
    (obsComponents g obs).flatMap fun dim =>
      if typed g dim qbDimensionProperty then
        (objs g dim qbCodeList).flatMap fun list =>
          if typed g list cls then
            match dim with
            | .iri d => (objs g obs d).map fun v => (list, v)
            | _ => []
          else []
      else []

def ic19 (g : Graph) : Bool :=
  (codedValues g skosConceptScheme).any (fun (list, v) =>
    !(typed g v skosConcept && (objs g v skosInScheme).contains list)) ||
  (codedValues g skosCollection).any (fun (list, v) =>
    !(typed g v skosConcept && (reachPlus g skosMember list).contains v))

/-- One instantiated IC-20 or IC-21 template. -/
def hierarchyViolated (g : Graph) (p : WfIri) (inverse : Bool) : Bool :=
  (codedValues g qbHierarchicalCodeList).any fun (list, v) =>
    !(reachStar g p inverse (objs g list qbHierarchyRoot)).contains v

def ic20 (g : Graph) : Bool :=
  let ps := ((instancesOf g qbHierarchicalCodeList).flatMap fun h =>
    (objectsOf g h qbParentChildProperty).filterMap fun
      | .iri i => some i
      | _ => none).eraseDups
  ps.any fun p => hierarchyViolated g p false

def ic21 (g : Graph) : Bool :=
  let ps := ((instancesOf g qbHierarchicalCodeList).flatMap fun h =>
    (objectsOf g h qbParentChildProperty).flatMap fun
      | .bnode b => (objectsOf g (.bnode b) owlInverseOf).filterMap fun
          | .iri i => some i
          | _ => none
      | _ => []).eraseDups
  ps.any fun p => hierarchyViolated g p true

/-- The verdict of every constraint by the direct functions: `true` means
violated. -/
def checkDirect (g : Graph) : List (String × Bool) :=
  [("IC-0", ic0Violated g), ("IC-1", ic1 g), ("IC-2", ic2 g), ("IC-3", ic3 g),
   ("IC-4", ic4 g), ("IC-5", ic5 g), ("IC-6", ic6 g), ("IC-7", ic7 g),
   ("IC-8", ic8 g), ("IC-9", ic9 g), ("IC-10", ic10 g), ("IC-11", ic11 g),
   ("IC-12", ic12 g), ("IC-13", ic13 g), ("IC-14", ic14 g), ("IC-15", ic15 g),
   ("IC-16", ic16 g), ("IC-17", ic17 g), ("IC-18", ic18 g), ("IC-19", ic19 g),
   ("IC-20", ic20 g), ("IC-21", ic21 g)]

/-- Section 11: "A well-formed RDF Data Cube is an RDF graph … for which each
of the integrity checks defined here passes"; a well-formed abbreviated cube is
one whose normalization is well-formed. -/
def wellFormedDirect (g : Graph) : Bool :=
  (checkDirect (normalize g)).all fun (_, v) => !v

end L4Factoidal.DataCube.QB2014
