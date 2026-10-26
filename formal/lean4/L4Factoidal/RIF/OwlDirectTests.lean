/-
L4Factoidal.RIF.OwlDirectTests — build-time checks for RIF-OWL Direct
entailment (`RIF/OwlDirect.lean`, RIF-RDF-OWL §4.2.2 and §9.2).

Every behaviour is pinned in BOTH directions: an implementation that
answered `holds` for every question, or `doesNotHold` for every
question, fails at least one guard below.
-/
import L4Factoidal.RIF.OwlDirect
import L4Factoidal.RIF.Ps
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.RIF.OwlDirect

open L4Factoidal.RDF
open L4Factoidal.RIF
open L4Factoidal.Syntax

private def pfx : String :=
  "@prefix ex: <http://example.org/ex#> . " ++
  "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . " ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . " ++
  "@prefix owl: <http://www.w3.org/2002/07/owl#> . " ++
  "@prefix dc: <http://purl.org/dc/elements/1.1/> . "

private def psPrologue : String :=
  "Prefix(ex <http://example.org/ex#>) " ++
  "Prefix(rdf <http://www.w3.org/1999/02/22-rdf-syntax-ns#>) " ++
  "Prefix(owl <http://www.w3.org/2002/07/owl#>) " ++
  "Prefix(dc <http://purl.org/dc/elements/1.1/>) "

/-- Verdict for a Turtle ontology, a RIF-PS group body and a goal. -/
private def verdictOf (ttl : String) (group : String) (goal : String) : Verdict :=
  match parseTurtle (pfx ++ ttl) none, parseDocument ("Document(" ++ psPrologue ++ "Group(" ++ group ++ "))") with
  | .ok g, .ok d =>
      (match parseFormulaText { prefixes := d.prefixes } goal with
       | .ok f    => entailsOwlDirect d.rules g f 24
       | .error _ => .undecided "test goal did not parse")
  | _, _ => .undecided "test input did not parse"

private def isUndecided : Verdict → Bool
  | .undecided _ => true
  | _ => false

/-! ## Annotations carry no Direct-Semantics content

`Non-Annotation_Entailment`: `dc:title` is declared an
`owl:OntologyProperty` (an annotation property, Mapping Table 5), so
`ex:o dc:title "T"` is an annotation and the frame `ex:o[dc:title -> "T"]`
is not part of the combination. The same triple on a DECLARED data
property is a DataPropertyAssertion and IS. -/

private def annRule : String := "Forall ?x ?y ( ?x[ex:hasTitle -> ?y] :- ?x[dc:title -> ?y] )"

#guard verdictOf
  "ex:o rdf:type owl:Ontology . ex:o dc:title \"T\" . dc:title rdf:type owl:OntologyProperty ."
  annRule "ex:o[ex:hasTitle -> \"T\"]" == .doesNotHold

#guard verdictOf
  "ex:o rdf:type owl:Ontology . ex:i dc:title \"T\" . dc:title rdf:type owl:DatatypeProperty ."
  annRule "ex:i[ex:hasTitle -> \"T\"]" == .holds

-- A built-in annotation property needs no declaration.
#guard verdictOf "ex:i rdfs:label \"L\" ."
  "Forall ?x ?y ( ?x[ex:named -> ?y] :- ?x[rdfs:label -> ?y] )" "ex:i[ex:named -> \"L\"]"
  == .doesNotHold

/-! ## A declaration is not a class assertion

Under the RDF-Based reading `ex:C rdf:type owl:Class` is a triple and
so a frame. Under the Direct Semantics it only declares `ex:C`. -/

#guard verdictOf "ex:C rdf:type owl:Class ." "" "ex:C[rdf:type -> owl:Class]" == .doesNotHold
#guard verdictOf "ex:C rdf:type owl:Class . ex:a rdf:type ex:C ." "" "ex:a[rdf:type -> ex:C]"
  == .holds
-- RIF membership `a # C` is the same question (§9.2.2.2, R').
#guard verdictOf "ex:C rdf:type owl:Class . ex:a rdf:type ex:C ." "" "ex:a # ex:C" == .holds

/-! ## SubClassOf feeds the rules (`Modeling_Brain_Anatomy`) -/

private def brainOnto : String :=
  "ex:Gyrus rdf:type owl:Class . ex:MAE rdf:type owl:Class . ex:GC rdf:type owl:Class . " ++
  "ex:bounded rdf:type owl:ObjectProperty . " ++
  "ex:g1 rdf:type ex:Gyrus . ex:g2 rdf:type ex:Gyrus . ex:op rdf:type ex:GC . " ++
  "ex:g1 ex:bounded ex:op . ex:g2 ex:bounded ex:op . "

private def brainRule : String :=
  "Forall ?X ?Y ?Z ( ?X[ex:connected -> ?Y] :- And( ?X[ex:bounded -> ?Z] ?Y[ex:bounded -> ?Z] " ++
  "?X[rdf:type -> ex:MAE] ?Y[rdf:type -> ex:MAE] ?Z[rdf:type -> ex:GC] ) )"

#guard verdictOf (brainOnto ++ "ex:Gyrus rdfs:subClassOf ex:MAE .") brainRule
  "ex:g1[ex:connected -> ex:g2]" == .holds
#guard verdictOf brainOnto brainRule "ex:g1[ex:connected -> ex:g2]" == .doesNotHold
-- EquivalentClasses works in both directions.
#guard verdictOf (brainOnto ++ "ex:MAE owl:equivalentClass ex:Gyrus .") brainRule
  "ex:g1[ex:connected -> ex:g2]" == .holds

/-! ## An axiom outside the embedded subset blocks only `doesNotHold`

A union in a range (`Modeling_Brain_Anatomy` has one) is not OWL 2 RL
in superclass position. Ignoring it keeps every `holds` sound and
makes every `doesNotHold` a guess, so the second answer is withheld. -/

private def unionRange : String :=
  "ex:bounded rdfs:range [ rdf:type owl:Class ; owl:unionOf ( ex:GC ex:MAE ) ] . "

#guard verdictOf (brainOnto ++ unionRange ++ "ex:Gyrus rdfs:subClassOf ex:MAE .") brainRule
  "ex:g1[ex:connected -> ex:g2]" == .holds
#guard isUndecided (verdictOf (brainOnto ++ unionRange) brainRule "ex:g1[ex:connected -> ex:g2]")
-- A functional property needs equality, which RIF Core lacks.
#guard isUndecided (verdictOf (brainOnto ++ "ex:bounded rdf:type owl:FunctionalProperty .")
  brainRule "ex:g1[ex:connected -> ex:g2]")
-- An undeclared predicate makes the graph something other than an OWL 2 DL ontology.
#guard isUndecided (verdictOf "ex:a ex:undeclared ex:b ." "" "ex:a[ex:other -> ex:b]")

/-! ## Property axioms -/

#guard verdictOf "ex:p rdf:type owl:ObjectProperty , owl:SymmetricProperty . ex:a ex:p ex:b ."
  "" "ex:b[ex:p -> ex:a]" == .holds
#guard verdictOf "ex:p rdf:type owl:ObjectProperty . ex:a ex:p ex:b ."
  "" "ex:b[ex:p -> ex:a]" == .doesNotHold
#guard verdictOf
  "ex:p rdf:type owl:ObjectProperty , owl:TransitiveProperty . ex:a ex:p ex:b . ex:b ex:p ex:c ."
  "" "ex:a[ex:p -> ex:c]" == .holds
#guard verdictOf
  "ex:p rdf:type owl:ObjectProperty . ex:q rdf:type owl:ObjectProperty . ex:p owl:inverseOf ex:q . ex:a ex:p ex:b ."
  "" "ex:b[ex:q -> ex:a]" == .holds
#guard verdictOf
  "ex:p rdf:type owl:ObjectProperty . ex:C rdf:type owl:Class . ex:p rdfs:domain ex:C . ex:a ex:p ex:b ."
  "" "ex:a[rdf:type -> ex:C]" == .holds
#guard verdictOf
  "ex:p rdf:type owl:ObjectProperty . ex:C rdf:type owl:Class . ex:p rdfs:range ex:C . ex:a ex:p ex:b ."
  "" "ex:a[rdf:type -> ex:C]" == .doesNotHold
#guard verdictOf
  "ex:p rdf:type owl:ObjectProperty . ex:q rdf:type owl:ObjectProperty . ex:p rdfs:subPropertyOf ex:q ."
  "ex:a[ex:p -> ex:b]" "ex:a[ex:q -> ex:b]" == .holds

/-! ## Inconsistency entails everything (ROWL-Direct (i), (ii), (xi))

`OWL_Combination_Vocabulary_Separation_Inconsistency_2`: an object
property valued by a literal puts a data value in `owl:Thing`. The
same fact on a property the ontology does NOT declare is consistent. -/

#guard verdictOf "ex:hasChild rdf:type owl:ObjectProperty ." "ex:i[ex:hasChild -> \"John\"]"
  "\"a\" = \"b\"" == .holds
#guard verdictOf "ex:C rdf:type owl:Class ." "ex:i[ex:hasChild -> \"John\"]"
  "\"a\" = \"b\"" == .doesNotHold
-- `..._Inconsistency_1`: an individual typed as a datatype.
#guard verdictOf "ex:C rdf:type owl:Class . ex:i rdf:type ex:C ."
  "ex:i[rdf:type -> <http://www.w3.org/2001/XMLSchema#string>]" "\"a\" = \"b\"" == .holds
-- Disjoint classes with a common member.
#guard verdictOf
  "ex:A rdf:type owl:Class . ex:B rdf:type owl:Class . ex:A owl:disjointWith ex:B . ex:i rdf:type ex:A ."
  "ex:i[rdf:type -> ex:B]" "ex:i[ex:anything -> ex:z]" == .holds
#guard verdictOf
  "ex:A rdf:type owl:Class . ex:B rdf:type owl:Class . ex:A owl:disjointWith ex:B . ex:i rdf:type ex:A ."
  "ex:j[rdf:type -> ex:B]" "ex:i[ex:anything -> ex:z]" == .doesNotHold
-- owl:Nothing is empty.
#guard verdictOf "ex:i rdf:type owl:Nothing ." "" "ex:i[ex:anything -> ex:z]" == .holds

/-! ## Only DL-document formulas have an OWL-Direct reading (§4.1, §5.2) -/

-- A variable in property position is not a DL-frame.
#guard isUndecided (verdictOf "ex:C rdf:type owl:Class ."
  "Forall ?x ?p ?y ( ?x[ex:q -> ?y] :- ?x[?p -> ?y] )" "ex:a[ex:q -> ex:b]")
-- A variable class after rdf:type is not a DL-frame either.
#guard isUndecided (verdictOf "ex:C rdf:type owl:Class ."
  "Forall ?x ?c ( ?x[ex:q -> ?c] :- ?x[rdf:type -> ?c] )" "ex:a[ex:q -> ex:b]")

/-! ## A datatype used as a class withholds `doesNotHold`

ROWL-Direct (viii)/(ix) are implemented for a literal's own datatype
only, so a rule that reads `?x[rdf:type -> xs:decimal]` could miss an
`xs:integer` literal. -/

#guard isUndecided (verdictOf "ex:C rdf:type owl:Class ."
  "Forall ?x ( ?x[ex:q -> ex:b] :- ?x[rdf:type -> <http://www.w3.org/2001/XMLSchema#decimal>] )"
  "ex:a[ex:q -> ex:b]")

end L4Factoidal.RIF.OwlDirect
