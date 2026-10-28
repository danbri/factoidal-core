/-
L4Factoidal.SPARQLRL.OwlRl — the OWL 2 RL/RDF rule table as one SPARQL-RL
rule set.

Source of the rules: OWL 2 Web Ontology Language Profiles (Second Edition),
§4.3 "Reasoning in OWL 2 RL and RDF Graphs using Rules",
https://www.w3.org/TR/owl2-profiles/#Reasoning_in_OWL_2_RL_and_RDF_Graphs_using_Rules
(Tables 4 to 9). Source of the language: the SPARQL 1.2 RL editor's draft,
https://w3c.github.io/data-shapes/sparql12-rl/ (vendored at
`third_party/testing/sparql-rl/spec/`). Requested on
https://github.com/danbri/factoidal-core/pull/163.

Each rule carries its table id in a `#` comment. `OwlRlDiff.lean` compares
`RuleSet.infer` of this rule set with the Lean OWL 2 RL closure
(`OWL/RLClosureIndexed.lean`); `OwlRlTests.lean` holds the `#guard`s.

## Decisions

1. **Every derived triple is an RDF triple.** The table is written over
   generalized triples (a literal may stand in subject position). SPARQL-RL
   keeps such triples in the evaluation graph (`SPARQLRL/Eval.lean`,
   "Generalized triples"), where later rules can match them. The Lean
   closure (`OWL/RLRules.lean`, whose `Subject` has no literal case) cannot
   hold them. So each rule whose head puts a variable from an object
   position into a subject position has the filter
   `FILTER(isIRI(?v) || isBlank(?v))`, and each rule whose head puts such a
   variable into the predicate position has `FILTER(isIRI(?v))`. With these
   filters the evaluation graph holds RDF triples only, and the rule set
   derives what `OWL.RL.Derives` derives for these rows.
2. **RDF collections** (`LIST[...]` in the table). SPARQL-RL has the path
   operators `/` and `^`, and no `*`. Two helper relations walk a list with
   recursive rules, in the helper namespace `h:` (`urn:x-factoidal:owlrl#`):
   * `?l h:member ?e`: `?e` is the `rdf:first` of a cell reachable from the
     cell `?l` through `rdf:rest` (cls-int2, cls-uni, cls-oo, scm-int,
     scm-uni);
   * `?l h:allTypes ?y`: `?y` has `rdf:type` every member of the
     well-formed list from cell `?l` to `rdf:nil` (cls-int1);
   * `?l h:cell ?c`: `?c` is a cell of the list headed by `?l`, for the
     heads of `owl:members` and `owl:distinctMembers` (the clash rows
     eq-diff2, eq-diff3, prp-adp, cax-adc).
   prp-spo2 and prp-key need the whole sequence and a relation of three
   places (the cell, and two individuals) that a SPARQL-RL head cannot
   build without a blank node or a triple term with a variable, and both of
   those make a rule run-once (draft "Run-once rule"), so it cannot recurse.
   These two rows are therefore unrolled, one rule per list length from 1 to
   `unrollMax` (8). A chain or a key of more members is not handled: this
   is a stated shortfall (`OwlRlTests.lean`, an expected failure).
3. **Clash rows** (no consequent). SPARQL-RL has no way to report a
   contradiction, so each clash row is a rule that adds the marker triple
   `h:result h:clash "<table id>"`. `owlRlClashes` reads the markers.
4. **Helper triples are in the inference graph** that `RuleSet.infer`
   gives (every `h:` triple and every triple that a rule with a variable
   predicate copied from one). `owlRlEntailments` removes every triple that
   mentions an `h:` IRI.
5. **Datatype rows (Table 8: dt-type1, dt-type2, dt-eq, dt-diff,
   dt-not-type) are not rules here.** dt-type2, dt-eq and dt-diff conclude
   triples with a literal subject, which decision 1 excludes and which the
   Lean closure cannot hold. dt-type1 and dt-not-type depend on the
   datatype map (the supported datatypes, their lexical spaces), which the
   table leaves to the implementation; the SPARQL-RL function library has no
   lexical-space test. `OWL/RLRules.lean` omits these rows for the same
   reasons.
6. **cls-maxqc3 and cls-maxqc4** are rules here (section `owlRlMaxqc`). The
   Lean closure does not have them (`OWL/RLClosure.lean` header), so the
   differential compares `owlRlCommonText` (every row except these two) with
   the Lean table rows.
-/
import L4Factoidal.SPARQLRL.Text

namespace L4Factoidal.SPARQLRL.OwlRl

open L4Factoidal.RDF
open L4Factoidal.SPARQLRL

/-- The helper namespace. -/
def helperNs : String := "urn:x-factoidal:owlrl#"

def prefixes : String := "
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
PREFIX h: <urn:x-factoidal:owlrl#>
"

/-! ## Table 4, the semantics of equality -/

def eqRules : String := "
# eq-ref (three rules: subject, predicate, object)
RULE { ?s owl:sameAs ?s } WHERE { ?s ?p ?o }
RULE { ?p owl:sameAs ?p } WHERE { ?s ?p ?o }
RULE { ?o owl:sameAs ?o } WHERE { ?s ?p ?o FILTER(isIRI(?o) || isBlank(?o)) }
# eq-sym
RULE { ?y owl:sameAs ?x } WHERE { ?x owl:sameAs ?y FILTER(isIRI(?y) || isBlank(?y)) }
# eq-trans
RULE { ?x owl:sameAs ?z } WHERE { ?x owl:sameAs ?y . ?y owl:sameAs ?z }
# eq-rep-s
RULE { ?s2 ?p ?o } WHERE { ?s owl:sameAs ?s2 FILTER(isIRI(?s2) || isBlank(?s2)) ?s ?p ?o }
# eq-rep-p
RULE { ?s ?p2 ?o } WHERE { ?p owl:sameAs ?p2 FILTER(isIRI(?p) && isIRI(?p2)) ?s ?p ?o }
# eq-rep-o
RULE { ?s ?p ?o2 } WHERE { ?o owl:sameAs ?o2 . ?s ?p ?o }
# eq-diff1 (clash)
RULE { h:result h:clash \"eq-diff1\" } WHERE { ?x owl:sameAs ?y . ?x owl:differentFrom ?y }
# eq-diff2 (clash)
RULE { h:result h:clash \"eq-diff2\" } WHERE {
  ?x rdf:type owl:AllDifferent ; owl:members ?l .
  ?l h:cell ?ci . ?l h:cell ?cj FILTER(!sameTerm(?ci, ?cj))
  ?ci rdf:first ?zi . ?cj rdf:first ?zj FILTER(!sameTerm(?zi, ?zj))
  ?zi owl:sameAs ?zj }
# eq-diff3 (clash)
RULE { h:result h:clash \"eq-diff3\" } WHERE {
  ?x rdf:type owl:AllDifferent ; owl:distinctMembers ?l .
  ?l h:cell ?ci . ?l h:cell ?cj FILTER(!sameTerm(?ci, ?cj))
  ?ci rdf:first ?zi . ?cj rdf:first ?zj FILTER(!sameTerm(?zi, ?zj))
  ?zi owl:sameAs ?zj }
"

/-! ## Table 5, the semantics of axioms about properties -/

def prpRules : String := "
# prp-ap
DATA {
  rdfs:label rdf:type owl:AnnotationProperty .
  rdfs:comment rdf:type owl:AnnotationProperty .
  rdfs:seeAlso rdf:type owl:AnnotationProperty .
  rdfs:isDefinedBy rdf:type owl:AnnotationProperty .
  owl:deprecated rdf:type owl:AnnotationProperty .
  owl:versionInfo rdf:type owl:AnnotationProperty .
  owl:priorVersion rdf:type owl:AnnotationProperty .
  owl:backwardCompatibleWith rdf:type owl:AnnotationProperty .
  owl:incompatibleWith rdf:type owl:AnnotationProperty .
}
# prp-dom
RULE { ?x rdf:type ?c } WHERE { ?p rdfs:domain ?c . ?x ?p ?y }
# prp-rng
RULE { ?y rdf:type ?c } WHERE { ?p rdfs:range ?c . ?x ?p ?y FILTER(isIRI(?y) || isBlank(?y)) }
# prp-fp
RULE { ?y1 owl:sameAs ?y2 } WHERE {
  ?p rdf:type owl:FunctionalProperty . ?x ?p ?y1 FILTER(isIRI(?y1) || isBlank(?y1)) ?x ?p ?y2 }
# prp-ifp
RULE { ?x1 owl:sameAs ?x2 } WHERE {
  ?p rdf:type owl:InverseFunctionalProperty . ?x1 ?p ?y . ?x2 ?p ?y }
# prp-irp (clash)
RULE { h:result h:clash \"prp-irp\" } WHERE { ?p rdf:type owl:IrreflexiveProperty . ?x ?p ?x }
# prp-symp
RULE { ?y ?p ?x } WHERE {
  ?p rdf:type owl:SymmetricProperty . ?x ?p ?y FILTER(isIRI(?y) || isBlank(?y)) }
# prp-asyp (clash)
RULE { h:result h:clash \"prp-asyp\" } WHERE {
  ?p rdf:type owl:AsymmetricProperty . ?x ?p ?y . ?y ?p ?x }
# prp-trp
RULE { ?x ?p ?z } WHERE { ?p rdf:type owl:TransitiveProperty . ?x ?p ?y . ?y ?p ?z }
# prp-spo1
RULE { ?x ?p2 ?y } WHERE { ?p1 rdfs:subPropertyOf ?p2 FILTER(isIRI(?p2)) ?x ?p1 ?y }
# prp-spo2: see `chainRule`, one rule per chain length
# prp-eqp1
RULE { ?x ?p2 ?y } WHERE { ?p1 owl:equivalentProperty ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p1 ?y }
# prp-eqp2
RULE { ?x ?p1 ?y } WHERE { ?p1 owl:equivalentProperty ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p2 ?y }
# prp-pdw (clash)
RULE { h:result h:clash \"prp-pdw\" } WHERE {
  ?p1 owl:propertyDisjointWith ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p1 ?y . ?x ?p2 ?y }
# prp-adp (clash)
RULE { h:result h:clash \"prp-adp\" } WHERE {
  ?x rdf:type owl:AllDisjointProperties ; owl:members ?l .
  ?l h:cell ?ci . ?l h:cell ?cj FILTER(!sameTerm(?ci, ?cj))
  ?ci rdf:first ?p1 . ?cj rdf:first ?p2 FILTER(!sameTerm(?p1, ?p2) && isIRI(?p1) && isIRI(?p2))
  ?u ?p1 ?w . ?u ?p2 ?w }
# prp-inv1
RULE { ?y ?p2 ?x } WHERE {
  ?p1 owl:inverseOf ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p1 ?y FILTER(isIRI(?y) || isBlank(?y)) }
# prp-inv2
RULE { ?y ?p1 ?x } WHERE {
  ?p1 owl:inverseOf ?p2 FILTER(isIRI(?p1) && isIRI(?p2)) ?x ?p2 ?y FILTER(isIRI(?y) || isBlank(?y)) }
# prp-key: see `keyRule`, one rule per key length
# prp-npa1 (clash)
RULE { h:result h:clash \"prp-npa1\" } WHERE {
  ?x owl:sourceIndividual ?i1 ; owl:assertionProperty ?p ; owl:targetIndividual ?i2 . ?i1 ?p ?i2 }
# prp-npa2 (clash)
RULE { h:result h:clash \"prp-npa2\" } WHERE {
  ?x owl:sourceIndividual ?i ; owl:assertionProperty ?p ; owl:targetValue ?lt . ?i ?p ?lt }
"

/-! ## Table 6, the semantics of classes -/

def clsRules : String := "
# cls-thing, cls-nothing1
DATA { owl:Thing rdf:type owl:Class . owl:Nothing rdf:type owl:Class . }
# cls-nothing2 (clash)
RULE { h:result h:clash \"cls-nothing2\" } WHERE { ?x rdf:type owl:Nothing }
# cls-int1
RULE { ?y rdf:type ?c } WHERE { ?c owl:intersectionOf ?l . ?l h:allTypes ?y }
# cls-int2
RULE { ?y rdf:type ?ci } WHERE { ?c owl:intersectionOf ?l . ?l h:member ?ci . ?y rdf:type ?c }
# cls-uni
RULE { ?y rdf:type ?c } WHERE { ?c owl:unionOf ?l . ?l h:member ?ci . ?y rdf:type ?ci }
# cls-com (clash)
RULE { h:result h:clash \"cls-com\" } WHERE {
  ?c1 owl:complementOf ?c2 . ?x rdf:type ?c1 . ?x rdf:type ?c2 }
# cls-svf1
RULE { ?u rdf:type ?x } WHERE {
  ?x owl:someValuesFrom ?y ; owl:onProperty ?p . ?u ?p ?v . ?v rdf:type ?y }
# cls-svf2
RULE { ?u rdf:type ?x } WHERE {
  ?x owl:someValuesFrom owl:Thing ; owl:onProperty ?p . ?u ?p ?v }
# cls-avf
RULE { ?v rdf:type ?y } WHERE {
  ?x owl:allValuesFrom ?y ; owl:onProperty ?p . ?u rdf:type ?x . ?u ?p ?v
  FILTER(isIRI(?v) || isBlank(?v)) }
# cls-hv1
RULE { ?u ?p ?y } WHERE { ?x owl:hasValue ?y ; owl:onProperty ?p FILTER(isIRI(?p)) ?u rdf:type ?x }
# cls-hv2
RULE { ?u rdf:type ?x } WHERE { ?x owl:hasValue ?y ; owl:onProperty ?p . ?u ?p ?y }
# cls-maxc1 (clash)
RULE { h:result h:clash \"cls-maxc1\" } WHERE {
  ?x owl:maxCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty ?p .
  ?u rdf:type ?x . ?u ?p ?y }
# cls-maxc2
RULE { ?y1 owl:sameAs ?y2 } WHERE {
  ?x owl:maxCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty ?p .
  ?u rdf:type ?x . ?u ?p ?y1 FILTER(isIRI(?y1) || isBlank(?y1)) ?u ?p ?y2 }
# cls-maxqc1 (clash)
RULE { h:result h:clash \"cls-maxqc1\" } WHERE {
  ?x owl:maxQualifiedCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty ?p ;
     owl:onClass ?c . ?u rdf:type ?x . ?u ?p ?y . ?y rdf:type ?c }
# cls-maxqc2 (clash)
RULE { h:result h:clash \"cls-maxqc2\" } WHERE {
  ?x owl:maxQualifiedCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty ?p ;
     owl:onClass owl:Thing . ?u rdf:type ?x . ?u ?p ?y }
# cls-oo
RULE { ?y rdf:type ?c } WHERE { ?c owl:oneOf ?l . ?l h:member ?y FILTER(isIRI(?y) || isBlank(?y)) }
"

/-- cls-maxqc3 and cls-maxqc4: rules of the table that the Lean closure
does not have (decision 6). -/
def owlRlMaxqc : String := "
# cls-maxqc3
RULE { ?y1 owl:sameAs ?y2 } WHERE {
  ?x owl:maxQualifiedCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty ?p ;
     owl:onClass ?c . ?u rdf:type ?x . ?u ?p ?y1 . ?y1 rdf:type ?c . ?u ?p ?y2 . ?y2 rdf:type ?c }
# cls-maxqc4
RULE { ?y1 owl:sameAs ?y2 } WHERE {
  ?x owl:maxQualifiedCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty ?p ;
     owl:onClass owl:Thing . ?u rdf:type ?x . ?u ?p ?y1 FILTER(isIRI(?y1) || isBlank(?y1)) ?u ?p ?y2 }
"

/-! ## Table 7, the semantics of class axioms -/

def caxRules : String := "
# cax-sco
RULE { ?x rdf:type ?c2 } WHERE { ?c1 rdfs:subClassOf ?c2 . ?x rdf:type ?c1 }
# cax-eqc1
RULE { ?x rdf:type ?c2 } WHERE { ?c1 owl:equivalentClass ?c2 . ?x rdf:type ?c1 }
# cax-eqc2
RULE { ?x rdf:type ?c1 } WHERE { ?c1 owl:equivalentClass ?c2 . ?x rdf:type ?c2 }
# cax-dw (clash)
RULE { h:result h:clash \"cax-dw\" } WHERE { ?c1 owl:disjointWith ?c2 . ?x rdf:type ?c1 . ?x rdf:type ?c2 }
# cax-adc (clash)
RULE { h:result h:clash \"cax-adc\" } WHERE {
  ?y rdf:type owl:AllDisjointClasses ; owl:members ?l .
  ?l h:cell ?ci . ?l h:cell ?cj FILTER(!sameTerm(?ci, ?cj))
  ?ci rdf:first ?c1 . ?cj rdf:first ?c2 FILTER(!sameTerm(?c1, ?c2))
  ?x rdf:type ?c1 . ?x rdf:type ?c2 }
"

/-! ## Table 9, the semantics of schema vocabulary -/

def scmRules : String := "
# scm-cls
RULE { ?c rdfs:subClassOf ?c . ?c owl:equivalentClass ?c . ?c rdfs:subClassOf owl:Thing .
       owl:Nothing rdfs:subClassOf ?c } WHERE { ?c rdf:type owl:Class }
# scm-sco
RULE { ?c1 rdfs:subClassOf ?c3 } WHERE { ?c1 rdfs:subClassOf ?c2 . ?c2 rdfs:subClassOf ?c3 }
# scm-eqc1 (two rules, one per conclusion)
RULE { ?c1 rdfs:subClassOf ?c2 } WHERE { ?c1 owl:equivalentClass ?c2 }
RULE { ?c2 rdfs:subClassOf ?c1 } WHERE { ?c1 owl:equivalentClass ?c2 FILTER(isIRI(?c2) || isBlank(?c2)) }
# scm-eqc2
RULE { ?c1 owl:equivalentClass ?c2 } WHERE { ?c1 rdfs:subClassOf ?c2 . ?c2 rdfs:subClassOf ?c1 }
# scm-op
RULE { ?p rdfs:subPropertyOf ?p . ?p owl:equivalentProperty ?p } WHERE { ?p rdf:type owl:ObjectProperty }
# scm-dp
RULE { ?p rdfs:subPropertyOf ?p . ?p owl:equivalentProperty ?p } WHERE { ?p rdf:type owl:DatatypeProperty }
# scm-spo
RULE { ?p1 rdfs:subPropertyOf ?p3 } WHERE { ?p1 rdfs:subPropertyOf ?p2 . ?p2 rdfs:subPropertyOf ?p3 }
# scm-eqp1 (two rules, one per conclusion)
RULE { ?p1 rdfs:subPropertyOf ?p2 } WHERE { ?p1 owl:equivalentProperty ?p2 }
RULE { ?p2 rdfs:subPropertyOf ?p1 } WHERE { ?p1 owl:equivalentProperty ?p2 FILTER(isIRI(?p2) || isBlank(?p2)) }
# scm-eqp2
RULE { ?p1 owl:equivalentProperty ?p2 } WHERE { ?p1 rdfs:subPropertyOf ?p2 . ?p2 rdfs:subPropertyOf ?p1 }
# scm-dom1
RULE { ?p rdfs:domain ?c2 } WHERE { ?p rdfs:domain ?c1 . ?c1 rdfs:subClassOf ?c2 }
# scm-dom2
RULE { ?p1 rdfs:domain ?c } WHERE { ?p2 rdfs:domain ?c . ?p1 rdfs:subPropertyOf ?p2 }
# scm-rng1
RULE { ?p rdfs:range ?c2 } WHERE { ?p rdfs:range ?c1 . ?c1 rdfs:subClassOf ?c2 }
# scm-rng2
RULE { ?p1 rdfs:range ?c } WHERE { ?p2 rdfs:range ?c . ?p1 rdfs:subPropertyOf ?p2 }
# scm-hv
RULE { ?c1 rdfs:subClassOf ?c2 } WHERE {
  ?c1 owl:hasValue ?i ; owl:onProperty ?p1 . ?p1 rdfs:subPropertyOf ?p2 .
  ?c2 owl:onProperty ?p2 ; owl:hasValue ?i }
# scm-svf1
RULE { ?c1 rdfs:subClassOf ?c2 } WHERE {
  ?c1 owl:someValuesFrom ?y1 ; owl:onProperty ?p . ?y1 rdfs:subClassOf ?y2 .
  ?c2 owl:onProperty ?p ; owl:someValuesFrom ?y2 }
# scm-svf2
RULE { ?c1 rdfs:subClassOf ?c2 } WHERE {
  ?c1 owl:someValuesFrom ?y ; owl:onProperty ?p1 . ?p1 rdfs:subPropertyOf ?p2 .
  ?c2 owl:onProperty ?p2 ; owl:someValuesFrom ?y }
# scm-avf1
RULE { ?c1 rdfs:subClassOf ?c2 } WHERE {
  ?c1 owl:allValuesFrom ?y1 ; owl:onProperty ?p . ?y1 rdfs:subClassOf ?y2 .
  ?c2 owl:onProperty ?p ; owl:allValuesFrom ?y2 }
# scm-avf2
RULE { ?c2 rdfs:subClassOf ?c1 } WHERE {
  ?c1 owl:allValuesFrom ?y ; owl:onProperty ?p1 . ?p1 rdfs:subPropertyOf ?p2 .
  ?c2 owl:onProperty ?p2 ; owl:allValuesFrom ?y }
# scm-int
RULE { ?c rdfs:subClassOf ?ci } WHERE { ?c owl:intersectionOf ?l . ?l h:member ?ci }
# scm-uni
RULE { ?ci rdfs:subClassOf ?c } WHERE {
  ?c owl:unionOf ?l . ?l h:member ?ci FILTER(isIRI(?ci) || isBlank(?ci)) }
"

/-! ## Helper relations over RDF collections (decision 2) -/

def listRules : String := "
# h:member, for cls-int2, cls-uni, cls-oo, scm-int, scm-uni
RULE { ?l h:member ?e } WHERE { ?l rdf:first ?e }
RULE { ?l h:member ?e } WHERE { ?l rdf:rest ?r . ?r h:member ?e }
# h:allTypes, for cls-int1: a reading of the list from ?l to rdf:nil
RULE { ?l h:allTypes ?y } WHERE { ?l rdf:first ?c ; rdf:rest rdf:nil . ?y rdf:type ?c }
RULE { ?l h:allTypes ?y } WHERE { ?l rdf:first ?c ; rdf:rest ?r . ?r h:allTypes ?y . ?y rdf:type ?c }
# h:cell, for eq-diff2, eq-diff3, prp-adp, cax-adc
RULE { ?l h:cell ?l } WHERE { ?x owl:members ?l FILTER(isIRI(?l) || isBlank(?l)) }
RULE { ?l h:cell ?l } WHERE { ?x owl:distinctMembers ?l FILTER(isIRI(?l) || isBlank(?l)) }
RULE { ?l h:cell ?r } WHERE { ?l h:cell ?c . ?c rdf:rest ?r FILTER(isIRI(?r) || isBlank(?r)) }
"

/-! ## prp-spo2 and prp-key, unrolled (decision 2) -/

/-- The longest property chain and key the rule set handles. -/
def unrollMax : Nat := 8

/-- The list `?l1 .. ?ln` with members `?q1 .. ?qn`, as triple patterns,
and the filter that every member is an IRI. -/
def listPattern (n : Nat) : String :=
  let cells := (List.range n).map fun i =>
    let next := if i + 1 == n then "rdf:nil" else s!"?l{i + 2}"
    s!"?l{i + 1} rdf:first ?q{i + 1} ; rdf:rest {next} . "
  let iris := String.intercalate " && " ((List.range n).map fun i => s!"isIRI(?q{i + 1})")
  String.join cells ++ s!"FILTER({iris}) "

/-- prp-spo2 for a chain of `n` properties. -/
def chainRule (n : Nat) : String :=
  let node (i : Nat) : String := if i == 0 then "?x" else if i == n then "?y" else s!"?m{i}"
  let steps := (List.range n).map fun i => s!"{node i} ?q{i + 1} {node (i + 1)} . "
  s!"# prp-spo2, chain of {n}\nRULE \{ ?x ?p ?y } WHERE \{ ?p owl:propertyChainAxiom ?l1 FILTER(isIRI(?p)) " ++
    listPattern n ++ String.join steps ++ "}\n"

/-- prp-key for a key of `n` properties. -/
def keyRule (n : Nat) : String :=
  let vals := (List.range n).map fun i => s!"?x ?q{i + 1} ?z{i + 1} . ?y ?q{i + 1} ?z{i + 1} . "
  s!"# prp-key, key of {n}\nRULE \{ ?x owl:sameAs ?y } WHERE \{ ?c owl:hasKey ?l1 . " ++
    listPattern n ++ "?x rdf:type ?c . " ++ String.join vals ++ "?y rdf:type ?c }\n"

def unrolledRules : String :=
  String.join ((List.range unrollMax).map fun i => chainRule (i + 1) ++ keyRule (i + 1))

/-! ## The documents -/

/-- Every row the Lean closure also has (decision 6). -/
def owlRlCommonText : String :=
  prefixes ++ eqRules ++ prpRules ++ clsRules ++ caxRules ++ scmRules ++ listRules ++
    unrolledRules

/-- The whole rule set: `owlRlCommonText` plus cls-maxqc3 and cls-maxqc4. -/
def owlRlText : String := owlRlCommonText ++ owlRlMaxqc

/-- The parsed rule sets (empty when the text does not parse; the tests
check that it does). -/
def owlRlCommon : RuleSet := ((parseRuleSet owlRlCommonText).toOption).getD {}
def owlRl : RuleSet := ((parseRuleSet owlRlText).toOption).getD {}

/-! ## Reading the inference graph -/

def iriIsHelper (i : WfIri) : Bool := helperNs.isPrefixOf i.val

def termMentionsHelper : Term → Bool
  | .iri i => iriIsHelper i
  | _ => false

def tripleMentionsHelper (t : Triple) : Bool :=
  termMentionsHelper t.s.toTerm || iriIsHelper t.p || termMentionsHelper t.o

/-- The entailed triples (helper triples removed, decision 4). -/
def entailments (inferred : Graph) : Graph := inferred.filter (fun t => !tripleMentionsHelper t)

/-- The table ids of the clash rows whose marker is in the inference graph,
without repetition, in the order first seen. -/
def clashes (inferred : Graph) : List String :=
  inferred.foldl (fun acc t =>
    match t.s, t.o with
    | .iri s, .literal l =>
        if s.val == helperNs ++ "result" && t.p.val == helperNs ++ "clash" &&
           !acc.contains l.val.lexicalForm then acc ++ [l.val.lexicalForm] else acc
    | _, _ => acc) []

/-! ## Evaluation with the stratification computed once

`RuleSet.infer` computes the dependency graph and the strata on every call.
For the 93 rules of `owlRlCommon` (95 of `owlRl`) that costs about 21 s in the Lean interpreter (the
`#guard`s) for a few milliseconds of evaluation. Every rule here is a
general rule with no `NOT` and no group element (decision 1 to 3), so the
draft's stratification gives one layer that holds every rule; the
`#guard`s of `OwlRlTests.lean` check `stratify` gives exactly that layer
for both rule sets. `inferOneLayer` is `RuleSet.evalGraph` and
`RuleSet.infer` with that layer passed in. -/

/-- One layer with every rule as a general rule. -/
def oneLayer (rs : RuleSet) : List Layer := [⟨[], List.range rs.rules.length⟩]

/-- `RuleSet.infer`, with `oneLayer` in place of `stratify`. -/
def inferOneLayer (rs : RuleSet) (base : Graph) : Except InferError Graph :=
  if !rs.imports.isEmpty then .error (.imports rs.imports)
  else if !rs.wellFormed then .error .notWellFormed
  else
    let g0 := IGraph.ofGraph base
    let pfx := freshPrefix (base.flatMap fun t =>
      (match t.s with | .bnode b => [b] | _ => []) ++ termBnodeIds t.o)
    let (d, ctr) := dataTriples rs pfx 0
    let ge := g0.insertAll d
    let (ge, _) := evalLayers { g0 } pfx rs.rules (oneLayer rs) ge ctr
    .ok (ge.all.toList.filterMap fun t => if g0.contains t then none else t3ToTriple? t)

/-- The inference graph of a rule set over `g`, read as the entailed
triples and the clash rows that fire. -/
def run (rs : RuleSet) (g : Graph) : Except String (Graph × List String) :=
  match inferOneLayer rs g with
  | .ok inf => .ok (entailments inf, clashes inf)
  | .error e => .error e.msg

end L4Factoidal.SPARQLRL.OwlRl
