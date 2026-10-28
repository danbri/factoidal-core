/-
L4Factoidal.SPARQLRL.OwlRlTests — build-time `#guard`s for the SPARQL-RL
OWL 2 RL rule set (`SPARQLRL/OwlRl.lean`) against the Lean OWL 2 RL closure
(`SPARQLRL/OwlRlDiff.lean`). Requested on
https://github.com/danbri/factoidal-core/pull/163.

Each case is a small graph for one or more table rows. For each case two
checks:
* the rule set and the table rows of the Lean closure give the same set of
  new triples and the same clash rows (`agreesTable`);
* the case is not vacuous: a named triple is entailed, or a named clash row
  fires (a comparison of two empty results agrees and shows nothing).

The W3C OWL 2 RL corpus run is `l4owl-probe --srl-diff` (Harness/OwlProbe.lean).
-/
import L4Factoidal.SPARQLRL.OwlRlDiff
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.SPARQLRL.OwlRlTests
open L4Factoidal.RDF
open L4Factoidal.SPARQLRL
open L4Factoidal.SPARQLRL.OwlRl
open L4Factoidal.OWL.RL (indexedClosureSN closureFuelBound)

def pfx : String := "PREFIX : <http://example/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX owl: <http://www.w3.org/2002/07/owl#>
PREFIX xsd: <http://www.w3.org/2001/XMLSchema#>
"

def ttl (body : String) : Graph :=
  match L4Factoidal.Syntax.parseTurtle (pfx ++ body) none .rdf12 with
  | .ok g => g
  | .error _ => []

/-- The rule set `rs` over `body` entails the one triple of `t`. -/
def entails (rs : RuleSet) (body t : String) : Bool :=
  match run rs (ttl body), ttl t with
  | .ok (ent, _), [x] => ent.contains x || (ttl body).contains x
  | _, _ => false

/-- The clash row `id` fires (rule set) on `body`. -/
def clashes (rs : RuleSet) (body id : String) : Bool :=
  match run rs (ttl body) with
  | .ok (_, cl) => cl.contains id
  | .error _ => false

/-! ## The documents parse, are well-formed, and are one stratum -/

#guard (parseRuleSet owlRlCommonText).toOption.isSome
#guard (parseRuleSet owlRlText).toOption.isSome
#guard owlRlCommon.rules.length == 93
#guard owlRl.rules.length == 95
#guard owlRl.wellFormed
-- `inferOneLayer` is sound to use: the draft's stratification is one layer of
-- general rules (each guard costs about 21 s in the interpreter)
#guard stratify owlRlCommon.rules == some (oneLayer owlRlCommon)
#guard stratify owlRl.rules == some (oneLayer owlRl)
-- and `RuleSet.infer` gives the same graph as `inferOneLayer` (one case)
#guard (match owlRlCommon.infer (ttl ":p a owl:TransitiveProperty . :a :p :b . :b :p :c ."),
              inferOneLayer owlRlCommon (ttl ":p a owl:TransitiveProperty . :a :p :b . :b :p :c .") with
        | .ok a, .ok b => a.length == b.length && a.all b.contains
        | _, _ => false)

/-! ## One case per row group: (name, graph, entailed triple or `clash:<id>`) -/

def cases : List (String × String × String) := [
  ("eq-ref", ":a :p \"x\" .", ":a owl:sameAs :a ."),
  ("eq-sym eq-trans", ":a owl:sameAs :b . :b owl:sameAs :c .", ":c owl:sameAs :a ."),
  ("eq-rep-s", ":a owl:sameAs :b . :a :p :o .", ":b :p :o ."),
  ("eq-rep-p", ":p owl:sameAs :q . :a :p :o .", ":a :q :o ."),
  ("eq-rep-o", ":o owl:sameAs :o2 . :a :p :o .", ":a :p :o2 ."),
  ("eq-sym literal", ":a owl:sameAs \"x\" . :s :p \"x\" .", ":a owl:sameAs :a ."),
  ("prp-ap cls-thing cls-nothing1", ":a :p :b .", "owl:Nothing a owl:Class ."),
  ("prp-dom", ":p rdfs:domain :C . :a :p \"v\" .", ":a a :C ."),
  ("prp-rng", ":p rdfs:range :C . :a :p :b . :a :p \"v\" .", ":b a :C ."),
  ("prp-fp", ":p a owl:FunctionalProperty . :a :p :b , :c , \"v\" .", ":b owl:sameAs :c ."),
  ("prp-ifp", ":p a owl:InverseFunctionalProperty . :a :p :o . :b :p :o .", ":a owl:sameAs :b ."),
  ("prp-symp", ":p a owl:SymmetricProperty . :a :p :b . :a :p \"v\" .", ":b :p :a ."),
  ("prp-trp", ":p a owl:TransitiveProperty . :a :p :b . :b :p :c . :c :p :d .", ":a :p :d ."),
  ("prp-spo1", ":p rdfs:subPropertyOf :q . :a :p :b .", ":a :q :b ."),
  ("prp-spo2 n=1", ":p owl:propertyChainAxiom ( :q ) . :a :q :b .", ":a :p :b ."),
  ("prp-spo2 n=2", ":p owl:propertyChainAxiom ( :q :r ) . :a :q :b . :b :r :c .", ":a :p :c ."),
  ("prp-spo2 n=3", ":p owl:propertyChainAxiom ( :q :r :s ) . :a :q :b . :b :r :c . :c :s \"z\" .",
    ":a :p \"z\" ."),
  ("prp-spo2 n=8", ":p owl:propertyChainAxiom ( :q :q :q :q :q :q :q :q ) . :a0 :q :a1 . :a1 :q :a2 . :a2 :q :a3 . :a3 :q :a4 . :a4 :q :a5 . :a5 :q :a6 . :a6 :q :a7 . :a7 :q :a8 .",
    ":a0 :p :a8 ."),
  ("prp-eqp1 prp-eqp2", ":p owl:equivalentProperty :q . :a :p :b . :c :q :d .", ":c :p :d ."),
  ("prp-inv1 prp-inv2", ":p owl:inverseOf :q . :a :p :b . :c :q :d . :e :p \"v\" .", ":d :p :c ."),
  ("prp-key n=1", ":C owl:hasKey ( :k ) . :a a :C ; :k \"1\" . :b a :C ; :k \"1\" . :c a :C ; :k \"2\" .",
    ":a owl:sameAs :b ."),
  ("prp-key n=2", ":C owl:hasKey ( :k :j ) . :a a :C ; :k 1 ; :j 2 . :b a :C ; :k 1 ; :j 2 . :c a :C ; :k 1 ; :j 3 .",
    ":b owl:sameAs :a ."),
  ("cls-int1 cls-int2", ":C owl:intersectionOf ( :A :B ) . :x a :A , :B . :y a :C .", ":x a :C ."),
  ("cls-int2", ":C owl:intersectionOf ( :A :B ) . :y a :C .", ":y a :B ."),
  ("cls-uni", ":C owl:unionOf ( :A :B ) . :x a :A . :y a :B .", ":y a :C ."),
  ("cls-svf1", ":R owl:someValuesFrom :D ; owl:onProperty :p . :a :p :b . :b a :D .", ":a a :R ."),
  ("cls-svf2", ":R owl:someValuesFrom owl:Thing ; owl:onProperty :p . :a :p \"v\" .", ":a a :R ."),
  ("cls-avf", ":R owl:allValuesFrom :D ; owl:onProperty :p . :a a :R ; :p :b , \"v\" .", ":b a :D ."),
  ("cls-hv1 cls-hv2", ":R owl:hasValue :v ; owl:onProperty :p . :a a :R . :b :p :v .", ":a :p :v ."),
  ("cls-hv2", ":R owl:hasValue :v ; owl:onProperty :p . :b :p :v .", ":b a :R ."),
  ("cls-maxc2", ":R owl:maxCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty :p . :a a :R ; :p :b , :c .",
    ":b owl:sameAs :c ."),
  ("cls-oo", ":C owl:oneOf ( :a :b \"lit\" ) .", ":b a :C ."),
  ("cax-sco", ":A rdfs:subClassOf :B . :x a :A .", ":x a :B ."),
  ("cax-eqc1 cax-eqc2", ":A owl:equivalentClass :B . :x a :A . :y a :B .", ":y a :A ."),
  ("scm-cls", ":A a owl:Class .", "owl:Nothing rdfs:subClassOf :A ."),
  ("scm-sco scm-eqc2", ":A rdfs:subClassOf :B . :B rdfs:subClassOf :C . :C rdfs:subClassOf :A .",
    ":B owl:equivalentClass :A ."),
  ("scm-eqc1", ":A owl:equivalentClass :B .", ":B rdfs:subClassOf :A ."),
  ("scm-op scm-dp", ":p a owl:ObjectProperty . :q a owl:DatatypeProperty .", ":q owl:equivalentProperty :q ."),
  ("scm-spo scm-eqp2", ":p rdfs:subPropertyOf :q . :q rdfs:subPropertyOf :r . :r rdfs:subPropertyOf :p .",
    ":r owl:equivalentProperty :q ."),
  ("scm-eqp1", ":p owl:equivalentProperty :q .", ":q rdfs:subPropertyOf :p ."),
  ("scm-dom1 scm-rng1", ":p rdfs:domain :A ; rdfs:range :B . :A rdfs:subClassOf :A2 . :B rdfs:subClassOf :B2 .",
    ":p rdfs:range :B2 ."),
  ("scm-dom2 scm-rng2", ":q rdfs:domain :A ; rdfs:range :B . :p rdfs:subPropertyOf :q .", ":p rdfs:domain :A ."),
  ("scm-hv", ":R1 owl:hasValue :i ; owl:onProperty :p . :R2 owl:hasValue :i ; owl:onProperty :q . :p rdfs:subPropertyOf :q .",
    ":R1 rdfs:subClassOf :R2 ."),
  ("scm-svf1", ":R1 owl:someValuesFrom :A ; owl:onProperty :p . :R2 owl:someValuesFrom :B ; owl:onProperty :p . :A rdfs:subClassOf :B .",
    ":R1 rdfs:subClassOf :R2 ."),
  ("scm-svf2", ":R1 owl:someValuesFrom :A ; owl:onProperty :p . :R2 owl:someValuesFrom :A ; owl:onProperty :q . :p rdfs:subPropertyOf :q .",
    ":R1 rdfs:subClassOf :R2 ."),
  ("scm-avf1", ":R1 owl:allValuesFrom :A ; owl:onProperty :p . :R2 owl:allValuesFrom :B ; owl:onProperty :p . :A rdfs:subClassOf :B .",
    ":R1 rdfs:subClassOf :R2 ."),
  ("scm-avf2", ":R1 owl:allValuesFrom :A ; owl:onProperty :p . :R2 owl:allValuesFrom :A ; owl:onProperty :q . :p rdfs:subPropertyOf :q .",
    ":R2 rdfs:subClassOf :R1 ."),
  ("scm-int", ":C owl:intersectionOf ( :A :B ) .", ":C rdfs:subClassOf :B ."),
  ("scm-uni", ":D owl:unionOf ( :E :F ) .", ":F rdfs:subClassOf :D ."),
  ("eq-diff1", ":a owl:sameAs :b . :a owl:differentFrom :b .", "clash:eq-diff1"),
  ("eq-diff2", ":x a owl:AllDifferent ; owl:members ( :a :b :c ) . :a owl:sameAs :c .", "clash:eq-diff2"),
  ("eq-diff3", ":x a owl:AllDifferent ; owl:distinctMembers ( :a :b ) . :b owl:sameAs :a .", "clash:eq-diff3"),
  ("prp-irp", ":p a owl:IrreflexiveProperty . :a :p :a .", "clash:prp-irp"),
  ("prp-asyp", ":p a owl:AsymmetricProperty . :a :p :b . :b :p :a .", "clash:prp-asyp"),
  ("prp-pdw", ":p owl:propertyDisjointWith :q . :a :p :b ; :q :b .", "clash:prp-pdw"),
  ("prp-adp", ":x a owl:AllDisjointProperties ; owl:members ( :p :q :r ) . :a :p :b ; :r :b .", "clash:prp-adp"),
  ("prp-npa1", ":n owl:sourceIndividual :a ; owl:assertionProperty :p ; owl:targetIndividual :b . :a :p :b .",
    "clash:prp-npa1"),
  ("prp-npa2", ":n owl:sourceIndividual :a ; owl:assertionProperty :p ; owl:targetValue 5 . :a :p 5 .",
    "clash:prp-npa2"),
  ("cls-nothing2", ":a a owl:Nothing .", "clash:cls-nothing2"),
  ("cls-com", ":A owl:complementOf :B . :x a :A , :B .", "clash:cls-com"),
  ("cls-maxc1", ":R owl:maxCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty :p . :a a :R ; :p :b .",
    "clash:cls-maxc1"),
  ("cls-maxqc1", ":R owl:maxQualifiedCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty :p ; owl:onClass :C . :a a :R ; :p :b . :b a :C .",
    "clash:cls-maxqc1"),
  ("cls-maxqc2", ":R owl:maxQualifiedCardinality \"0\"^^xsd:nonNegativeInteger ; owl:onProperty :p ; owl:onClass owl:Thing . :a a :R ; :p :b .",
    "clash:cls-maxqc2"),
  ("cax-dw", ":A owl:disjointWith :B . :x a :A , :B .", "clash:cax-dw"),
  ("cax-adc", ":y a owl:AllDisjointClasses ; owl:members ( :A :B :C ) . :x a :A , :C .", "clash:cax-adc"),
  -- the Lean reading of the table's 1 <= i < j <= n: two distinct members,
  -- so a class listed twice is no clash; the rule set reads it the same way
  ("cax-adc repeated member", ":y a owl:AllDisjointClasses ; owl:members ( :A :A ) . :x a :A .",
    ":x owl:sameAs :x .")
]

/-- Both checks of one case. -/
def caseOk (c : String × String × String) : Bool :=
  let (_, body, want) := c
  agreesTable (ttl body) &&
  (if "clash:".isPrefixOf want then clashes owlRlCommon body (want.drop 6).toString
   else entails owlRlCommon body want)

/-- The names of the failing cases (empty when all pass). -/
def failing : List String := cases.filterMap fun c => if caseOk c then none else some c.1

#guard cases.length == 66
#guard failing == []
-- no clash on the consistent case
#guard !clashes owlRlCommon ":y a owl:AllDisjointClasses ; owl:members ( :A :A ) . :x a :A ." "cax-adc"

/-! ## cls-maxqc3 and cls-maxqc4: in `owlRl`, not in the Lean closure -/

def maxqc3 : String := ":R owl:maxQualifiedCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty :p ; owl:onClass :C . :a a :R ; :p :b , :c . :b a :C . :c a :C ."
def maxqc4 : String := ":R owl:maxQualifiedCardinality \"1\"^^xsd:nonNegativeInteger ; owl:onProperty :p ; owl:onClass owl:Thing . :a a :R ; :p :b , :c ."

#guard entails owlRl maxqc3 ":b owl:sameAs :c ."
#guard entails owlRl maxqc4 ":c owl:sameAs :b ."
#guard !entails owlRlCommon maxqc3 ":b owl:sameAs :c ."

/-- The library closure (`indexedClosureSN`) entails the one triple of `t`. -/
def libraryEntails (body t : String) : Bool :=
  let g := ttl body
  match ttl t with
  | [x] => (indexedClosureSN g (closureFuelBound g)).contains x
  | _ => false

-- xfail https://github.com/danbri/factoidal/issues/1113: the Lean OWL 2 RL
-- closure has no cls-maxqc3 or cls-maxqc4, so it does not entail these. When
-- a guard fails, the rows are in: change both to the positive form and close
-- the issue.
#guard !libraryEntails maxqc3 ":b owl:sameAs :c ."
#guard !libraryEntails maxqc4 ":c owl:sameAs :b ."

/-! ## Expected failures: chains and keys longer than `unrollMax`

prp-spo2 and prp-key are unrolled to 8 members (`OwlRl.lean` decision 2).
With 9 members the Lean closure derives the triple and the rule set does
not, so the two differ. Expected failure,
https://github.com/danbri/factoidal/issues/1112. When one of these two
guards fails, the shortfall is repaired: change it to the positive form and
close the issue. -/

def chain9 : String := ":p owl:propertyChainAxiom ( :q :q :q :q :q :q :q :q :q ) . :a0 :q :a1 . :a1 :q :a2 . :a2 :q :a3 . :a3 :q :a4 . :a4 :q :a5 . :a5 :q :a6 . :a6 :q :a7 . :a7 :q :a8 . :a8 :q :a9 ."
def key9 : String := ":C owl:hasKey ( :k1 :k2 :k3 :k4 :k5 :k6 :k7 :k8 :k9 ) . :a a :C ; :k1 1 ; :k2 2 ; :k3 3 ; :k4 4 ; :k5 5 ; :k6 6 ; :k7 7 ; :k8 8 ; :k9 9 . :b a :C ; :k1 1 ; :k2 2 ; :k3 3 ; :k4 4 ; :k5 5 ; :k6 6 ; :k7 7 ; :k8 8 ; :k9 9 ."

-- xfail https://github.com/danbri/factoidal/issues/1112: prp-spo2 with a chain of 9 members
#guard !agreesTable (ttl chain9)
-- xfail https://github.com/danbri/factoidal/issues/1112: prp-key with a key of 9 members
#guard !agreesTable (ttl key9)

end L4Factoidal.SPARQLRL.OwlRlTests
