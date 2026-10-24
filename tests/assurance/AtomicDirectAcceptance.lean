/-
Finite adversarial QA for the restricted, proved RDF-to-Direct reader.
These expected outcomes are fixed independently of the reader. A null
verdict is unknown, never a proof of consistency; `true` comes only from a
checked model (https://github.com/danbri/factoidal/issues/960). The preservation theorem
is audited separately below; these guards do not replace it.
-/
import L4Factoidal.OWL.AtomicModel
import L4Factoidal.OWL.CertNames
import L4Factoidal.Syntax.NQuadsFast
import Lean

namespace AtomicDirectAcceptance

open L4Factoidal.OWL L4Factoidal.Syntax

def rdf (localName : String) := "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ++ localName
def rdfs (localName : String) := "http://www.w3.org/2000/01/rdf-schema#" ++ localName
def owl (localName : String) := "http://www.w3.org/2002/07/owl#" ++ localName
def edge (s p o : String) := s!"<{s}> <{p}> <{o}> .\n"
def literal (s p value : String) := s!"<{s}> <{p}> \"{value}\" .\n"
def annotationDecl := edge "urn:p" (rdf "type") (owl "AnnotationProperty")
def annotationDomain := edge "urn:p" (rdfs "domain") (owl "Nothing")
def annotationValue := literal "urn:a" "urn:p" "note"
def classDecl := edge "urn:C" (rdf "type") (owl "Class")
def emptyClass := edge "urn:C" (rdfs "subClassOf") (owl "Nothing")
def member := edge "urn:a" (rdf "type") "urn:C"
def same := edge "urn:a" (owl "sameAs") "urn:b"
def different := edge "urn:a" (owl "differentFrom") "urn:b"
def restriction (node property filler : String) :=
  s!"_:{node} <{owl "onProperty"}> <{property}> .\n" ++
  s!"_:{node} <{owl "someValuesFrom"}> <{filler}> .\n"
def cyclic := edge "urn:i" (rdf "type") "urn:A" ++
  s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++ restriction "r" "urn:p" "urn:A"
/-- An owl:Axiom node for the triple `source property target` (Mapping section 3.2.5). -/
def axiomNode (node source property target : String) :=
  s!"_:{node} <{rdf "type"}> <{owl "Axiom"}> .\n" ++
  s!"_:{node} <{owl "annotatedSource"}> <{source}> .\n" ++
  s!"_:{node} <{owl "annotatedProperty"}> <{property}> .\n" ++
  s!"_:{node} <{owl "annotatedTarget"}> {target} .\n"
/-- i : A, A ⊑ ∃p.B, B ⊑ ∃p.C, p transitive: the model needs the edge from
the element of i to the witness of C (the search closes the edges). -/
def transitiveChain := edge "urn:p" (rdf "type") (owl "TransitiveProperty") ++
  edge "urn:i" (rdf "type") "urn:A" ++
  s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++ restriction "r" "urn:p" "urn:B" ++
  s!"<urn:B> <{rdfs "subClassOf"}> _:s .\n" ++ restriction "s" "urn:p" "urn:C"

structure Case where
  id : String
  input : String
  supported : Bool
  consistent : Option Bool

def cases : List Case := [
  ⟨"empty", "", true, some true⟩,
  ⟨"annotation-domain", annotationDecl ++ annotationDomain ++ annotationValue, true, some true⟩,
  ⟨"annotation-declaration-last", annotationValue ++ annotationDomain ++ annotationDecl, true, some true⟩,
  ⟨"annotation-range", annotationDecl ++ edge "urn:p" (rdfs "range") (owl "Nothing") ++
    edge "urn:a" "urn:p" "urn:b", true, some true⟩,
  ⟨"annotation-blank-value", annotationDecl ++ s!"<urn:a> <urn:p> _:value .\n", true, some true⟩,
  ⟨"builtin-comment", literal "urn:a" (rdfs "comment") "note", true, some true⟩,
  ⟨"builtin-label", literal "urn:a" (rdfs "label") "name", true, some true⟩,
  ⟨"builtin-version-info", literal "urn:a" (owl "versionInfo") "one", true, some true⟩,
  ⟨"empty-named-class", classDecl ++ emptyClass, true, some true⟩,
  ⟨"generated-prefix-user-class",
    edge "urn:factoidal:owl-cert:one-of:urn:a" (rdf "type") (owl "Class") ++
    edge "urn:factoidal:owl-cert:one-of:urn:a" (rdfs "subClassOf") (owl "Nothing"), true, some true⟩,
  ⟨"data-prefix-user-class",
    edge "urn:factoidal:owl-cert:data-min:1:urn:p" (rdfs "subClassOf") (owl "Nothing"), true, some true⟩,
  ⟨"empty-class-with-member", classDecl ++ emptyClass ++ member, true, some false⟩,
  ⟨"bottom-membership", edge "urn:a" (rdf "type") (owl "Nothing"), true, some false⟩,
  ⟨"top-subclass-bottom", edge (owl "Thing") (rdfs "subClassOf") (owl "Nothing"), true, some false⟩,
  ⟨"same-and-different", same ++ different, true, some false⟩,
  ⟨"same-only", same, true, some true⟩,
  ⟨"different-only", different, true, some true⟩,
  ⟨"self-different", edge "urn:a" (owl "differentFrom") "urn:a", true, some false⟩,
  ⟨"class-individual-punning", classDecl ++ emptyClass ++
    edge "urn:C" (rdf "type") (owl "Thing"), true, some true⟩,
  ⟨"annotation-and-real-contradiction", annotationDecl ++ annotationDomain ++
    annotationValue ++ same ++ different, true, some false⟩,
  ⟨"duplicate-statements", same ++ same ++ different ++ different, true, some false⟩,
  ⟨"ontology-header", edge "urn:ontology" (rdf "type") (owl "Ontology"), true, some true⟩,
  ⟨"blank-ontology-header", s!"_:ontology <{rdf "type"}> <{owl "Ontology"}> .\n", true, some true⟩,
  ⟨"named-individual-declaration", edge "urn:a" (rdf "type") (owl "NamedIndividual"), true, some true⟩,
  ⟨"unsupported-object-property", edge "urn:p" (rdf "type") (owl "ObjectProperty") ++
    edge "urn:p" (rdfs "domain") (owl "Nothing") ++ edge "urn:a" "urn:p" "urn:b", false, none⟩,
  ⟨"unsupported-undeclared-predicate", edge "urn:a" "urn:p" "urn:b", false, none⟩,
  ⟨"unsupported-import", edge "urn:ontology" (owl "imports") "urn:other", false, none⟩,
  ⟨"unsupported-restriction", s!"_:r <{rdf "type"}> <{owl "Restriction"}> .\n", false, none⟩,
  ⟨"forbidden-logical-predicate-annotation",
    edge (rdf "type") (rdf "type") (owl "AnnotationProperty") ++ member, false, none⟩,
  ⟨"mixed-property-roles", annotationDecl ++
    edge "urn:p" (rdf "type") (owl "ObjectProperty") ++ annotationValue, false, none⟩,
  ⟨"sameas-does-not-merge-classes", classDecl ++ emptyClass ++
    edge "urn:D" (rdf "type") (owl "Class") ++ edge "urn:C" (owl "sameAs") "urn:D" ++
    edge "urn:a" (rdf "type") "urn:D", true, some true⟩,
  ⟨"builtin-seeAlso", edge "urn:a" (rdfs "seeAlso") "urn:b", true, some true⟩,
  ⟨"builtin-isDefinedBy", edge "urn:a" (rdfs "isDefinedBy") "urn:b", true, some true⟩,
  ⟨"builtin-deprecated", literal "urn:a" (owl "deprecated") "true", true, some true⟩,
  ⟨"builtin-priorVersion", edge "urn:a" (owl "priorVersion") "urn:b", true, some true⟩,
  ⟨"builtin-backwardCompatibleWith", edge "urn:a" (owl "backwardCompatibleWith") "urn:b", true, some true⟩,
  ⟨"builtin-incompatibleWith", edge "urn:a" (owl "incompatibleWith") "urn:b", true, some true⟩,
  ⟨"unsupported-reserved-individual-declaration", edge (owl "Thing") (rdf "type") (owl "NamedIndividual"), false, none⟩,
  ⟨"unsupported-reserved-individual-assertion", edge (owl "Nothing") (rdf "type") (owl "Thing"), false, none⟩,
  ⟨"unsupported-reserved-individual-same", edge "urn:a" (owl "sameAs") (owl "Thing"), false, none⟩,
  ⟨"unsupported-reserved-individual-different", edge (owl "Nothing") (owl "differentFrom") (owl "Nothing"), false, none⟩,
  ⟨"unsupported-triple-among-annotations", annotationDecl ++ annotationValue ++
    edge "urn:ontology" (owl "imports") "urn:other", false, none⟩,
  ⟨"unsupported-directional-annotation", annotationDecl ++
    "<urn:a> <urn:p> \"note\"@en--ltr .\n", false, none⟩,
  ⟨"unsupported-triple-term-annotation", annotationDecl ++
    "<urn:a> <urn:p> <<( <urn:s> <urn:q> <urn:o> )>> .\n", false, none⟩,
  ⟨"multiple-headers-fragment-admission", edge "urn:first" (rdf "type") (owl "Ontology") ++
    edge "urn:second" (rdf "type") (owl "Ontology"), true, some true⟩,
  ⟨"object-property-declaration", edge "urn:p" (rdf "type") (owl "ObjectProperty"), true, some true⟩,
  ⟨"some-values-from-cyclic", cyclic, true, some true⟩,
  ⟨"some-values-from-assertion", s!"<urn:a> <{rdf "type"}> _:r .\n" ++
    restriction "r" "urn:p" "urn:C" ++ edge "urn:p" (rdf "type") (owl "ObjectProperty"), true, some true⟩,
  ⟨"some-values-from-typed-restriction", cyclic ++ s!"_:r <{rdf "type"}> <{owl "Restriction"}> .\n",
    true, some true⟩,
  ⟨"some-values-from-witness-clash", cyclic ++ s!"<urn:A> <{rdfs "subClassOf"}> _:s .\n" ++
    restriction "s" "urn:q" "urn:B" ++ edge "urn:B" (rdfs "subClassOf") "urn:E" ++
    edge "urn:E" (rdfs "subClassOf") (owl "Nothing"), true, some false⟩,
  ⟨"some-values-from-nothing-filler", edge "urn:i" (rdf "type") "urn:A" ++
    s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++ restriction "r" "urn:p" (owl "Nothing"), true, some false⟩,
  ⟨"unsupported-restriction-two-properties", cyclic ++
    s!"_:r <{owl "onProperty"}> <urn:q> .\n", false, none⟩,
  ⟨"unsupported-restriction-no-filler", s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++
    s!"_:r <{owl "onProperty"}> <urn:p> .\n", false, none⟩,
  ⟨"unsupported-annotation-property-restriction", annotationDecl ++ s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++
    restriction "r" "urn:p" "urn:A", false, none⟩,
  -- Issue 960 item 5: the constructors the Cell Ontology uses.
  ⟨"transitive-property", edge "urn:p" (rdf "type") (owl "TransitiveProperty"), true, some true⟩,
  ⟨"transitive-chain-model", transitiveChain, true, some true⟩,
  ⟨"transitive-chain-witness-clash", transitiveChain ++ edge "urn:C" (rdfs "subClassOf") (owl "Nothing"),
    true, some false⟩,
  ⟨"unsupported-transitive-annotation-property", annotationDecl ++
    edge "urn:p" (rdf "type") (owl "TransitiveProperty"), false, none⟩,
  ⟨"axiom-annotation", annotationDecl ++ classDecl ++ emptyClass ++
    axiomNode "x" "urn:C" (rdfs "subClassOf") s!"<{owl "Nothing"}>" ++
    s!"_:x <urn:p> \"source\" .\n", true, some true⟩,
  ⟨"axiom-annotation-of-restriction-axiom", cyclic ++ edge "urn:note" (rdf "type") (owl "AnnotationProperty") ++
    axiomNode "x" "urn:A" (rdfs "subClassOf") "_:r" ++ s!"_:x <urn:note> \"source\" .\n", true, some true⟩,
  ⟨"unsupported-axiom-annotation-without-axiom", annotationDecl ++ classDecl ++
    axiomNode "x" "urn:C" (rdfs "subClassOf") s!"<{owl "Nothing"}>", false, none⟩,
  ⟨"unsupported-axiom-node-two-sources", annotationDecl ++ classDecl ++ emptyClass ++
    axiomNode "x" "urn:C" (rdfs "subClassOf") s!"<{owl "Nothing"}>" ++
    s!"_:x <{owl "annotatedSource"}> <urn:D> .\n", false, none⟩,
  ⟨"unsupported-annotated-source-untyped", classDecl ++ emptyClass ++
    s!"_:x <{owl "annotatedSource"}> <urn:C> .\n", false, none⟩,
  ⟨"unsupported-annotated-restriction-node", cyclic ++ edge "urn:note" (rdf "type") (owl "AnnotationProperty") ++
    s!"_:r <urn:note> \"note\" .\n", false, none⟩,
  ⟨"anonymous-individual-annotation", annotationDecl ++ s!"_:a <urn:p> \"note\" .\n", true, some true⟩,
  ⟨"unsupported-undeclared-blank-annotation", s!"_:a <urn:p> \"note\" .\n", false, none⟩,
  ⟨"version-iri", edge "urn:ontology" (rdf "type") (owl "Ontology") ++
    edge "urn:ontology" (owl "versionIRI") "urn:ontology/1", true, some true⟩,
  ⟨"unsupported-version-iri-without-header", edge "urn:ontology" (owl "versionIRI") "urn:ontology/1",
    false, none⟩,
  ⟨"sub-annotation-property", annotationDecl ++ edge "urn:q" (rdf "type") (owl "AnnotationProperty") ++
    edge "urn:p" (rdfs "subPropertyOf") "urn:q", true, some true⟩,
  ⟨"unsupported-sub-object-property", edge "urn:p" (rdf "type") (owl "ObjectProperty") ++
    edge "urn:q" (rdf "type") (owl "ObjectProperty") ++ edge "urn:p" (rdfs "subPropertyOf") "urn:q",
    false, none⟩
]

def observed (test : Case) : Except ParseError (Bool × Option Bool) :=
  (parseNQuadsFast test.input .rdf12).bind (fun ds =>
    if ds.named.isEmpty then
      .ok ((AtomicDirect.readOntology ds.default).isSome,
           (AtomicModel.decideFuel ds.default AtomicModel.defaultFuel).consistent)
    else .error { msg := "this graph-only fixture must not contain named graphs", pos := 0 })

def passed (test : Case) : Bool :=
  (observed test).toOption == some (test.supported, test.consistent)

def reportCase (test : Case) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", Lean.toJson test.id), ("expectedSupported", Lean.toJson test.supported),
    ("expectedConsistent", Lean.toJson test.consistent), ("passed", Lean.toJson (passed test)),
    ("observed", match observed test with
      | .error error => Lean.Json.mkObj [("parseError", Lean.toJson error.msg)]
      | .ok (supported, consistent) => Lean.Json.mkObj [
          ("supported", Lean.toJson supported), ("consistent", Lean.toJson consistent)])]

#eval IO.println ("ATOMIC_DIRECT_ACCEPTANCE=" ++ (Lean.toJson (cases.map reportCase)).compress)
#guard cases.length == 70
#guard cases.all passed
#guard !(observed ⟨"named-graph-scope-control",
  "<urn:a> <urn:p> <urn:b> <urn:graph> .\n", false, none⟩).isOk

#print axioms AtomicDirect.readOntology_preserves_models
#print axioms AtomicDirect.accepted_covers_triples
#print axioms AtomicDirect.readOntology_hasModel
#print axioms AtomicDirect.decide_sound
#print axioms AtomicDirect.knownAnnotation
#print axioms AtomicDirect.addAxiom_preserves_model
#print axioms AtomicDirect.erase_sound
#print axioms AtomicDirect.definitive_admitted
#print axioms AtomicDirect.unsupported_is_unknown
#print axioms AtomicModel.checkModel_sound
#print axioms AtomicModel.decideFuel_sound
#print axioms CertNames.decode_encode
#print axioms CertNames.encode_injective
#print axioms CertNames.source_ne_nominal
#print axioms CertNames.source_ne_dataMin
#print axioms CertNames.source_ne_dataMax
#print axioms CertNames.frame_eq_frameTR

end AtomicDirectAcceptance
