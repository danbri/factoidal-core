/-
Finite adversarial QA for the restricted, proved RDF-to-Direct reader.
These expected outcomes are fixed independently of the reader. A null
verdict is unknown, never a proof of consistency. The preservation theorem
is audited separately below; these guards do not replace it.
-/
import L4Factoidal.OWL.AtomicDirect
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

structure Case where
  id : String
  input : String
  supported : Bool
  consistent : Option Bool

def cases : List Case := [
  ⟨"empty", "", true, none⟩,
  ⟨"annotation-domain", annotationDecl ++ annotationDomain ++ annotationValue, true, none⟩,
  ⟨"annotation-declaration-last", annotationValue ++ annotationDomain ++ annotationDecl, true, none⟩,
  ⟨"annotation-range", annotationDecl ++ edge "urn:p" (rdfs "range") (owl "Nothing") ++
    edge "urn:a" "urn:p" "urn:b", true, none⟩,
  ⟨"annotation-blank-value", annotationDecl ++ s!"<urn:a> <urn:p> _:value .\n", true, none⟩,
  ⟨"builtin-comment", literal "urn:a" (rdfs "comment") "note", true, none⟩,
  ⟨"builtin-label", literal "urn:a" (rdfs "label") "name", true, none⟩,
  ⟨"builtin-version-info", literal "urn:a" (owl "versionInfo") "one", true, none⟩,
  ⟨"empty-named-class", classDecl ++ emptyClass, true, none⟩,
  ⟨"generated-prefix-user-class",
    edge "urn:factoidal:owl-cert:one-of:urn:a" (rdf "type") (owl "Class") ++
    edge "urn:factoidal:owl-cert:one-of:urn:a" (rdfs "subClassOf") (owl "Nothing"), true, none⟩,
  ⟨"data-prefix-user-class",
    edge "urn:factoidal:owl-cert:data-min:1:urn:p" (rdfs "subClassOf") (owl "Nothing"), true, none⟩,
  ⟨"empty-class-with-member", classDecl ++ emptyClass ++ member, true, some false⟩,
  ⟨"bottom-membership", edge "urn:a" (rdf "type") (owl "Nothing"), true, some false⟩,
  ⟨"top-subclass-bottom", edge (owl "Thing") (rdfs "subClassOf") (owl "Nothing"), true, some false⟩,
  ⟨"same-and-different", same ++ different, true, some false⟩,
  ⟨"same-only", same, true, none⟩,
  ⟨"different-only", different, true, none⟩,
  ⟨"self-different", edge "urn:a" (owl "differentFrom") "urn:a", true, some false⟩,
  ⟨"class-individual-punning", classDecl ++ emptyClass ++
    edge "urn:C" (rdf "type") (owl "Thing"), true, none⟩,
  ⟨"annotation-and-real-contradiction", annotationDecl ++ annotationDomain ++
    annotationValue ++ same ++ different, true, some false⟩,
  ⟨"duplicate-statements", same ++ same ++ different ++ different, true, some false⟩,
  ⟨"ontology-header", edge "urn:ontology" (rdf "type") (owl "Ontology"), true, none⟩,
  ⟨"blank-ontology-header", s!"_:ontology <{rdf "type"}> <{owl "Ontology"}> .\n", true, none⟩,
  ⟨"named-individual-declaration", edge "urn:a" (rdf "type") (owl "NamedIndividual"), true, none⟩,
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
    edge "urn:a" (rdf "type") "urn:D", true, none⟩,
  ⟨"unsupported-builtin-seeAlso", edge "urn:a" (rdfs "seeAlso") "urn:b", false, none⟩,
  ⟨"unsupported-builtin-isDefinedBy", edge "urn:a" (rdfs "isDefinedBy") "urn:b", false, none⟩,
  ⟨"unsupported-builtin-deprecated", literal "urn:a" (owl "deprecated") "true", false, none⟩,
  ⟨"unsupported-builtin-priorVersion", edge "urn:a" (owl "priorVersion") "urn:b", false, none⟩,
  ⟨"unsupported-builtin-backwardCompatibleWith", edge "urn:a" (owl "backwardCompatibleWith") "urn:b", false, none⟩,
  ⟨"unsupported-builtin-incompatibleWith", edge "urn:a" (owl "incompatibleWith") "urn:b", false, none⟩,
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
    edge "urn:second" (rdf "type") (owl "Ontology"), true, none⟩
]

def observed (test : Case) : Except ParseError (Bool × Option Bool) :=
  (parseNQuadsFast test.input .rdf12).bind (fun ds =>
    if ds.named.isEmpty then
      .ok ((AtomicDirect.readOntology ds.default).isSome,
           (AtomicDirect.decide ds.default .close).consistent)
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
#guard cases.length == 45
#guard cases.all passed
#guard !(observed ⟨"named-graph-scope-control",
  "<urn:a> <urn:p> <urn:b> <urn:graph> .\n", false, none⟩).isOk

#print axioms AtomicDirect.readOntology_preserves_models
#print axioms AtomicDirect.accepted_covers_triples
#print axioms AtomicDirect.readOntology_hasModel
#print axioms AtomicDirect.decide_sound
#print axioms AtomicDirect.isAnnotation_sound
#print axioms AtomicDirect.addAxiom_preserves_model
#print axioms AtomicDirect.erase_sound
#print axioms AtomicDirect.definitive_admitted
#print axioms AtomicDirect.unsupported_is_unknown
#print axioms CertNames.decode_encode
#print axioms CertNames.encode_injective
#print axioms CertNames.source_ne_nominal
#print axioms CertNames.source_ne_dataMin
#print axioms CertNames.source_ne_dataMax
#print axioms CertNames.frame_eq_frameTR

end AtomicDirectAcceptance
