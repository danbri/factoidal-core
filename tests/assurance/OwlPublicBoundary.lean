/- Actual public consistency producer, including text and dataset adapters.
Unknown is an API observation, not a successful consistency decision. `true`
needs a checked model and `false` a checked refutation
(https://github.com/danbri/factoidal/issues/960). -/
import Wasm.Ops.ReasonDl
import Wasm.Dispatch
import Lean

namespace OwlPublicBoundary
open L4Wasm.Ops L4Factoidal.JSON L4Factoidal.Syntax

def rdf (name : String) := "http://www.w3.org/1999/02/22-rdf-syntax-ns#" ++ name
def owl (name : String) := "http://www.w3.org/2002/07/owl#" ++ name
def rdfs (name : String) := "http://www.w3.org/2000/01/rdf-schema#" ++ name
def edge (s p o : String) := s!"<{s}> <{p}> <{o}> .\n"
def same := edge "urn:a" (owl "sameAs") "urn:b"
def different := edge "urn:a" (owl "differentFrom") "urn:b"
def contradiction := same ++ different
def annotation := edge "urn:p" (rdf "type") (owl "AnnotationProperty") ++
  edge "urn:p" (rdfs "domain") (owl "Nothing") ++ "<urn:a> <urn:p> \"note\" .\n"
def negativeProperty := edge "urn:a" "urn:p" "urn:b" ++
  s!"_:n <{rdf "type"}> <{owl "NegativePropertyAssertion"}> .\n" ++
  s!"_:n <{owl "sourceIndividual"}> <urn:a> .\n" ++
  s!"_:n <{owl "assertionProperty"}> <urn:p> .\n" ++
  s!"_:n <{owl "targetIndividual"}> <urn:b> .\n"

structure Case where
  id : String
  input : String
  opts : String := ""
  ok : Bool := true
  consistent : Option Bool := none
  reasonPrefix : String := "incomplete-search"

def restriction (node property filler : String) :=
  s!"_:{node} <{owl "onProperty"}> <{property}> .\n" ++
  s!"_:{node} <{owl "someValuesFrom"}> <{filler}> .\n"
def cyclic := edge "urn:i" (rdf "type") "urn:A" ++
  s!"<urn:A> <{rdfs "subClassOf"}> _:r .\n" ++ restriction "r" "urn:p" "urn:A"

def cases : List Case := [
  { id := "empty", input := "", consistent := some true, reasonPrefix := "" },
  { id := "annotation-domain", input := annotation, consistent := some true, reasonPrefix := "" },
  { id := "annotation-plus-real-clash", input := annotation ++ contradiction,
    consistent := some false, reasonPrefix := "" },
  { id := "same-different", input := contradiction, consistent := some false, reasonPrefix := "" },
  { id := "same-chain", input := same ++ edge "urn:b" (owl "sameAs") "urn:c" ++
      edge "urn:a" (owl "differentFrom") "urn:c", consistent := some false, reasonPrefix := "" },
  { id := "top-below-bottom", input := edge (owl "Thing") (rdfs "subClassOf") (owl "Nothing"),
    consistent := some false, reasonPrefix := "" },
  { id := "generated-looking-source-name", input :=
      edge "urn:factoidal:owl-cert:one-of:urn:a" (rdf "type") (owl "Class") ++
      edge "urn:factoidal:owl-cert:one-of:urn:a" (rdfs "subClassOf") (owl "Nothing"),
    consistent := some true, reasonPrefix := "" },
  { id := "class-individual-punning", input := edge "urn:C" (rdf "type") (owl "Class") ++
      edge "urn:C" (rdfs "subClassOf") (owl "Nothing") ++
      edge "urn:C" (rdf "type") (owl "Thing"), consistent := some true, reasonPrefix := "" },
  { id := "unsupported-equivalence-contradiction", input :=
      edge "urn:C" (owl "equivalentClass") (owl "Thing") ++
      edge "urn:C" (owl "equivalentClass") (owl "Nothing"), reasonPrefix := "unsupported-syntax" },
  { id := "unsupported-import", input := edge "urn:ontology" (owl "imports") "urn:other",
    reasonPrefix := "unsupported-syntax" },
  { id := "unsupported-negative-property", input := negativeProperty,
    reasonPrefix := "unsupported-syntax" },
  { id := "named-contradiction-is-outside-default", input :=
      s!"<urn:a> <{owl "sameAs"}> <urn:b> <urn:g> .\n" ++
      s!"<urn:a> <{owl "differentFrom"}> <urn:b> <urn:g> .\n", consistent := some true,
    reasonPrefix := "" },
  { id := "default-clash-with-named-data", input := contradiction ++
      "<urn:s> <urn:p> <urn:o> <urn:g> .\n", consistent := some false, reasonPrefix := "" },
  { id := "default-annotation-with-named-clash", input := annotation ++
      s!"<urn:a> <{owl "differentFrom"}> <urn:a> <urn:g> .\n", consistent := some true,
    reasonPrefix := "" },
  { id := "named-declaration-does-not-classify-default", input :=
      s!"<urn:p> <{rdf "type"}> <{owl "AnnotationProperty"}> <urn:g> .\n" ++
      "<urn:a> <urn:p> \"note\" .\n", reasonPrefix := "unsupported-syntax" },
  { id := "zero-search-fuel", input := contradiction, opts := "{\"fuel\":\"0\"}",
    consistent := some false, reasonPrefix := "" },
  { id := "malformed-options", input := contradiction, opts := "{", consistent := some false,
    reasonPrefix := "" },
  { id := "rdf12-refusal", input := "<urn:s> <urn:p> \"note\"@en--ltr .\n",
    ok := false, reasonPrefix := "" },
  { id := "named-rdf12-preflight", input := contradiction ++
      "<urn:s> <urn:p> \"note\"@en--ltr <urn:g> .\n", ok := false, reasonPrefix := "" },
  { id := "parse-error", input := "<urn:s> <urn:p> .\n", ok := false, reasonPrefix := "" },
  { id := "cyclic-some-values-from", input := cyclic, consistent := some true, reasonPrefix := "" },
  { id := "cyclic-some-values-from-fuel-one", input := cyclic, opts := "{\"fuel\":\"1\"}",
    reasonPrefix := "budget-out" },
  { id := "some-values-from-witness-clash", input := cyclic ++
      s!"<urn:A> <{rdfs "subClassOf"}> _:s .\n" ++ restriction "s" "urn:q" "urn:B" ++
      edge "urn:B" (rdfs "subClassOf") (owl "Nothing"), consistent := some false,
    reasonPrefix := "" }
]

def dispatchResponse (test : Case) : String :=
  L4Wasm.call "owlIsConsistent" (Json.array [.string test.input, .string test.opts]).toString

/-- Independent dispatch expectations for the current error ABI. The raw
producer's proof/schema remains separate from dispatch enrichment. This
does not call attachCode, classify, specOfCode, or positionJson to compute
the expected metadata. The OWL text op's parse refusal currently has no
structured position; the public facade's preliminary parser is distinct. -/
def dispatchMatches (test : Case) (raw dispatched : Json) : Bool :=
  if test.ok then dispatched == raw
  else
    let message := (raw.getString? "error").getD ""
    if test.id == "parse-error" then
      dispatched == .object [("ok", .bool false), ("error", .string message),
        ("code", .string "reason.failed")]
    else
      dispatched == .object [("ok", .bool false), ("error", .string message),
        ("code", .string "owl.unsupported-rdf12"),
        ("spec", .string "https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification")]

def observed (test : Case) : Option (Bool × Option Bool × Bool × Bool) := do
  let response ← (parseJson (owlIsConsistent test.input test.opts)).toOption
  let dispatched ← (parseJson (dispatchResponse test)).toOption
  let ok ← response.getBool? "ok"
  let field := response.field? "consistent"
  let agreesWithDataset := match parseNQuadsFast test.input .rdf12 with
    | .error _ => true
    | .ok ds => owlIsConsistentOf ds test.opts == owlIsConsistent test.input test.opts
  let agreesWithDispatch := dispatchMatches test response dispatched
  let shape := if ok then
      field == some .null || field == some (.bool false) ||
        (field == some (.bool true) && (response.field? "reason").isNone)
    else (response.getString? "error").isSome && field.isNone
  let reason := test.reasonPrefix == "" ||
    ((response.getString? "reason").getD "").startsWith test.reasonPrefix
  pure (ok, response.getBool? "consistent", shape && reason,
    agreesWithDataset && agreesWithDispatch)

def passed (test : Case) : Bool :=
  observed test == some (test.ok, test.consistent, true, true)

def report (test : Case) : Lean.Json := Lean.Json.mkObj [
  ("id", Lean.toJson test.id), ("input", Lean.toJson test.input),
  ("options", Lean.toJson test.opts), ("expectedOk", Lean.toJson test.ok),
  ("expectedConsistent", Lean.toJson test.consistent),
  ("expectedReasonPrefix", Lean.toJson test.reasonPrefix),
  ("passed", Lean.toJson (passed test)),
  ("response", Lean.toJson (owlIsConsistent test.input test.opts)),
  ("dispatchResponse", Lean.toJson (dispatchResponse test)),
  ("adapterAgrees", Lean.toJson ((observed test).map (fun (_, _, _, same) => same)))]

#eval IO.println ("OWL_PUBLIC_BOUNDARY=" ++ (Lean.toJson (cases.map report)).compress)
#guard cases.length == 23
#guard cases.all passed

#print axioms L4Wasm.Ops.owlConsistencyJson_sound
#print axioms L4Wasm.Ops.owlConsistencyJson_success_schema
#print axioms L4Wasm.Ops.owlConsistencyJson_refusal_schema
#print axioms L4Wasm.Ops.owlConsistencyJson_unique_fields
#print axioms L4Wasm.Ops.owlEntailsJson_false_sound
#print axioms L4Factoidal.OWL.AtomicModel.checkModel_sound
#print axioms L4Factoidal.OWL.AtomicModel.checkCountermodel_sound
#print axioms L4Factoidal.OWL.AtomicModel.decideFuel_sound
#print axioms L4Factoidal.OWL.AtomicModel.entailsFuel_sound
#print axioms L4Wasm.Ops.owlIsConsistentParsed_certified
#print axioms L4Wasm.Ops.owlIsConsistent_certified

end OwlPublicBoundary
