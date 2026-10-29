/-
L4Factoidal.WebAnnotation.Vocab — the Web Annotation Vocabulary
(Recommendation, 2017-02-23) and the JSON-LD serialisation of the Data
Model (Recommendation, 2017-02-23, §1.3 and Appendix A), on the existing
JSON-LD 1.1, RDF 1.1 syntax and isomorphism code. No algorithm here is a
second copy of one of those.

The W3C vocabulary tests (`annotation-vocab/` of web-platform-tests,
vendored in `third_party/testing/web-annotation/annotation-vocab/`) are six
manual pages. Each states a check; this module gives each a Lean function:

1. `01-validJSON-LD`: the sample expands with the `anno.jsonld` context
   (`expandWa`).
2. `02-context-to-triples`: the context converts the sample to RDF triples
   (`toRdfWa`, JSON-LD 1.1 API §8.2 Deserialize JSON-LD to RDF).
3. `03-graphs-are-isomorphic`: the graph written as N-Triples, Turtle and
   RDF/XML and read back is isomorphic to the graph (RDF 1.1 Concepts §3.6)
   in each syntax (`syntaxRoundTrips`).
4. `04-graphs-convert-lossless`: the graph converted back to JSON-LD
   (§8.4 Serialize RDF as JSON-LD, then §6 compaction with the context)
   gives an isomorphic graph again (`jsonLdRoundTrip`). The page asks "Is
   the content the same?"; the comparison is of the RDF graphs, because
   the compacted JSON can differ in member order and array form with no
   difference in what it says.
5. `05-ontology-parsed-as-valid`: `oa.ttl` parses (`parseOntologyTurtle`).
6. `06-ontology-internally-consistent`: every `rdfs:domain` and
   `rdfs:range` of the ontology names a class the ontology declares, or a
   datatype of RDF 1.1 Concepts §5 (`domainRangeProblems`).

The context and the ontology are given by the caller (the harness reads
the vendored copies in `third_party/testing/web-annotation/w3c-ns/`); the
library reads no file and no network.
-/
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Loader
import L4Factoidal.JSON.Serialize
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.RdfXmlWrite
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.WebAnnotation

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Data Model §1.3: the JSON-LD context IRI. The Recommendation writes it
    with `http`; the same document is served at `https`. -/
def annoContextIri : String := "http://www.w3.org/ns/anno.jsonld"

/-- The IRIs at which a document can cite the context. -/
def annoContextIris : List String :=
  [annoContextIri, "https://www.w3.org/ns/anno.jsonld"]

/-- Annotation Protocol §4: the LDP context that containers also cite. -/
def ldpContextIris : List String :=
  ["http://www.w3.org/ns/ldp.jsonld", "https://www.w3.org/ns/ldp.jsonld"]

/-- A JSON-LD document loader that knows the two contexts, given their
    texts, and nothing else (an unknown IRI is `none`, which JSON-LD
    processing turns into `loading remote context failed`). -/
def waLoader (annoCtx ldpCtx : String) : Loader :=
  tableLoader (annoContextIris.map (·, annoCtx) ++ ldpContextIris.map (·, ldpCtx))

/-- Vocabulary test 1: JSON-LD 1.1 API §5.1 expansion. -/
def expandWa (loader : Loader) (doc : Json) : Res Json :=
  expandRoot loader doc none none none

/-- Vocabulary test 2: JSON-LD 1.1 API §8.2, JSON-LD to RDF. -/
def toRdfWa (loader : Loader) (doc : Json) : Res Dataset :=
  parseJsonLdRoot loader doc none none none none

/-- Why a round trip did not give an isomorphic graph. -/
inductive RoundTripError where
  | write (syntaxName : String) (detail : String)
  | read (syntaxName : String) (detail : String)
  | notIsomorphic (syntaxName : String)
  deriving Repr

def RoundTripError.render : RoundTripError → String
  | .write s d => s!"{s}: the writer refused the graph: {d}"
  | .read s d => s!"{s}: the reader refused the written text: {d}"
  | .notIsomorphic s => s!"{s}: the graph read back is not isomorphic to the graph written"

/-- Write a graph in one syntax, read it back, compare. -/
def roundTripIn (name : String) (write : Graph → Except String String)
    (read : String → Except String Graph) (g : Graph) : Except RoundTripError Unit :=
  match write g with
  | .error e => .error (.write name e)
  | .ok text =>
    match read text with
    | .error e => .error (.read name e)
    | .ok g' => if g.isomorphic? g' then .ok () else .error (.notIsomorphic name)

private def errStr {ε α : Type} [Repr ε] : Except ε α → Except String α
  | .ok a => .ok a
  | .error e => .error (reprStr e)

/-- Vocabulary test 3: N-Triples, Turtle and RDF/XML (RDF 1.1). The list
    gives the syntaxes whose round trip did not give an isomorphic graph. -/
def syntaxRoundTrips (g : Graph) : List RoundTripError :=
  let checks : List (Except RoundTripError Unit) :=
    [ roundTripIn "N-Triples" (fun g => Graph.toNTriples g) (fun t => errStr (parseNTriples t)) g,
      roundTripIn "Turtle" (fun g => .ok (turtleOfGraphAuto g)) (fun t => errStr (parseTurtle t)) g,
      roundTripIn "RDF/XML" RdfXmlWrite.graphToRdfXml (fun t => errStr (RdfXml.parseRdfXml t)) g ]
  checks.filterMap (fun c => match c with
    | .error e => some e
    | .ok () => none)

/-- The compaction context document `{"@context": "<anno.jsonld IRI>"}`. -/
def annoContextDocument : String := "{\"@context\": \"" ++ annoContextIri ++ "\"}"

/-- Vocabulary test 4: RDF to JSON-LD (§8.4), compacted with the context
    (§6), back to RDF (§8.2); the result must be isomorphic to `ds`. -/
def jsonLdRoundTrip (loader : Loader) (ds : Dataset) : Except String Unit :=
  match FromRdf.fromRdf ds FromRdf.defaultOptions with
  | none => .error "RDF to JSON-LD refused the dataset"
  | some expanded =>
    match compactDocument loader expanded.toString annoContextDocument none
            (some annoContextIri) true false none with
    | .error e => .error s!"compaction failed: {reprStr e}"
    | .ok compacted =>
      match toRdfWa loader compacted with
      | .error e => .error s!"the compacted document does not convert to RDF: {reprStr e}"
      | .ok ds' => if ds.isomorphic? ds' then .ok ()
                   else .error "the dataset of the compacted document is not isomorphic"

/-! ## The ontology -/

def rdfType : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsDomain : String := "http://www.w3.org/2000/01/rdf-schema#domain"
def rdfsRange : String := "http://www.w3.org/2000/01/rdf-schema#range"
def rdfsClass : String := "http://www.w3.org/2000/01/rdf-schema#Class"
def owlClass : String := "http://www.w3.org/2002/07/owl#Class"

/-- Vocabulary §1.1: the `oa:` namespace. -/
def oaNs : String := "http://www.w3.org/ns/oa#"

/-- Vocabulary test 5: read `oa.ttl` (RDF 1.1 Turtle). The ontology's own
    IRI is the base. -/
def parseOntologyTurtle (text : String) : Except String Graph :=
  errStr (parseTurtle text (some oaNs))

/-- The datatypes of RDF 1.1 Concepts §5.1 (the XSD built-in types that are
    RDF-compatible), `rdf:langString`, `rdf:HTML`, `rdf:XMLLiteral`, and
    `rdfs:Literal`, which a range may name. -/
def knownDatatypes : List String :=
  let xsd := "http://www.w3.org/2001/XMLSchema#"
  (["string", "boolean", "decimal", "integer", "double", "float", "date", "time",
    "dateTime", "dateTimeStamp", "gYear", "gMonth", "gDay", "gYearMonth", "gMonthDay",
    "duration", "yearMonthDuration", "dayTimeDuration", "byte", "short", "int", "long",
    "unsignedByte", "unsignedShort", "unsignedInt", "unsignedLong", "positiveInteger",
    "nonNegativeInteger", "negativeInteger", "nonPositiveInteger", "hexBinary",
    "base64Binary", "anyURI", "language", "normalizedString", "token", "NMTOKEN",
    "Name", "NCName"].map (xsd ++ ·)) ++
  ["http://www.w3.org/1999/02/22-rdf-syntax-ns#langString",
   "http://www.w3.org/1999/02/22-rdf-syntax-ns#HTML",
   "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral",
   "http://www.w3.org/2000/01/rdf-schema#Literal"]

/-- The IRIs the ontology types as `rdfs:Class` or `owl:Class`. -/
def declaredClasses (g : Graph) : List String :=
  g.filterMap (fun t =>
    match t.s, t.o with
    | .iri s, .iri o =>
      if t.p.val == rdfType && (o.val == rdfsClass || o.val == owlClass) then some s.val else none
    | _, _ => none)

/-- Vocabulary test 6: each `(property, domain or range, object)` whose
    object is neither a declared class nor a known datatype. An object that
    is not an IRI is reported too. -/
def domainRangeProblems (g : Graph) : List (String × String × String) :=
  let classes := declaredClasses g
  g.filterMap (fun t =>
    if t.p.val == rdfsDomain || t.p.val == rdfsRange then
      let subj := match t.s with
        | .iri s => s.val
        | .bnode _ => "_:b"
      let which := if t.p.val == rdfsDomain then "domain" else "range"
      match t.o with
      | .iri o =>
        if classes.contains o.val || (which == "range" && knownDatatypes.contains o.val) then none
        else some (subj, which, o.val)
      | _ => some (subj, which, "(not an IRI)")
    else none)

end L4Factoidal.WebAnnotation
