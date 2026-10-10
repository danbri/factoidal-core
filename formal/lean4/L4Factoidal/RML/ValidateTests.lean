/-
L4Factoidal.RML.ValidateTests — build-time checks for the rejections of
RML-Core: static validation of the mapping graph, strict templates,
and the data errors of term generation.

Every rejection has an accepting twin that differs from it by the one
clause under test, so a validator that rejects everything fails here as
surely as one that rejects nothing.
-/
import L4Factoidal.RML.Run
import L4Factoidal.RML.Tests
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.Syntax

/-! ## Strict templates (RML-Core, "Generating values with expressions") -/

private def tplOk (s : String) : Bool := (parseTemplateStrict s).toOption.isSome

#guard tplOk "http://ex/{id}"
#guard tplOk "plain"
#guard tplOk "{a}{b}"
#guard tplOk "x\\{y\\}z"
#guard tplOk "back\\\\slash {id}"
-- Braces and backslashes inside a reference expression are escaped too.
#guard tplOk "http://example.com/{$['\\{Name\\}']}"
-- The five shapes the specification forbids.
#guard !tplOk "http://example.com/{{Name}}"
#guard !tplOk "http://example.com/{Name"
#guard !tplOk "http://example.com/Name}"
#guard !tplOk "http://example.com/{}"
#guard !tplOk "a\\b"
#guard !tplOk "{\\\\{Name\\\\}}"
#guard !tplOk "ends with a backslash \\"

-- The strict parse and the lenient one agree on every valid template.
#guard (parseTemplateStrict "http://ex/{id}/{name}").toOption ==
       some (parseTemplate "http://ex/{id}/{name}")
#guard (parseTemplateStrict "x\\{y\\}z").toOption == some (parseTemplate "x\\{y\\}z")

/-! ## Data errors of term generation -/

private def rec1 : String → Option String
  | "id"   => some "7"
  | "name" => some "Zoë Krüger"
  | "bad"  => some "not an iri"
  | "tag"  => some "a-english"
  | "ok"   => some "en-GB"
  | "empty" => some ""
  | _      => none

private def isErr {α : Type} : Except RmlError α → Bool
  | .error _ => true
  | .ok _    => false

private def isNoTerm : Except RmlError (Option Term) → Bool
  | .ok none => true
  | _        => false

private def isTerm : Except RmlError (Option Term) → Bool
  | .ok (some _) => true
  | _            => false

-- A value that is not an IRI where one is required is a DATA ERROR, with
-- or without a base IRI; the old reading was "no term".
#guard isErr (generateTermE none { form := .reference "bad", termType := some .iri } rec1)
#guard isErr (generateTermE (some "http://example.com/")
                { form := .reference "bad", termType := some .iri } rec1)
#guard isErr (generateTermE none { form := .reference "name", termType := some .iri } rec1)
-- Its twin: a real IRI, and a relative one that a base completes.
#guard isTerm (generateTermE none
         { form := .template "http://ex/{id}", termType := some .iri } rec1)
#guard isTerm (generateTermE (some "http://example.com/")
         { form := .reference "id", termType := some .iri } rec1)
-- An unresolved reference and an empty value are NO TERM, not errors.
#guard isNoTerm (generateTermE none { form := .reference "missing", termType := some .iri } rec1)
#guard isNoTerm (generateTermE none { form := .reference "empty", termType := some .iri } rec1)
-- URI is stricter than IRI: non-ASCII is percent-encoded first, so the
-- result is a valid URI.
#guard isTerm (generateTermE none
         { form := .template "http://ex/{name}", termType := some .uri } rec1)
-- UnsafeIRI keeps the weak test: the specification's own example has a space.
#guard isTerm (generateTermE none
         { form := .template "http://ex/{name}", termType := some .unsafeIri } rec1)

-- An ill-formed language tag is a data error; a well-formed one is not.
#guard isErr (generateTermE none
         { form := .reference "name", language := some "a-english" } rec1)
#guard isTerm (generateTermE none
         { form := .reference "name", language := some "en-GB" } rec1)

-- An ill-typed datatype override is a data error; a well-typed one is not.
#guard isErr (generateTermE none
         { form := .reference "name",
           datatype := some "http://www.w3.org/2001/XMLSchema#integer" } rec1)
#guard isTerm (generateTermE none
         { form := .reference "id",
           datatype := some "http://www.w3.org/2001/XMLSchema#integer" } rec1)
-- A datatype this port does not model is not judged.
#guard isTerm (generateTermE none
         { form := .reference "name", datatype := some "http://example.com/dt" } rec1)

-- `generateTerm` keeps its old answer: an error reads as no term.
#guard generateTerm none { form := .reference "bad", termType := some .iri } rec1 == none

/-! ## A reference that selects an array or object (RMLTC0025b) -/

private def person : Json :=
  .object [("fname", .string "Bob"),
           ("amounts", .array [.number "30", .number "40"]),
           ("nick", .null),
           ("addr", .object [("city", .string "X")])]

#guard (refValuesE (Record.json person) "$.fname").2.isEmpty
#guard (refValuesE (Record.json person) "$.amounts[*]").2.isEmpty
#guard (refValuesE (Record.json person) "$.amounts[*]").1.length == 2
#guard (refValuesE (Record.json person) "$.amounts").2.length == 1
#guard (refValuesE (Record.json person) "$.addr").2.length == 1
-- `null` is Empty, not an error.
#guard (refValuesE (Record.json person) "$.nick").2.isEmpty
#guard (refValuesE (Record.json person) "$.nick").1.isEmpty
#guard (refValuesE (Record.json person) "$.absent").2.isEmpty

/-! ## Static validation of the mapping graph -/

private def graphOf (ttl : String) : Graph :=
  match parseTurtle ttl none with
  | .ok g    => g
  | .error _ => []

private def prefixes : String :=
  "@prefix rml: <http://w3id.org/rml/> .\n@prefix ex: <http://example.com/> .\n" ++
  "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n"

private def source : String :=
  "rml:logicalSource [ rml:source [ rml:path \"a.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$[*]\" ]"

/-- One triples map with the given subject map and predicate-object map. -/
private def mapping (subject pom : String) : String :=
  prefixes ++ s!"ex:tm a rml:TriplesMap ; {source} ; {subject} ; {pom} ."

private def goodSubject : String := "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ]"
private def goodPom : String :=
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ] ]"

private def valid (ttl : String) : Bool := (validateMapping (graphOf ttl)).isEmpty
private def invalid (ttl : String) : Bool := !(validateMapping (graphOf ttl)).isEmpty

-- The base mapping is valid, and the fixture graph is not empty.
#guard !(graphOf (mapping goodSubject goodPom)).isEmpty
#guard valid (mapping goodSubject goodPom)

-- Exactly one subject map.
#guard invalid (prefixes ++ s!"ex:tm a rml:TriplesMap ; {source} ; {goodPom} .")
#guard invalid (mapping (goodSubject ++ " ; rml:subjectMap [ rml:template \"http://example.com/{$.id}x\" ]") goodPom)
#guard valid (mapping "rml:subject ex:s" goodPom)

-- A subject map may not be a literal map (RMLTC0004b); its twin may be a blank-node map.
#guard invalid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ; rml:termType rml:Literal ]" goodPom)
#guard valid (mapping "rml:subjectMap [ rml:template \"{$.id}\" ; rml:termType rml:BlankNode ]" goodPom)
#guard valid (mapping "rml:subjectMap [ rml:termType rml:BlankNode ]" goodPom)

-- A constant subject must be an IRI (RMLTC0024a).
#guard invalid (mapping "rml:subjectMap [ rml:constant \"School\" ]" goodPom)
#guard valid (mapping "rml:subjectMap [ rml:constant ex:School ]" goodPom)

-- A graph map may not be a literal map (RMLTC0007h).
#guard invalid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ; rml:graphMap [ rml:reference \"$.id\" ; rml:termType rml:Literal ] ]" goodPom)
#guard valid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ; rml:graphMap [ rml:template \"http://example.com/g/{$.id}\" ] ]" goodPom)

-- An invalid JSONPath iterator (RMLTC0002g).
#guard invalid ((mapping goodSubject goodPom).replace "$[*]" "$[*]]")
-- Templates (RMLTC0023a, d).
#guard invalid (mapping "rml:subjectMap [ rml:template \"http://example.com/{{Name}}\" ]" goodPom)
#guard invalid (mapping "rml:subjectMap [ rml:template \"http://example.com/{Name\" ]" goodPom)
#guard valid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.Name}\" ]" goodPom)
-- A reference that is not a JSONPath.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.a[*]]\" ] ]")

-- A language tag (RMLTC0015b).
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ; rml:language \"a-english\" ] ]")
#guard valid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ; rml:language \"en\" ] ]")
-- A language or a datatype only on a literal map; and not both.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:template \"http://example.com/{$.id}\" ; rml:termType rml:IRI ; rml:language \"en\" ] ]")
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ; rml:language \"en\" ; rml:datatype xsd:string ] ]")
#guard valid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ; rml:datatype xsd:string ] ]")

-- A predicate-object map needs a predicate and an object.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:objectMap [ rml:reference \"$.name\" ] ]")
#guard invalid (mapping goodSubject "rml:predicateObjectMap [ rml:predicate ex:p ]")
-- A constant predicate must be an IRI, and a constant object may not be a blank node.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate \"p\" ; rml:objectMap [ rml:reference \"$.name\" ] ]")
-- A term map has at most one expression.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:reference \"$.name\" ; rml:template \"{$.name}\" ] ]")
-- ...and needs one, unless it is a blank-node map.
#guard invalid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:termType rml:Literal ] ]")
#guard valid (mapping goodSubject
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:termType rml:BlankNode ] ]")
-- rml:class values are IRIs.
#guard valid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ; rml:class ex:C ]" goodPom)
#guard invalid (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ; rml:class \"C\" ]" goodPom)

/-! ### Referencing object maps and joins -/

private def twoMaps (pom : String) (otherSource : String) : String :=
  prefixes ++
  s!"ex:tm a rml:TriplesMap ; {source} ; {goodSubject} ; {pom} .\n" ++
  "ex:parent a rml:TriplesMap ; " ++ otherSource ++
  " ; rml:subjectMap [ rml:template \"http://example.com/p/{$.id}\" ] ."

private def parentSame : String := source
private def parentOther : String :=
  "rml:logicalSource [ rml:source [ rml:path \"b.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$[*]\" ]"

private def refPom (joins : String) : String :=
  s!"rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:parentTriplesMap ex:parent {joins} ] ]"

private def oneJoin : String :=
  "; rml:joinCondition [ rml:child \"$.id\" ; rml:parent \"$.id\" ]"

-- Same logical source: no join is needed. Different source: one is.
#guard valid (twoMaps (refPom "") parentSame)
#guard invalid (twoMaps (refPom "") parentOther)
#guard valid (twoMaps (refPom oneJoin) parentOther)
-- A join condition needs both sides.
#guard invalid (twoMaps (refPom "; rml:joinCondition [ rml:child \"$.id\" ]") parentOther)
-- The parent must be a triples map of the document.
#guard invalid (prefixes ++
  s!"ex:tm a rml:TriplesMap ; {source} ; {goodSubject} ; " ++
  "rml:predicateObjectMap [ rml:predicate ex:p ; rml:objectMap [ rml:parentTriplesMap ex:nothing ] ] .")

/-! ## The run as a whole: validation first, then evaluation

`runMappingGraph` rejects a run with ANY error and returns no quads. -/

private def docs : String → Option Json := fun p =>
  if p == "a.json" then
    some (.array [.object [("id", .number "1"), ("name", .string "Ann"),
                           ("full", .string "Ann Lee")],
                  .object [("id", .number "2"), ("name", .string "Bob"),
                           ("full", .string "Bob Roe")]])
  else none

private def runOf (ttl : String) : EvalResult :=
  runMappingGraph (graphOf ttl) (some "http://example.com/") docs

#guard !(runOf (mapping goodSubject goodPom)).rejected
#guard (runOf (mapping goodSubject goodPom)).quads.length == 2
-- A missing source is a rejection (RMLTC0002e); its twin has the file.
#guard (runOf ((mapping goodSubject goodPom).replace "a.json" "missing.json")).rejected
-- A data error rejects the whole run and leaves no quads behind: a
-- name with a space is not an IRI as a reference, and is one as a
-- template, which percent-encodes it.
#guard (runOf (mapping "rml:subjectMap [ rml:reference \"$.full\" ]" goodPom)).rejected
#guard (runOf (mapping "rml:subjectMap [ rml:reference \"$.full\" ]" goodPom)).quads.isEmpty
#guard !(runOf (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.full}\" ]" goodPom)).rejected
#guard (runOf (mapping "rml:subjectMap [ rml:template \"http://example.com/{$.full}\" ]" goodPom)).quads.length == 2
-- A reference to an array rejects the run; the wildcard twin does not.
#guard (runOf ((mapping goodSubject goodPom).replace "$.name" "$")).rejected
-- A validation failure rejects before any record is read.
#guard (runOf (mapping "rml:subjectMap [ rml:template \"{{x}}\" ]" goodPom)).rejected

end L4Factoidal.RML
