/-
L4Factoidal.RML.Model — the mapping document, as a value.

Spec: RML-Core (https://w3id.org/rml/core/spec). A mapping is a set of
TRIPLES MAPS; each names a LOGICAL SOURCE, a SUBJECT MAP, and
PREDICATE-OBJECT MAPS.

The model is kept apart from the RDF graph it is read out of
(`RML/FromGraph.lean`) and from the evaluation that runs it
(`RML/Eval.lean`). That is not tidiness: a mapping graph is arbitrary
RDF and reading it can fail in many ways, while evaluation is a total
function of a mapping and a source, and mixing the two would make
"this mapping is malformed" and "this record has no value" the same
kind of answer.
-/
import L4Factoidal.RML.Mapping

namespace L4Factoidal.RML

/-! ## Reference formulation IRIs -/

def jsonPathIri : String := "http://w3id.org/rml/JSONPath"
def csvIri : String := "http://w3id.org/rml/CSV"
def xpathIri : String := "http://w3id.org/rml/XPath"
/-- `formats:SPARQL_Results_CSV`, the formulation of RMLSTC0003. -/
def sparqlResultsCsvIri : String := "http://www.w3.org/ns/formats/SPARQL_Results_CSV"

/-- `rml:logicalSource` — where the records come from.

    Two logical sources are "effectively equal" (RML-Core, Joins) when
    every field below is equal, so the structure holds nothing but
    effective properties: the NAME of the source node is not a field. -/
structure LogicalSource where
  /-- `rml:path` of the `rml:FilePath` or `rml:RelativePathSource`. -/
  path           : String := ""
  /-- `rml:iterator` — the expression that cuts the document into
      records. Absent means the whole document is one record. -/
  iterator       : Option String := none
  /-- `rml:referenceFormulation`, as an IRI. -/
  refFormulation : String := ""
  /-- `rml:root`: the IRI `rml:MappingDirectory` or
      `rml:CurrentWorkingDirectory`, or the text of a literal naming an
      absolute directory. Empty when the source states none (RML-IO:
      the current working directory). -/
  root           : String := ""
  /-- `rml:encoding`, as an IRI; empty means UTF-8. -/
  encoding       : String := ""
  /-- `rml:compression`, as an IRI; empty means none. -/
  compression    : String := ""
  /-- Every `rml:null` value of the source. -/
  nulls          : List String := []
  /-- XPath namespace declarations (`rml:namespace`): prefix and URL. -/
  namespaces     : List (String × String) := []
  /-- Not a file: a relational database, or a source this port has no
      access description for. The class IRI of the source node. -/
  accessKind     : String := ""
deriving Repr, Inhabited, BEq

/-- An OBJECT map: either a term map, or a reference to another
    triples map with join conditions.

    The two are not variants of one thing. A term map produces a term
    from THIS record; a `rml:RefObjectMap` produces the SUBJECTS of
    another triples map's records, filtered by the joins. Modelling
    the second as a term map with extra fields would hide that it
    reads a different source. -/
inductive ObjectMap where
  | term (base : TermMap) (datatypeMap : Option TermMap) (languageMap : Option TermMap)
  | ref  (parent : String) (joins : List JoinCondition)
deriving Repr

structure PredicateObjectMap where
  predicates : List TermMap := []
  objects    : List ObjectMap := []
  graphs     : List TermMap := []
deriving Repr

structure TriplesMap where
  /-- The IRI (or blank-node label) the mapping graph gives it —
      what a `rml:parentTriplesMap` names. -/
  id       : String
  /-- `rml:baseIRI` — what a RELATIVE result resolves against. -/
  base     : Option String := none
  source   : LogicalSource := {}
  subject  : TermMap
  /-- `rml:class` on the subject map. -/
  classes  : List String := []
  /-- `rml:graph` / `rml:graphMap` on the SUBJECT map: they apply to
      every triple the map generates, not only to the type triples. -/
  graphs   : List TermMap := []
  poms     : List PredicateObjectMap := []
  /-- RML-star: an `rml:AssertedTriplesMap` (or a plain `rml:TriplesMap`)
      puts the triples it generates in the output graph; an
      `rml:NonAssertedTriplesMap` generates them only as quoted triples,
      for the star maps that name it. -/
  asserted : Bool := true
deriving Repr

abbrev Mapping := List TriplesMap

/-- `rml:LogicalTarget` (RML-IO): where the triples generated with a
    term map are exported, and how. -/
structure LogicalTarget where
  /-- The node that names the target; what a term map's
      `rml:logicalTarget` points at. -/
  id            : String
  /-- `rml:path` of the target's `rml:FilePath`. -/
  path          : String := ""
  /-- `rml:root`, as for a source. -/
  root          : String := ""
  /-- `rml:serialization`, a `formats:` IRI; empty means N-Quads, the
      default of RML-IO "Serialization formats". -/
  serialization : String := ""
  /-- `rml:compression`; empty means none. -/
  compression   : String := ""
  /-- `rml:encoding`; empty means UTF-8. -/
  encoding      : String := ""
  /-- Not a file (a SPARQL endpoint, a void dataset...): the class
      IRIs of the target access description that this port has no
      access for. Empty for a file. -/
  accessKind    : String := ""
deriving Repr, Inhabited, BEq

end L4Factoidal.RML
