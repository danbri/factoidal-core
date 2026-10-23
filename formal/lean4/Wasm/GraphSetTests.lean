/-
Wasm.GraphSetTests — build-time checks that a parsed document is a SET of
quads.

RDF 1.1 Concepts and Abstract Syntax, section 3: "An RDF graph is a set of RDF
triples." Section 4: an RDF dataset is a default graph and a set of named
graphs, each a pair of a name and a graph. So a document that states one triple
two times denotes a graph with one triple. These checks go through the parse
that `datasetOpen` uses (`parseDocumentOutcome`, the full dispatch with
JSON-LD), the parse that the command line uses (`parseTextToDataset`), the
quad count of the envelope, a SPARQL `COUNT(*)`, the N-Quads writer of
`datasetSerialize`, and SPARQL 1.1 Update `INSERT DATA` of a triple that is
already in the graph (SPARQL 1.1 Update section 3.1.1: the data is added to
the graph, and adding a triple that the graph has does not change the graph).

A triple in two different graphs is two quads: the default graph and a named
graph, or two named graphs, are different graphs of the dataset.
-/
import Wasm.Ops.Handles
import Wasm.Ops.ParseJsonLd

namespace L4Wasm.GraphSetTests

open L4Factoidal.RDF
open L4Wasm.Ops

/-- The dataset `datasetOpen` stores for a document, before the blank-node
scope (these documents have no blank node). -/
def opened (fmt text : String) : Option Dataset :=
  (parseDocumentOutcome text fmt "").toOption.map (·.ds)

/-- The quad count of the `datasetOpen` envelope. -/
def openCount (fmt text : String) : Option Nat := (opened fmt text).map datasetQuadCount

/-- The quad count of the dataset that the command line reads. -/
def cliCount (fmt text : String) : Option Nat :=
  (parseTextToDataset text fmt "").toOption.map datasetQuadCount

/-- The `COUNT(*)` over every graph of the dataset, as the text of the
binding. -/
def countStar (fmt text : String) : Option Bool :=
  (opened fmt text).map fun ds =>
    let r := queryParsedDataset ds
      "SELECT (COUNT(*) AS ?n) WHERE { { ?s ?p ?o } UNION { GRAPH ?g { ?s ?p ?o } } }"
    (r.splitOn "\"value\":\"").length == 2 &&
      (r.splitOn "\"value\":\"").getLast!.startsWith "1\""

/-- The N-Quads text of `datasetSerialize(h, "nquads")`. -/
def written (fmt text : String) : Option String :=
  (opened fmt text).bind fun ds =>
    match handleWriterText "nquads" ds with
    | some (.ok s) => some s
    | _ => none

/-- The quad count after `INSERT DATA` of `<http://e/a> <http://e/p> "v"`
into the default graph. -/
def countAfterInsert (fmt text : String) : Option Nat :=
  (opened fmt text).bind fun ds =>
    (applyUpdateText ds "INSERT DATA { <http://e/a> <http://e/p> \"v\" }").toOption.map
      datasetQuadCount

def line : String := "<http://e/a> <http://e/p> \"v\" .\n"
def lineG : String := "<http://e/a> <http://e/p> \"v\" <http://e/g> .\n"
def lineH : String := "<http://e/a> <http://e/p> \"v\" <http://e/h> .\n"

def ntDup : String := line ++ line
def ttlDup : String := "@prefix e: <http://e/> . e:a e:p \"v\" . e:a e:p \"v\" .\n"
def ttlDupList : String := "@prefix e: <http://e/> . e:a e:p \"v\", \"v\" .\n"
def nqDup : String := lineG ++ lineG
def nqTwoGraphs : String := lineG ++ lineG ++ lineH
def trigDup : String :=
  "@prefix e: <http://e/> . e:g { e:a e:p \"v\" . e:a e:p \"v\" } e:g { e:a e:p \"v\" }\n"
def trigDefaultAndNamed : String :=
  "@prefix e: <http://e/> . e:a e:p \"v\" . { e:a e:p \"v\" } e:g { e:a e:p \"v\" }\n"
def rdfXmlDup : String :=
  "<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" xmlns:e=\"http://e/\">" ++
  "<rdf:Description rdf:about=\"http://e/a\"><e:p>v</e:p><e:p>v</e:p></rdf:Description>" ++
  "<rdf:Description rdf:about=\"http://e/a\"><e:p>v</e:p></rdf:Description></rdf:RDF>"
def jsonLdDup : String := "{\"@id\":\"http://e/a\",\"http://e/p\":[\"v\",\"v\"]}"
def jsonLdNamedDup : String :=
  "[{\"@id\":\"http://e/g\",\"@graph\":[{\"@id\":\"http://e/a\",\"http://e/p\":\"v\"}]}," ++
  "{\"@id\":\"http://e/g\",\"@graph\":[{\"@id\":\"http://e/a\",\"http://e/p\":[\"v\",\"v\"]}]}]"

-- N-Triples: the same triple on two lines is one triple.
#guard openCount "ntriples" ntDup == some 1
#guard cliCount "ntriples" ntDup == some 1
#guard countStar "ntriples" ntDup == some true
#guard written "ntriples" ntDup == some line
#guard countAfterInsert "ntriples" ntDup == some 1
#guard countAfterInsert "ntriples" line == some 1

-- Turtle: two statements, and one object list with the object two times.
#guard openCount "turtle" ttlDup == some 1
#guard openCount "turtle" ttlDupList == some 1
#guard cliCount "turtle" ttlDup == some 1
#guard countStar "turtle" ttlDup == some true
#guard written "turtle" ttlDup == some line
#guard countAfterInsert "turtle" ttlDup == some 1

-- N-Quads: the same quad two times is one quad; the same triple in two
-- named graphs is two quads.
#guard openCount "nquads" nqDup == some 1
#guard countStar "nquads" nqDup == some true
#guard written "nquads" nqDup == some lineG
#guard openCount "nquads" nqTwoGraphs == some 2
#guard written "nquads" nqTwoGraphs == some (lineG ++ lineH)
#guard openCount "nquads" (line ++ lineG ++ line) == some 2

-- TriG: a repeated triple in one block and across two blocks of one graph is
-- one quad; the same triple in the default graph and in a named graph is two.
#guard openCount "trig" trigDup == some 1
#guard countStar "trig" trigDup == some true
#guard written "trig" trigDup == some lineG
#guard openCount "trig" trigDefaultAndNamed == some 2
#guard written "trig" trigDefaultAndNamed == some (line ++ lineG)

-- RDF/XML and JSON-LD.
#guard openCount "rdfxml" rdfXmlDup == some 1
#guard written "rdfxml" rdfXmlDup == some line
#guard countAfterInsert "rdfxml" rdfXmlDup == some 1
#guard openCount "jsonld" jsonLdDup == some 1
#guard written "jsonld" jsonLdDup == some line
#guard openCount "jsonld" jsonLdNamedDup == some 1
#guard written "jsonld" jsonLdNamedDup == some lineG

-- The lenient (recovery) parse gives the same set.
def lenientCount (fmt text : String) : Option Nat :=
  (lenientDocumentOutcomeBy jsonLdReader text fmt "" {}).toOption.map
    (fun r => datasetQuadCount r.1.ds)

#guard lenientCount "ntriples" ntDup == some 1
#guard lenientCount "turtle" ttlDup == some 1
#guard lenientCount "nquads" nqDup == some 1
#guard lenientCount "trig" trigDup == some 1

-- The first occurrence fixes the order: a, b, a is written a, b.
#guard written "ntriples"
    (line ++ "<http://e/b> <http://e/p> \"v\" .\n" ++ line) ==
  some (line ++ "<http://e/b> <http://e/p> \"v\" .\n")

end L4Wasm.GraphSetTests
