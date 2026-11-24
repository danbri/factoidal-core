/- WDQS default prefix environment and parsing against the actual SPARQL AST.
The input prefix mappings match Wikimedia's Apache-2.0 Wikidata Query Rewriter,
WdqsPrefixes.java, commit e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74.
Explicit prologue declarations shadow these defaults, as in WDQS. -/
import L4Factoidal.SPARQL.Parser
namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.Syntax

def defaultPrefixes : List (String × String) := [
  ("wd", "http://www.wikidata.org/entity/"),
  ("wdt", "http://www.wikidata.org/prop/direct/"),
  ("wdtn", "http://www.wikidata.org/prop/direct-normalized/"),
  ("wds", "http://www.wikidata.org/entity/statement/"),
  ("wdv", "http://www.wikidata.org/value/"),
  ("wdref", "http://www.wikidata.org/reference/"),
  ("wdno", "http://www.wikidata.org/prop/novalue/"),
  ("wdata", "http://www.wikidata.org/wiki/Special:EntityData/"),
  ("p", "http://www.wikidata.org/prop/"),
  ("ps", "http://www.wikidata.org/prop/statement/"),
  ("psv", "http://www.wikidata.org/prop/statement/value/"),
  ("psn", "http://www.wikidata.org/prop/statement/value-normalized/"),
  ("pq", "http://www.wikidata.org/prop/qualifier/"),
  ("pqv", "http://www.wikidata.org/prop/qualifier/value/"),
  ("pqn", "http://www.wikidata.org/prop/qualifier/value-normalized/"),
  ("pr", "http://www.wikidata.org/prop/reference/"),
  ("prv", "http://www.wikidata.org/prop/reference/value/"),
  ("prn", "http://www.wikidata.org/prop/reference/value-normalized/"),
  ("wikibase", "http://wikiba.se/ontology#"),
  ("wikibaseqs", "http://wikiba.se/queryservice#"),
  ("wdsubgraph", "https://query.wikidata.org/subgraph/"),
  ("rdf", "http://www.w3.org/1999/02/22-rdf-syntax-ns#"),
  ("rdfs", "http://www.w3.org/2000/01/rdf-schema#"),
  ("owl", "http://www.w3.org/2002/07/owl#"),
  ("skos", "http://www.w3.org/2004/02/skos/core#"),
  ("schema", "http://schema.org/"),
  ("xsd", "http://www.w3.org/2001/XMLSchema#"),
  ("prov", "http://www.w3.org/ns/prov#"),
  ("cc", "http://creativecommons.org/ns#"),
  ("dc", "http://purl.org/dc/elements/1.1/"),
  ("dct", "http://purl.org/dc/terms/"),
  ("ontolex", "http://www.w3.org/ns/lemon/ontolex#"),
  ("geo", "http://www.opengis.net/ont/geosparql#"),
  ("geof", "http://www.opengis.net/def/geosparql/function/"),
  ("bd", "http://www.bigdata.com/rdf#"),
  ("gas", "http://www.bigdata.com/rdf/gas#"),
  ("hint", "http://www.bigdata.com/queryHints#"),
  ("mwapi", "https://www.mediawiki.org/ontology#API/")
]

/-- Uses the shipping tokenizer and parser, with WDQS prefixes as the initial
state; errors retain offsets in the original input. No network is accessed. -/
def parseWithFuel (fuel : Nat) (text : String) (base : Option String)
    (version : SparqlVersion) : Except ParseError Query :=
  let toks := tokenizeAt version text
  match firstInvalidToken toks with
  | some e => .error e
  | none =>
    match pSelectQuery fuel { prefixes := defaultPrefixes, v12 := version.is12 } base toks with
    | .error e => .error e
    | .ok (q, rest) =>
      if !tokensOnlyEof rest then .error ⟨"unexpected tokens after query", peekPos rest⟩
      else if !validateBnodeScopeTop q then
        .error ⟨"blank node label reused across graph-pattern scope", 0⟩
      else .ok q

/-- Parse WDQS syntax while retaining property paths for rewrite analysis. -/
def parseQuerySyntax (text : String) (base : Option String := none)
    (version : SparqlVersion := .v11) : Except ParseError Query :=
  match parseWithFuel topFuel text base version with
  | .ok q => .ok q
  | .error e =>
    match parseWithFuel (scaledFuel text) text base version with
    | .ok q => .ok q
    | .error _ => .error e

/-- Same retry and path-alternative lowering as `parseSparql`. -/
def parseQuery (text : String) (base : Option String := none)
    (version : SparqlVersion := .v11) : Except ParseError Query :=
  (parseQuerySyntax text base version).map (·.expandIriAlternatives)

#guard (parseQuery "SELECT * WHERE { wd:Q42 wdt:P31 ?o }").isOk
#guard (match parseQuery "SELECT * WHERE { noSuchPrefix:foo ?p ?o }" with | .error _ => true | .ok _ => false)
#guard (match parseQuery "PREFIX wd: <http://example.org/> SELECT * WHERE { wd:Q42 ?p ?o }" with
  | .ok q => (q.toSse.splitOn "http://example.org/Q42").length == 2
  | .error _ => false)
end L4Factoidal.Wikidata
