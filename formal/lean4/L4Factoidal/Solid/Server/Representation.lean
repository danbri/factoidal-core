/-
L4Factoidal.Solid.Server.Representation — the RDF representations a Solid
server writes, and the content negotiation between them.

Source: https://solidproject.org/TR/protocol (v0.11.0), verbatim:

§5.5: "When a server creates an RDF source on HTTP PUT, POST, or PATCH
requests, the server MUST satisfy GET requests on this resource when the
Accept header field requests text/turtle or application/ld+json."

So a resource stored as Turtle is also served as JSON-LD, and one stored as
JSON-LD is also served as Turtle. The choice between the two follows the
`Accept` field (RFC 9110 §12.5.1) through `HTTP.negotiate`; the stored media
type is listed first, so a tie or a wildcard keeps the stored bytes.

## The Turtle writer of this server

`solidTurtle` writes every IRI in full except under four fixed vocabulary
namespaces (`ldp:`, `stat:`, `xsd:`, `solid:`), whose local names hold no
`.`. The general writer `turtleOfGraphAuto` derives prefixes from the graph
and so writes a contained resource `<…/a/b.ttl>` as `ns1:b.ttl`. That is
valid Turtle (RDF 1.1 Turtle §6.5, `PN_LOCAL` admits `.` before the last
character), but rdflib.js, which the Solid community test suite
(solid-crud-tests) and most Solid applications use, reads `text/turtle`
with its Notation3 parser, and that parser reads the `.` as a path
operator: "Bad syntax: EOF found in middle of path syntax". Every container
listing of a storage with a dotted file name was unreadable to it
(2026-10-21: 7 of the suite's checks failed on it).
-/
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.Turtle
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSON.Serialize
import L4Factoidal.HTTP.Server

namespace L4Factoidal.Solid.Server

open L4Factoidal.RDF
open L4Factoidal.Syntax

def mediaTurtle : String := "text/turtle"
def mediaJsonLd : String := "application/ld+json"

/-- The prefixes `solidTurtle` uses. -/
def solidPrefixes : PrefixTable :=
  [ ("http://www.w3.org/ns/ldp#", "ldp:")
  , ("http://www.w3.org/ns/posix/stat#", "stat:")
  , ("http://www.w3.org/2001/XMLSchema#", "xsd:")
  , ("http://www.w3.org/ns/solid/terms#", "solid:") ]

/-- A graph as Turtle, with IRIs outside `solidPrefixes` written in full. -/
def solidTurtle (g : Graph) : String := turtleOfGraph solidPrefixes true g

/-- The RDF media types of §5.5. -/
def rdfSourceMedia : List String := [mediaTurtle, mediaJsonLd]

def isRdfSourceMedia (m : String) : Bool := rdfSourceMedia.contains m

/-- The media type a GET answers for an RDF source stored as `stored`. -/
def negotiateRdf (accept : Option String) (stored : String) : String :=
  match accept with
  | none => stored
  | some a =>
      (HTTP.negotiate a (stored :: rdfSourceMedia.filter (· != stored))).getD stored

/-- Read an RDF source. `none` when the body does not parse, or when a
JSON-LD body holds named graphs, which Turtle cannot carry. -/
def readRdfSource (media : String) (base : String) (body : String) : Option Graph :=
  if media == mediaTurtle then
    match parseTurtle body (some base) .rdf11 with
    | .ok g => some g
    | .error _ => none
  else if media == mediaJsonLd then
    match JSONLD.parseJsonLd JSONLD.Loader.none body (some base) none none none with
    | .ok ds => if ds.named.isEmpty then some ds.default else none
    | .error _ => none
  else none

/-- Write a graph in one of the media types of §5.5. -/
def writeRdfSource (media : String) (g : Graph) : Option String :=
  if media == mediaTurtle then some (solidTurtle g)
  else if media == mediaJsonLd then
    (JSONLD.FromRdf.fromRdf { default := g, named := [] } {}).map JSON.toStringCompact
  else none

/-- The representation of a stored RDF source in media type `want`: the
stored body when `want` is the stored type, else the converted graph. -/
def convertRdfSource (stored want base body : String) : Option String :=
  if want == stored then some body
  else (readRdfSource stored base body).bind (writeRdfSource want)

/-- The entity tag of a converted representation. RFC 9110 §8.8.3: a strong
tag names one representation, so the JSON-LD form of a Turtle resource has a
tag of its own: the stored tag with a media suffix inside the quotes. -/
def convertedTag (stored want : String) : String :=
  let suffix := if want == mediaTurtle then "-ttl" else if want == mediaJsonLd then "-jsonld" else "-x"
  if stored.endsWith "\"" then String.ofList stored.toList.dropLast ++ suffix ++ "\""
  else stored ++ suffix

#guard convertedTag "\"17\"" mediaJsonLd == "\"17-jsonld\""
#guard convertedTag "\"17\"" mediaTurtle == "\"17-ttl\""

/-! ## Build-time checks -/

private def exBase : String := "http://pod.example/c/example.ttl"
private def exTurtle : String := "<#hello> <#linked> <#world> ."
private def exJson : String :=
  "{\"@context\":{\"name\":\"http://store.example.com/name\"}," ++
  "\"@id\":\"http://store.example.com/\",\"name\":\"Links Bike Shop\"}"

-- Turtle to JSON-LD keeps the triple, with the IRIs resolved against the base.
#guard (match convertRdfSource mediaTurtle mediaJsonLd exBase exTurtle with
        | some j => (readRdfSource mediaJsonLd exBase j).map (·.length) == some 1 &&
                    (j.splitOn "http://pod.example/c/example.ttl#world").length == 2
        | none => false)
-- JSON-LD to Turtle keeps the triple.
#guard (match convertRdfSource mediaJsonLd mediaTurtle exBase exJson with
        | some t => (readRdfSource mediaTurtle exBase t).map (·.length) == some 1
        | none => false)
-- The stored type is answered unchanged.
#guard convertRdfSource mediaTurtle mediaTurtle exBase "not turtle" == some "not turtle"
-- A body that does not parse has no other representation.
#guard convertRdfSource mediaTurtle mediaJsonLd exBase "<a" == none
#guard convertRdfSource "text/plain" mediaTurtle exBase "x" == none

-- Negotiation: the stored type wins ties and wildcards, the Accept field
-- picks the other type when it asks for it.
#guard negotiateRdf none mediaTurtle == mediaTurtle
#guard negotiateRdf (some "*/*") mediaJsonLd == mediaJsonLd
#guard negotiateRdf (some "application/ld+json") mediaTurtle == mediaJsonLd
#guard negotiateRdf (some "text/turtle") mediaJsonLd == mediaTurtle
#guard negotiateRdf (some "text/turtle;q=0.5, application/ld+json") mediaTurtle == mediaJsonLd
#guard negotiateRdf (some "text/html") mediaTurtle == mediaTurtle

-- A contained IRI with a dot in its last segment is written in full, so a
-- Notation3 reader does not see a path operator; vocabulary terms keep
-- their prefix.
private def exIri (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://example.org/x", by simp [isIri, String.isEmpty]⟩
#guard
  let t := solidTurtle [{ s := .iri (exIri "http://pod.example/a/"),
                          p := exIri "http://www.w3.org/ns/ldp#contains",
                          o := .iri (exIri "http://pod.example/a/b.ttl") }]
  (t.splitOn "<http://pod.example/a/b.ttl>").length == 2 &&
  (t.splitOn "ldp:contains").length == 2 &&
  (t.splitOn "ns1:").length == 1

end L4Factoidal.Solid.Server
