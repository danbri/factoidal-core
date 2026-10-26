/-
L4Factoidal.Solid.Client.Responses — interpret a server's response.

Wraps: `L4Factoidal.Solid.Client.Discovery` (the `Link` field reader).
Adds: the reading of the status code, `Location`, `Allow`, the `Accept-*`
fields and `WAC-Allow`.

Source: https://solidproject.org/TR/protocol, verbatim:

§5.2: "Servers MUST indicate the HTTP methods supported by the target
resource by generating an Allow header field in successful responses."
"When responding to authorized requests, servers MUST indicate supported
media types in the HTTP Accept-Patch, Accept-Post and Accept-Put response
header fields."

§2.2: "When a client receives a response with a 403 or 404 status code, the
client MAY repeat the request with different credentials."

Web Access Control §6.1, verbatim:

  "wac-allow = \"WAC-Allow\" \":\" OWS #access-param OWS
   access-param = permission-group OWS \"=\" OWS access-modes
   access-modes = DQUOTE OWS *1(access-mode *(RWS access-mode)) OWS DQUOTE
   access-mode = \"read\" / \"write\" / \"append\" / \"control\""

  "Client parsing algorithms for WAC-Allow header field-values MUST
  incorporate error handling. When the received message fails to match an
  allowed pattern, clients MUST ignore the received WAC-Allow header-field.
  When unrecognised access parameters (such as permission groups or access
  modes) are found, clients MUST continue processing the access parameters
  as if those properties were not present."

That last rule is why `parseWacAllow` returns a list of recognised
(group, modes) pairs and silently drops everything else, rather than
failing.

Each `interpretation` here is what the `solidClientResponse` wasm operation
answers; the members are named in `docs/lws-solid-conformance.md` § wasm
ABI.
-/
import L4Factoidal.Solid.Client.Discovery
import L4Factoidal.Solid.Server.Representation

namespace L4Factoidal.Solid.Client

open L4Factoidal.LWS
open L4Factoidal.HTTP (Response)

private def trim2 (s : String) : String :=
  String.ofList
    (((s.toList.dropWhile (fun c => c == ' ' || c == '\t')).reverse.dropWhile
        (fun c => c == ' ' || c == '\t')).reverse)

/-- Look a header field up by name. RFC 9110 §5.1: "Field names are
case-insensitive", so a host that reports `Last-Modified` and one that
reports `last-modified` are read the same way. -/
def headerOf (resp : Response) (name : String) : Option String :=
  (resp.headers.find? (fun (k, _) => k.toLower == name.toLower)).map (·.2)

/-! ## Status -/

def isSuccess (resp : Response) : Bool := resp.status ≥ 200 && resp.status < 300

/-- §2.2: "When a client receives a response with a 403 or 404 status code,
the client MAY repeat the request with different credentials." -/
def mayRetryWithCredentials (resp : Response) : Bool :=
  resp.status == 401 || resp.status == 403 || resp.status == 404

/-! ## Communication options -/

/-- The methods the server said it supports, from `Allow`. -/
def allowedMethodsOf (resp : Response) : List String :=
  match headerOf resp "allow" with
  | none => []
  | some v => (v.splitOn ",").map trim2

/-- The media types a PATCH, POST or PUT may carry, from `Accept-Patch`,
`Accept-Post` and `Accept-Put`. -/
def acceptedTypesOf (resp : Response) (field : String) : List String :=
  match headerOf resp field with
  | none => []
  | some v => (v.splitOn ",").map trim2

/-! ## Creation -/

/-- The URI the server assigned, from `Location`. §5.1: "When a successful
POST request creates a resource, the server MUST assign a URI to that
resource." -/
def createdLocation? (resp : Response) : Option String :=
  if resp.status == 201 then headerOf resp "location" else none

/-! ## Access privileges -/

/-- The recognised access modes of Web Access Control §6.1. -/
def wacModeNames : List String := ["read", "write", "append", "control"]

/-- Parse a `WAC-Allow` field value into recognised (group, modes) pairs.
Unrecognised access modes are dropped; a group whose value is not quoted
does not match the pattern, so it is dropped too. -/
def parseWacAllow (v : String) : List (String × List String) :=
  (v.splitOn ",").filterMap (fun param =>
    match (trim2 param).splitOn "=" with
    | [g, modes] =>
        let g := trim2 g
        let m := trim2 modes
        if m.startsWith "\"" && m.endsWith "\"" && m.length ≥ 2 then
          let inner := String.ofList ((m.toList.drop 1).dropLast)
          let names := (inner.splitOn " ").map trim2
          some (g, names.filter (fun n => wacModeNames.contains n))
        else none
    | _ => none)

/-- The modes granted to the requesting agent (`user`) and to the public. -/
def wacAllowOf (resp : Response) : List (String × List String) :=
  match headerOf resp "wac-allow" with
  | none => []
  | some v => parseWacAllow v

def wacGranted (resp : Response) (group mode : String) : Bool :=
  ((wacAllowOf resp).find? (fun (g, _) => g == group)).any (fun (_, ms) => ms.contains mode)

/-! ## Auxiliaries and storage -/

/-- What a HEAD or GET on a resource tells a client about it. -/
structure ResourceFacts where
  isStorage : Bool
  acl : Option String
  describedBy : Option String
  inbox : Option String
  storageDescription : Option String
  owner : Option String
  lastModified : Option String
  allow : List String
deriving Repr

def resourceFacts (resp : Response) : ResourceFacts :=
  { isStorage := Client.isStorage resp
  , acl := aclOf? resp
  , describedBy := describedByOf? resp
  , inbox := inboxOf? resp
  , storageDescription := storageDescriptionOf? resp
  , owner := ownerOf? resp
  , lastModified := headerOf resp "last-modified"
  , allow := allowedMethodsOf resp }

/-- What a reply tells a client that is walking up to the storage: the facts
of the resource, plus where the walk stands.

`target?` is the resource the reply answers; a caller that does not name it
gets the facts and no walk, because §4.1's rule is about the path hierarchy
of a named resource. -/
structure StorageReading where
  facts : ResourceFacts
  /-- The resource whose reply carried the storage type link. -/
  storage : Option String
  /-- Is a further request part of this operation? -/
  more : Bool
  /-- The resource to ask for next, when `more` is true. -/
  next : Option String
deriving Repr

def storageReading (target? : Option String) (resp : Response) : StorageReading :=
  let f := resourceFacts resp
  match target? with
  | none => { facts := f, storage := none, more := false, next := none }
  | some t =>
      let s := storageStepOf t resp
      { facts := f, storage := s.storage, more := s.next.isSome, next := s.next }

/-! ## Containment — §4.2

"Clients can determine the containment of a container by its containment
triples": the `ldp:contains` triples of the container's representation.

RFC 3986 §5.1.3: the base IRI of a retrieved representation is the URI it
was retrieved from. Community Solid Server writes members as relative
references (`<one>`), so a reading with no base parses nothing and reported
an empty container (2026-10-21, against Community Solid Server 7.2).
`base` is the request URI; the host passes it as `requestUri`. -/
def containmentMembers (base : Option String) (resp : Response) : List String :=
  let media := ((headerOf resp "content-type").map (fun c => trim2 ((c.splitOn ";").headD c))).getD
                 Server.mediaTurtle
  let media := if Server.isRdfSourceMedia media then media else Server.mediaTurtle
  let g := match base with
    | some b => Server.readRdfSource media b resp.body
    | none =>
        match L4Factoidal.Syntax.parseTurtle resp.body none .rdf11 with
        | .ok g => some g
        | .error _ => none
  (g.getD []).filterMap (fun t =>
    if t.p.val == "http://www.w3.org/ns/ldp#contains" then
      match t.o with | .iri i => some i.val | _ => none
    else none)

-- Relative members resolve against the request URI.
#guard containmentMembers (some "http://pod.example/c/")
  { status := 200, headers := [("content-type", "text/turtle")],
    body := "@prefix ldp: <http://www.w3.org/ns/ldp#>. <> ldp:contains <one>, <two/>." } ==
  ["http://pod.example/c/one", "http://pod.example/c/two/"]
-- A JSON-LD listing is read as JSON-LD.
#guard containmentMembers (some "http://pod.example/c/")
  { status := 200, headers := [("content-type", "application/ld+json; charset=utf-8")],
    body := "{\"@id\":\"\",\"http://www.w3.org/ns/ldp#contains\":{\"@id\":\"one\"}}" } ==
  ["http://pod.example/c/one"]
-- Negative: no containment triple, no member; other predicates are not members.
#guard containmentMembers (some "http://pod.example/c/")
  { status := 200, headers := [("content-type", "text/turtle")],
    body := "<> <http://www.w3.org/2000/01/rdf-schema#seeAlso> <one>." } == []

end L4Factoidal.Solid.Client
