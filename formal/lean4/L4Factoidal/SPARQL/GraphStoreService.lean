/-
L4Factoidal.SPARQL.GraphStoreService — the SPARQL 1.1 Graph Store HTTP
Protocol as one total function from a Graph Store and an HTTP request
to the new Graph Store and an HTTP response.

Spec: https://www.w3.org/TR/sparql11-http-rdf-update/

`SPARQL/GraphStore.lean` holds the store model and the five operations
on it. This module adds what a service needs on top of them:

  * graph identification relative to the service endpoint: §4.1 direct
    identification (a request path under the endpoint path names the
    graph whose IRI is the request IRI) and §4.2 indirect identification
    (`?graph=<IRI>`, decoded once; `?default` for the default graph);
    a request to the endpoint itself with neither parameter addresses
    the Graph Store, which only POST accepts (§5.5);
  * the RDF payload: `text/turtle` and `application/n-triples` are
    parsed with the request IRI as base; `multipart/form-data` (§5.5)
    is split into parts (`HTTP/Multipart.lean`) and each part parsed by
    its own Content-Type; any other media type is 415;
  * blank nodes are kept apart when graphs are merged (§5.5 "merge"):
    each part of a multipart payload, and every POSTed payload, has its
    blank-node labels prefixed with a stem no label of the graph it
    joins starts with (`freshPrefix`);
  * the status codes of §5: GET and HEAD 200, or 404 for an absent
    named graph; PUT 201 when it creates a graph and 204 when it
    replaces one; DELETE 204, or 404; POST to a graph 204, or 201 when
    it creates the graph; POST to the Graph Store creates a graph with a
    new IRI and answers 201 with that IRI in `Location` (§5.5: "return a
    designated graph IRI associated with the new graph … in the
    Location HTTP header along with a 201 Created code");
  * GET answers `text/turtle` (`Syntax.turtleOfGraphAuto`) or
    `application/n-triples`, chosen from `Accept` by
    `HTTP.negotiate`; 406 when neither is acceptable.

The default graph always exists (§5.2 GET of the default graph is 200,
possibly empty). This differs from `GraphStore.handle`, which models
the deprecated `http-rdf-update` suite's convention that an empty
default graph is absent.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.GraphStore
import L4Factoidal.HTTP.Server
import L4Factoidal.HTTP.Multipart
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.SPARQL.GraphStoreService

open L4Factoidal.RDF
open L4Factoidal.SPARQL.GraphStore
open L4Factoidal.SPARQL.Protocol

/-- The service endpoint: the URI authority and the path prefix of the
Graph Store (e.g. `www.example` and `/gsp`). -/
structure Endpoint where
  authority : String
  path      : String
  deriving Repr, DecidableEq

/-- The absolute IRI of a request path on this endpoint's authority. -/
def Endpoint.iriOf (ep : Endpoint) (path : String) : String :=
  "http://" ++ ep.authority ++ path

/-- What a request addresses. -/
inductive Resource where
  /-- The Graph Store itself (§5.5: POST creates a new graph). -/
  | store
  /-- One graph: the default graph or a named graph. -/
  | graph (t : Target)
  deriving DecidableEq, Repr

/-- §4.1 / §4.2 graph identification. On the endpoint path, `?default`
is the default graph and `?graph=<IRI>` the named graph (the value
decoded once; a value that is not an IRI is 400); with neither, the
Graph Store. A path under the endpoint path identifies the graph named
by the request IRI (direct identification). Any other path is 404. -/
def resolve (ep : Endpoint) (path qs : String) : Except Nat Resource :=
  let kvs := parseQueryString qs
  if path == ep.path || path == ep.path ++ "/" then
    if kvs.any (fun kv => kv.1 == "default") then .ok (.graph .default)
    else
      match firstValue "graph" kvs with
      | some g => if isIri g then .ok (.graph (.named g)) else .error 400
      | none   => .ok .store
  else if path.startsWith (ep.path ++ "/") then .ok (.graph (.named (ep.iriOf path)))
  else .error 404

/-! ## Blank nodes kept apart -/

/-- A label stem `stem ++ k ++ "_"` that no label in `labels` starts
with. Each label starts with at most one of the `labels.length + 1`
candidates (the candidates differ before their `_`), so one is free;
the fallback is never reached. -/
def freshPrefix (stem : String) (labels : List BNodeId) : String :=
  let cands := (List.range (labels.length + 1)).map (fun k => stem ++ toString k ++ "_")
  (cands.find? (fun c => !labels.any (fun l => l.startsWith c))).getD (stem ++ "_")

/-- Prefix every blank-node label of `g`. -/
def prefixBnodes (pre : String) (g : Graph) : Graph :=
  g.renameBnodes (fun b => pre ++ b)

/-- RDF merge of `g` into `into`: `g`'s blank nodes are renamed apart
from `into`'s first (RDF 1.1 Semantics §4.1, merge). -/
def mergeInto (into g : Graph) : Graph :=
  Graph.union into (prefixBnodes (freshPrefix "m" (Graph.bnodes into)) g)

/-! ## The payload -/

/-- Parse one RDF document by its media type. `none` is 415 (media type
not supported), an `Except.error` a payload that does not parse (400). -/
def parseRdfAs (mediaType base text : String) : Option (Except String Graph) :=
  if mediaType == "text/turtle" || mediaType == "application/x-turtle" then
    some ((Syntax.parseTurtle text (some base)).mapError (·.msg))
  else if mediaType == "application/n-triples" then
    some ((Syntax.parseNTriples text).mapError (·.msg))
  else none

/-- The graph a request body carries: one RDF document, or (§5.5) a
`multipart/form-data` body whose parts are RDF documents, merged with
their blank nodes kept apart. Error: the status code (400 or 415). -/
def payloadGraph (contentType base body : String) : Except Nat Graph :=
  let mt := contentTypeBase contentType
  if mt == "multipart/form-data" then
    match HTTP.Multipart.boundaryOf contentType with
    | none   => .error 400
    | some b =>
      match HTTP.Multipart.parseMultipart b body with
      | none       => .error 400
      | some parts =>
        let parsed := (parts.zip (List.range parts.length)).map (fun (p, i) =>
          match parseRdfAs (contentTypeBase (p.header "content-type")) base p.content with
          | none            => Except.error 415
          | some (.error _) => .error 400
          | some (.ok g)    => .ok (prefixBnodes ("part" ++ toString i ++ "_") g))
        match parsed.mapM id with
        | .error code => .error code
        | .ok gs      => .ok (gs.foldl Graph.union [])
  else
    match parseRdfAs mt base body with
    | none            => .error 415
    | some (.error _) => .error 400
    | some (.ok g)    => .ok g

/-! ## Responses -/

/-- The media types GET can answer with, in the service's order of
preference. -/
def getMediaTypes : List String := ["text/turtle", "application/n-triples"]

/-- A GET response carrying `g` in the negotiated media type. -/
def graphResponse (accept : String) (g : Graph) : HTTP.Response :=
  match HTTP.negotiate accept getMediaTypes with
  | some "application/n-triples" =>
    match Syntax.Graph.toNTriples g with
    | .ok text => { status := 200, headers := [("content-type", "application/n-triples")], body := text }
    | .error e => { status := 500, body := e }
  | some _ =>
    { status := 200, headers := [("content-type", "text/turtle; charset=utf-8")],
      body := Syntax.turtleOfGraphAuto g }
  | none => { status := 406 }

/-- A new graph IRI under the endpoint, not yet in the store: the
first `<endpoint>/graph-<k>` free, `k` from 1. One of the
`named.length + 1` candidates is free. -/
def freshGraphIri (ep : Endpoint) (s : GraphStore) : String :=
  let cands := (List.range (s.named.length + 1)).map (fun k =>
    ep.iriOf (ep.path ++ "/graph-" ++ toString (k + 1)))
  (cands.find? (fun c => !namedExists c s.named)).getD (ep.iriOf (ep.path ++ "/graph-0"))

/-- The named graph's content, `[]` when absent. -/
def namedOrEmpty (k : GraphKey) (s : GraphStore) : Graph :=
  (lookupNamed k s.named).getD []

/-! ## The service -/

/-- Execute one Graph Store request. `headers` are lower-cased names.
Returns the store after the request and the HTTP response. -/
def serve (ep : Endpoint) (s : GraphStore) (method path qs : String)
    (headers : List (String × String)) (body : String) : GraphStore × HTTP.Response :=
  let hdr (k : String) : String := (headers.find? (fun kv => kv.1 == k)).map (·.2) |>.getD ""
  let requestIri := ep.iriOf path ++ (if qs.isEmpty then "" else "?" ++ qs)
  match resolve ep path qs with
  | .error code => (s, { status := code })
  | .ok res =>
    match GraphStore.Method.ofString method, res with
    | some .get, .graph t =>
      match get t s with
      | some g => (s, graphResponse (hdr "accept") g)
      | none   => (s, { status := 404 })
    | some .head, .graph t =>
      match get t s with
      | some g => (s, { (graphResponse (hdr "accept") g) with body := "" })
      | none   => (s, { status := 404 })
    | some .put, .graph t =>
      match payloadGraph (hdr "content-type") requestIri body with
      | .error code => (s, { status := code })
      | .ok g =>
        let existed := match t with
                       | .default => true
                       | .named k => namedExists k s.named
        ((put t g s).1, { status := if existed then 204 else 201 })
    | some .delete, .graph t =>
      match t with
      | .default => ((delete t s).1, { status := 204 })
      | .named k =>
        if namedExists k s.named then ((delete t s).1, { status := 204 })
        else (s, { status := 404 })
    | some .post, .graph t =>
      match payloadGraph (hdr "content-type") requestIri body with
      | .error code => (s, { status := code })
      | .ok g =>
        match t with
        | .default => ({ s with default := mergeInto s.default g }, { status := 204 })
        | .named k =>
          let existed := namedExists k s.named
          ({ s with named := replaceNamed k (mergeInto (namedOrEmpty k s) g) s.named },
           { status := if existed then 204 else 201 })
    | some .post, .store =>
      match payloadGraph (hdr "content-type") requestIri body with
      | .error code => (s, { status := code })
      | .ok g =>
        let iri := freshGraphIri ep s
        ({ s with named := replaceNamed iri g s.named },
         { status := 201, headers := [("location", iri)] })
    | some _, .store => (s, { status := 405, headers := [("allow", "POST")] })
    | some .patch, .graph _ => (s, { status := 405, headers := [("allow", "GET, HEAD, PUT, DELETE, POST")] })
    | none, _ => (s, { status := 405, headers := [("allow", "GET, HEAD, PUT, DELETE, POST")] })

/-! ## Checks -/

private def ep0 : Endpoint := { authority := "www.example", path := "/gsp" }
private def ttl : List (String × String) := [("content-type", "text/turtle; charset=utf-8")]
private def doc1 : String := "<http://ex/s> <http://ex/p> \"a\" ."
private def doc2 : String := "<http://ex/s> <http://ex/p> \"b\" ."

private def resolveErr (r : Except Nat Resource) : Option Nat :=
  match r with
  | .error c => some c
  | .ok _    => none

-- §4.1 / §4.2: direct and indirect identification name the same graph.
#guard (resolve ep0 "/gsp/person/1.ttl" "").toOption ==
  some (.graph (.named "http://www.example/gsp/person/1.ttl"))
#guard (resolve ep0 "/gsp" "graph=http%3A%2F%2Fwww.example%2Fgsp%2Fperson%2F1.ttl").toOption ==
  some (.graph (.named "http://www.example/gsp/person/1.ttl"))
-- The value is decoded ONCE: %2531 becomes %31, not 1.
#guard (resolve ep0 "/gsp" "graph=http://www.example/gsp/person/%2531.ttl").toOption ==
  some (.graph (.named "http://www.example/gsp/person/%31.ttl"))
#guard (resolve ep0 "/gsp" "default").toOption == some (.graph .default)
#guard (resolve ep0 "/gsp" "").toOption == some .store
#guard resolveErr (resolve ep0 "/gsp" "graph=nocolon") == some 400
#guard resolveErr (resolve ep0 "/other/x" "") == some 404

-- PUT creates (201), PUT again replaces (204), GET returns the last
-- payload, DELETE removes (204), a second DELETE and a GET are 404.
#guard
  let (s1, r1) := serve ep0 {} "PUT" "/gsp/a" "" ttl doc1
  let (s2, r2) := serve ep0 s1 "PUT" "/gsp/a" "" ttl doc2
  let (_, r3) := serve ep0 s2 "GET" "/gsp/a" "" [] ""
  let (s4, r4) := serve ep0 s2 "DELETE" "/gsp/a" "" [] ""
  let (_, r5) := serve ep0 s4 "DELETE" "/gsp/a" "" [] ""
  let (_, r6) := serve ep0 s4 "GET" "/gsp/a" "" [] ""
  [r1.status, r2.status, r3.status, r4.status, r5.status, r6.status] == [201, 204, 200, 204, 404, 404] &&
  (Syntax.parseTurtle r3.body).toOption == some [⟨.iri ⟨"http://ex/s", rfl⟩, ⟨"http://ex/p", rfl⟩,
                                                 .literal (Literal.string "b")⟩]
-- HEAD: 200 with no body, or 404.
#guard
  let (s1, _) := serve ep0 {} "PUT" "/gsp/a" "" ttl doc1
  ((serve ep0 s1 "HEAD" "/gsp/a" "" [] "").2.status, (serve ep0 s1 "HEAD" "/gsp/a" "" [] "").2.body,
   (serve ep0 s1 "HEAD" "/gsp/b" "" [] "").2.status) == (200, "", 404)
-- The default graph always exists.
#guard (serve ep0 {} "GET" "/gsp" "default" [] "").2.status == 200
-- POST merges; POST to the store creates a graph and says where.
#guard
  let (s1, r1) := serve ep0 {} "POST" "/gsp/a" "" ttl doc1
  let (s2, r2) := serve ep0 s1 "POST" "/gsp/a" "" ttl doc2
  (r1.status, r2.status, (namedOrEmpty "http://www.example/gsp/a" s2).length) == (201, 204, 2)
#guard
  let (s1, r1) := serve ep0 {} "POST" "/gsp" "" ttl doc1
  r1.status == 201 && r1.headers == [("location", "http://www.example/gsp/graph-1")] &&
  (namedOrEmpty "http://www.example/gsp/graph-1" s1).length == 1
-- 415 for a media type the service does not read; 400 for bad Turtle.
#guard (serve ep0 {} "PUT" "/gsp/a" "" [("content-type", "text/html")] "<p/>").2.status == 415
#guard (serve ep0 {} "PUT" "/gsp/a" "" ttl "<http://ex/s> .").2.status == 400
-- Blank nodes of two POSTs stay two nodes.
#guard
  let (s1, _) := serve ep0 {} "POST" "/gsp/a" "" ttl "_:b <http://ex/p> \"a\" ."
  let (s2, _) := serve ep0 s1 "POST" "/gsp/a" "" ttl "_:b <http://ex/p> \"b\" ."
  (Graph.bnodes (namedOrEmpty "http://www.example/gsp/a" s2)).length == 2
-- §5.5 multipart/form-data: both parts land in the graph.
#guard
  let body := "--XY\r\nContent-Type: text/turtle\r\n\r\n" ++ doc1 ++ "\r\n--XY\r\n" ++
              "Content-Type: text/turtle\r\n\r\n" ++ doc2 ++ "\r\n--XY--\r\n"
  let (s1, r1) := serve ep0 {} "POST" "/gsp/a" "" [("content-type", "multipart/form-data; boundary=XY")] body
  r1.status == 201 && (namedOrEmpty "http://www.example/gsp/a" s1).length == 2

end L4Factoidal.SPARQL.GraphStoreService
